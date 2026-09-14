/-!
# The calendar: civil dates, ISO week dates, and one named tie-break

`Grain.lean` used to index the timeline with `d`, `d/7`, `d/30` and said so.
This module replaces that with the real thing: proleptic Gregorian civil dates
with leap years, and ISO 8601 week dates with the week-numbering year.

**The origin.**  A `Day` is a `Nat`: days since **0001-01-01** in the proleptic
Gregorian calendar.  Two consequences are worth stating, because both are load
bearing and neither is arbitrary:

* every `Day` is a real date — `ofDay` is total and always lands on a *valid*
  date, so there is no partial accessor and no default to fall back to;
* 0001-01-01 is a **Monday**, so `n % 7` *is* the weekday and `n / 7` *is* the
  ISO week ordinal.  Week boundaries need no offset constant.

**The one datum that is not derived.**  The weekday cycle has period 7 and
nothing in the Gregorian rules fixes its phase; one real-world fact must be put
in by hand.  Here it is the origin's weekday, and it enters through the
*definition* of `weekdayOf`.  It is cross-checked against three dates a reader
can verify independently (`weekday_1970_01_01`, `weekday_2000_01_01`,
`weekday_2026_09_07`); if the phase were wrong, all three would fail.

**A note on `Day`.**  `Day` is an abbreviation for `Nat`, and `omega` does not
see through it when it is the type argument of `=` or `≤`.  So `Day` appears
only in *parameter* positions here; every day-valued result is typed `Nat`.
Ignoring this produces "omega could not prove the goal" on statements that are
arithmetically trivial.

**The month table is data, not a generator.**  §4.1's carve-out applies:
`cumBefore` is a thirteen-entry table because month lengths are an arbitrary
list of facts.  Everything else here is derived from it and from the leap rule.

## The week → month tie-break, which is a CHOICE

An ISO week can straddle two civil months
(`a_week_can_straddle_two_civil_months`, with 2026-W36 = Aug 31 – Sep 6 as the
witness; `Grain.week_does_not_refine_month` says the same about the chain).  So "the month of week *w*" is not
determined by containment and something has to be named.

> **Chosen:** `monthOfIsoWeek w` is the civil month containing week `w`'s
> **Thursday**.

It is total, it is a function of `w` alone, and it generalises ISO 8601's own
rule — the standard already resolves the same straddle for *years* by the
Thursday, so resolving it for months the same way adds no new principle.  Its
stability is structural rather than a theorem: `monthOfIsoWeek : Nat → Nat` has
no `now` in its type, so there is no second argument two callers could differ
on.

**Rejected, as a name: "the month of today".**  It is written here as
`monthOfWeekByToday`, whose first argument is unused — the answer does not
depend on the week at all — and `monthOfWeekByToday_is_not_stable` exhibits one
week named by two different months depending on the day the command runs.
That is the *same* witness as the non-refinement, because it is the same fact
seen twice.  A file name that depends on when you looked is not a file name.

**What this tie-break is not: the close rule.**  `closeTo g now` files a close's
leftovers into the coarser region containing `now`, and that is right: a close
happens at a time, and `now` is the honest input.  `closeTo week now` and
`monthOfWeekByToday w now` are the same month (`rfl`) — one function in two
roles, right as a destination and wrong as a name.  Fork-point
`horizon::close_week` computes exactly that destination
(`YearMonth::from_date(cx.today())`, the `month/<current>#Demoted` of spec §6.3),
so the Rust **agrees** with the kernel's close rule and nothing about it is a
behaviour change.  *(Corrected 2026-09-12, stage 4 step 1: this header used to
call that Rust line the rejected alternative; see `kernel/README.md`'s stage-4
block and `Grain.closeTo_week_is_not_monthOfWeek`.)*  The tie-break answers a
different question — *name the month a given week belongs to* — which has no
`now` in it, and which nothing in the kernel yet asks.

## Instants, offsets and the zone (stage 5, step B1)

Sections 8 and 9 add time of day, which the log needs: an `Instant` (UTC seconds
and nanoseconds from this module's origin), an `Offset`, chrono's durations with
its leap-second rule, and the zone as a **table the host probes** — the kernel
carries no tz database.  `offsetAt` reads the table, `localDate` is the date a
log line is attributed to, and `instantOf` is the fork's `capacity::local_dt`.
Each section's header states what is ported and what was refuted on the way.
-/
-- The exhaustive `decide` lemmas over the month table run over 731 days and 416
-- (month, day) pairs.  They are checked by the **kernel** (`decide`),
-- not by `native_decide` -- same trust as `decide`, but the elaborator does not
-- also evaluate them, which is what these two budgets are for.
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace Tm

/-- A day: days since **0001-01-01**, proleptic Gregorian, which is a Monday.
Every `Nat` is a date, so nothing here is partial. -/
abbrev Day := Nat

namespace Cal

/-! ## 1. Leap years and the year table

Internally years are counted from **0000**-01-01, because year 0 is divisible
by 400 and so starts a 400-year era cleanly; `Day` is that count shifted by
`originShift`.  Nothing outside this section sees year 0. -/

/-- The Gregorian leap rule. -/
def isLeap (y : Nat) : Bool := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

/-- Days in year `y`. -/
def yearLen (y : Nat) : Nat := if isLeap y then 366 else 365

/-- Days from 0000-01-01 to `y`-01-01.  `(y+3)/4 + (y+399)/400 - (y+99)/100`
counts the leap years strictly before `y`, written so the subtraction never
truncates. -/
def ys (y : Nat) : Nat := 365 * y + (y + 3) / 4 + (y + 399) / 400 - (y + 99) / 100

theorem ys_zero : ys 0 = 0 := by decide
/-- Year 0 is a leap year, so 0001-01-01 is day 366 of the internal count. -/
theorem ys_one : ys 1 = 366 := by decide
/-- A 400-year era is 146097 days. -/
theorem ys_era_len : ys 400 = 146097 := by decide

/-- The era identity: shifting the year by a whole era shifts the day count by
a whole era.  Exact, for every `e` and `k`. -/
theorem ys_era (e k : Nat) : ys (400 * e + k) = 146097 * e + ys k := by
  unfold ys; omega

theorem q4 (y : Nat) : (y + 4) / 4 = (y + 3) / 4 + (if y % 4 = 0 then 1 else 0) := by
  split <;> omega
theorem q100 (y : Nat) : (y + 100) / 100 = (y + 99) / 100 + (if y % 100 = 0 then 1 else 0) := by
  split <;> omega
theorem q400 (y : Nat) : (y + 400) / 400 = (y + 399) / 400 + (if y % 400 = 0 then 1 else 0) := by
  split <;> omega

/-- The leap rule, as arithmetic: +1 for every fourth year, +1 back for every
four-hundredth, −1 for every hundredth. -/
theorem isLeap_arith (y : Nat) : (if isLeap y then (1:Nat) else 0)
    = (if y % 4 = 0 then 1 else 0) + (if y % 400 = 0 then 1 else 0)
        - (if y % 100 = 0 then 1 else 0) := by
  simp only [isLeap, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  split <;> split <;> split <;> split <;> omega

theorem yearLen_as_if (y : Nat) : yearLen y = 365 + (if isLeap y then 1 else 0) := by
  unfold yearLen; split <;> rfl

/-- **The year table steps by exactly the year's length.**  This is where the
leap rule and the day count are tied together; everything downstream uses it
and never re-derives it. -/
theorem ys_step (y : Nat) : ys (y + 1) = ys y + yearLen y := by
  have a := q4 y; have b := q100 y; have c := q400 y
  have l := isLeap_arith y
  have e : y + 1 + 3 = y + 4 := by omega
  have f : y + 1 + 99 = y + 100 := by omega
  have g : y + 1 + 399 = y + 400 := by omega
  have hif := yearLen_as_if y
  unfold ys
  rw [e, f, g, a, b, c, hif, l]
  split <;> split <;> split <;> omega

theorem yearLen_bounds (y : Nat) : 365 ≤ yearLen y ∧ yearLen y ≤ 366 := by
  unfold yearLen; split <;> omega

theorem ys_succ_bounds (y : Nat) : ys y + 365 ≤ ys (y + 1) ∧ ys (y + 1) ≤ ys y + 366 := by
  have := ys_step y; have := yearLen_bounds y; omega

theorem ys_mono : ∀ {a b : Nat}, a ≤ b → ys a ≤ ys b := by
  intro a b h
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge a (n + 1) with hn | hn
    · have := ih (by omega); have := ys_succ_bounds n; omega
    · have : a = n + 1 := by omega
      subst this; exact Nat.le_refl _

theorem ys_le (k : Nat) (h : k ≤ 400) : ys k ≤ 365 * k + 97 := by
  unfold ys; omega

theorem ys_ge (k : Nat) : 365 * k ≤ ys k := by
  unfold ys; omega

/-! ### Inverting the year table

`ys` has no closed-form inverse, but it is invertible by one *guess and one
correction*.  Within an era a year start is never more than 97 days ahead of
`365 * k`, so `r / 365` is either the right year of era or exactly one too many;
the `if` is the whole correction and `yoe_bracket` is the proof that one step
suffices.  No search, no fuel, no recursion. -/

/-- Year of era, from the day of era. -/
def yoe (r : Nat) : Nat := if ys (r / 365) ≤ r then r / 365 else r / 365 - 1

/-- The year containing internal day `z`. -/
def yearOfZ (z : Nat) : Nat := 400 * (z / 146097) + yoe (z % 146097)

theorem yoe_bracket (r : Nat) (h : r < 146097) : ys (yoe r) ≤ r ∧ r < ys (yoe r + 1) := by
  have hkr : 365 * (r / 365) ≤ r ∧ r < 365 * (r / 365) + 365 := by omega
  have hk400 : r / 365 ≤ 400 := by omega
  unfold yoe
  by_cases hc : ys (r / 365) ≤ r
  · rw [if_pos hc]
    exact ⟨hc, by have := ys_ge (r / 365 + 1); omega⟩
  · rw [if_neg hc]
    have hk1 : 1 ≤ r / 365 := by
      rcases Nat.eq_zero_or_pos (r / 365) with h0 | h0
      · rw [h0] at hc; simp [ys] at hc
      · exact h0
    have hkm : r / 365 - 1 + 1 = r / 365 := by omega
    refine ⟨?_, by rw [hkm]; omega⟩
    have := ys_le (r / 365 - 1) (by omega)
    omega

/-- **`yearOfZ` lands in the right year.**  Everything about civil dates is
downstream of this bracket. -/
theorem yearOfZ_bracket (z : Nat) : ys (yearOfZ z) ≤ z ∧ z < ys (yearOfZ z + 1) := by
  have hz : z = 146097 * (z / 146097) + z % 146097 := by omega
  have hb := yoe_bracket (z % 146097) (by omega)
  unfold yearOfZ
  refine ⟨by rw [ys_era]; omega, ?_⟩
  have he : 400 * (z / 146097) + yoe (z % 146097) + 1
          = 400 * (z / 146097) + (yoe (z % 146097) + 1) := by omega
  rw [he, ys_era]; omega

/-- And it is the *only* year that brackets `z`. -/
theorem yearOfZ_unique (z y : Nat) (h1 : ys y ≤ z) (h2 : z < ys (y + 1)) : yearOfZ z = y := by
  have hb := yearOfZ_bracket z
  rcases Nat.lt_trichotomy (yearOfZ z) y with h | h | h
  · have := ys_mono (show yearOfZ z + 1 ≤ y by omega); omega
  · exact h
  · have := ys_mono (show y + 1 ≤ yearOfZ z by omega); omega

theorem yearOfZ_mono {a b : Nat} (h : a ≤ b) : yearOfZ a ≤ yearOfZ b := by
  have ha := yearOfZ_bracket a
  have hb := yearOfZ_bracket b
  rcases Nat.lt_or_ge (yearOfZ b) (yearOfZ a) with hlt | hge
  · have := ys_mono (show yearOfZ b + 1 ≤ yearOfZ a by omega); omega
  · exact hge

/-! ## 2. The month table

This is §4.1's carve-out: month lengths are a list of arbitrary facts a human
types, so they are **data**.  `cumBefore` is that data; `monthLen`,
`monthOfDoy`, `dayOfDoy` and `doyOf` are all derived from it, and the `decide`
lemmas below check the derivation exhaustively over both year shapes — 731 days
and 416 (month, day) pairs, every one of them. -/

/-- Days before month `m` of a year, for `m ∈ [1,13]`.  **Data.** -/
def cumBefore (leap : Bool) (m : Nat) : Nat :=
  let l := if leap then 1 else 0
  match m with
  | 1  => 0       | 2  => 31      | 3  => 59 + l  | 4  => 90 + l
  | 5  => 120 + l | 6  => 151 + l | 7  => 181 + l | 8  => 212 + l
  | 9  => 243 + l | 10 => 273 + l | 11 => 304 + l | 12 => 334 + l
  | 13 => 365 + l
  | _  => 0

/-- Days in month `m`.  Outside `[1,12]` this is `0`, so a bad month cannot
carry a valid day. -/
def monthLen (leap : Bool) (m : Nat) : Nat := cumBefore leap (m + 1) - cumBefore leap m

/-- 0-based day of year → month. -/
def monthOfDoy (leap : Bool) (n : Nat) : Nat :=
  if n < cumBefore leap 2 then 1
  else if n < cumBefore leap 3 then 2
  else if n < cumBefore leap 4 then 3
  else if n < cumBefore leap 5 then 4
  else if n < cumBefore leap 6 then 5
  else if n < cumBefore leap 7 then 6
  else if n < cumBefore leap 8 then 7
  else if n < cumBefore leap 9 then 8
  else if n < cumBefore leap 10 then 9
  else if n < cumBefore leap 11 then 10
  else if n < cumBefore leap 12 then 11
  else 12

/-- 0-based day of year → day of month. -/
def dayOfDoy (leap : Bool) (n : Nat) : Nat := n - cumBefore leap (monthOfDoy leap n) + 1

/-- (month, day) → 0-based day of year. -/
def doyOf (leap : Bool) (m d : Nat) : Nat := cumBefore leap m + (d - 1)

theorem md_of_doy_common : ∀ n, n < 365 →
    1 ≤ monthOfDoy false n ∧ monthOfDoy false n ≤ 12 ∧
    doyOf false (monthOfDoy false n) (dayOfDoy false n) = n ∧
    1 ≤ dayOfDoy false n ∧ dayOfDoy false n ≤ monthLen false (monthOfDoy false n) := by
  decide

theorem md_of_doy_leap : ∀ n, n < 366 →
    1 ≤ monthOfDoy true n ∧ monthOfDoy true n ≤ 12 ∧
    doyOf true (monthOfDoy true n) (dayOfDoy true n) = n ∧
    1 ≤ dayOfDoy true n ∧ dayOfDoy true n ≤ monthLen true (monthOfDoy true n) := by
  decide

theorem doy_of_md_common : ∀ m, m < 13 → ∀ d, d < 32 →
    (1 ≤ m ∧ 1 ≤ d ∧ d ≤ monthLen false m) →
      doyOf false m d < 365 ∧ monthOfDoy false (doyOf false m d) = m
        ∧ dayOfDoy false (doyOf false m d) = d := by
  decide

theorem doy_of_md_leap : ∀ m, m < 13 → ∀ d, d < 32 →
    (1 ≤ m ∧ 1 ≤ d ∧ d ≤ monthLen true m) →
      doyOf true m d < 366 ∧ monthOfDoy true (doyOf true m d) = m
        ∧ dayOfDoy true (doyOf true m d) = d := by
  decide

theorem cumBefore_mono_common : ∀ a, a < 14 → ∀ b, b < 14 → a ≤ b →
    cumBefore false a ≤ cumBefore false b := by decide
theorem cumBefore_mono_leap : ∀ a, a < 14 → ∀ b, b < 14 → a ≤ b →
    cumBefore true a ≤ cumBefore true b := by decide
theorem monthLen_le_31_common : ∀ m, m < 13 → monthLen false m ≤ 31 := by decide
theorem monthLen_le_31_leap : ∀ m, m < 13 → monthLen true m ≤ 31 := by decide

theorem cumBefore_mono (l : Bool) {a b : Nat} (ha : a < 14) (hb : b < 14) (h : a ≤ b) :
    cumBefore l a ≤ cumBefore l b := by
  cases l
  · exact cumBefore_mono_common a ha b hb h
  · exact cumBefore_mono_leap a ha b hb h

theorem monthLen_le_31 (l : Bool) {m : Nat} (h : m < 13) : monthLen l m ≤ 31 := by
  cases l
  · exact monthLen_le_31_common m h
  · exact monthLen_le_31_leap m h

/-- The month table read forwards, for a `leap` that is not a literal. -/
theorem md_of_doy (l : Bool) (n : Nat) (h : n < 365 + (if l then 1 else 0)) :
    1 ≤ monthOfDoy l n ∧ monthOfDoy l n ≤ 12 ∧
    doyOf l (monthOfDoy l n) (dayOfDoy l n) = n ∧
    1 ≤ dayOfDoy l n ∧ dayOfDoy l n ≤ monthLen l (monthOfDoy l n) := by
  cases l
  · exact md_of_doy_common n (by simpa using h)
  · exact md_of_doy_leap n (by simpa using h)

/-- And backwards. -/
theorem doy_of_md (l : Bool) (m d : Nat) (hm1 : 1 ≤ m) (hm2 : m ≤ 12) (hd1 : 1 ≤ d)
    (hd2 : d ≤ monthLen l m) :
    doyOf l m d < 365 + (if l then 1 else 0) ∧ monthOfDoy l (doyOf l m d) = m
      ∧ dayOfDoy l (doyOf l m d) = d := by
  have h31 : d < 32 := by have := monthLen_le_31 l (show m < 13 by omega); omega
  cases l
  · have := doy_of_md_common m (by omega) d h31 ⟨hm1, hd1, hd2⟩
    simpa using this
  · have := doy_of_md_leap m (by omega) d h31 ⟨hm1, hd1, hd2⟩
    simpa using this

/-- The month table, as a bracket: a day of year sits inside its month. -/
theorem month_bracket (l : Bool) (n : Nat) (h : n < 365 + (if l then 1 else 0)) :
    1 ≤ monthOfDoy l n ∧ monthOfDoy l n ≤ 12 ∧
      cumBefore l (monthOfDoy l n) ≤ n ∧ n < cumBefore l (monthOfDoy l n + 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := md_of_doy l n h
  unfold doyOf at h3
  unfold monthLen at h5
  have := cumBefore_mono l (show monthOfDoy l n < 14 by omega)
    (show monthOfDoy l n + 1 < 14 by omega) (by omega)
  exact ⟨h1, h2, by omega, by omega⟩

/-- Days of year are ordered the same way as months. -/
theorem monthOfDoy_mono (l : Bool) {a b : Nat} (h : a ≤ b)
    (hb : b < 365 + (if l then 1 else 0)) : monthOfDoy l a ≤ monthOfDoy l b := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := month_bracket l a (by omega)
  obtain ⟨hb1, hb2, hb3, hb4⟩ := month_bracket l b hb
  rcases Nat.lt_or_ge (monthOfDoy l b) (monthOfDoy l a) with hlt | hge
  · have := cumBefore_mono l (show monthOfDoy l b + 1 < 14 by omega)
      (show monthOfDoy l a < 14 by omega) (by omega)
    omega
  · exact hge

/-! ## 3. Civil dates, and the round trip

The load-bearing theorem of the module: `toDay` and `ofDay` are mutually
inverse, `ofDay` always produces a **valid** date, and validity is decidable.
Following the kernel's three-tier rule, validity is a `Bool` predicate and
`ValidDate` is the `Subtype` — no dependent proof field inside the record. -/

structure Date where
  year  : Nat
  month : Nat
  day   : Nat
deriving DecidableEq, Repr, Inhabited

/-- Decidable validity: a real year (≥ 1, so there is no year 0 and no ISO week
before week 1 of year 1), a real month, and a day the month has. -/
def Date.valid (d : Date) : Bool :=
  decide (1 ≤ d.year) && decide (1 ≤ d.month) && decide (d.month ≤ 12) &&
  decide (1 ≤ d.day) && decide (d.day ≤ monthLen (isLeap d.year) d.month)

/-- The only way in. -/
abbrev ValidDate := { d : Date // Date.valid d = true }

theorem valid_iff (d : Date) : Date.valid d = true ↔
    (1 ≤ d.year ∧ 1 ≤ d.month ∧ d.month ≤ 12 ∧ 1 ≤ d.day ∧
      d.day ≤ monthLen (isLeap d.year) d.month) := by
  simp [Date.valid, and_assoc]

/-- Days from 0000-01-01 to 0001-01-01: the shift between the internal count
and `Day`. -/
def originShift : Nat := 366

/-- Internal day number of a date (from 0000-01-01). -/
def zOf (d : Date) : Nat := ys d.year + doyOf (isLeap d.year) d.month d.day

/-- Civil date → `Day`. -/
def toDay (d : Date) : Nat := zOf d - originShift

/-- Internal day number → civil date. -/
def dateOfZ (z : Nat) : Date :=
  ⟨yearOfZ z, monthOfDoy (isLeap (yearOfZ z)) (z - ys (yearOfZ z)),
    dayOfDoy (isLeap (yearOfZ z)) (z - ys (yearOfZ z))⟩

/-- `Day` → civil date.  Total: every `Nat` names a date. -/
def ofDay (n : Day) : Date := dateOfZ (n + originShift)

theorem ofDay_year (n : Nat) : (ofDay n).year = yearOfZ (n + originShift) := rfl
theorem ofDay_month (n : Nat) : (ofDay n).month =
    monthOfDoy (isLeap (yearOfZ (n + originShift)))
      (n + originShift - ys (yearOfZ (n + originShift))) := rfl

/-- The day of year of an internal day number is inside its year. -/
theorem doy_in_range (z : Nat) :
    z - ys (yearOfZ z) < 365 + (if isLeap (yearOfZ z) then 1 else 0) := by
  have hb := yearOfZ_bracket z
  have hs := ys_step (yearOfZ z)
  have := yearLen_as_if (yearOfZ z)
  omega

/-- Below the origin shift there is no year ≥ 1, and above it there always is. -/
theorem yearOfZ_ge_one (z : Nat) (h : originShift ≤ z) : 1 ≤ yearOfZ z := by
  have hb := yearOfZ_bracket z
  rcases Nat.eq_zero_or_pos (yearOfZ z) with h0 | h0
  · rw [h0, ys_one] at hb; unfold originShift at h; omega
  · exact h0

/-- **`ofDay` is total onto valid dates.**  There is no `Day` whose date has to
be repaired, defaulted or rejected. -/
theorem ofDay_valid (n : Nat) : Date.valid (ofDay n) = true := by
  obtain ⟨h1, h2, _, h4, h5⟩ := md_of_doy _ _ (doy_in_range (n + originShift))
  rw [valid_iff]
  exact ⟨yearOfZ_ge_one _ (by unfold originShift; omega), h1, h2, h4, h5⟩

/-- **Round trip, one way: `Day → Date → Day`.** -/
theorem toDay_ofDay (n : Nat) : toDay (ofDay n) = n := by
  obtain ⟨_, _, h3, _, _⟩ := md_of_doy _ _ (doy_in_range (n + originShift))
  have hb := yearOfZ_bracket (n + originShift)
  show zOf (dateOfZ (n + originShift)) - originShift = n
  unfold zOf dateOfZ
  simp only []
  rw [h3]
  unfold originShift at *
  omega

/-- Every valid date's internal day number brackets in its own year. -/
theorem zOf_bracket (d : Date) (h : Date.valid d = true) :
    ys d.year ≤ zOf d ∧ zOf d < ys (d.year + 1) := by
  rw [valid_iff] at h
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := h
  obtain ⟨hlt, _, _⟩ := doy_of_md (isLeap d.year) d.month d.day hm1 hm2 hd1 hd2
  have hs := ys_step d.year
  have := yearLen_as_if d.year
  unfold zOf
  omega

theorem originShift_le_zOf (d : Date) (h : Date.valid d = true) : originShift ≤ zOf d := by
  rw [valid_iff] at h
  have := ys_mono (show 1 ≤ d.year by omega)
  rw [ys_one] at this
  unfold zOf originShift
  omega

/-- **Round trip, the other way: `Date → Day → Date`, on valid dates.**  This is
the theorem everything else in the module rests on. -/
theorem ofDay_toDay (d : Date) (h : Date.valid d = true) : ofDay (toDay d) = d := by
  have hv := h
  rw [valid_iff] at hv
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := hv
  have hb := zOf_bracket d h
  have hz366 := originShift_le_zOf d h
  have hyz : yearOfZ (zOf d) = d.year := yearOfZ_unique _ _ hb.1 hb.2
  have hrestore : toDay d + originShift = zOf d := by unfold toDay; omega
  have hdoy : zOf d - ys d.year = doyOf (isLeap d.year) d.month d.day := by unfold zOf; omega
  obtain ⟨_, hm, hdd⟩ := doy_of_md (isLeap d.year) d.month d.day hm1 hm2 hd1 hd2
  show dateOfZ (toDay d + originShift) = d
  unfold dateOfZ
  rw [hrestore, hyz, hdoy, hm, hdd]

/-- The round trip packaged on the subtype: `Day` and `ValidDate` carry the same
information. -/
def dateOf (n : Day) : ValidDate := ⟨ofDay n, ofDay_valid n⟩
def dayOf (d : ValidDate) : Nat := toDay d.val

theorem dayOf_dateOf (n : Nat) : dayOf (dateOf n) = n := toDay_ofDay n
theorem dateOf_dayOf (d : ValidDate) : dateOf (dayOf d) = d :=
  Subtype.ext (ofDay_toDay d.val d.property)

/-- Days are ordered the same way as dates: a later year is a later day.
(Injectivity of `toDay` on valid dates is `ofDay_toDay`; this is the order
half.) -/
theorem toDay_lt_of_year_lt (a b : Date) (ha : Date.valid a = true) (hb : Date.valid b = true)
    (h : a.year < b.year) : toDay a < toDay b := by
  have hba := zOf_bracket a ha
  have hbb := zOf_bracket b hb
  have := ys_mono (show a.year + 1 ≤ b.year by omega)
  have := originShift_le_zOf a ha
  unfold toDay; omega

/-! ### The calendar, checked against dates a reader can verify

Spot checks are not the proof — the round trip is — but a table can be
self-consistently wrong, and these say it is not. -/

theorem leap_2000 : isLeap 2000 = true := by decide
theorem leap_1900 : isLeap 1900 = false := by decide
theorem leap_2024 : isLeap 2024 = true := by decide
theorem leap_2026 : isLeap 2026 = false := by decide
theorem feb_2024_has_29 : monthLen (isLeap 2024) 2 = 29 := by decide
theorem feb_1900_has_28 : monthLen (isLeap 1900) 2 = 28 := by decide
theorem feb_30_is_not_a_date : Date.valid ⟨2024, 2, 30⟩ = false := by decide
theorem feb_29_2024_is_a_date : Date.valid ⟨2024, 2, 29⟩ = true := by decide
theorem feb_29_2023_is_not_a_date : Date.valid ⟨2023, 2, 29⟩ = false := by decide
theorem month_13_is_not_a_date : Date.valid ⟨2026, 13, 1⟩ = false := by decide
theorem month_0_is_not_a_date : Date.valid ⟨2026, 0, 1⟩ = false := by decide
theorem year_0_is_not_a_date : Date.valid ⟨0, 1, 1⟩ = false := by decide

/-- The Unix epoch, as a `Day`.  A host counting from 1970 adds this. -/
def unixEpoch : Nat := toDay ⟨1970, 1, 1⟩
theorem unixEpoch_eq : unixEpoch = 719162 := by decide

theorem after_feb28_2024 : ofDay (toDay ⟨2024, 2, 28⟩ + 1) = ⟨2024, 2, 29⟩ := by decide
theorem after_feb28_2023 : ofDay (toDay ⟨2023, 2, 28⟩ + 1) = ⟨2023, 3, 1⟩ := by decide
theorem year_2024_is_366 : toDay ⟨2025, 1, 1⟩ - toDay ⟨2024, 1, 1⟩ = 366 := by decide
theorem year_1900_is_365 : toDay ⟨1901, 1, 1⟩ - toDay ⟨1900, 1, 1⟩ = 365 := by decide
theorem year_2000_is_366 : toDay ⟨2001, 1, 1⟩ - toDay ⟨2000, 1, 1⟩ = 366 := by decide

/-! ## 4. The weekday

**The one datum.**  0001-01-01 is a Monday.  The Gregorian rules fix the
*length* of everything but not the *phase* of the seven-day cycle, so exactly
one real-world fact has to be supplied, and this is it. -/

inductive Weekday | monday | tuesday | wednesday | thursday | friday | saturday | sunday
deriving DecidableEq, Repr, Inhabited

def Weekday.ofIndex : Nat → Weekday
  | 0 => .monday | 1 => .tuesday | 2 => .wednesday | 3 => .thursday
  | 4 => .friday | 5 => .saturday | _ => .sunday

/-- The weekday of a day.  Day 0 is 0001-01-01, a Monday, so this is `n % 7`
with no offset — the origin was chosen to make it so. -/
def weekdayOf (n : Day) : Weekday := Weekday.ofIndex (n % 7)

theorem weekday_origin : weekdayOf 0 = .monday := by decide
/-- Cross-checks against three dates a reader can verify on any calendar.  If
the phase of the seven-day cycle were wrong, all three would fail. -/
theorem weekday_1970_01_01 : weekdayOf (toDay ⟨1970, 1, 1⟩) = .thursday := by decide
theorem weekday_2000_01_01 : weekdayOf (toDay ⟨2000, 1, 1⟩) = .saturday := by decide
theorem weekday_2026_09_07 : weekdayOf (toDay ⟨2026, 9, 7⟩) = .monday := by decide

theorem weekdayOf_thursday_iff (n : Nat) : weekdayOf n = .thursday ↔ n % 7 = 3 := by
  unfold weekdayOf
  have h : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5
      ∨ n % 7 = 6 := by omega
  rcases h with h | h | h | h | h | h | h <;> rw [h] <;> decide

theorem weekdayOf_wednesday_iff (n : Nat) : weekdayOf n = .wednesday ↔ n % 7 = 2 := by
  unfold weekdayOf
  have h : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5
      ∨ n % 7 = 6 := by omega
  rcases h with h | h | h | h | h | h | h <;> rw [h] <;> decide

/-! ## 5. ISO 8601 week dates

The ISO week-numbering year is **not** the civil year: early January can belong
to the previous ISO year and late December to the next.  The standard resolves
it by the week's Thursday, and so does this. -/

/-- The ISO week ordinal of a day: a monotone number, constant on ISO weeks.  It
is `n / 7` because day 0 is a Monday. -/
def weekOrdinal (n : Day) : Nat := n / 7

/-- The Thursday of week `w`. -/
def thursdayOf (w : Nat) : Nat := 7 * w + 3

theorem thursdayOf_is_thursday (w : Nat) : weekdayOf (thursdayOf w) = .thursday := by
  rw [weekdayOf_thursday_iff]; unfold thursdayOf; omega
theorem thursdayOf_in_week (w : Nat) : weekOrdinal (thursdayOf w) = w := by
  unfold weekOrdinal thursdayOf; omega
theorem weekOrdinal_mono {a b : Nat} (h : a ≤ b) : weekOrdinal a ≤ weekOrdinal b := by
  unfold weekOrdinal; omega
/-- A week holds exactly seven days, and they are the ones from its Monday. -/
theorem weekOrdinal_eq_iff (n w : Nat) : weekOrdinal n = w ↔ (7 * w ≤ n ∧ n < 7 * w + 7) := by
  unfold weekOrdinal; omega

/-- Jan 1 of year `y`, as a `Day` (meaningful for `y ≥ 1`). -/
def jan1 (y : Nat) : Nat := ys y - originShift

theorem jan1_shift (y : Nat) (h : 1 ≤ y) : jan1 y + originShift = ys y := by
  have := ys_mono h; rw [ys_one] at this
  unfold jan1 originShift at *; omega

theorem jan1_step (y : Nat) (h : 1 ≤ y) : jan1 (y + 1) = jan1 y + yearLen y := by
  have h1 := jan1_shift y h
  have h2 := jan1_shift (y + 1) (by omega)
  have := ys_step y
  omega

/-- `jan1` is January 1st: it agrees with `toDay` on the date, unconditionally. -/
theorem jan1_toDay (y : Nat) : toDay ⟨y, 1, 1⟩ = jan1 y := by
  show zOf ⟨y, 1, 1⟩ - originShift = jan1 y
  unfold zOf jan1 doyOf cumBefore
  simp

/-- An ISO week date. -/
structure IsoDate where
  year    : Nat     -- the ISO week-numbering year
  week    : Nat     -- 1 … 53
  weekday : Nat     -- 1 = Monday … 7 = Sunday
deriving DecidableEq, Repr, Inhabited

/-- **The ISO week date of a day**: the week-numbering year is the civil year of
the week's Thursday, and the week number counts Thursdays inside that year. -/
def isoOf (n : Day) : IsoDate :=
  ⟨yearOfZ (thursdayOf (weekOrdinal n) + originShift),
    (thursdayOf (weekOrdinal n)
      - jan1 (yearOfZ (thursdayOf (weekOrdinal n) + originShift))) / 7 + 1,
    n % 7 + 1⟩

/-- The number of ISO weeks in ISO year `y`: the number of Thursdays in the
civil year `y`, since every ISO week of year `y` contains exactly one. -/
def isoWeeksIn (y : Nat) : Nat := (jan1 (y + 1) + 3) / 7 - (jan1 y + 3) / 7

/-- The Monday that starts ISO week 1 of year `y`: the Monday of the week
containing January 4th, equivalently of the year's first Thursday. -/
def isoWeek1Monday (y : Nat) : Nat := 7 * ((jan1 y + 3) / 7)

/-- An ISO week date → the day. -/
def dayOfIso (d : IsoDate) : Nat :=
  isoWeek1Monday d.year + 7 * (d.week - 1) + (d.weekday - 1)

theorem isoOf_year (n : Nat) :
    (isoOf n).year = yearOfZ (thursdayOf (weekOrdinal n) + originShift) := rfl
theorem isoOf_week (n : Nat) :
    (isoOf n).week = (thursdayOf (weekOrdinal n) - jan1 (isoOf n).year) / 7 + 1 := rfl
theorem isoOf_weekday (n : Nat) : (isoOf n).weekday = n % 7 + 1 := rfl

/-- The bracket for the Thursday: it lands inside the civil year `isoOf` names,
and that year is ≥ 1. -/
theorem isoOf_year_bracket (n : Nat) :
    1 ≤ (isoOf n).year ∧
    jan1 (isoOf n).year ≤ thursdayOf (weekOrdinal n) ∧
    thursdayOf (weekOrdinal n) < jan1 ((isoOf n).year + 1) := by
  have hb := yearOfZ_bracket (thursdayOf (weekOrdinal n) + originShift)
  rw [← isoOf_year n] at hb
  have hy1 : 1 ≤ (isoOf n).year := by
    rw [isoOf_year]
    exact yearOfZ_ge_one _ (by unfold thursdayOf originShift; omega)
  have hj := jan1_shift (isoOf n).year hy1
  have hj1 := jan1_shift ((isoOf n).year + 1) (by omega)
  exact ⟨hy1, by omega, by omega⟩

/-- `isoOf` gives a weekday in 1…7, Monday first. -/
theorem isoOf_weekday_range (n : Nat) : 1 ≤ (isoOf n).weekday ∧ (isoOf n).weekday ≤ 7 := by
  rw [isoOf_weekday]; omega

/-- **The week number is at least 1 and never past the year's own week count.**
That is the honest form of "a year has 52 or 53 ISO weeks": no day is ever in a
week its ISO year does not have. -/
theorem isoOf_week_range (n : Nat) :
    1 ≤ (isoOf n).week ∧ (isoOf n).week ≤ isoWeeksIn (isoOf n).year := by
  obtain ⟨hy1, hlo, hhi⟩ := isoOf_year_bracket n
  have hw := isoOf_week n
  have hthu : thursdayOf (weekOrdinal n) = 7 * (n / 7) + 3 := rfl
  refine ⟨by omega, ?_⟩
  unfold isoWeeksIn
  rw [hw]
  omega

/-- A year has 52 or 53 ISO weeks — never fewer, never more. -/
theorem isoWeeksIn_52_or_53 (y : Nat) (h : 1 ≤ y) :
    isoWeeksIn y = 52 ∨ isoWeeksIn y = 53 := by
  have h1 := jan1_step y h
  have h2 := yearLen_bounds y
  unfold isoWeeksIn
  omega

/-- **And exactly when it has 53**: the classic rule, derived rather than
tabulated.  A year has 53 ISO weeks iff it starts on a Thursday, or it is a leap
year starting on a Wednesday. -/
theorem isoWeeksIn_53_iff (y : Nat) (h : 1 ≤ y) :
    isoWeeksIn y = 53 ↔
      (weekdayOf (jan1 y) = .thursday ∨ (isLeap y = true ∧ weekdayOf (jan1 y) = .wednesday)) := by
  have h1 := jan1_step y h
  have hlen := yearLen_as_if y
  rw [weekdayOf_thursday_iff, weekdayOf_wednesday_iff]
  unfold isoWeeksIn
  cases hl : isLeap y
  · rw [hl] at hlen; simp only [Bool.false_eq_true, false_and, or_false, if_false] at *
    omega
  · rw [hl] at hlen; simp only [true_and, if_true] at *
    omega

/-- ISO week 1 starts on or before January 4th and on or after December 29th. -/
theorem isoWeek1Monday_bracket (y : Nat) :
    jan1 y ≤ isoWeek1Monday y + 3 ∧ isoWeek1Monday y ≤ jan1 y + 3 := by
  unfold isoWeek1Monday; omega

/-- **The ISO coordinate system is faithful.**  Every day round trips through
its ISO week date, so `2026-W37-1` names one day and no other. -/
theorem dayOfIso_isoOf (n : Nat) : dayOfIso (isoOf n) = n := by
  obtain ⟨hy1, hlo, hhi⟩ := isoOf_year_bracket n
  have hw := isoOf_week n
  have hd := isoOf_weekday n
  have hthu : thursdayOf (weekOrdinal n) = 7 * (n / 7) + 3 := rfl
  unfold dayOfIso isoWeek1Monday
  rw [hw, hd]
  omega

/-- And the other way, on the valid range: a well-formed ISO triple names a day
whose ISO date is that triple. -/
theorem isoOf_dayOfIso (d : IsoDate) (hy : 1 ≤ d.year)
    (hw1 : 1 ≤ d.week) (hw2 : d.week ≤ isoWeeksIn d.year)
    (hd1 : 1 ≤ d.weekday) (hd2 : d.weekday ≤ 7) : isoOf (dayOfIso d) = d := by
  have hstep := jan1_step d.year hy
  have hlen := yearLen_bounds d.year
  have hm : dayOfIso d = 7 * ((jan1 d.year + 3) / 7 + (d.week - 1)) + (d.weekday - 1) := by
    unfold dayOfIso isoWeek1Monday; omega
  have hwk : weekOrdinal (dayOfIso d) = (jan1 d.year + 3) / 7 + (d.week - 1) := by
    unfold weekOrdinal; rw [hm]; omega
  have hthu : thursdayOf (weekOrdinal (dayOfIso d))
            = 7 * ((jan1 d.year + 3) / 7 + (d.week - 1)) + 3 := by
    unfold thursdayOf; rw [hwk]
  have hj := jan1_shift d.year hy
  have hj1 := jan1_shift (d.year + 1) (by omega)
  have hyear : yearOfZ (thursdayOf (weekOrdinal (dayOfIso d)) + originShift) = d.year := by
    refine yearOfZ_unique _ _ ?_ ?_
    · rw [hthu]; omega
    · rw [hthu]; unfold isoWeeksIn at hw2; omega
  have hy' : (isoOf (dayOfIso d)).year = d.year := hyear
  have hw' : (isoOf (dayOfIso d)).week = d.week := by
    rw [isoOf_week, hy', hthu]; unfold isoWeeksIn at hw2; omega
  have hd' : (isoOf (dayOfIso d)).weekday = d.weekday := by
    rw [isoOf_weekday, hm]; omega
  cases d
  cases h : isoOf (dayOfIso _)
  simp_all

/-! ### The neighbouring-ISO-year cases, on real dates

These are exactly the cases a naive "week number of the civil year" gets wrong,
and they are the file names §2 and §4.3 write. -/

/-- The spec's own example: 2026-09-07 is Monday of 2026-W37. -/
theorem iso_2026_09_07 : isoOf (toDay ⟨2026, 9, 7⟩) = ⟨2026, 37, 1⟩ := by decide
/-- 2026 starts on a Thursday, so it has 53 ISO weeks … -/
theorem iso_2026_has_53_weeks : isoWeeksIn 2026 = 53 := by decide
/-- … and 2027-01-01 falls in the last of them: an ISO year *before* its civil
one. -/
theorem iso_2027_01_01 : isoOf (toDay ⟨2027, 1, 1⟩) = ⟨2026, 53, 5⟩ := by decide
/-- The mirror case: late December belongs to the *next* ISO year. -/
theorem iso_2025_12_29 : isoOf (toDay ⟨2025, 12, 29⟩) = ⟨2026, 1, 1⟩ := by decide
/-- 2020 was a leap year starting on a Wednesday — the second 53-week shape. -/
theorem iso_2020_has_53_weeks : isoWeeksIn 2020 = 53 := by decide
theorem iso_2019_has_52_weeks : isoWeeksIn 2019 = 52 := by decide
theorem iso_2021_01_01 : isoOf (toDay ⟨2021, 1, 1⟩) = ⟨2020, 53, 5⟩ := by decide
/-- The ISO year and the civil year disagree here, which is the whole point. -/
theorem iso_year_can_differ_from_civil_year :
    (isoOf (toDay ⟨2027, 1, 1⟩)).year ≠ (ofDay (toDay ⟨2027, 1, 1⟩)).year := by decide

/-! ## 6. The civil month as a period index -/

/-- The civil month of a day, as a monotone ordinal: `12 * (year - 1) + month - 1`. -/
def monthOrdinal (n : Day) : Nat := 12 * ((ofDay n).year - 1) + ((ofDay n).month - 1)

theorem monthOrdinal_origin : monthOrdinal 0 = 0 := by decide

/-- Time only moves months forward. -/
theorem monthOrdinal_mono {a b : Nat} (h : a ≤ b) : monthOrdinal a ≤ monthOrdinal b := by
  have hy := yearOfZ_mono (show a + originShift ≤ b + originShift by omega)
  have hba := month_bracket _ _ (doy_in_range (a + originShift))
  have hbb := month_bracket _ _ (doy_in_range (b + originShift))
  have hya := yearOfZ_ge_one (a + originShift) (by unfold originShift; omega)
  unfold monthOrdinal
  rw [ofDay_year, ofDay_year, ofDay_month, ofDay_month]
  rcases Nat.lt_or_ge (yearOfZ (a + originShift)) (yearOfZ (b + originShift)) with hlt | hge
  · omega
  · have heq : yearOfZ (a + originShift) = yearOfZ (b + originShift) := by omega
    have hbrA := yearOfZ_bracket (a + originShift)
    have hbrB := yearOfZ_bracket (b + originShift)
    have hdle : a + originShift - ys (yearOfZ (b + originShift))
              ≤ b + originShift - ys (yearOfZ (b + originShift)) := by omega
    have hmono := monthOfDoy_mono (isLeap (yearOfZ (b + originShift))) hdle
      (doy_in_range (b + originShift))
    rw [heq]
    omega

theorem monthOrdinal_2026_09 : monthOrdinal (toDay ⟨2026, 9, 7⟩) = 12 * 2025 + 8 := by decide

/-! ## 7. The week → month tie-break

The module header states the choice and the alternative it rejects.  Here is the
evidence for both. -/

/-- **A week can straddle two civil months**, so week does not refine month and
a tie-break is forced.  Witness: 2026-W36 runs Aug 31 – Sep 6. -/
theorem a_week_can_straddle_two_civil_months :
    ∃ a b : Nat, weekOrdinal a = weekOrdinal b ∧ monthOrdinal a ≠ monthOrdinal b :=
  ⟨toDay ⟨2026, 8, 31⟩, toDay ⟨2026, 9, 6⟩, by decide, by decide⟩

/-- **The chosen tie-break**: the civil month containing the week's Thursday.
There is no `now` in the type, which is what "stable" means here. -/
def monthOfIsoWeek (w : Nat) : Nat := monthOrdinal (thursdayOf w)

/-- **The rejected alternative, as a name for a week's month**, written down: the
month of *today*.  The week argument is unused, which is already the whole
objection.  (As a close *destination* the same month is right — it is
`closeTo week now`, and what `horizon::close_week` computes; see the header.) -/
def monthOfWeekByToday (_w : Nat) (now : Day) : Nat := monthOrdinal now

/-- And here it is failing: one week, two days inside it, two different months.
Same witness as `week_does_not_refine_month`, because it is the same fact. -/
theorem monthOfWeekByToday_is_not_stable :
    ∃ (w : Nat) (now now' : Nat), weekOrdinal now = w ∧ weekOrdinal now' = w ∧
      monthOfWeekByToday w now ≠ monthOfWeekByToday w now' :=
  ⟨weekOrdinal (toDay ⟨2026, 8, 31⟩), toDay ⟨2026, 8, 31⟩, toDay ⟨2026, 9, 6⟩,
    rfl, by decide, by decide⟩

/-- The month it picks is one the week actually meets — by construction, since
the Thursday is in both.  Stated because a tie-break that named a month the week
never touches would be a legal function and a wrong one. -/
theorem monthOfIsoWeek_is_met (w : Nat) :
    ∃ d : Nat, weekOrdinal d = w ∧ monthOrdinal d = monthOfIsoWeek w :=
  ⟨thursdayOf w, thursdayOf_in_week w, rfl⟩

/-- It never runs backwards. -/
theorem monthOfIsoWeek_mono {a b : Nat} (h : a ≤ b) : monthOfIsoWeek a ≤ monthOfIsoWeek b :=
  monthOrdinal_mono (by unfold thursdayOf; omega)

/-- 2026-W36 straddles August and September; the Thursday rule files it under
September, while 2026-W35 (Aug 24–30) stays in August. -/
theorem monthOfIsoWeek_W36 :
    monthOfIsoWeek (weekOrdinal (toDay ⟨2026, 8, 31⟩)) = monthOrdinal (toDay ⟨2026, 9, 1⟩) := by
  decide
theorem monthOfIsoWeek_W35 :
    monthOfIsoWeek (weekOrdinal (toDay ⟨2026, 8, 24⟩)) = monthOrdinal (toDay ⟨2026, 8, 1⟩) := by
  decide

/-! ## 8. Instants and offsets (stage 5, step B1; design §5.2)

A log line's `t` is an instant with the offset it was written in, and the replay
does arithmetic on instants: minutes between two of them, seconds since a wake,
an idle's start `min` minutes before its stamp.  That arithmetic belongs here,
beside `Day` (AGENTS §8.3's trap), and it is **chrono 0.4.45's**, ported, because
parity against the fork point is the acceptance.

**An instant** is UTC seconds since 0001-01-01T00:00:00Z, the origin of `Day`,
plus nanoseconds, so `t.sec / 86400` is the UTC `Day`.  chrono represents a leap
second as a nanosecond count of 1,000,000,000 or more on second 59 of a minute
(`NaiveTime`'s `frac`), and so does `Instant.wf`.

**Its order is chrono's**: `DateTime` compares its UTC `(secs, frac)`
lexicographically.  That is **not** the order of `Instant.nanos`: a leap second's
nanosecond count passes the next second's
(`the_instant_order_is_not_the_nanos_order`); the two agree off a leap second
(`Instant.lt_iff_nanos_off_a_leap_second`).

**Its durations are chrono's too**, and chrono's leap-second rule is not
arithmetic on nanoseconds: `NaiveTime::signed_duration_since` counts a leap
second only when the other side is a later second *of the same day*, so a leap
second counts before 03:00:00 and does not count before midnight
(`the_leap_second_counts_within_a_day_but_not_across_midnight`).  `durationBetween`
is that function, written in its date and time halves as chrono writes it.

**Day-valued results are typed `Nat`**, never `Day` (the `omega` trap in this
file's header). -/

/-- An instant: UTC seconds since 0001-01-01T00:00:00Z, and nanoseconds. -/
structure Instant where
  sec : Nat
  ns  : Nat
deriving DecidableEq, Repr

/-- chrono's representable instants: a nanosecond count below two seconds, at or
above one second only on second 59 of a minute (a leap second), and a year of at
most 9999 (R10; `the_witness_seconds_are_the_dates_they_name` checks the bound is
0001-01-01 plus the days to 10000-01-01). -/
def Instant.wf (i : Instant) : Bool :=
  decide (i.ns < 2000000000) && (decide (i.ns < 1000000000) || i.sec % 60 == 59)
    && decide (i.sec < 315537897600)

abbrev VInstant := { i : Instant // i.wf = true }

/-- The only constructor a decoder uses (R10). -/
def mkInstant? (sec ns : Nat) : Option VInstant :=
  if h : Instant.wf ⟨sec, ns⟩ = true then some ⟨⟨sec, ns⟩, h⟩ else none

/-- Nanoseconds since the origin.  Not the order, and not chrono's duration: see
the section header. -/
def Instant.nanos (i : Instant) : Nat := i.sec * 1000000000 + i.ns

/-- chrono's order: `(sec, ns)` lexicographically. -/
instance : LT Instant := ⟨fun a b => a.sec < b.sec ∨ (a.sec = b.sec ∧ a.ns < b.ns)⟩
instance : LE Instant := ⟨fun a b => a.sec < b.sec ∨ (a.sec = b.sec ∧ a.ns ≤ b.ns)⟩
instance (a b : Instant) : Decidable (a < b) := inferInstanceAs (Decidable (_ ∨ _))
instance (a b : Instant) : Decidable (a ≤ b) := inferInstanceAs (Decidable (_ ∨ _))

theorem Instant.lt_iff (a b : Instant) : a < b ↔ (a.sec < b.sec ∨ (a.sec = b.sec ∧ a.ns < b.ns)) :=
  Iff.rfl
theorem Instant.le_iff (a b : Instant) : a ≤ b ↔ (a.sec < b.sec ∨ (a.sec = b.sec ∧ a.ns ≤ b.ns)) :=
  Iff.rfl
theorem Instant.lt_irrefl (a : Instant) : ¬ a < a := by
  rw [Instant.lt_iff]; omega
theorem Instant.lt_trans {a b c : Instant} (h₁ : a < b) (h₂ : b < c) : a < c := by
  rw [Instant.lt_iff] at *; omega
theorem Instant.not_lt (a b : Instant) : ¬ a < b ↔ b ≤ a := by
  rw [Instant.lt_iff, Instant.le_iff]; omega
theorem Instant.le_total (a b : Instant) : a ≤ b ∨ b ≤ a := by
  rw [Instant.le_iff, Instant.le_iff]; omega
theorem Instant.le_antisymm {a b : Instant} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  obtain ⟨as, an⟩ := a
  obtain ⟨bs, bn⟩ := b
  simp only [Instant.le_iff] at h₁ h₂
  simp only [Instant.mk.injEq]; omega

/-- **Refuted** (design §5.2 lists `Instant.lt_iff_nanos`): chrono's order is not
the order of nanosecond counts.  A leap second `…:59` plus 1.5 s is before the
next second in chrono's order and after it in nanoseconds.  Both instants are
representable. -/
theorem the_instant_order_is_not_the_nanos_order :
    ∃ a b : VInstant, a.val < b.val ∧ b.val.nanos < a.val.nanos :=
  ⟨⟨⟨59, 1500000000⟩, by decide⟩, ⟨⟨60, 0⟩, by decide⟩, by decide⟩

/-- The narrowing, named by its subdomain: off a leap second the two orders agree. -/
theorem Instant.lt_iff_nanos_off_a_leap_second (a b : Instant)
    (ha : a.ns < 1000000000) (hb : b.ns < 1000000000) : a < b ↔ a.nanos < b.nanos := by
  rw [Instant.lt_iff]; unfold Instant.nanos
  constructor <;> intro h <;> omega

/-- A UTC offset: `±HH:MM[:SS]`, as a sign and seconds.  UTC is `⟨false, 0⟩`; zone
offsets before 1972 carry seconds, so the unit is the second (D9-6). -/
structure Offset where
  west : Bool
  sec  : Nat
deriving DecidableEq, Repr

/-- chrono's `FixedOffset` range: strictly less than a day. -/
def Offset.wf (o : Offset) : Bool := decide (o.sec < 86400)

abbrev VOffset := { o : Offset // o.wf = true }

/-- The only constructor a decoder uses (R10). -/
def mkOffset? (west : Bool) (sec : Nat) : Option VOffset :=
  if h : Offset.wf ⟨west, sec⟩ = true then some ⟨⟨west, sec⟩, h⟩ else none

def Offset.utc : Offset := ⟨false, 0⟩

/-- The local clock of `t` at `o`, in whole seconds from the origin: chrono's
`naive_utc() + offset`, with the leap nanoseconds dropped.  West of UTC it
saturates at the origin, the one place a `Nat` cannot follow chrono's
proleptic year 0. -/
def localSecAt (o : Offset) (t : Instant) : Nat :=
  if o.west then t.sec - o.sec else t.sec + o.sec

/-- The UTC second whose local clock at `o` reads `l`: local time minus offset.
`none` when that falls before the origin. -/
def utcSecAt (o : Offset) (l : Nat) : Option Nat :=
  if o.west then some (l + o.sec) else if o.sec ≤ l then some (l - o.sec) else none

theorem localSecAt_utcSecAt (o : Offset) (l s ns : Nat) (h : utcSecAt o l = some s) :
    localSecAt o ⟨s, ns⟩ = l := by
  unfold utcSecAt at h; unfold localSecAt
  cases hw : o.west <;> simp only [hw, if_true, if_false, Bool.false_eq_true] at h ⊢
  · split at h
    · simp only [Option.some.injEq] at h; omega
    · simp at h
  · simp only [Option.some.injEq] at h; omega

theorem utcSecAt_localSecAt (o : Offset) (t : Instant) (h : 0 < localSecAt o t) :
    utcSecAt o (localSecAt o t) = some t.sec := by
  unfold localSecAt at *; unfold utcSecAt
  cases hw : o.west <;> simp only [hw, if_true, if_false, Bool.false_eq_true] at h ⊢
  · rw [if_pos (by omega)]; simp
  · simp only [Option.some.injEq]; omega

/-! ### Durations: chrono's `signed_duration_since`, leap seconds included -/

/-- `b.signed_duration_since(a)` for UTC instants, as `(secs, nanos)` with
`0 ≤ nanos < 10^9`: chrono 0.4.45 `NaiveDateTime::signed_duration_since`, which is
the dates' difference in days plus `NaiveTime::signed_duration_since` of the
times of day.  The latter counts a leap second "yet to be counted" only when the
other side is a later (or earlier) second **of the day**, which is the rule
`the_leap_second_counts_within_a_day_but_not_across_midnight` pins. -/
def durationBetween (a b : Instant) : Int × Int :=
  let days : Int := ((b.sec / 86400 : Nat) : Int) - ((a.sec / 86400 : Nat) : Int)
  let bs := b.sec % 86400
  let as := a.sec % 86400
  let frac : Int := (b.ns : Int) - (a.ns : Int)
  let secs : Int :=
    if as < bs ∧ 1000000000 ≤ a.ns then (bs : Int) - as + 1
    else if bs < as ∧ 1000000000 ≤ b.ns then (bs : Int) - as - 1
    else (bs : Int) - as
  (days * 86400 + secs + frac / 1000000000, frac % 1000000000)

/-- `TimeDelta::num_seconds` of `b − a`: whole seconds, truncated toward zero
(`hours_since_wake`, site R11). -/
def secondsBetween (a b : Instant) : Int :=
  if (durationBetween a b).1 < 0 ∧ 0 < (durationBetween a b).2 then (durationBetween a b).1 + 1
  else (durationBetween a b).1

/-- `num_minutes().max(0)` of `b − a`, as `close_sub` reads it.  `num_minutes` is
`num_seconds / 60` truncated toward zero, so a negative count gives at most 0 and
the clamp makes it 0: this is the clamped seconds over 60
(`minutesBetween_is_num_minutes_max_zero`). -/
def minutesBetween (a b : Instant) : Nat := (secondsBetween a b).toNat / 60

theorem minutesBetween_is_num_minutes_max_zero (a b : Instant) :
    (minutesBetween a b : Int) = max 0 ((secondsBetween a b).tdiv 60) := by
  unfold minutesBetween
  by_cases h : 0 ≤ secondsBetween a b
  · rw [Int.tdiv_eq_ediv_of_nonneg h]; omega
  · have : (secondsBetween a b).tdiv 60 ≤ 0 := by
      have e : secondsBetween a b = -(-secondsBetween a b) := by omega
      rw [e, Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by omega)]
      omega
    omega

/-- `t − Duration::minutes(m)` (idle's start): chrono's
`NaiveTime::overflowing_add_signed` with a negative whole-minute delta.  A leap
second is left as the next second before subtracting; a zero delta leaves the
instant, leap second and all.  Below the origin it saturates at the origin. -/
def subMinutes (t : Instant) (m : Nat) : Instant :=
  if m = 0 then t
  else if 1000000000 ≤ t.ns then
    (if 60 * m ≤ t.sec + 1 then ⟨t.sec + 1 - 60 * m, t.ns - 1000000000⟩ else ⟨0, 0⟩)
  else if 60 * m ≤ t.sec then ⟨t.sec - 60 * m, t.ns⟩ else ⟨0, 0⟩

theorem subMinutes_zero (t : Instant) : subMinutes t 0 = t := by
  simp [subMinutes]

/-- Off the origin, subtracting minutes is subtracting nanoseconds, leap second
or not. -/
theorem subMinutes_nanos (t : Instant) (m : Nat) (hm : 0 < m) (hns : t.ns < 2000000000)
    (h : m * 60000000000 ≤ t.nanos) : (subMinutes t m).nanos = t.nanos - m * 60000000000 := by
  unfold subMinutes Instant.nanos at *
  rw [if_neg (by omega)]
  split
  · rw [if_pos (by omega)]; simp only; omega
  · rw [if_pos (by omega)]; simp only; omega

theorem subMinutes_wf (t : Instant) (m : Nat) (h : t.wf = true) : (subMinutes t m).wf = true := by
  unfold subMinutes
  simp only [Instant.wf, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  split
  · simp only [Instant.wf, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]; omega
  · split
    · split <;> simp only [Instant.wf, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        beq_iff_eq] <;> omega
    · split <;> simp only [Instant.wf, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        beq_iff_eq] <;> omega

/-- chrono's own documented examples for `signed_duration_since` with a leap second
(CRIT 29): the five `NaiveTime` ones on day 0 (`03:00:59` plus 1,000 ms and 1,500 ms,
against `03:00:59`, `03:00:00` and `02:59:59` plus 1,000 ms), and the two
`NaiveDateTime` ones around 2015-06-30T23:59:60.5. -/
theorem durationBetween_across_a_leap_second :
    durationBetween ⟨10859, 0⟩ ⟨10859, 1000000000⟩ = (1, 0) ∧
    durationBetween ⟨10859, 0⟩ ⟨10859, 1500000000⟩ = (1, 500000000) ∧
    durationBetween ⟨10800, 0⟩ ⟨10859, 1000000000⟩ = (60, 0) ∧
    durationBetween ⟨10799, 1000000000⟩ ⟨10800, 0⟩ = (1, 0) ∧
    durationBetween ⟨10799, 1000000000⟩ ⟨10859, 1000000000⟩ = (61, 0) ∧
    durationBetween ⟨63571302000, 0⟩ ⟨63571305599, 1500000000⟩ = (3600, 500000000) ∧
    durationBetween ⟨63571305599, 1500000000⟩ ⟨63571309200, 0⟩ = (3599, 500000000) := by
  decide

/-- **chrono's rule, which nanosecond arithmetic is not.**  From a leap second
`…:59` plus 1.5 s to 200 ms past the next second: 0.7 s when the next second is
in the same day (03:00:00.2), and **−0.3 s** when it is the next day's midnight,
although both pairs are in order.  The design's "leap seconds included" means
this. -/
theorem the_leap_second_counts_within_a_day_but_not_across_midnight :
    (⟨10799, 1500000000⟩ : Instant) < ⟨10800, 200000000⟩ ∧
    durationBetween ⟨10799, 1500000000⟩ ⟨10800, 200000000⟩ = (0, 700000000) ∧
    (⟨63571305599, 1500000000⟩ : Instant) < ⟨63571305600, 200000000⟩ ∧
    durationBetween ⟨63571305599, 1500000000⟩ ⟨63571305600, 200000000⟩ = (-1, 700000000) := by
  decide

theorem minutesBetween_truncates :
    minutesBetween ⟨0, 0⟩ ⟨119, 0⟩ = 1 ∧ minutesBetween ⟨0, 0⟩ ⟨119, 999999999⟩ = 1 ∧
    minutesBetween ⟨0, 0⟩ ⟨120, 0⟩ = 2 ∧ minutesBetween ⟨119, 0⟩ ⟨0, 0⟩ = 0 := by
  decide

/-- −59.5 s is −59 whole seconds, and +59.5 s is 59. -/
theorem secondsBetween_truncates_toward_zero :
    secondsBetween ⟨59, 500000000⟩ ⟨0, 0⟩ = -59 ∧ secondsBetween ⟨0, 0⟩ ⟨59, 500000000⟩ = 59 := by
  decide

/-- The duration, as one count of nanoseconds: the nanosecond difference plus
chrono's leap adjustment of at most one second either way. -/
theorem durationBetween_total (a b : Instant) :
    ∃ adj : Int, (adj = 0 ∨ adj = 1 ∨ adj = -1) ∧
      (a.sec = b.sec → adj = 0) ∧
      (durationBetween a b).1 * 1000000000 + (durationBetween a b).2
        = ((b.sec : Int) - a.sec) * 1000000000 + ((b.ns : Int) - a.ns) + adj * 1000000000 ∧
      0 ≤ (durationBetween a b).2 ∧ (durationBetween a b).2 < 1000000000 := by
  unfold durationBetween
  simp only
  split
  · exact ⟨1, by omega, by omega, by omega, by omega, by omega⟩
  · split
    · exact ⟨-1, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, by omega, by omega, by omega, by omega, by omega⟩

/-- An interval that runs backwards has no minutes, as `close_sub`'s clamp
intends — chrono's leap rule included, which can make such a duration up to two
seconds positive but never a minute. -/
theorem minutesBetween_zero_of_le (a b : Instant) (hb : b.wf = true) (h : b ≤ a) :
    minutesBetween a b = 0 := by
  obtain ⟨adj, hadj, hsame, htot, hlo, hhi⟩ := durationBetween_total a b
  simp only [Instant.wf, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
  rw [Instant.le_iff] at h
  unfold minutesBetween secondsBetween
  split <;> omega

theorem mkInstant?_isSome_iff (sec ns : Nat) :
    (mkInstant? sec ns).isSome = Instant.wf ⟨sec, ns⟩ := by
  unfold mkInstant?; split <;> simp_all

/-- R10's rejection: a leap nanosecond off second 59, two seconds of nanoseconds,
year 10000; and the edges that are accepted. -/
theorem mkInstant?_refuses_a_bad_nanosecond :
    mkInstant? 0 1000000000 = none ∧ mkInstant? 59 2000000000 = none ∧
    mkInstant? 315537897600 0 = none ∧
    (mkInstant? 59 1999999999).isSome = true ∧ (mkInstant? 315537897599 999999999).isSome = true := by
  decide

theorem mkOffset?_isSome_iff (west : Bool) (sec : Nat) :
    (mkOffset? west sec).isSome = Offset.wf ⟨west, sec⟩ := by
  unfold mkOffset?; split <;> simp_all

theorem mkOffset?_refuses_a_whole_day :
    mkOffset? false 86400 = none ∧ mkOffset? true 86400 = none ∧
    (mkOffset? true 86399).isSome = true := by
  decide

/-- **The written clock is not the instant order** (cheat 92's control).
`2026-09-07T22:00:00-05:00` and `2026-09-08T03:00:00+00:00` are one instant,
whose written clocks are five hours apart: ordering the two by their clocks
would put one before the other, and no instant is before itself
(`Instant.lt_irrefl`). -/
theorem the_written_clock_is_not_the_instant_order :
    utcSecAt ⟨true, 18000⟩ (toDay ⟨2026, 9, 7⟩ * 86400 + 22 * 3600) = some 63924433200 ∧
    utcSecAt Offset.utc (toDay ⟨2026, 9, 8⟩ * 86400 + 3 * 3600) = some 63924433200 ∧
    localSecAt ⟨true, 18000⟩ ⟨63924433200, 0⟩ < localSecAt Offset.utc ⟨63924433200, 0⟩ := by
  decide

/-! ## 9. The zone: a table the host probes (stage 5, step B1; design §6.1)

The kernel carries **no tz database**.  The host samples chrono-tz's offset for
the configured zone at every UTC hour over [1900, 2200), bisects each change to
the second, and sends the result: the offset in force before the first change,
and every change as the instant it takes effect with the offset from then on.
The kernel reads it, and nothing else about zones (D9-7).

**Stated assumptions**, each tested on the host at B4 (T4): a zone never changes
and changes back inside one sampled hour; and outside [1900, 2200) the edge
offset applies (parity entry P16).

**`offsetAt` is chrono-tz's lookup** (`offset_from_utc_datetime`: the timestamp,
in whole seconds, against the spans): the last transition at or before `t`.  A
transition is a whole second (chrono-tz's spans are `i64` seconds, and the host
bisects to the second), so in chrono's order "at or before `t`" is exactly "at a
second at or before `t.sec`".

**`localHits` is chrono-tz's local lookup** (`offset_from_local_datetime`): the
table's spans, each read at its own offset, and the instants whose span holds
them, earliest first.  chrono-tz finds them by a binary search over local spans
plus a check of both neighbours; the scan below agrees with it whenever at most
two local spans overlap and the local spans are ordered, which a table probed from
a real zone satisfies.  A table that broke that would be a table no zone has; T4
(d) is the host's check.

Both are `foldl`s over at most 4,096 transitions (rule D9-21). -/

/-- The host's zone table.  `key` names the zone, the tzdb version and the span;
the kernel only compares it. -/
structure TzTable where
  key   : List Char
  base  : Offset
  trans : List (Instant × Offset)
deriving DecidableEq, Repr

/-- Transitions after `lo`: whole, representable seconds, strictly increasing, with
representable offsets.  A tail call, run only after the length guard in
`TzTable.wf`. -/
def transFrom : Option Nat → List (Instant × Offset) → Bool
  | _, [] => true
  | lo, (i, o) :: rest =>
      (match lo with | none => true | some l => decide (l < i.sec)) && i.ns == 0 && i.wf && o.wf
        && transFrom (some i.sec) rest

/-- R10: a key of at most 128 characters, a representable base, at most 4,096
transitions, and `transFrom`.  The cheap guards come first, so `transFrom` never
runs over an over-long list. -/
def TzTable.wf (z : TzTable) : Bool :=
  decide (z.key.length ≤ 128) && z.base.wf && decide (z.trans.length ≤ 4096) && transFrom none z.trans

abbrev Tz := { z : TzTable // z.wf = true }

/-- The only constructor a decoder uses (R10). -/
def mkTz? (z : TzTable) : Option Tz := if h : z.wf = true then some ⟨z, h⟩ else none

def offsetStep (t : Instant) (acc : Offset) (p : Instant × Offset) : Offset :=
  if p.1.sec ≤ t.sec then p.2 else acc

/-- The offset in force at `t`: the last transition at or before it, else the base. -/
def offsetAt (z : Tz) (t : Instant) : Offset := z.val.trans.foldl (offsetStep t) z.val.base

/-- `t`'s local clock in the zone, in whole seconds from the origin. -/
def localSec (z : Tz) (t : Instant) : Nat := localSecAt (offsetAt z t) t

/-- `t`'s local date in the zone. -/
def localDate (z : Tz) (t : Instant) : Nat := localSec z t / 86400

/-- One span of the table: UTC seconds `[lo, hi)` (an absent bound is unbounded)
and the offset in force over it. -/
structure Span where
  lo  : Option Nat
  hi  : Option Nat
  off : Offset
deriving DecidableEq, Repr

def Span.holds (sp : Span) (x : Nat) : Bool :=
  (match sp.lo with | none => true | some l => decide (l ≤ x)) &&
    (match sp.hi with | none => true | some h => decide (x < h))

/-- The UTC second of local clock `l` in this span, if the span holds it. -/
def Span.hit (sp : Span) (l : Nat) : Option Nat :=
  match utcSecAt sp.off l with
  | some s => if sp.holds s then some s else none
  | none => none

/-- The spans, in order.  Specification: proofs read it, the run time does not. -/
def spansFrom (lo : Option Nat) (off : Offset) : List (Instant × Offset) → List Span
  | [] => [⟨lo, none, off⟩]
  | (i, o) :: rest => ⟨lo, some i.sec, off⟩ :: spansFrom (some i.sec) o rest

def TzTable.spans (z : TzTable) : List Span := spansFrom none z.base z.trans

def pushHit : Option Nat → List Nat → List Nat
  | some s, acc => s :: acc
  | none, acc => acc

def hitStep (l : Nat) (st : Option Nat × Offset × List Nat) (p : Instant × Offset) :
    Option Nat × Offset × List Nat :=
  (some p.1.sec, p.2, pushHit (Span.hit ⟨st.1, some p.1.sec, st.2.1⟩ l) st.2.2)

def hitFinish (l : Nat) (st : Option Nat × Offset × List Nat) : List Nat :=
  (pushHit (Span.hit ⟨st.1, none, st.2.1⟩ l) st.2.2).reverse

/-- The UTC seconds whose local clock in the zone reads `l`, earliest first. -/
def localHits (z : Tz) (l : Nat) : List Nat :=
  hitFinish l (z.val.trans.foldl (hitStep l) (none, z.val.base, []))

/-- The first local clock 1 to 180 minutes after `l` that the zone has. -/
def gapHit (z : Tz) (l : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, m =>
      match localHits z (l + 60 * m) with
      | s :: _ => some s
      | [] => gapHit z l fuel (m + 1)

/-! ### `instantOf`: the fork's `local_dt` (design §6.3)

`capacity::local_dt(tz, date, time)`: `Single` gives that instant; `Ambiguous`
the earliest; `None` (a spring-forward gap) the first valid local time 1 to 180
minutes later, earliest; and failing that, the local time read as UTC
(`from_utc_datetime`).  The clock is minutes of the day, `Field.Clock`'s
`Fin 1440`, which `Line.lean` defines and this module cannot import. -/

def instantOf (z : Tz) (d : Nat) (c : Fin 1440) : Instant :=
  match localHits z (d * 86400 + c.val * 60) with
  | s :: _ => ⟨s, 0⟩
  | [] =>
      match gapHit z (d * 86400 + c.val * 60) 180 1 with
      | some s => ⟨s, 0⟩
      | none => ⟨d * 86400 + c.val * 60, 0⟩

/-- Exactly one instant has this local clock.  The origin's first second is not
claimed: `localSec` saturates there, so it is the reading of every instant up to
an offset west of UTC. -/
def unambiguousAt (z : Tz) (d : Nat) (c : Fin 1440) : Bool :=
  (localHits z (d * 86400 + c.val * 60)).length == 1 && decide (0 < d * 86400 + c.val * 60)

/-- Why `unambiguousAt` leaves out the origin's first second: a zone west of UTC
with one hit there still has another instant reading that clock, because
`localSec` saturates. -/
theorem the_origin_second_is_not_unambiguous :
    ∃ (z : Tz) (t : Instant), (localHits z 0).length = 1 ∧ t.ns = 0 ∧
      localSec z t = 0 * 86400 + (0 : Fin 1440).val * 60 ∧ instantOf z 0 0 ≠ t :=
  ⟨⟨⟨[], ⟨true, 21600⟩, []⟩, by decide⟩, ⟨100, 0⟩, by decide, rfl, by decide, by decide⟩

/-! ### What the table's well-formedness gives -/

theorem transFrom_mem : ∀ (L : List (Instant × Offset)) (lo : Option Nat) (p : Instant × Offset),
    transFrom lo L = true → p ∈ L →
      p.1.ns = 0 ∧ p.1.wf = true ∧ p.2.wf = true ∧ (∀ l, lo = some l → l < p.1.sec)
  | [], _, _, _, hm => by simp at hm
  | (i, o) :: rest, lo, p, hw, hm => by
      simp only [transFrom, Bool.and_eq_true, beq_iff_eq] at hw
      obtain ⟨⟨⟨⟨hlo, hns⟩, hiw⟩, how⟩, hrest⟩ := hw
      rcases List.mem_cons.mp hm with h | h
      · subst h
        refine ⟨hns, hiw, how, ?_⟩
        intro l hl; subst hl; simpa using hlo
      · obtain ⟨a, b, c, d⟩ := transFrom_mem rest (some i.sec) p hrest h
        refine ⟨a, b, c, ?_⟩
        intro l hl; subst hl
        have := d i.sec rfl
        simp only [decide_eq_true_eq] at hlo
        omega

theorem transFrom_tail {lo : Option Nat} {i : Instant} {o : Offset} {rest : List (Instant × Offset)}
    (h : transFrom lo ((i, o) :: rest) = true) : transFrom (some i.sec) rest = true := by
  simp only [transFrom, Bool.and_eq_true] at h; exact h.2

theorem Tz.transFrom (z : Tz) : transFrom none z.val.trans = true := by
  have h := z.property
  simp only [TzTable.wf, Bool.and_eq_true] at h
  exact h.2

theorem Tz.trans_ns (z : Tz) {p : Instant × Offset} (h : p ∈ z.val.trans) : p.1.ns = 0 :=
  (transFrom_mem _ _ _ z.transFrom h).1

/-- **A table's transitions strictly increase**, in chrono's order. -/
theorem tz_transitions_strictly_increase (z : Tz) :
    z.val.trans.Pairwise (fun p q => p.1 < q.1) := by
  suffices ∀ (L : List (Instant × Offset)) lo, transFrom lo L = true → L.Pairwise (fun p q => p.1 < q.1) from
    this _ _ z.transFrom
  intro L
  induction L with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons p rest ih =>
    intro lo hw
    obtain ⟨i, o⟩ := p
    have ht := transFrom_tail hw
    refine List.Pairwise.cons ?_ (ih _ ht)
    intro q hq
    have := (transFrom_mem rest (some i.sec) q ht hq).2.2.2 i.sec rfl
    exact Or.inl this

theorem mkTz?_isSome_iff (z : TzTable) : (mkTz? z).isSome = z.wf := by
  unfold mkTz?; split <;> simp_all

theorem mkTz?_refuses_a_long_key (z : TzTable) (h : 128 < z.key.length) : mkTz? z = none := by
  unfold mkTz? TzTable.wf
  rw [dif_neg]; simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]; omega

theorem mkTz?_refuses_too_many_transitions (z : TzTable) (h : 4096 < z.trans.length) :
    mkTz? z = none := by
  unfold mkTz? TzTable.wf
  rw [dif_neg]; simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]; intros; omega

/-- R10's rejection: transitions out of order, a repeated instant, a transition off
a whole second, a transition to an offset of a day, and a base of a day; and a
sorted table, which is accepted. -/
theorem mkTz?_refuses_an_unsorted_table :
    mkTz? ⟨[], Offset.utc, [(⟨120, 0⟩, ⟨false, 3600⟩), (⟨60, 0⟩, Offset.utc)]⟩ = none ∧
    mkTz? ⟨[], Offset.utc, [(⟨60, 0⟩, ⟨false, 3600⟩), (⟨60, 0⟩, Offset.utc)]⟩ = none ∧
    mkTz? ⟨[], Offset.utc, [(⟨60, 1⟩, ⟨false, 3600⟩)]⟩ = none ∧
    mkTz? ⟨[], Offset.utc, [(⟨60, 0⟩, ⟨false, 86400⟩)]⟩ = none ∧
    mkTz? ⟨[], ⟨true, 86400⟩, []⟩ = none ∧
    (mkTz? ⟨[], Offset.utc, [(⟨60, 0⟩, ⟨false, 3600⟩), (⟨120, 0⟩, Offset.utc)]⟩).isSome = true := by
  decide

/-! ### `offsetAt` reads the last transition -/

theorem offsetFold_none (t : Instant) : ∀ (L : List (Instant × Offset)) (acc : Offset),
    (∀ p ∈ L, t.sec < p.1.sec) → L.foldl (offsetStep t) acc = acc
  | [], _, _ => rfl
  | p :: rest, acc, h => by
      rw [List.foldl_cons]
      have hp := h p (List.mem_cons_self ..)
      have : offsetStep t acc p = acc := by unfold offsetStep; rw [if_neg (by omega)]
      rw [this]
      exact offsetFold_none t rest acc (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem offsetFold_last (t i : Instant) (o : Offset) :
    ∀ (L : List (Instant × Offset)) (lo : Option Nat) (acc : Offset),
      transFrom lo L = true → (i, o) ∈ L → i.sec ≤ t.sec →
      (∀ j o', (j, o') ∈ L → i.sec < j.sec → t.sec < j.sec) →
      L.foldl (offsetStep t) acc = o
  | [], _, _, _, hm, _, _ => by simp at hm
  | (j, o') :: rest, lo, acc, hw, hm, hle, hnext => by
      rw [List.foldl_cons]
      have ht := transFrom_tail hw
      rcases List.mem_cons.mp hm with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have : offsetStep t acc (i, o) = o := by unfold offsetStep; rw [if_pos hle]
        rw [this]
        apply offsetFold_none
        intro q hq
        have hs := (transFrom_mem rest (some i.sec) q ht hq).2.2.2 i.sec rfl
        exact hnext q.1 q.2 (List.mem_cons_of_mem _ hq) hs
      · exact offsetFold_last t i o rest (some j.sec) _ ht h hle
          (fun j' o'' hm' => hnext j' o'' (List.mem_cons_of_mem _ hm'))

/-- **`offsetAt` reads the last transition** (design §15, B1), in chrono's order:
the offset of a transition at or before `t` with no later transition at or before
`t`.  The design stated it over `Instant.nanos`, where it is false
(`offsetAt_does_not_read_the_last_transition_by_nanos`). -/
theorem offsetAt_reads_the_last_transition (z : Tz) (t i : Instant) (o : Offset)
    (hmem : (i, o) ∈ z.val.trans) (hle : i ≤ t)
    (hnext : ∀ j o', (j, o') ∈ z.val.trans → i < j → t < j) :
    offsetAt z t = o := by
  have hi : i.ns = 0 := z.trans_ns hmem
  apply offsetFold_last t i o z.val.trans none z.val.base z.transFrom hmem
  · rw [Instant.le_iff] at hle; omega
  · intro j o' hj hij
    have hj0 : j.ns = 0 := z.trans_ns hj
    have := hnext j o' hj (by rw [Instant.lt_iff]; omega)
    rw [Instant.lt_iff] at this; omega

/-- Its other direction: before every transition, the base. -/
theorem offsetAt_before_every_transition (z : Tz) (t : Instant)
    (h : ∀ j o', (j, o') ∈ z.val.trans → t < j) : offsetAt z t = z.val.base := by
  apply offsetFold_none
  intro p hp
  have hp0 : p.1.ns = 0 := z.trans_ns hp
  have := h p.1 p.2 hp
  rw [Instant.lt_iff] at this; omega

/-- And exactly at a transition, its offset. -/
theorem offsetAt_at_a_transition (z : Tz) (i : Instant) (o : Offset) (hmem : (i, o) ∈ z.val.trans) :
    offsetAt z i = o :=
  offsetAt_reads_the_last_transition z i i o hmem (by rw [Instant.le_iff]; omega)
    (fun _ _ _ h => h)

/-- **Refuted as the design stated it**, over nanoseconds: a leap second one and a
half seconds before a transition has a nanosecond count past the transition's,
and chrono-tz (and `offsetAt`) still give the base. -/
theorem offsetAt_does_not_read_the_last_transition_by_nanos :
    ∃ (z : Tz) (t i : Instant) (o : Offset), (i, o) ∈ z.val.trans ∧ i.nanos ≤ t.nanos ∧
      (∀ j o', (j, o') ∈ z.val.trans → i.nanos < j.nanos → t.nanos < j.nanos) ∧
      t.wf = true ∧ offsetAt z t ≠ o := by
  refine ⟨⟨⟨[], Offset.utc, [(⟨60, 0⟩, ⟨false, 3600⟩)]⟩, by decide⟩, ⟨59, 1500000000⟩, ⟨60, 0⟩,
    ⟨false, 3600⟩, by simp, by decide, ?_, by decide, by decide⟩
  intro j o' hj hlt
  simp only [List.mem_singleton, Prod.mk.injEq] at hj
  obtain ⟨rfl, rfl⟩ := hj
  exact absurd hlt (Nat.lt_irrefl _)

theorem offsetAt_wf (z : Tz) (t : Instant) : (offsetAt z t).wf = true := by
  have hb : z.val.base.wf = true := by
    have h := z.property
    simp only [TzTable.wf, Bool.and_eq_true] at h
    exact h.1.1.2
  suffices ∀ (L : List (Instant × Offset)) (acc : Offset), acc.wf = true →
      (∀ p ∈ L, p.2.wf = true) → (L.foldl (offsetStep t) acc).wf = true from
    this _ _ hb (fun p hp => (transFrom_mem _ _ _ z.transFrom hp).2.2.1)
  intro L
  induction L with
  | nil => intro acc h _; exact h
  | cons p rest ih =>
    intro acc hacc hall
    rw [List.foldl_cons]
    apply ih _ _ (fun q hq => hall q (List.mem_cons_of_mem _ hq))
    unfold offsetStep; split
    · exact hall p (List.mem_cons_self ..)
    · exact hacc

/-- A local date is within a day of the UTC date: an offset is under a day. -/
theorem localDate_near_the_utc_date (z : Tz) (t : Instant) :
    t.sec / 86400 ≤ localDate z t + 1 ∧ localDate z t ≤ t.sec / 86400 + 1 := by
  have hw := offsetAt_wf z t
  unfold localDate localSec localSecAt
  simp only [Offset.wf, decide_eq_true_eq] at hw
  split <;> omega

theorem foldl_offsetStep_congr (t t' : Instant) : ∀ (L : List (Instant × Offset)) (acc : Offset),
    (∀ p ∈ L, (p.1.sec ≤ t.sec ↔ p.1.sec ≤ t'.sec)) →
      L.foldl (offsetStep t) acc = L.foldl (offsetStep t') acc
  | [], _, _ => rfl
  | p :: rest, acc, h => by
      rw [List.foldl_cons, List.foldl_cons]
      have hp := h p (List.mem_cons_self ..)
      have : offsetStep t acc p = offsetStep t' acc p := by
        unfold offsetStep
        by_cases hc : p.1.sec ≤ t.sec
        · rw [if_pos hc, if_pos (hp.mp hc)]
        · rw [if_neg hc, if_neg (fun h' => hc (hp.mpr h'))]
      rw [this]
      exact foldl_offsetStep_congr t t' rest _ (fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- Between transitions the offset is one offset. -/
theorem offsetAt_is_constant_between_transitions (z : Tz) (t t' : Instant)
    (h : ∀ j o', (j, o') ∈ z.val.trans → (j ≤ t ↔ j ≤ t')) : offsetAt z t = offsetAt z t' := by
  apply foldl_offsetStep_congr
  intro p hp
  have hp0 : p.1.ns = 0 := z.trans_ns hp
  have := h p.1 p.2 hp
  rw [Instant.le_iff, Instant.le_iff] at this
  constructor <;> intro hc <;> omega

/-- Between transitions the local date only moves forward.  (Across one it can move
back: a fall-back at local midnight repeats a date, which is why C2's `keptWakes`
dedups runs, not dates.) -/
theorem localDate_mono_between_transitions (z : Tz) (t t' : Instant)
    (h : ∀ j o', (j, o') ∈ z.val.trans → (j ≤ t ↔ j ≤ t')) (hle : t ≤ t') :
    localDate z t ≤ localDate z t' := by
  have ho := offsetAt_is_constant_between_transitions z t t' h
  unfold localDate localSec
  rw [ho]
  rw [Instant.le_iff] at hle
  apply Nat.div_le_div_right
  unfold localSecAt; split <;> omega

/-! ### `localHits` is the spans, read at their own offsets -/

theorem pushHit_reverse (o : Option Nat) (acc : List Nat) :
    (pushHit o acc).reverse = acc.reverse ++ o.toList := by
  cases o <;> simp [pushHit]

theorem hitFold (l : Nat) : ∀ (L : List (Instant × Offset)) (lo : Option Nat) (off : Offset)
    (acc : List Nat),
    hitFinish l (L.foldl (hitStep l) (lo, off, acc))
      = acc.reverse ++ (spansFrom lo off L).filterMap (fun sp => sp.hit l)
  | [], lo, off, acc => by
      simp only [List.foldl_nil, hitFinish, spansFrom, pushHit_reverse]
      cases h : Span.hit ⟨lo, none, off⟩ l <;> simp [h]
  | (i, o) :: rest, lo, off, acc => by
      rw [List.foldl_cons]
      have := hitFold l rest (some i.sec) o (pushHit (Span.hit ⟨lo, some i.sec, off⟩ l) acc)
      simp only [hitStep] at this ⊢
      rw [this, pushHit_reverse, spansFrom]
      cases h : Span.hit ⟨lo, some i.sec, off⟩ l <;> simp [h]

theorem localHits_eq (z : Tz) (l : Nat) :
    localHits z l = z.val.spans.filterMap (fun sp => sp.hit l) := by
  unfold localHits TzTable.spans
  rw [hitFold]; simp

theorem spansFrom_lo (l : Nat) : ∀ (L : List (Instant × Offset)) (off : Offset) (sp : Span),
    transFrom (some l) L = true → sp ∈ spansFrom (some l) off L → ∃ l', sp.lo = some l' ∧ l ≤ l'
  | [], off, sp, _, hm => by
      simp only [spansFrom, List.mem_singleton] at hm; subst hm; exact ⟨l, rfl, Nat.le_refl _⟩
  | (i, o) :: rest, off, sp, hw, hm => by
      simp only [spansFrom, List.mem_cons] at hm
      rcases hm with h | h
      · subst h; exact ⟨l, rfl, Nat.le_refl _⟩
      · obtain ⟨l', hl', hle⟩ := spansFrom_lo i.sec rest o sp (transFrom_tail hw) h
        have : l < i.sec := (transFrom_mem _ _ (i, o) hw (List.mem_cons_self ..)).2.2.2 l rfl
        exact ⟨l', hl', by omega⟩

/-- The fold reads a span's offset at every second the span holds. -/
theorem offsetFold_span (t : Instant) : ∀ (L : List (Instant × Offset)) (lo : Option Nat)
    (off : Offset) (sp : Span),
    transFrom lo L = true → sp ∈ spansFrom lo off L → sp.holds t.sec = true →
      L.foldl (offsetStep t) off = sp.off
  | [], lo, off, sp, _, hm, _ => by
      simp only [spansFrom, List.mem_singleton] at hm; subst hm; rfl
  | (i, o) :: rest, lo, off, sp, hw, hm, hh => by
      rw [List.foldl_cons]
      have ht := transFrom_tail hw
      simp only [spansFrom, List.mem_cons] at hm
      rcases hm with h | h
      · subst h
        simp only [Span.holds, Bool.and_eq_true, decide_eq_true_eq] at hh
        have hx := hh.2
        have : offsetStep t off (i, o) = off := by unfold offsetStep; rw [if_neg (by simp; omega)]
        rw [this]
        apply offsetFold_none
        intro q hq
        have := (transFrom_mem rest (some i.sec) q ht hq).2.2.2 i.sec rfl
        omega
      · obtain ⟨l', hl', hle⟩ := spansFrom_lo i.sec rest o sp ht h
        have hx : l' ≤ t.sec := by
          simp only [Span.holds, hl', Bool.and_eq_true, decide_eq_true_eq] at hh; exact hh.1
        have : offsetStep t off (i, o) = o := by unfold offsetStep; rw [if_pos (by simp; omega)]
        rw [this]
        exact offsetFold_span t rest (some i.sec) o sp ht h hh

theorem exists_span (x : Nat) : ∀ (L : List (Instant × Offset)) (lo : Option Nat) (off : Offset),
    (∀ l, lo = some l → l ≤ x) → ∃ sp ∈ spansFrom lo off L, sp.holds x = true
  | [], lo, off, h => by
      refine ⟨⟨lo, none, off⟩, by simp [spansFrom], ?_⟩
      cases lo with
      | none => rfl
      | some l => simpa [Span.holds] using h l rfl
  | (i, o) :: rest, lo, off, h => by
      by_cases hx : x < i.sec
      · refine ⟨⟨lo, some i.sec, off⟩, by simp [spansFrom], ?_⟩
        cases lo with
        | none => simpa [Span.holds] using hx
        | some l => simpa [Span.holds, hx] using h l rfl
      · obtain ⟨sp, hsp, hh⟩ := exists_span x rest (some i.sec) o (by intro l hl; cases hl; omega)
        exact ⟨sp, by simp [spansFrom, hsp], hh⟩

/-- Every hit is an instant whose local clock reads `l`. -/
theorem localSec_of_mem_localHits (z : Tz) (l s ns : Nat) (h : s ∈ localHits z l) :
    localSec z ⟨s, ns⟩ = l := by
  rw [localHits_eq, List.mem_filterMap] at h
  obtain ⟨sp, hsp, hhit⟩ := h
  unfold Span.hit at hhit
  split at hhit
  · rename_i s' hu
    split at hhit
    · rename_i hholds
      simp only [Option.some.injEq] at hhit
      subst hhit
      have hoff : offsetAt z ⟨s', ns⟩ = sp.off :=
        offsetFold_span ⟨s', ns⟩ z.val.trans none z.val.base sp z.transFrom hsp hholds
      unfold localSec
      rw [hoff]
      exact localSecAt_utcSecAt sp.off l s' ns hu
    · simp at hhit
  · simp at hhit

/-- And every whole-second instant whose local clock reads `l` is a hit, away from
the origin's saturated second. -/
theorem mem_localHits_of_localSec (z : Tz) (t : Instant) (l : Nat) (hl : 0 < l)
    (h : localSec z t = l) : t.sec ∈ localHits z l := by
  obtain ⟨sp, hsp, hh⟩ := exists_span t.sec z.val.trans none z.val.base (by intro _ h; cases h)
  have hoff : offsetAt z t = sp.off :=
    offsetFold_span t z.val.trans none z.val.base sp z.transFrom hsp hh
  unfold localSec at h
  rw [hoff] at h
  have hu := utcSecAt_localSecAt sp.off t (by omega)
  rw [h] at hu
  rw [localHits_eq, List.mem_filterMap]
  refine ⟨sp, hsp, ?_⟩
  unfold Span.hit
  rw [hu]; simp [hh]

/-- `instantOf` lands on its local clock whenever the zone has that clock. -/
theorem localSec_instantOf (z : Tz) (d : Nat) (c : Fin 1440)
    (h : localHits z (d * 86400 + c.val * 60) ≠ []) :
    localSec z (instantOf z d c) = d * 86400 + c.val * 60 := by
  unfold instantOf
  cases hh : localHits z (d * 86400 + c.val * 60) with
  | nil => exact absurd hh h
  | cons s rest =>
    simp only
    exact localSec_of_mem_localHits z _ s 0 (by rw [hh]; exact List.mem_cons_self ..)

/-- **`instantOf` is `local_dt` on an unambiguous time** (design §15, B1): when
exactly one instant has the local clock, `instantOf` is that instant. -/
theorem instantOf_is_local_dt_on_an_unambiguous_time (z : Tz) (d : Nat) (c : Fin 1440) (t : Instant)
    (hu : unambiguousAt z d c = true) (hns : t.ns = 0)
    (ht : localSec z t = d * 86400 + c.val * 60) :
    instantOf z d c = t := by
  unfold unambiguousAt at hu
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hu
  obtain ⟨hlen, hpos⟩ := hu
  have hmem := mem_localHits_of_localSec z t _ hpos ht
  unfold instantOf
  cases hh : localHits z (d * 86400 + c.val * 60) with
  | nil => rw [hh] at hlen; simp at hlen
  | cons s rest =>
    rw [hh] at hlen hmem
    have hr : rest = [] := by simpa using hlen
    subst hr
    simp only [List.mem_singleton] at hmem
    cases t
    simp_all

/-! ### Witnesses on Chicago's 2026 rules (two transitions; design §14.0 item 4)

Chicago springs forward at 2026-03-08T08:00:00Z (02:00 CST becomes 03:00 CDT) and
falls back at 2026-11-01T07:00:00Z (02:00 CDT becomes 01:00 CST).  Instants are
`Nat` literals; `the_witness_seconds_are_the_dates_they_name` ties each to the
calendar. -/

def chicago2026 : TzTable :=
  ⟨['A', 'm', 'e', 'r', 'i', 'c', 'a', '/', 'C', 'h', 'i', 'c', 'a', 'g', 'o'], ⟨true, 21600⟩,
    [(⟨63908553600, 0⟩, ⟨true, 18000⟩), (⟨63929113200, 0⟩, ⟨true, 21600⟩)]⟩

theorem chicago2026_wf : chicago2026.wf = true := by decide

def chicago : Tz := ⟨chicago2026, chicago2026_wf⟩

theorem the_witness_seconds_are_the_dates_they_name :
    toDay ⟨10000, 1, 1⟩ * 86400 = 315537897600 ∧
    toDay ⟨2026, 3, 8⟩ * 86400 + 8 * 3600 = 63908553600 ∧
    toDay ⟨2026, 11, 1⟩ * 86400 + 7 * 3600 = 63929113200 ∧
    toDay ⟨2026, 9, 8⟩ * 86400 + 3 * 3600 = 63924433200 ∧
    toDay ⟨2015, 6, 30⟩ * 86400 + 23 * 3600 = 63571302000 ∧
    toDay ⟨2015, 7, 1⟩ * 86400 + 3600 = 63571309200 := by
  decide

/-- Design §6.1's witnesses: one second before each transition the old offset, at
it the new one, each on its local date; and `2026-09-08T03:00:00+00:00` is
2026-09-07 in Chicago. -/
theorem chicago_2026_offsets :
    offsetAt chicago ⟨63908553599, 0⟩ = ⟨true, 21600⟩ ∧
    offsetAt chicago ⟨63908553600, 0⟩ = ⟨true, 18000⟩ ∧
    offsetAt chicago ⟨63929113199, 0⟩ = ⟨true, 18000⟩ ∧
    offsetAt chicago ⟨63929113200, 0⟩ = ⟨true, 21600⟩ ∧
    localDate chicago ⟨63908553599, 0⟩ = toDay ⟨2026, 3, 8⟩ ∧
    localDate chicago ⟨63908553600, 0⟩ = toDay ⟨2026, 3, 8⟩ ∧
    localDate chicago ⟨63929113199, 0⟩ = toDay ⟨2026, 11, 1⟩ ∧
    localDate chicago ⟨63929113200, 0⟩ = toDay ⟨2026, 11, 1⟩ ∧
    localDate chicago ⟨63924433200, 0⟩ = toDay ⟨2026, 9, 7⟩ := by
  decide

/-- **Refuted as the design named it** (§6.1 lists
`localDate_is_constant_between_transitions`): between Chicago's 2026 transitions,
17:00:00Z on 2026-09-07 and on 2026-09-08 share an offset and not a local date.
What holds between transitions is one offset
(`offsetAt_is_constant_between_transitions`) and a date that only moves forward
(`localDate_mono_between_transitions`). -/
theorem localDate_is_not_constant_between_transitions :
    offsetAt chicago ⟨63924397200, 0⟩ = offsetAt chicago ⟨63924483600, 0⟩ ∧
    localDate chicago ⟨63924397200, 0⟩ ≠ localDate chicago ⟨63924483600, 0⟩ := by
  decide

/-- Design §6.3's gap witness: 02:30 on 2026-03-08 does not exist in Chicago, and
`local_dt` gives 03:00 CDT, 08:00:00Z. -/
theorem instantOf_in_the_spring_gap :
    localHits chicago (toDay ⟨2026, 3, 8⟩ * 86400 + 150 * 60) = [] ∧
    instantOf chicago (toDay ⟨2026, 3, 8⟩) 150 = ⟨63908553600, 0⟩ := by
  decide

/-- Design §6.3's fold witness: 01:30 on 2026-11-01 happens twice in Chicago, at
06:30Z and 07:30Z, and `local_dt` gives the earlier. -/
theorem instantOf_in_the_fall_fold :
    localHits chicago (toDay ⟨2026, 11, 1⟩ * 86400 + 90 * 60) = [63929111400, 63929115000] ∧
    unambiguousAt chicago (toDay ⟨2026, 11, 1⟩) 90 = false ∧
    instantOf chicago (toDay ⟨2026, 11, 1⟩) 90 = ⟨63929111400, 0⟩ := by
  decide

/-- The unambiguous law's hypotheses are satisfiable: noon on 2026-09-07 is one
instant in Chicago, 17:00:00Z. -/
theorem instantOf_on_an_unambiguous_noon :
    unambiguousAt chicago (toDay ⟨2026, 9, 7⟩) 720 = true ∧
    localSec chicago ⟨63924397200, 0⟩ = toDay ⟨2026, 9, 7⟩ * 86400 + 720 * 60 ∧
    instantOf chicago (toDay ⟨2026, 9, 7⟩) 720 = ⟨63924397200, 0⟩ := by
  decide

end Cal
end Tm
