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

**Rejected: "the month of today"**, which is what `horizon.rs:1543` does.  It
is written here as `monthOfWeekByToday`, whose first argument is unused — the
answer does not depend on the week at all — and
`monthOfWeekByToday_is_not_stable` exhibits one week filed into two different
months depending on the day the command runs.  That is the *same* witness as
the non-refinement, because it is the same fact seen twice.  A file name that
depends on when you looked is not a file name.

Note what this tie-break is **not** for.  `closeTo g now` files leftovers into
the coarser region containing `now`, and that is right: a close happens at a
time, and `now` is the honest input.  The tie-break answers a different
question — *name the month a given week belongs to* — which has no `now` in it.
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

/-- **The rejected alternative**, written down: `horizon.rs:1543` takes the month
of *today*.  The week argument is unused, which is already the whole objection. -/
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

end Cal
end Tm
