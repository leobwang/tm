import TmKernel.Priority
/-!
# Capacity — §7.3's EDF reservation pass, over given capacities, in exact minutes (D10)

Fork-point `tm-core/src/capacity.rs` and `tm-core/src/priority.rs` are the oracle, read
by function name: `capacity::reserve` (earliest days first, the highest matching level
first within a day, returning the minutes actually taken), `capacity::available_until`
(Σ over days `≤ due` of `DayCapacity::at_least ci`), `capacity::upto`, and the EDF loop of
`priority::compute` (deadlines by due ascending, ties in input order; `avail` read before
the item's own reservation; `take = need.min(avail)` reserved; `shortfall_min =
need.saturating_sub(avail)` when `u ≥ 1`).

## The type D10 forces

§8.4 writes `minutes_at_level : [u32; 6]`.  Under the owner's D10 a future day's expected
minutes are the exact mixture `p·lounge + (1 − p)·home`, so a level holds a rational, not a
`Nat`.  The pass is written over **one positive denominator for the whole lookahead**
(`Den`): a `DayCapacity` holds, at each level, the *numerator* over that denominator
(`numAt`), and `c.minutesAt den l : Arith.Pos` is the rational it denotes.  A `Nat` need
enters as `need · den` numerator units.  Why one denominator:

* **Nothing grows through the pass.**  A reservation subtracts numerators over a fixed
  denominator, so the pairs the EDF pass carries are bounded by the lookahead's own
  (D10 cost (ii), README "Stage 5 step 1").  Per-day or per-level denominators would multiply
  on every partial take.
* **Every comparison is still a cross-multiplication** (type (b)): availability `a/den`
  against a need `n` is `a ≤ n·den`; the §7.1 bin at that availability is Priority's
  `binOfQ` / `binOfScaledQ` on `Grant.availQ`.
* **The lookahead that produces it is not built here** (the D9/D10 tranche): a mixture over
  weekdays with `p_lounge = a_w / b_w` lands on the common denominator `∏ b_w` (or their
  `lcm`), a bound fixed by §16's configuration, not by the pass.

## What is built

* `Den`, `denOf?`, `levelOf?`, `DayCapacity`, `Deadline` (R10: a `Fin 6` level, a positive
  denominator, each with its smart constructor and rejection theorem), and `Lookahead`
  (`lookaheadOf?`: a positive denominator and strictly ascending days).
* One day: `dayLeft`, `dayTake`, `dayRest`, `dayOut` — `capacity::reserve`'s inner loop over
  `(min_ci..6).rev()`.
* The days: `availUntil` (`capacity::available_until`), `reserveRest` and `reserveOut`
  (`capacity::reserve`'s outer loop, restricted to the days `≤ due` like `capacity::upto`).
* The pass: `sortDue` (by due, stable), `edfCaps`, `edfGrantsGo`, and `edf` / `edfGrants`.
* **What the compiled code runs** (stage 5 D10 L8, gap 106): proved `@[csimp]` twins at the end of
  the file, a `foldl` over the deadlines and an accumulator over the days that holds each reserved
  day's six numerators once (`edfGrantsGo_eq_edfGrantsGoFast`, `edfCaps_eq_edfCapsFast`,
  `reserveRest_eq_reserveRestFast`, `availUntil_eq_availUntilFast`, `reserveOut_eq_reserveOutFast`,
  `edf_eq_edfFast`, `edfGrants_eq_edfGrantsFast`).  Every theorem here is about the definitions.

## Not here, by name

* **The lookahead** (§8.4, D10): capacities are an argument.
* **Which candidates enter** (walls, optionals and window instances do not; the need is
  `needMin` of a replayed remaining — D9): `ds` is an argument, in the caller's line order.
* **The floor pass** (§7.2's `u_floor`, `priority::floor_pass`): it reads the capacity left
  after this pass and the replayed `done_this_period` (D9).
-/

namespace Tm

open Arith

/-! ## The unit and the level (D10, R10) -/

/-- The lookahead's one positive denominator (D10).  Capacity minutes are numerators over it. -/
abbrev Den := { d : Nat // 0 < d }

/-- The smart constructor: a zero denominator is refused. -/
def denOf? (d : Nat) : Option Den := if h : 0 < d then some ⟨d, h⟩ else none

theorem denOf?_refuses_zero : denOf? 0 = none := by
  unfold denOf?
  rw [dif_neg (by omega)]

theorem denOf?_accepts (d : Nat) (h : 0 < d) : (denOf? d).map Subtype.val = some d := by
  unfold denOf?
  rw [dif_pos h]
  rfl

/-- Whole minutes. -/
def Den.one : Den := ⟨1, Nat.one_pos⟩

/-- An energy level off the wire: `0..5`. -/
def levelOf? (n : Nat) : Option (Fin 6) := if h : n < 6 then some ⟨n, h⟩ else none

theorem levelOf?_refuses_six_and_above (n : Nat) (h : 6 ≤ n) : levelOf? n = none := by
  unfold levelOf?
  rw [dif_neg (by omega)]

theorem levelOf?_accepts (n : Nat) (h : n < 6) : (levelOf? n).map Fin.val = some n := by
  unfold levelOf?
  rw [dif_pos h]
  rfl

/-! ## `DayCapacity` and `Deadline` -/

/-- **§8.4's `DayCapacity` under D10**: a date, and at each energy level `0..5` the
numerator of the expected minutes over the lookahead's denominator. -/
structure DayCapacity where
  day   : Day
  numAt : Fin 6 → Nat

/-- The expected minutes at one level: an exact rational, never rounded. -/
def DayCapacity.minutesAt (c : DayCapacity) (den : Den) (l : Fin 6) : Pos :=
  mkPos (c.numAt l) den.val den.property

/-- The six numerators, level `0` first — for reading a witness. -/
def DayCapacity.levels (c : DayCapacity) : List Nat :=
  [c.numAt 0, c.numAt 1, c.numAt 2, c.numAt 3, c.numAt 4, c.numAt 5]

/-- A day from six numerators, level `0` first (missing levels are `0`). -/
def DayCapacity.ofLevels (day : Day) (ns : List Nat) : DayCapacity :=
  ⟨day, fun l => ns.getD l.val 0⟩

/-- Over one denominator the rational order is the numerators' order. -/
theorem minutesAt_le_iff (c c' : DayCapacity) (den : Den) (l : Fin 6) :
    Q.le (c'.minutesAt den l).val (c.minutesAt den l).val = true ↔ c'.numAt l ≤ c.numAt l := by
  constructor
  · intro h
    have := Q.le_elim h
    simp only [DayCapacity.minutesAt, mkPos_num, mkPos_den] at this
    exact Nat.le_of_mul_le_mul_right this den.property
  · intro h
    apply Q.le_of
    simp only [DayCapacity.minutesAt, mkPos_num, mkPos_den]
    exact Nat.mul_le_mul_right _ h

theorem minutesAt_eq_iff (c c' : DayCapacity) (den : Den) (l : Fin 6) :
    c'.minutesAt den l = c.minutesAt den l ↔ c'.numAt l = c.numAt l := by
  constructor
  · intro h
    have := congrArg (fun p : Pos => p.val.num) h
    simpa [DayCapacity.minutesAt] using this
  · intro h
    unfold DayCapacity.minutesAt
    rw [h]

/-- At whole minutes a level is the `Nat` it always was. -/
theorem minutesAt_one (c : DayCapacity) (l : Fin 6) :
    c.minutesAt Den.one l = posOfNat (c.numAt l) := rfl

/-- **§7.3's three numbers of one dated candidate** — `need(item)` in whole minutes (R1's
`needMin`, a ceiling), `item.ci`, and its effective due. -/
structure Deadline where
  need : Nat
  ci   : Fin 6
  due  : Day
deriving DecidableEq, Repr

/-- The need a reservation takes: R1's ceiling of `remaining × safety`
(`priority::safety_minutes`, rounded up per §3.5).  The remaining is an argument (D9). -/
def Deadline.ofRemaining (s : Pos) (rem : Nat) (ci : Fin 6) (due : Day) : Deadline :=
  ⟨needMin s rem, ci, due⟩

/-! ## One day: `capacity::reserve`'s inner loop

`for level in (min_ci..6).rev() { take = min(cap[level], left); cap[level] -= take;
left -= take }`.  Step `n` serves level `5 − n`.  `left − min(cap, left)` is
`left − cap` in truncated subtraction, which is how `dayLeft` is written. -/

/-- The level step `n` serves: `5, 4, …, 0`. -/
def stepLevel (n : Nat) : Fin 6 := ⟨5 - n, by omega⟩

theorem stepLevel_val (n : Nat) : (stepLevel n).val = 5 - n := rfl

theorem stepLevel_five_sub (l : Fin 6) : stepLevel (5 - l.val) = l := by
  apply Fin.ext
  simp only [stepLevel_val]
  have := l.isLt
  omega

/-- What a request of `left` numerator units still wants before the day's step `n`. -/
def dayLeft (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) : Nat → Nat
  | 0     => left
  | n + 1 => dayLeft ci f left n - (if ci.val ≤ 5 - n then f (stepLevel n) else 0)

/-- What step `n` takes: `min(cap, left)` at a matching level, nothing below `ci`. -/
def stepTake (ci : Fin 6) (f : Fin 6 → Nat) (left n : Nat) : Nat :=
  if ci.val ≤ 5 - n then min (f (stepLevel n)) (dayLeft ci f left n) else 0

/-- **`left -= take`, as the fork point writes it.** -/
theorem dayLeft_succ (ci : Fin 6) (f : Fin 6 → Nat) (left n : Nat) :
    dayLeft ci f left (n + 1) = dayLeft ci f left n - stepTake ci f left n := by
  simp only [dayLeft, stepTake]
  by_cases h : ci.val ≤ 5 - n <;> simp only [h, ↓reduceIte] <;> omega

theorem stepTake_le_left (ci : Fin 6) (f : Fin 6 → Nat) (left n : Nat) :
    stepTake ci f left n ≤ dayLeft ci f left n := by
  unfold stepTake
  split <;> omega

/-- What one level gives. -/
def dayTake (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) (l : Fin 6) : Nat :=
  if ci.val ≤ l.val then min (f l) (dayLeft ci f left (5 - l.val)) else 0

/-- The day after the reservation. -/
def dayRest (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) : Fin 6 → Nat := fun l =>
  if ci.val ≤ l.val then f l - dayLeft ci f left (5 - l.val) else f l

/-- What the request still wants after the day. -/
def dayOut (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) : Nat := dayLeft ci f left 6

/-- **`cap[level] -= take`, as the fork point writes it.** -/
theorem dayRest_eq_sub_take (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) (l : Fin 6) :
    dayRest ci f left l = f l - dayTake ci f left l := by
  unfold dayRest dayTake
  split <;> omega

theorem dayTake_eq_stepTake (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) (l : Fin 6) :
    dayTake ci f left l = stepTake ci f left (5 - l.val) := by
  unfold dayTake stepTake
  rw [stepLevel_five_sub]
  have : 5 - (5 - l.val) = l.val := by have := l.isLt; omega
  rw [this]

theorem dayTake_le (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) (l : Fin 6) :
    dayTake ci f left l ≤ f l := by
  unfold dayTake
  split <;> omega

theorem dayRest_le (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) (l : Fin 6) :
    dayRest ci f left l ≤ f l := by
  unfold dayRest
  split <;> omega

/-- **The ci filter: a level below `ci` is not touched.** -/
theorem dayRest_below_ci (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) (l : Fin 6)
    (h : l.val < ci.val) : dayRest ci f left l = f l := by
  unfold dayRest
  rw [if_neg (by omega)]

/-! ### The eligible minutes of a day: `DayCapacity::at_least` -/

/-- The eligible numerators of the top `n` levels. -/
def topElig (ci : Fin 6) (f : Fin 6 → Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => topElig ci f n + (if ci.val ≤ 5 - n then f (stepLevel n) else 0)

/-- `DayCapacity::at_least ci`: Σ over levels `≥ ci`. -/
def eligAt (ci : Fin 6) (f : Fin 6 → Nat) : Nat := topElig ci f 6

theorem dayLeft_eq_sub (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) :
    ∀ n, dayLeft ci f left n = left - topElig ci f n := by
  intro n
  induction n with
  | zero => simp [dayLeft, topElig]
  | succ n ih =>
    simp only [dayLeft, topElig, ih]
    by_cases h : ci.val ≤ 5 - n <;> simp only [h, ↓reduceIte] <;> omega

theorem dayOut_eq (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) :
    dayOut ci f left = left - eligAt ci f :=
  dayLeft_eq_sub ci f left 6

theorem dayOut_le (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) : dayOut ci f left ≤ left := by
  rw [dayOut_eq]
  omega

theorem topElig_mono_n (ci : Fin 6) (f : Fin 6 → Nat) {n m : Nat} (h : n ≤ m) :
    topElig ci f n ≤ topElig ci f m := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have := ih (by omega)
      simp only [topElig]
      omega
    · have : n = m + 1 := by omega
      subst this
      exact Nat.le_refl _

theorem topElig_mono_f (ci : Fin 6) {f f' : Fin 6 → Nat} (hf : ∀ l, f l ≤ f' l) :
    ∀ n, topElig ci f n ≤ topElig ci f' n := by
  intro n
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [topElig]
    have := hf (stepLevel n)
    by_cases h : ci.val ≤ 5 - n <;> simp only [h, ↓reduceIte] <;> omega

theorem eligAt_mono (ci : Fin 6) {f f' : Fin 6 → Nat} (hf : ∀ l, f l ≤ f' l) :
    eligAt ci f ≤ eligAt ci f' :=
  topElig_mono_f ci hf 6

theorem topElig_at (ci : Fin 6) (f : Fin 6 → Nat) (l : Fin 6) (hci : ci.val ≤ l.val) :
    topElig ci f (5 - l.val + 1) = topElig ci f (5 - l.val) + f l := by
  have hl := l.isLt
  simp only [topElig, stepLevel_five_sub]
  rw [if_pos (by omega)]

theorem topElig_at_le_eligAt (ci : Fin 6) (f : Fin 6 → Nat) (l : Fin 6) (hci : ci.val ≤ l.val) :
    topElig ci f (5 - l.val) + f l ≤ eligAt ci f := by
  rw [← topElig_at ci f l hci]
  have := l.isLt
  exact topElig_mono_n ci f (by omega)

/-! ### Conservation within a day -/

/-- The six levels' numerators. -/
def sum6 (f : Fin 6 → Nat) : Nat := f 0 + f 1 + f 2 + f 3 + f 4 + f 5

/-- What the top `n` steps take. -/
def topTake (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => topTake ci f left n + stepTake ci f left n

theorem topTake_add_dayLeft (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) :
    ∀ n, topTake ci f left n + dayLeft ci f left n = left := by
  intro n
  induction n with
  | zero => simp [topTake, dayLeft]
  | succ n ih =>
    have h := stepTake_le_left ci f left n
    rw [topTake, dayLeft_succ]
    omega

theorem sum6_dayTake (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) :
    sum6 (dayTake ci f left) = topTake ci f left 6 := by
  have e0 : dayTake ci f left 0 = stepTake ci f left 5 := dayTake_eq_stepTake ci f left 0
  have e1 : dayTake ci f left 1 = stepTake ci f left 4 := dayTake_eq_stepTake ci f left 1
  have e2 : dayTake ci f left 2 = stepTake ci f left 3 := dayTake_eq_stepTake ci f left 2
  have e3 : dayTake ci f left 3 = stepTake ci f left 2 := dayTake_eq_stepTake ci f left 3
  have e4 : dayTake ci f left 4 = stepTake ci f left 1 := dayTake_eq_stepTake ci f left 4
  have e5 : dayTake ci f left 5 = stepTake ci f left 0 := dayTake_eq_stepTake ci f left 5
  simp only [sum6, topTake, e0, e1, e2, e3, e4, e5]
  omega

/-- **A day spends exactly what it gives.** -/
theorem day_conserves (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) :
    sum6 (dayRest ci f left) + (left - dayOut ci f left) = sum6 f := by
  have h1 := topTake_add_dayLeft ci f left 6
  have h2 := sum6_dayTake ci f left
  have t0 := dayTake_le ci f left 0
  have t1 := dayTake_le ci f left 1
  have t2 := dayTake_le ci f left 2
  have t3 := dayTake_le ci f left 3
  have t4 := dayTake_le ci f left 4
  have t5 := dayTake_le ci f left 5
  simp only [sum6, dayRest_eq_sub_take, dayOut] at *
  omega

/-- **A day gives `min(left, at_least ci)`.** -/
theorem day_gives_the_min (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) :
    left - dayOut ci f left = min left (eligAt ci f) := by
  rw [dayOut_eq]
  omega

/-! ### The greedy order within a day -/

/-- A request of nothing leaves the day as it was. -/
theorem dayRest_zero (ci : Fin 6) (f : Fin 6 → Nat) : dayRest ci f 0 = f := by
  funext l
  unfold dayRest
  split
  · rw [dayLeft_eq_sub]
    omega
  · rfl

/-- A request at least the day's eligible minutes drains every eligible level. -/
theorem dayRest_drained (ci : Fin 6) (f : Fin 6 → Nat) {left : Nat} (hle : eligAt ci f ≤ left)
    (l : Fin 6) (hci : ci.val ≤ l.val) : dayRest ci f left l = 0 := by
  unfold dayRest
  rw [if_pos hci, dayLeft_eq_sub]
  have := topElig_at_le_eligAt ci f l hci
  omega

/-- A request the day cannot fill drains every eligible level. -/
theorem dayRest_drained_of_dayOut_pos (ci : Fin 6) (f : Fin 6 → Nat) {left : Nat}
    (h : 0 < dayOut ci f left) (l : Fin 6) (hci : ci.val ≤ l.val) : dayRest ci f left l = 0 := by
  rw [dayOut_eq] at h
  exact dayRest_drained ci f (by omega) l hci

/-- **Highest matching level first**: a level that gave anything has every higher matching
level drained. -/
theorem dayRest_drains_higher_levels (ci : Fin 6) (f : Fin 6 → Nat) (left : Nat) {l l' : Fin 6}
    (ht : dayRest ci f left l < f l) (hll : l.val < l'.val) (hci : ci.val ≤ l'.val) :
    dayRest ci f left l' = 0 := by
  have hl := l.isLt
  have hl' := l'.isLt
  unfold dayRest at ht ⊢
  rw [if_pos hci, dayLeft_eq_sub]
  split at ht
  · rw [dayLeft_eq_sub] at ht
    have h1 := topElig_at ci f l' hci
    have h2 := topElig_mono_n ci f (show 5 - l'.val + 1 ≤ 5 - l.val by omega)
    omega
  · omega

/-- Monotone: more capacity and a smaller request leave at least as much. -/
theorem dayRest_mono (ci : Fin 6) {f f' : Fin 6 → Nat} (hf : ∀ l, f l ≤ f' l) {left left' : Nat}
    (hl : left' ≤ left) (l : Fin 6) : dayRest ci f left l ≤ dayRest ci f' left' l := by
  unfold dayRest
  have := hf l
  have hE := topElig_mono_f ci hf (5 - l.val)
  split
  · rw [dayLeft_eq_sub, dayLeft_eq_sub]
    omega
  · exact this

theorem dayOut_mono (ci : Fin 6) {f f' : Fin 6 → Nat} (hf : ∀ l, f l ≤ f' l) {left left' : Nat}
    (hl : left' ≤ left) : dayOut ci f' left' ≤ dayOut ci f left := by
  rw [dayOut_eq, dayOut_eq]
  have := eligAt_mono ci hf
  omega

/-! ## The days: `capacity::available_until` and `capacity::reserve` -/

/-- **`capacity::available_until`**: Σ over days `≤ due` of the minutes at levels `≥ ci`. -/
def availUntil (due : Day) (ci : Fin 6) : List DayCapacity → Nat
  | []      => 0
  | c :: cs => (if c.day ≤ due then eligAt ci c.numAt else 0) + availUntil due ci cs

/-- **`capacity::reserve` over the days `≤ due`**: earliest day first. -/
def reserveRest (due : Day) (ci : Fin 6) : List DayCapacity → Nat → List DayCapacity
  | [],      _    => []
  | c :: cs, left =>
    if c.day ≤ due then
      ⟨c.day, dayRest ci c.numAt left⟩ :: reserveRest due ci cs (dayOut ci c.numAt left)
    else c :: reserveRest due ci cs left

/-- What the request still wants after the days `≤ due`. -/
def reserveOut (due : Day) (ci : Fin 6) : List DayCapacity → Nat → Nat
  | [],      left => left
  | c :: cs, left =>
    if c.day ≤ due then reserveOut due ci cs (dayOut ci c.numAt left)
    else reserveOut due ci cs left

/-- The total numerators of a list of days. -/
def totalMin : List DayCapacity → Nat
  | []      => 0
  | c :: cs => sum6 c.numAt + totalMin cs

theorem reserveOut_eq (due : Day) (ci : Fin 6) :
    ∀ (caps : List DayCapacity) (left : Nat),
      reserveOut due ci caps left = left - availUntil due ci caps
  | [], left => by simp [reserveOut, availUntil]
  | c :: cs, left => by
    have ih := reserveOut_eq due ci cs
    simp only [reserveOut, availUntil]
    by_cases h : c.day ≤ due
    · simp only [h, ↓reduceIte, ih, dayOut_eq]
      omega
    · simp only [h, ↓reduceIte, ih]
      omega

theorem reserveOut_le (due : Day) (ci : Fin 6) (caps : List DayCapacity) (left : Nat) :
    reserveOut due ci caps left ≤ left := by
  rw [reserveOut_eq]
  omega

/-- **The days give `min(left, available_until)`**: the fork point's `reserve` returns
less than asked exactly when the days run out. -/
theorem reserve_gives_the_min (due : Day) (ci : Fin 6) (caps : List DayCapacity) (left : Nat) :
    left - reserveOut due ci caps left = min left (availUntil due ci caps) := by
  rw [reserveOut_eq]
  omega

/-- **The days spend exactly what they give.** -/
theorem reserve_conserves (due : Day) (ci : Fin 6) :
    ∀ (caps : List DayCapacity) (left : Nat),
      totalMin (reserveRest due ci caps left) + (left - reserveOut due ci caps left) = totalMin caps
  | [], left => by simp [reserveRest, reserveOut, totalMin]
  | c :: cs, left => by
    have ih := reserve_conserves due ci cs
    simp only [reserveRest, reserveOut]
    by_cases h : c.day ≤ due
    · simp only [h, ↓reduceIte, totalMin]
      have hd := day_conserves ci c.numAt left
      have h1 := ih (dayOut ci c.numAt left)
      have h2 := reserveOut_le due ci cs (dayOut ci c.numAt left)
      have h3 := dayOut_le ci c.numAt left
      omega
    · simp only [h, ↓reduceIte, totalMin]
      have h1 := ih left
      have h2 := reserveOut_le due ci cs left
      omega

/-- A request of nothing leaves the days as they were. -/
theorem reserveRest_zero (due : Day) (ci : Fin 6) :
    ∀ caps : List DayCapacity, reserveRest due ci caps 0 = caps
  | [] => rfl
  | c :: cs => by
    have ih := reserveRest_zero due ci cs
    simp only [reserveRest]
    split
    · rw [dayRest_zero, dayOut_eq, Nat.zero_sub, ih]
    · rw [ih]

/-- **Fork-point `priority::compute` reserves `need.min(avail)`, not `need`; the clamp is
invisible.**  The kernel reserves the need and proves it the same. -/
theorem reserving_the_clamped_request_is_the_same (due : Day) (ci : Fin 6) :
    ∀ (caps : List DayCapacity) (left : Nat),
      reserveRest due ci caps (min left (availUntil due ci caps)) = reserveRest due ci caps left
  | [], _ => rfl
  | c :: cs, left => by
    have ih := reserving_the_clamped_request_is_the_same due ci cs
    simp only [availUntil, reserveRest]
    by_cases h : c.day ≤ due
    · simp only [h, ↓reduceIte]
      have hrest : dayRest ci c.numAt (min left (eligAt ci c.numAt + availUntil due ci cs))
          = dayRest ci c.numAt left := by
        funext l
        unfold dayRest
        split
        · rename_i hci
          rw [dayLeft_eq_sub, dayLeft_eq_sub]
          have := topElig_at_le_eligAt ci c.numAt l hci
          omega
        · rfl
      have hout : dayOut ci c.numAt (min left (eligAt ci c.numAt + availUntil due ci cs))
          = min (dayOut ci c.numAt left) (availUntil due ci cs) := by
        rw [dayOut_eq, dayOut_eq]
        omega
      rw [hrest, hout, ih]
    · simp only [h, ↓reduceIte, Nat.zero_add]
      rw [ih]

/-! ### What one reservation does to one day -/

/-- Two lists related position by position (core has no `List.Forall₂`). -/
inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → Forall2 R as bs → Forall2 R (a :: as) (b :: bs)

/-- The four facts about one day across one reservation for `(due, ci)`. -/
def Spent (due : Day) (ci : Fin 6) (c' c : DayCapacity) : Prop :=
  c'.day = c.day ∧ (∀ l, c'.numAt l ≤ c.numAt l) ∧
    (due < c.day → ∀ l, c'.numAt l = c.numAt l) ∧
    (∀ l : Fin 6, l.val < ci.val → c'.numAt l = c.numAt l)

theorem reserveRest_spent (due : Day) (ci : Fin 6) :
    ∀ (caps : List DayCapacity) (left : Nat),
      Forall2 (Spent due ci) (reserveRest due ci caps left) caps
  | [], _ => Forall2.nil
  | c :: cs, left => by
    simp only [reserveRest]
    split
    · rename_i h
      refine Forall2.cons ⟨rfl, dayRest_le ci c.numAt left, ?_, ?_⟩
        (reserveRest_spent due ci cs _)
      · intro hlt
        exact absurd h (Nat.not_le_of_lt hlt)
      · intro l hl
        exact dayRest_below_ci ci c.numAt left l hl
    · exact Forall2.cons ⟨rfl, fun _ => Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩
        (reserveRest_spent due ci cs _)

/-- **Earliest day first**: if a reservation touched a day, every earlier day `≤ due` has
every matching level drained. -/
theorem reserveRest_drains_earlier_days (due : Day) (ci : Fin 6) :
    ∀ (caps : List DayCapacity) (left i j : Nat) (a b a' b' : DayCapacity),
      i < j → caps[i]? = some a → caps[j]? = some b →
      (reserveRest due ci caps left)[i]? = some a' → (reserveRest due ci caps left)[j]? = some b' →
      (∃ l, b'.numAt l < b.numAt l) → a.day ≤ due →
      ∀ l : Fin 6, ci.val ≤ l.val → a'.numAt l = 0
  | [], _, _, _, _, _, _, _, _, ha, _, _, _, _, _ => by simp at ha
  | c :: cs, left, i, j, a, b, a', b', hij, ha, hb, ha', hb', ht, hdue => by
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
        subst ha
        simp only [List.getElem?_cons_succ] at hb
        simp only [reserveRest, hdue, ↓reduceIte, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.some.injEq] at ha' hb'
        subst ha'
        intro l hci
        by_cases hz : dayOut ci c.numAt left = 0
        · rw [hz, reserveRest_zero] at hb'
          rw [hb] at hb'
          cases hb'
          obtain ⟨l0, hl0⟩ := ht
          exact absurd hl0 (Nat.lt_irrefl _)
        · exact dayRest_drained_of_dayOut_pos ci c.numAt (by omega) l hci
      | succ i =>
        simp only [List.getElem?_cons_succ] at ha hb
        simp only [reserveRest] at ha' hb'
        split at ha' <;> split at hb' <;>
          simp only [List.getElem?_cons_succ] at ha' hb' <;>
          first
            | exact reserveRest_drains_earlier_days due ci cs _ i j a b a' b' (by omega)
                ha hb ha' hb' ht hdue
            | contradiction

/-! ### Monotone in the capacity (two runs) -/

/-- One day holds at least as much as another, on the same date. -/
def CapLe (c c' : DayCapacity) : Prop := c.day = c'.day ∧ ∀ l, c.numAt l ≤ c'.numAt l

theorem availUntil_mono (due : Day) (ci : Fin 6) :
    ∀ {caps caps' : List DayCapacity}, Forall2 CapLe caps caps' →
      availUntil due ci caps ≤ availUntil due ci caps'
  | _, _, Forall2.nil => Nat.le_refl _
  | c :: cs, c' :: cs', Forall2.cons hc hs => by
    have ih := availUntil_mono due ci hs
    simp only [availUntil]
    rw [← hc.1]
    have := eligAt_mono ci hc.2
    split <;> omega

theorem reserveRest_mono (due : Day) (ci : Fin 6) :
    ∀ {caps caps' : List DayCapacity}, Forall2 CapLe caps caps' →
      ∀ {left left' : Nat}, left' ≤ left →
        Forall2 CapLe (reserveRest due ci caps left) (reserveRest due ci caps' left')
  | _, _, Forall2.nil, _, _, _ => Forall2.nil
  | c :: cs, c' :: cs', Forall2.cons hc hs, left, left', hl => by
    simp only [reserveRest]
    rw [← hc.1]
    split
    · exact Forall2.cons ⟨rfl, dayRest_mono ci hc.2 hl⟩
        (reserveRest_mono due ci hs (dayOut_mono ci hc.2 hl))
    · exact Forall2.cons hc (reserveRest_mono due ci hs hl)

theorem reserveOut_anti (due : Day) (ci : Fin 6) {caps caps' : List DayCapacity}
    (h : Forall2 CapLe caps caps') {left left' : Nat} (hl : left' ≤ left) :
    reserveOut due ci caps' left' ≤ reserveOut due ci caps left := by
  rw [reserveOut_eq, reserveOut_eq]
  have := availUntil_mono due ci h
  omega

/-! ## §7.3's pass -/

/-- The earliest-deadline order: insert before the first deadline that is not earlier, so
equal dues keep their input order (`priority::compute`'s sort, ties by line then input). -/
def insertDue (d : Deadline) : List Deadline → List Deadline
  | []      => [d]
  | x :: xs => if d.due ≤ x.due then d :: x :: xs else x :: insertDue d xs

/-- **§7.3's `dated … sorted by due ascending`**, stable. -/
def sortDue : List Deadline → List Deadline
  | []      => []
  | d :: ds => insertDue d (sortDue ds)

/-- One deadline's outcome: what was available (before its own reservation) and what it
reserved, both numerators over the pass's denominator. -/
structure Grant where
  deadline : Deadline
  avail    : Nat
  reserved : Nat
deriving DecidableEq, Repr

/-- One step of the loop over the capacity left so far. -/
def grantOf (den : Nat) (caps : List DayCapacity) (d : Deadline) : Grant :=
  ⟨d, availUntil d.due d.ci caps, d.need * den - reserveOut d.due d.ci caps (d.need * den)⟩

/-- The capacity left after serving `ds` in the order given. -/
def edfCaps (den : Nat) : List DayCapacity → List Deadline → List DayCapacity
  | caps, []      => caps
  | caps, d :: ds => edfCaps den (reserveRest d.due d.ci caps (d.need * den)) ds

/-- The grants of serving `ds` in the order given. -/
def edfGrantsGo (den : Nat) : List DayCapacity → List Deadline → List Grant
  | _,    []      => []
  | caps, d :: ds =>
    grantOf den caps d :: edfGrantsGo den (reserveRest d.due d.ci caps (d.need * den)) ds

/-- **§7.3's pass**: capacities in, capacities out, deadlines served earliest first. -/
def edf (den : Den) (caps : List DayCapacity) (ds : List Deadline) : List DayCapacity :=
  edfCaps den.val caps (sortDue ds)

/-- **§7.3's per-item numbers**, in the order served. -/
def edfGrants (den : Den) (caps : List DayCapacity) (ds : List Deadline) : List Grant :=
  edfGrantsGo den.val caps (sortDue ds)

/-! ### The order -/

theorem perm_insertDue (d : Deadline) :
    ∀ xs : List Deadline, List.Perm (insertDue d xs) (d :: xs)
  | [] => List.Perm.refl _
  | x :: xs => by
    unfold insertDue
    split
    · exact List.Perm.refl _
    · exact ((perm_insertDue d xs).cons x).trans (List.Perm.swap d x xs)

theorem sortDue_perm : ∀ ds : List Deadline, List.Perm (sortDue ds) ds
  | [] => List.Perm.refl _
  | d :: ds => (perm_insertDue d (sortDue ds)).trans ((sortDue_perm ds).cons d)

theorem mem_sortDue {d : Deadline} {ds : List Deadline} : d ∈ sortDue ds ↔ d ∈ ds :=
  (sortDue_perm ds).mem_iff

theorem sorted_insertDue (d : Deadline) :
    ∀ xs : List Deadline, xs.Pairwise (fun a b => a.due ≤ b.due) →
      (insertDue d xs).Pairwise (fun a b => a.due ≤ b.due)
  | [], _ => List.pairwise_singleton _ _
  | x :: xs, h => by
    rw [List.pairwise_cons] at h
    unfold insertDue
    split
    · rename_i hle
      refine List.Pairwise.cons ?_ (List.Pairwise.cons h.1 h.2)
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hle
      · exact Nat.le_trans hle (h.1 b hb)
    · rename_i hlt
      refine List.Pairwise.cons ?_ (sorted_insertDue d xs h.2)
      intro b hb
      rcases ((perm_insertDue d xs).mem_iff.trans List.mem_cons).mp hb with rfl | hb
      · exact Nat.le_of_lt (Nat.lt_of_not_le hlt)
      · exact h.1 b hb

/-- **Earliest deadline first**: the served order is sorted by due. -/
theorem sortDue_sorted : ∀ ds : List Deadline, (sortDue ds).Pairwise (fun a b => a.due ≤ b.due)
  | [] => List.Pairwise.nil
  | d :: ds => sorted_insertDue d _ (sortDue_sorted ds)

theorem filter_due_insertDue (t : Day) (d : Deadline) :
    ∀ xs : List Deadline,
      (insertDue d xs).filter (fun x => decide (x.due = t)) =
        (d :: xs).filter (fun x => decide (x.due = t))
  | [] => rfl
  | x :: xs => by
    have ih := filter_due_insertDue t d xs
    unfold insertDue
    split
    · rfl
    · rename_i hlt
      by_cases hd : d.due = t
      · have hx : ¬ x.due = t := by
          intro hx
          exact hlt (Nat.le_of_eq (hd.trans hx.symm))
        simp [ih, hd, hx]
      · simp [List.filter_cons, ih, hd]

/-- **Ties keep their input order** (the caller's line order): the deadlines of one due
are served in the order given. -/
theorem sortDue_is_stable (t : Day) :
    ∀ ds : List Deadline,
      (sortDue ds).filter (fun x => decide (x.due = t)) = ds.filter (fun x => decide (x.due = t))
  | [] => rfl
  | d :: ds => by
    simp only [sortDue]
    rw [filter_due_insertDue, List.filter_cons, List.filter_cons, sortDue_is_stable t ds]

theorem insertDue_append_last (x d : Deadline) (h : x.due ≤ d.due) :
    ∀ L : List Deadline, insertDue x (L ++ [d]) = insertDue x L ++ [d]
  | [] => by simp [insertDue, h]
  | y :: L => by
    simp only [List.cons_append, insertDue]
    split
    · rfl
    · rw [insertDue_append_last x d h L]
      rfl

theorem sortDue_append_last (d : Deadline) :
    ∀ ds : List Deadline, (∀ x ∈ ds, x.due ≤ d.due) → sortDue (ds ++ [d]) = sortDue ds ++ [d]
  | [], _ => rfl
  | x :: ds, h => by
    simp only [List.cons_append, sortDue]
    rw [sortDue_append_last d ds (fun y hy => h y (List.mem_cons_of_mem x hy))]
    exact insertDue_append_last x d (h x (List.mem_cons_self)) _

theorem edfGrantsGo_deadlines (den : Nat) :
    ∀ (caps : List DayCapacity) (ds : List Deadline), (edfGrantsGo den caps ds).map Grant.deadline = ds
  | _, [] => rfl
  | caps, d :: ds => by
    simp only [edfGrantsGo, List.map_cons, grantOf]
    rw [edfGrantsGo_deadlines den _ ds]

/-- The grants are the deadlines, in the served order. -/
theorem edfGrants_deadlines (den : Den) (caps : List DayCapacity) (ds : List Deadline) :
    (edfGrants den caps ds).map Grant.deadline = sortDue ds :=
  edfGrantsGo_deadlines den.val caps (sortDue ds)

theorem edfGrants_length (den : Den) (caps : List DayCapacity) (ds : List Deadline) :
    (edfGrants den caps ds).length = ds.length := by
  have := congrArg List.length (edfGrants_deadlines den caps ds)
  rw [List.length_map] at this
  rw [this]
  exact (sortDue_perm ds).length_eq

/-- **EDF order is respected: an earlier deadline is served first.** -/
theorem edf_serves_an_earlier_deadline_first (den : Den) (caps : List DayCapacity)
    (ds : List Deadline) {d₁ d₂ : Deadline} (h₁ : d₁ ∈ ds) (h₂ : d₂ ∈ ds) (hlt : d₁.due < d₂.due) :
    ∃ i j : Nat, i < j ∧ (edfGrants den caps ds)[i]?.map Grant.deadline = some d₁ ∧
      (edfGrants den caps ds)[j]?.map Grant.deadline = some d₂ := by
  simp only [← List.getElem?_map, edfGrants_deadlines]
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (mem_sortDue.mpr h₁)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (mem_sortDue.mpr h₂)
  refine ⟨i, j, ?_, hi, hj⟩
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact hij
  · subst hij
    rw [hi] at hj
    cases hj
    exact absurd hlt (Nat.lt_irrefl _)
  · obtain ⟨hi', hi⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hj', hj⟩ := List.getElem?_eq_some_iff.mp hj
    have := List.pairwise_iff_getElem.mp (sortDue_sorted ds) j i hj' hi' hij
    rw [hi, hj] at this
    exact absurd hlt (Nat.not_lt_of_le this)

/-- **A later deadline takes nothing from an earlier one** (two runs): adding a deadline no
earlier than any other leaves every earlier grant as it was, and it is served over exactly
what those left. -/
theorem edf_a_later_deadline_takes_nothing_from_an_earlier_one (den : Den)
    (caps : List DayCapacity) (ds : List Deadline) (d : Deadline) (h : ∀ x ∈ ds, x.due ≤ d.due) :
    edfGrants den caps (ds ++ [d]) = edfGrants den caps ds ++ [grantOf den.val (edf den caps ds) d] := by
  unfold edfGrants edf
  rw [sortDue_append_last d ds h]
  generalize sortDue ds = L
  induction L generalizing caps with
  | nil => rfl
  | cons x L ih =>
    simp only [List.cons_append, edfGrantsGo, edfCaps]
    rw [ih]

/-! ### What the pass does to the days -/

/-- The facts about one day across the whole pass. -/
def PassSpent (ds : List Deadline) (c' c : DayCapacity) : Prop :=
  c'.day = c.day ∧ (∀ l, c'.numAt l ≤ c.numAt l) ∧
    ((∀ d ∈ ds, d.due < c.day) → ∀ l, c'.numAt l = c.numAt l) ∧
    (∀ l : Fin 6, (∀ d ∈ ds, l.val < d.ci.val) → c'.numAt l = c.numAt l)

theorem forall₂_refl {α : Type} {R : α → α → Prop} (hR : ∀ a, R a a) :
    ∀ l : List α, Forall2 R l l
  | [] => Forall2.nil
  | a :: l => Forall2.cons (hR a) (forall₂_refl hR l)

theorem forall₂_trans {α : Type} {R S T : α → α → Prop} (hT : ∀ a b c, R a b → S b c → T a c) :
    ∀ {l₁ l₂ l₃ : List α}, Forall2 R l₁ l₂ → Forall2 S l₂ l₃ → Forall2 T l₁ l₃
  | _, _, _, Forall2.nil, Forall2.nil => Forall2.nil
  | _, _, _, Forall2.cons h₁ t₁, Forall2.cons h₂ t₂ =>
    Forall2.cons (hT _ _ _ h₁ h₂) (forall₂_trans hT t₁ t₂)

theorem forall₂_length {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, Forall2 R l₁ l₂ → l₁.length = l₂.length
  | _, _, Forall2.nil => rfl
  | _, _, Forall2.cons _ t => by simp [forall₂_length t]

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, Forall2 R l₁ l₂ →
      ∀ {n : Nat} {a : α} {b : β}, l₁[n]? = some a → l₂[n]? = some b → R a b
  | _, _, Forall2.nil, _, _, _, ha, _ => by simp at ha
  | _, _, Forall2.cons h t, n, a, b, ha, hb => by
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
      subst ha
      subst hb
      exact h
    | succ n =>
      simp only [List.getElem?_cons_succ] at ha hb
      exact forall₂_getElem? t ha hb

theorem edfCaps_spent (den : Nat) :
    ∀ (caps : List DayCapacity) (ds : List Deadline), Forall2 (PassSpent ds) (edfCaps den caps ds) caps
  | caps, [] => forall₂_refl
      (fun c => ⟨rfl, fun _ => Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩) caps
  | caps, d :: ds => by
    simp only [edfCaps]
    refine forall₂_trans ?_ (edfCaps_spent den _ ds) (reserveRest_spent d.due d.ci caps (d.need * den))
    intro o m c hom hmc
    refine ⟨hom.1.trans hmc.1, fun l => Nat.le_trans (hom.2.1 l) (hmc.2.1 l), ?_, ?_⟩
    · intro hall l
      have hm := hmc.2.2.1 (hall d List.mem_cons_self) l
      have ho := hom.2.2.1 (fun x hx => by rw [hmc.1]; exact hall x (List.mem_cons_of_mem d hx)) l
      rw [ho, hm]
    · intro l hall
      have hm := hmc.2.2.2 l (hall d List.mem_cons_self)
      have ho := hom.2.2.2 l (fun x hx => hall x (List.mem_cons_of_mem d hx))
      rw [ho, hm]

/-- **P\*, stage 5, §7.3.  The pass keeps the same days**: reservation is subtraction, not a
filter. -/
theorem edf_keeps_the_days (den : Den) (caps : List DayCapacity) (ds : List Deadline) :
    (edf den caps ds).length = caps.length :=
  forall₂_length (edfCaps_spent den.val caps (sortDue ds))

/-- …and the same dates, in the same order. -/
theorem edf_keeps_the_dates (den : Den) (caps : List DayCapacity) (ds : List Deadline) :
    (edf den caps ds).map DayCapacity.day = caps.map DayCapacity.day := by
  have h := edfCaps_spent den.val caps (sortDue ds)
  unfold edf
  generalize edfCaps den.val caps (sortDue ds) = out at h
  induction h with
  | nil => rfl
  | cons hc _ ih => simp only [List.map_cons, hc.1, ih]

/-- The numerator form of `edf_only_spends_capacity`: `Goals.lean`'s statement over
`minutesAt : Fin 6 → Nat`, verbatim, for the numerators at every denominator. -/
theorem edf_only_spends_numerators (den : Den) (caps : List DayCapacity) (ds : List Deadline)
    (n : Nat) (c c' : DayCapacity) (l : Fin 6)
    (h : caps[n]? = some c) (h' : (edf den caps ds)[n]? = some c') :
    c'.numAt l ≤ c.numAt l :=
  (forall₂_getElem? (edfCaps_spent den.val caps (sortDue ds)) h' h).2.1 l

/-- **P\*, stage 5, §7.3, over D10's rational minutes.  The pass only ever spends
capacity.**  Rules out E1's shape one layer up: a reservation that grows the pool it draws
from makes every downstream `u` optimistic and nothing downstream can detect it. -/
theorem edf_only_spends_capacity (den : Den) (caps : List DayCapacity) (ds : List Deadline)
    (n : Nat) (c c' : DayCapacity) (l : Fin 6)
    (h : caps[n]? = some c) (h' : (edf den caps ds)[n]? = some c') :
    Q.le (c'.minutesAt den l).val (c.minutesAt den l).val = true :=
  (minutesAt_le_iff c c' den l).mpr (edf_only_spends_numerators den caps ds n c c' l h h')

/-- **P\*, stage 5, §7.3, over D10's rational minutes.**  "what is left after earlier
deadlines": a day past every deadline in the pass is untouched by it.  Rules out an EDF
pass that reserves *after* an item's due date and so reports capacity the item can never
use — which is exactly how a HOT item comes out looking comfortable. -/
theorem edf_reserves_only_before_the_deadline (den : Den) (caps : List DayCapacity)
    (ds : List Deadline) (n : Nat) (c c' : DayCapacity) (l : Fin 6)
    (h : caps[n]? = some c) (h' : (edf den caps ds)[n]? = some c')
    (hafter : ∀ d ∈ ds, d.due < c.day) :
    c'.minutesAt den l = c.minutesAt den l :=
  (minutesAt_eq_iff c c' den l).mpr
    ((forall₂_getElem? (edfCaps_spent den.val caps (sortDue ds)) h' h).2.2.1
      (fun d hd => hafter d (mem_sortDue.mp hd)) l)

/-- **The ci filter, across the pass**: a level below every deadline's `ci` is untouched. -/
theorem edf_spares_levels_below_every_ci (den : Den) (caps : List DayCapacity)
    (ds : List Deadline) (n : Nat) (c c' : DayCapacity) (l : Fin 6)
    (h : caps[n]? = some c) (h' : (edf den caps ds)[n]? = some c')
    (hbelow : ∀ d ∈ ds, l.val < d.ci.val) :
    c'.minutesAt den l = c.minutesAt den l :=
  (minutesAt_eq_iff c c' den l).mpr
    ((forall₂_getElem? (edfCaps_spent den.val caps (sortDue ds)) h' h).2.2.2 l
      (fun d hd => hbelow d (mem_sortDue.mp hd)))

/-- The numerators reserved by a list of grants. -/
def reservedTotal : List Grant → Nat
  | []      => 0
  | g :: gs => g.reserved + reservedTotal gs

theorem edfCaps_conserves (den : Nat) :
    ∀ (caps : List DayCapacity) (ds : List Deadline),
      totalMin (edfCaps den caps ds) + reservedTotal (edfGrantsGo den caps ds) = totalMin caps
  | caps, [] => by simp [edfCaps, edfGrantsGo, reservedTotal]
  | caps, d :: ds => by
    simp only [edfCaps, edfGrantsGo, reservedTotal, grantOf]
    have h1 := edfCaps_conserves den (reserveRest d.due d.ci caps (d.need * den)) ds
    have h2 := reserve_conserves d.due d.ci caps (d.need * den)
    omega

/-- **The pass spends exactly what it reserves**: the minutes before are the minutes after
plus the minutes granted.  Nothing is created and nothing is lost. -/
theorem edf_spends_exactly_what_it_reserves (den : Den) (caps : List DayCapacity)
    (ds : List Deadline) :
    totalMin (edf den caps ds) + reservedTotal (edfGrants den caps ds) = totalMin caps :=
  edfCaps_conserves den.val caps (sortDue ds)

/-! ### What each grant says -/

/-- The shortfall, in numerator units: the need the pass could not reserve. -/
def Grant.shortfall (den : Nat) (g : Grant) : Nat := g.deadline.need * den - g.reserved

/-- The minutes available before this deadline's own reservation, as a rational. -/
def Grant.availQ (g : Grant) (den : Den) : Pos := mkPos g.avail den.val den.property

/-- The minutes reserved, as a rational. -/
def Grant.reservedQ (g : Grant) (den : Den) : Pos := mkPos g.reserved den.val den.property

/-- The shortfall, as a rational. -/
def Grant.shortfallQ (g : Grant) (den : Den) : Pos :=
  mkPos (g.shortfall den.val) den.val den.property

/-- **§7.3's `u ≥ 1`**, by cross-multiplication against the rational availability. -/
def Grant.hot (g : Grant) (den : Den) : Bool := utilQGe g.deadline.need (g.availQ den) hotEdge

/-- **§7.3's IMPOSSIBLE**: `need > avail`, cross-multiplied. -/
def Grant.impossible (g : Grant) (den : Den) : Bool := decide (g.avail < g.deadline.need * den.val)

theorem Grant.hot_iff (g : Grant) (den : Den) :
    g.hot den = decide (g.avail ≤ g.deadline.need * den.val) := by
  simp only [Grant.hot, utilQGe_cross, Grant.availQ, mkPos_num, mkPos_den, hotEdge, ofNat,
    Nat.one_mul]

theorem Grant.impossible_imp_hot (g : Grant) (den : Den) (h : g.impossible den = true) :
    g.hot den = true := by
  simp only [Grant.impossible, decide_eq_true_eq] at h
  rw [Grant.hot_iff, decide_eq_true_eq]
  omega

theorem grantOf_reserved (den : Nat) (caps : List DayCapacity) (d : Deadline) :
    (grantOf den caps d).reserved = min (d.need * den) (grantOf den caps d).avail :=
  reserve_gives_the_min d.due d.ci caps (d.need * den)

theorem edfGrantsGo_exact (den : Nat) :
    ∀ (caps : List DayCapacity) (ds : List Deadline), ∀ g ∈ edfGrantsGo den caps ds,
      g.reserved = min (g.deadline.need * den) g.avail
  | _, [], g, hg => by simp [edfGrantsGo] at hg
  | caps, d :: ds, g, hg => by
    simp only [edfGrantsGo, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact grantOf_reserved den caps d
    · exact edfGrantsGo_exact den _ ds g hg

/-- **§7.3's `reserve = min(need(item), avail)`**, for every grant of the pass. -/
theorem edf_reserves_the_min (den : Den) (caps : List DayCapacity) (ds : List Deadline)
    (g : Grant) (hg : g ∈ edfGrants den caps ds) :
    g.reserved = min (g.deadline.need * den.val) g.avail :=
  edfGrantsGo_exact den.val caps (sortDue ds) g hg

/-- **Reserved minutes never exceed the need** — in rationals, `reserved ≤ need`. -/
theorem edf_reserves_no_more_than_the_need (den : Den) (caps : List DayCapacity)
    (ds : List Deadline) (g : Grant) (hg : g ∈ edfGrants den caps ds) :
    Q.le (g.reservedQ den).val (ofNat g.deadline.need) = true := by
  have := edf_reserves_the_min den caps ds g hg
  apply Q.le_of
  simp only [Grant.reservedQ, mkPos_num, mkPos_den, ofNat, Nat.mul_one]
  omega

/-- …nor what was available. -/
theorem edf_reserves_no_more_than_was_available (den : Den) (caps : List DayCapacity)
    (ds : List Deadline) (g : Grant) (hg : g ∈ edfGrants den caps ds) :
    g.reserved ≤ g.avail := by
  have := edf_reserves_the_min den caps ds g hg
  omega

/-- **The shortfall is exactly need minus reserved, and it is reported**: reserved and
shortfall add up to the need, in rationals. -/
theorem edf_reports_the_shortfall (den : Den) (caps : List DayCapacity) (ds : List Deadline)
    (g : Grant) (hg : g ∈ edfGrants den caps ds) :
    g.reserved + g.shortfall den.val = g.deadline.need * den.val ∧
      Q.equiv ⟨g.reserved + g.shortfall den.val, den.val⟩ (ofNat g.deadline.need) = true := by
  have := edf_reserves_the_min den caps ds g hg
  have h : g.reserved + g.shortfall den.val = g.deadline.need * den.val := by
    unfold Grant.shortfall
    omega
  refine ⟨h, ?_⟩
  unfold Q.equiv
  exact decide_eq_true (by show (g.reserved + g.shortfall den.val) * 1 = g.deadline.need * den.val; omega)

/-- **Fork-point `shortfall_min = need.saturating_sub(avail)`**: the same number. -/
theorem edf_shortfall_is_need_minus_avail (den : Den) (caps : List DayCapacity)
    (ds : List Deadline) (g : Grant) (hg : g ∈ edfGrants den caps ds) :
    g.shortfall den.val = g.deadline.need * den.val - g.avail := by
  have := edf_reserves_the_min den caps ds g hg
  unfold Grant.shortfall
  omega

/-- **Both directions of IMPOSSIBLE**: a grant is IMPOSSIBLE exactly when it reports a
shortfall. -/
theorem edf_impossible_iff_shortfall (den : Den) (caps : List DayCapacity) (ds : List Deadline)
    (g : Grant) (hg : g ∈ edfGrants den caps ds) :
    g.impossible den = true ↔ 0 < g.shortfall den.val := by
  rw [edf_shortfall_is_need_minus_avail den caps ds g hg]
  simp only [Grant.impossible, decide_eq_true_eq]
  omega

/-! ### More capacity never hurts (two runs, D5) -/

/-- Two grants for one deadline, the second with at least as much. -/
def GrantLe (g g' : Grant) : Prop :=
  g.deadline = g'.deadline ∧ g.avail ≤ g'.avail ∧ g.reserved ≤ g'.reserved

theorem edfCaps_mono (den : Nat) :
    ∀ (ds : List Deadline) {caps caps' : List DayCapacity}, Forall2 CapLe caps caps' →
      Forall2 CapLe (edfCaps den caps ds) (edfCaps den caps' ds)
  | [], _, _, h => h
  | d :: ds, _, _, h => by
    simp only [edfCaps]
    exact edfCaps_mono den ds (reserveRest_mono d.due d.ci h (Nat.le_refl _))

theorem edfGrantsGo_mono (den : Nat) :
    ∀ (ds : List Deadline) {caps caps' : List DayCapacity}, Forall2 CapLe caps caps' →
      Forall2 GrantLe (edfGrantsGo den caps ds) (edfGrantsGo den caps' ds)
  | [], _, _, _ => Forall2.nil
  | d :: ds, caps, caps', h => by
    simp only [edfGrantsGo]
    refine Forall2.cons ⟨rfl, availUntil_mono d.due d.ci h, ?_⟩
      (edfGrantsGo_mono den ds (reserveRest_mono d.due d.ci h (Nat.le_refl _)))
    have := reserveOut_anti d.due d.ci h (Nat.le_refl (d.need * den))
    simp only [grantOf]
    omega

/-- **More capacity leaves more capacity** (two runs). -/
theorem edf_more_capacity_leaves_more_capacity (den : Den) (ds : List Deadline)
    {caps caps' : List DayCapacity} (h : Forall2 CapLe caps caps') :
    Forall2 CapLe (edf den caps ds) (edf den caps' ds) :=
  edfCaps_mono den.val (sortDue ds) h

/-- **Adding capacity never increases a shortfall** (two runs, D5): every deadline sees at
least as much available, reserves at least as much, and falls at most as short. -/
theorem edf_more_capacity_never_raises_a_shortfall (den : Den) (ds : List Deadline)
    {caps caps' : List DayCapacity} (h : Forall2 CapLe caps caps') :
    Forall2 (fun g g' => GrantLe g g' ∧ g'.shortfall den.val ≤ g.shortfall den.val)
      (edfGrants den caps ds) (edfGrants den caps' ds) := by
  have hm := edfGrantsGo_mono den.val (sortDue ds) h
  unfold edfGrants
  generalize edfGrantsGo den.val caps (sortDue ds) = gs at hm
  generalize edfGrantsGo den.val caps' (sortDue ds) = gs' at hm
  induction hm with
  | nil => exact Forall2.nil
  | cons hg _ ih =>
    refine Forall2.cons ⟨hg, ?_⟩ ih
    unfold Grant.shortfall
    rw [hg.1]
    have := hg.2.2
    omega

/-! ## The lookahead the pass is handed -/

/-- Strictly ascending days: list order is date order, and no date twice. -/
def daysAscending : List DayCapacity → Bool
  | []            => true
  | [_]           => true
  | a :: b :: cs  => decide (a.day < b.day) && daysAscending (b :: cs)

/-- **§8.4's lookahead as the pass consumes it**: one positive denominator, ascending days. -/
abbrev Lookahead := { p : Den × List DayCapacity // daysAscending p.2 = true }

/-- The smart constructor. -/
def lookaheadOf? (den : Nat) (days : List DayCapacity) : Option Lookahead :=
  match denOf? den with
  | some d => if h : daysAscending days = true then some ⟨(d, days), h⟩ else none
  | none   => none

theorem lookaheadOf?_refuses_a_zero_denominator (days : List DayCapacity) :
    lookaheadOf? 0 days = none := by
  simp [lookaheadOf?, denOf?_refuses_zero]

theorem lookaheadOf?_refuses_unsorted_days (den : Nat) (days : List DayCapacity)
    (h : daysAscending days = false) : lookaheadOf? den days = none := by
  unfold lookaheadOf?
  split
  · rw [dif_neg (by simp [h])]
  · rfl

theorem lookaheadOf?_accepts (den : Nat) (hd : 0 < den) (days : List DayCapacity)
    (h : daysAscending days = true) :
    (lookaheadOf? den days).map (fun la => (la.val.1.val, la.val.2.length)) = some (den, days.length) := by
  unfold lookaheadOf? denOf?
  rw [dif_pos hd]
  simp only [dif_pos h, Option.map_some]

theorem daysAscending_pairwise :
    ∀ days : List DayCapacity, daysAscending days = true → days.Pairwise (fun a b => a.day < b.day)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: cs, h => by
    simp only [daysAscending, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := daysAscending_pairwise (b :: cs) h.2
    refine List.Pairwise.cons ?_ ih
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

/-! ## Witnesses (both directions, decided)

Each is small by design (AGENTS §5.10): a handful of days and deadlines, probed under an
8 GB cap before it was committed. -/

/-- Fork-point `capacity.rs`'s own unit test, two days at whole minutes. -/
def rustTestCaps : List DayCapacity :=
  [DayCapacity.ofLevels 7 [0, 0, 0, 60, 60, 60], DayCapacity.ofLevels 8 [0, 0, 0, 60, 0, 0]]

/-- **Fork-point `reserve_takes_the_best_levels_earliest`, transcribed**: 90 minutes at
`ci ≥ 4` take day 7's level 5 and half of its level 4 and leave day 8 alone; a further 60
minutes at `ci ≥ 5` find nothing. -/
theorem reserve_takes_the_best_levels_earliest :
    (reserveRest 8 4 rustTestCaps 90).map DayCapacity.levels =
        [[0, 0, 0, 60, 30, 0], [0, 0, 0, 60, 0, 0]] ∧
      reserveOut 8 4 rustTestCaps 90 = 0 ∧
      reserveOut 8 5 (reserveRest 8 4 rustTestCaps 90) 60 = 60 := by
  decide

/-- Two days of 60 minutes at level 3. -/
def edfExampleCaps : List DayCapacity :=
  [DayCapacity.ofLevels 1 [0, 0, 0, 60, 0, 0], DayCapacity.ofLevels 2 [0, 0, 0, 60, 0, 0]]

/-- A later deadline listed before an earlier one. -/
def edfExampleDeadlines : List Deadline := [⟨90, 3, 2⟩, ⟨60, 3, 1⟩]

/-- **EDF order and the shortfall, on a witness.**  The due-1 deadline is served first
though it is listed second: 60 available, 60 reserved, HOT and not IMPOSSIBLE.  The due-2
deadline then sees the 60 minutes day 2 still has against a need of 90: IMPOSSIBLE, 30
short, and the shortfall is reported.  Served in input order it would have taken 90 and
starved the earlier deadline (cheat 87). -/
theorem edf_serves_the_earlier_deadline_first_on_a_witness :
    (edfGrants Den.one edfExampleCaps edfExampleDeadlines).map
        (fun g => (g.deadline.due, g.avail, g.reserved, g.shortfall 1)) = [(1, 60, 60, 0), (2, 60, 60, 30)] ∧
      (edfGrants Den.one edfExampleCaps edfExampleDeadlines).map
        (fun g => (g.hot Den.one, g.impossible Den.one)) = [(true, false), (true, true)] ∧
      (edf Den.one edfExampleCaps edfExampleDeadlines).map DayCapacity.levels =
        [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]] := by
  decide

/-- **Both directions of the deadline, on a witness**: a 30-minute reservation due on day 1
spends day 1 and leaves day 2 as it was. -/
theorem edf_spends_before_the_deadline_and_not_after_on_a_witness :
    (edf Den.one edfExampleCaps [⟨30, 3, 1⟩]).map DayCapacity.levels =
      [[0, 0, 0, 30, 0, 0], [0, 0, 0, 60, 0, 0]] := by
  decide

/-- Half-minute numerators: the denominator of a `p_lounge = ½` mixture. -/
def halfDen : Den := ⟨2, by decide⟩

/-- One day, `½·(61 at level 5, lounge) + ½·(61 at level 4, home)`: `30½` minutes at each of
levels 4 and 5, over `halfDen`. -/
def mixtureCaps : List DayCapacity := [DayCapacity.ofLevels 1 [0, 0, 0, 0, 61, 61]]

/-- The same day with each level floored to whole minutes. -/
def flooredCaps : List DayCapacity := [DayCapacity.ofLevels 1 [0, 0, 0, 0, 30, 30]]

/-- **Why D10 carries capacity exact through the pass.**  A 61-minute need at `ci ≥ 4`
against the exact mixture (`30½ + 30½ = 61` minutes) is HOT, fully reserved, no shortfall.
Against the per-level floor (`30 + 30 = 60`) it is IMPOSSIBLE with a minute short.  A
rounding between the mixture and the pass changes §7.3's verdict. -/
theorem flooring_the_capacity_changes_the_verdict :
    mixtureCaps.map (fun c => ((c.minutesAt halfDen 4).val, (c.minutesAt halfDen 5).val)) =
        [(⟨61, 2⟩, ⟨61, 2⟩)] ∧
      (edfGrants halfDen mixtureCaps [⟨61, 4, 1⟩]).map
        (fun g => (g.avail, g.reserved, g.shortfall 2, g.impossible halfDen)) = [(122, 122, 0, false)] ∧
      (edfGrants Den.one flooredCaps [⟨61, 4, 1⟩]).map
        (fun g => (g.avail, g.reserved, g.shortfall 1, g.impossible Den.one)) = [(60, 60, 1, true)] := by
  decide

/-- **The ci filter, both directions, on a witness**: 60 minutes at level 4 are nothing to a
`ci 5` item and enough for a `ci 4` one. -/
theorem the_ci_filter_on_a_witness :
    (edfGrants Den.one [DayCapacity.ofLevels 1 [0, 0, 0, 0, 60, 0]] [⟨30, 5, 1⟩]).map
        (fun g => (g.avail, g.reserved, g.shortfall 1)) = [(0, 0, 30)] ∧
      (edfGrants Den.one [DayCapacity.ofLevels 1 [0, 0, 0, 0, 60, 0]] [⟨30, 4, 1⟩]).map
        (fun g => (g.avail, g.reserved, g.shortfall 1)) = [(60, 30, 0)] := by
  decide

/-- **Ties keep input order, on a witness.** -/
theorem sortDue_keeps_ties_in_input_order_on_a_witness :
    sortDue [⟨10, 0, 2⟩, ⟨20, 0, 1⟩, ⟨30, 0, 2⟩] = [⟨20, 0, 1⟩, ⟨10, 0, 2⟩, ⟨30, 0, 2⟩] := by
  decide

/-- **The lookahead's smart constructor, both directions**: days out of order, a repeated
day and a zero denominator are refused; the mixture day over `2` is accepted. -/
theorem lookaheadOf?_on_witnesses :
    (lookaheadOf? 1 [DayCapacity.ofLevels 2 [], DayCapacity.ofLevels 1 []]).isNone = true ∧
      (lookaheadOf? 1 [DayCapacity.ofLevels 1 [], DayCapacity.ofLevels 1 []]).isNone = true ∧
      (lookaheadOf? 2 mixtureCaps).isSome = true ∧
      (lookaheadOf? 0 mixtureCaps).isNone = true := by
  decide

/-- Three days with every level filled. -/
def deepCaps : List DayCapacity :=
  [DayCapacity.ofLevels 1 [10, 20, 30, 40, 50, 60], DayCapacity.ofLevels 2 [10, 20, 30, 40, 50, 60],
   DayCapacity.ofLevels 3 [10, 20, 30, 40, 50, 60]]

/-- Five deadlines, out of order, three of them due on day 3. -/
def deepDeadlines : List Deadline := [⟨100, 2, 3⟩, ⟨70, 4, 1⟩, ⟨200, 0, 2⟩, ⟨40, 5, 3⟩, ⟨300, 1, 3⟩]

/-- **Five deadlines over three days, worked by hand and decided.**  Served in the order
due 1, due 2, then the three due-3 deadlines in input order.  The last one finds 200 of its
300 minutes and reports 100 short.  `630 = 20 + (70 + 200 + 100 + 40 + 200)`: the minutes
left plus the minutes reserved. -/
theorem edf_five_deadlines_over_three_days :
    (edfGrants Den.one deepCaps deepDeadlines).map
        (fun g => (g.deadline.need, g.avail, g.reserved, g.shortfall 1)) =
      [(70, 110, 70, 0), (200, 350, 200, 0), (100, 300, 100, 0), (40, 60, 40, 0), (300, 200, 200, 100)] ∧
    (edf Den.one deepCaps deepDeadlines).map DayCapacity.levels =
      [[0, 0, 0, 0, 0, 0], [10, 0, 0, 0, 0, 0], [10, 0, 0, 0, 0, 0]] ∧
    totalMin deepCaps = 630 := by
  decide

/-! ## Gap 106: the pass as the compiled code runs it (`@[csimp]`; stage 5 D10 L8)

APPENDED 2026-09-14 (stage 5, D10 track, step L8).  `reserveRest` returned
`⟨c.day, dayRest ci c.numAt left⟩` for every day up to the due date, a closure over the previous
`numAt`: after `k` deadlines a level was read through `k` closures, each also reading the levels
above it (`dayLeft`), and `availUntil`, `reserveRest`, `reserveOut`, `edfCaps` and `edfGrantsGo`
recursed once per day or deadline, not in tail position.  Measured through the wire over a 3,660-day
lookahead (README, "Stage 5 D10 L8"): 40 deadlines took 18.4 s.

The twins below are what the compiled code runs.  Each is proved equal to its definition, so each
law above, the EDF laws included, is still about the definition (D5: none is restated), and the
compiled program is that definition (the stage-4 `Fast.lean` device).

* `availUntilFast`: a `foldl`.
* `reserveRestAcc`: an accumulator, stopping at a request of nothing (fork `reserve`'s `left == 0`
  break; `reserveRest_zero` is why the rest is unchanged), each reserved day's six numerators held
  once (`NumSix`), so a later read is constant time.
* `edfStepFast`: one deadline's grant and reservation; `edfGrantsGoFast` and `edfCapsFast` are one
  `foldl` over the deadlines.

`edf`, `edfGrants`, `availUntil`, `reserveRest` and `reserveOut` were compiled before these lemmas, so
each gets a twin compiled after them, with a `csimp` lemma of its own. -/

/-- Six numerators, held: a `DayCapacity`'s `numAt` is a function, so a level read re-runs what
built it; `NumSix` is built once and read in constant time. -/
structure NumSix where
  n0 : Nat
  n1 : Nat
  n2 : Nat
  n3 : Nat
  n4 : Nat
  n5 : Nat

def NumSix.of (f : Fin 6 → Nat) : NumSix := ⟨f 0, f 1, f 2, f 3, f 4, f 5⟩

def NumSix.get (s : NumSix) (l : Fin 6) : Nat :=
  if l.val = 0 then s.n0 else if l.val = 1 then s.n1 else if l.val = 2 then s.n2
  else if l.val = 3 then s.n3 else if l.val = 4 then s.n4 else s.n5

theorem NumSix.get_of (f : Fin 6 → Nat) : (NumSix.of f).get = f := by
  funext l
  obtain ⟨n, hn⟩ := l
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `availUntil` as a `foldl`. -/
def availUntilFast (due : Day) (ci : Fin 6) (caps : List DayCapacity) : Nat :=
  caps.foldl (fun a c => if c.day ≤ due then a + eligAt ci c.numAt else a) 0

theorem availUntil_foldl (due : Day) (ci : Fin 6) :
    ∀ (caps : List DayCapacity) (a : Nat),
      caps.foldl (fun a c => if c.day ≤ due then a + eligAt ci c.numAt else a) a = a + availUntil due ci caps
  | [], a => by simp [availUntil]
  | c :: cs, a => by
    simp only [List.foldl_cons, availUntil]
    rw [availUntil_foldl due ci cs]
    split <;> omega

@[csimp] theorem availUntil_eq_availUntilFast : @availUntil = @availUntilFast := by
  funext due ci caps
  simp [availUntilFast, availUntil_foldl]

/-- `reserveRest` with an accumulator: stops at a request of nothing (fork `reserve`'s `left == 0`
break), holds each reserved day's six numerators once. -/
def reserveRestAcc (due : Day) (ci : Fin 6) : List DayCapacity → Nat → List DayCapacity → List DayCapacity
  | [],      _,    acc => acc.reverse
  | c :: cs, left, acc =>
    if left = 0 then acc.reverseAux (c :: cs)
    else if c.day ≤ due then
      reserveRestAcc due ci cs (dayOut ci c.numAt left)
        (⟨c.day, (NumSix.of (dayRest ci c.numAt left)).get⟩ :: acc)
    else reserveRestAcc due ci cs left (c :: acc)

theorem reserveRestAcc_eq (due : Day) (ci : Fin 6) :
    ∀ (caps : List DayCapacity) (left : Nat) (acc : List DayCapacity),
      reserveRestAcc due ci caps left acc = acc.reverse ++ reserveRest due ci caps left
  | [], left, acc => by simp [reserveRestAcc, reserveRest]
  | c :: cs, left, acc => by
    unfold reserveRestAcc
    by_cases h0 : left = 0
    · subst h0
      rw [if_pos rfl, reserveRest_zero, List.reverseAux_eq]
    · rw [if_neg h0]
      simp only [reserveRest]
      split
      · rw [reserveRestAcc_eq due ci cs, NumSix.get_of]
        simp
      · rw [reserveRestAcc_eq due ci cs]
        simp

/-- One deadline of the pass, over the capacity left so far: its grant consed on, the days after its
reservation. -/
def edfStepFast (den : Nat) (acc : List DayCapacity × List Grant) (d : Deadline) :
    List DayCapacity × List Grant :=
  let want := d.need * den
  let a := availUntilFast d.due d.ci acc.1
  (reserveRestAcc d.due d.ci acc.1 want [], ⟨d, a, want - (want - a)⟩ :: acc.2)

theorem edfStepFast_foldl (den : Nat) :
    ∀ (ds : List Deadline) (caps : List DayCapacity) (gs : List Grant),
      ds.foldl (edfStepFast den) (caps, gs) = (edfCaps den caps ds, (edfGrantsGo den caps ds).reverse ++ gs)
  | [], caps, gs => by simp [edfCaps, edfGrantsGo]
  | d :: ds, caps, gs => by
    simp only [List.foldl_cons, edfStepFast]
    rw [reserveRestAcc_eq, List.reverse_nil, List.nil_append]
    have hg : (⟨d, availUntilFast d.due d.ci caps, d.need * den - (d.need * den - availUntilFast d.due d.ci caps)⟩ : Grant)
        = grantOf den caps d := by
      simp only [grantOf, reserveOut_eq, ← availUntil_eq_availUntilFast]
    rw [hg, edfStepFast_foldl den ds]
    simp [edfCaps, edfGrantsGo]

/-- `edfGrantsGo` as the compiled code runs it: one `foldl` over the deadlines. -/
def edfGrantsGoFast (den : Nat) (caps : List DayCapacity) (ds : List Deadline) : List Grant :=
  (ds.foldl (edfStepFast den) (caps, [])).2.reverse

/-- `edfCaps` as the compiled code runs it. -/
def edfCapsFast (den : Nat) (caps : List DayCapacity) (ds : List Deadline) : List DayCapacity :=
  (ds.foldl (edfStepFast den) (caps, [])).1

@[csimp] theorem edfGrantsGo_eq_edfGrantsGoFast : @edfGrantsGo = @edfGrantsGoFast := by
  funext den caps ds
  simp [edfGrantsGoFast, edfStepFast_foldl]

@[csimp] theorem edfCaps_eq_edfCapsFast : @edfCaps = @edfCapsFast := by
  funext den caps ds
  simp [edfCapsFast, edfStepFast_foldl]


/-- `reserveRest` as the compiled code runs it. -/
def reserveRestFast (due : Day) (ci : Fin 6) (caps : List DayCapacity) (left : Nat) : List DayCapacity :=
  reserveRestAcc due ci caps left []

@[csimp] theorem reserveRest_eq_reserveRestFast : @reserveRest = @reserveRestFast := by
  funext due ci caps left
  simp only [reserveRestFast, reserveRestAcc_eq, List.reverse_nil, List.nil_append]

/-- `reserveOut` as the compiled code runs it: `reserveOut_eq`. -/
def reserveOutFast (due : Day) (ci : Fin 6) (caps : List DayCapacity) (left : Nat) : Nat :=
  left - availUntilFast due ci caps

@[csimp] theorem reserveOut_eq_reserveOutFast : @reserveOut = @reserveOutFast := by
  funext due ci caps left
  rw [reserveOut_eq, availUntil_eq_availUntilFast]
  rfl

/-- `edf`, compiled after `edfCaps_eq_edfCapsFast`. -/
def edfFast (den : Den) (caps : List DayCapacity) (ds : List Deadline) : List DayCapacity :=
  edfCaps den.val caps (sortDue ds)

@[csimp] theorem edf_eq_edfFast : @edf = @edfFast := rfl

/-- `edfGrants`, compiled after `edfGrantsGo_eq_edfGrantsGoFast`. -/
def edfGrantsFast (den : Den) (caps : List DayCapacity) (ds : List Deadline) : List Grant :=
  edfGrantsGo den.val caps (sortDue ds)

@[csimp] theorem edfGrants_eq_edfGrantsFast : @edfGrants = @edfGrantsFast := rfl

end Tm
