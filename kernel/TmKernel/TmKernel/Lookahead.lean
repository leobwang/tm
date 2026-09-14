import TmKernel.Capacity
import TmKernel.Cal
/-!
# Lookahead — D10's exact mixture over step 3's EDF (stage 5, track L)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §13.  This module **produces** the
`List DayCapacity` that `Capacity.lean`'s `edf` consumes, and never restates it.  Step L1
(§13.2) builds the unit, the weight and the mixture.  Step L2 (§13.3, pulled from stage 6
by the owner's D12) builds the day's window, E7, in real seconds through `Cal`'s zone
table, and the plan's walls; its section below says what it ports and what it refutes.
**Stage 6's `dayPlan` must reuse L2's `windowEnd`, `windowOn`, `wallIndex` and `wallsOn`,
never a second copy** (design §2.3).  The slot cut, energy and the budget limit's slots are
L3–L4's, so each location's histogram is still an argument.

## The owner's D10 and D17, and the fork point they replace

Fork-point `capacity::lookahead` (tm-core/src/capacity.rs) picks **one** location per future
day, `lounge` iff `model.p_lounge_on(wd, cfg) >= 0.5`, and keeps that location's
budget-limited minutes as `u32`.  Under D10 a future day's capacity is the **expected**
minutes, `p·lounge + (1 − p)·home`, carried exactly through the EDF pass.  Parity entry P1
(refined) records the difference; `twin_is_the_forks_threshold` states the twin L7 checks it
through.

* **One unit, `capDen = 10^18` (D17, OWNER Q8 (b)).**  A weight `p = w / capDen` with
  `w : Nat`, `w ≤ capDen` (`Weight`).  Every capacity numerator is over `capDen`, so step 3's
  one-denominator contract (`Den`, its README (d1)–(d3)) holds with no `lcm` over weekdays.
* **The weight is decoded, never rounded** (`mkWeight?`).  Rust hands the kernel `p_lounge` as
  the decimal pair of its shortest round-trip text (`0.9` → `9 / 10`; §13.6's
  `decimal_pair`).  The pair is accepted exactly when `d ≠ 0`, `n ≤ d` and `d ∣ capDen`, and
  the weight is then `n · (capDen / d)`, which denotes `n / d` exactly
  (`mkWeight?_denotes`).  The three refusals are named: `badWeight` (a zero denominator),
  `weightAboveOne` (`n > d`), `weightPrecision` (`capDen % d ≠ 0`, which for a decimal
  denominator `10^k` is exactly "more than 18 places": `mkWeight?_refuses_more_than_18_places`).
  A negative weight and NaN cannot be spelled as a `Nat` pair; the wire refuses them in L6.
* **Mix after each location's budget limit (D10-3).**  `mix w lounge home` takes the two
  already-limited histograms.  Mixing first and limiting the mixture is a different number
  (`mixing_before_the_budget_is_not_the_expectation`), equal only at a certain weight
  (`mixing_before_the_budget_agrees_at_a_certain_weight`).

## R10: the widths

| value | bound | where |
|---|---|---|
| `Weight` | `w ≤ capDen = 10^18 < 2^60` | the subtype; `mkWeight?` is its only decoder |
| an accepted pair `n / d` | `n ≤ d ≤ 10^18` | `mkWeight?_accepted_width` |
| a mixed level numerator | `≤ capDen · max lounge home`; at L6's `≤ 1440` minutes a level, `≤ 1440 · 10^18 < 2^71` | `mix_width` |

Unit counts exceed 2^53 and `u64` from one minute up, so they cross the wire as **digit
strings** and the host holds them as `u128` (D17; the wire is L6's, `Boundary.lean`).

## The recursion rule (D9-21)

L1 recurses over no list the wire can make large: a histogram is `Fin 6 → Nat`, and the
scaling laws recurse over step 3's own `reserveRest`/`edfCaps` only inside proofs.  L2's
walls are listed in its section: every run-time pass is a `foldl` or core's tail-recursive
`map`/`filter`/`filterMap`, and the one quadratic sort is behind a proved `@[csimp]` twin
(`windowEnd_eq_windowEndFast`).

## Not here, by name

* `pureDay`, `lookahead`, `Input`, `mkInput?` (L5); the cut and energy (L3–L4).
* The zone table's refusal of a sub-minute offset (`badTz subMinuteOffset`, §13.6): L6's.
  L2's window counts seconds, so it needs no such refusal to be exact.
* Day 0 (`ofHist` over the host's histogram until L9, gap 93 of the design).
* The wire (`capacity`, `lookahead` sections, digit strings): L6.
-/

namespace Tm
namespace Look

open Arith

/-! ## The unit and the weight (D17, R10) -/

/-- **The lookahead's one denominator**: `10^18` (the owner's D17). -/
def capDen : Nat := 1000000000000000000

theorem capDen_eq_pow : capDen = 10 ^ 18 := by decide

theorem capDen_pos : 0 < capDen := by decide

/-- `capDen` as step 3's `Den`. -/
def capDenD : Den := ⟨capDen, capDen_pos⟩

/-- A lounge weight: `p = w / capDen`, `0 ≤ p ≤ 1` by the type. -/
abbrev Weight := { w : Nat // w ≤ capDen }

/-- The certain weights. -/
def Weight.home : Weight := ⟨0, Nat.zero_le _⟩
def Weight.lounge : Weight := ⟨capDen, Nat.le_refl _⟩

/-- Why a weight pair is refused, by name (AGENTS §5.7). -/
inductive WErr where
  | badWeight
  | weightAboveOne
  | weightPrecision
deriving DecidableEq, Repr

private theorem scaled_le {n d : Nat} (hn : n ≤ d) (hp : capDen % d = 0) :
    n * (capDen / d) ≤ capDen := by
  have h1 : n * (capDen / d) ≤ d * (capDen / d) := Nat.mul_le_mul_right _ hn
  have h2 : d * (capDen / d) = capDen := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hp)
  omega

/-- **The smart constructor** (R10): Rust's decimal pair `n / d`, accepted exactly when it
denotes a rational in `[0, 1]` that `capDen` represents.  Checked in the order
`badWeight`, `weightAboveOne`, `weightPrecision`.  Never rounds. -/
def mkWeight? (n d : Nat) : Except WErr Weight :=
  if d = 0 then .error .badWeight
  else if hn : n ≤ d then
    if hp : capDen % d = 0 then .ok ⟨n * (capDen / d), scaled_le hn hp⟩
    else .error .weightPrecision
  else .error .weightAboveOne

theorem mkWeight?_zero_den (n : Nat) : mkWeight? n 0 = .error .badWeight := by
  simp [mkWeight?]

theorem mkWeight?_above_one {n d : Nat} (hd : 0 < d) (h : d < n) :
    mkWeight? n d = .error .weightAboveOne := by
  unfold mkWeight?
  rw [if_neg (by omega), dif_neg (by omega)]

theorem mkWeight?_precision {n d : Nat} (hd : 0 < d) (hn : n ≤ d) (hp : capDen % d ≠ 0) :
    mkWeight? n d = .error .weightPrecision := by
  unfold mkWeight?
  rw [if_neg (by omega), dif_pos hn, dif_neg hp]

/-- **More than 18 decimal places is refused**, whatever the digits: a denominator `10^k`,
`k > 18`, does not divide `capDen`.  (A written trailing zero counts as a place; the host's
shortest round-trip text has none.) -/
theorem mkWeight?_refuses_more_than_18_places {n k : Nat} (hk : 18 < k) (hn : n ≤ 10 ^ k) :
    mkWeight? n (10 ^ k) = .error .weightPrecision := by
  have hlt : capDen < 10 ^ k := by
    rw [capDen_eq_pow]
    exact Nat.pow_lt_pow_right (by decide) hk
  apply mkWeight?_precision (by omega) hn
  rw [Nat.mod_eq_of_lt hlt]
  exact Nat.ne_of_gt capDen_pos

theorem mkWeight?_accepts {n d : Nat} (hd : 0 < d) (hn : n ≤ d) (hp : capDen % d = 0) :
    mkWeight? n d = .ok ⟨n * (capDen / d), scaled_le hn hp⟩ := by
  unfold mkWeight?
  rw [if_neg (by omega), dif_pos hn, dif_pos hp]

/-- What an accepted pair satisfied. -/
theorem mkWeight?_ok_elim {n d : Nat} {w : Weight} (h : mkWeight? n d = .ok w) :
    0 < d ∧ n ≤ d ∧ capDen % d = 0 ∧ w.val = n * (capDen / d) := by
  unfold mkWeight? at h
  by_cases hd : d = 0
  · rw [if_pos hd] at h; cases h
  · rw [if_neg hd] at h
    by_cases hn : n ≤ d
    · rw [dif_pos hn] at h
      by_cases hp : capDen % d = 0
      · rw [dif_pos hp] at h
        cases h
        exact ⟨by omega, hn, hp, rfl⟩
      · rw [dif_neg hp] at h; cases h
    · rw [dif_neg hn] at h; cases h

/-- **An accepted weight denotes the pair exactly**: `w / capDen = n / d`. -/
theorem mkWeight?_denotes {n d : Nat} {w : Weight} (h : mkWeight? n d = .ok w) :
    w.val * d = n * capDen := by
  obtain ⟨_, _, hp, hw⟩ := mkWeight?_ok_elim h
  rw [hw, Nat.mul_assoc, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hp)]

/-- **R10's width of an accepted pair**: `n ≤ d ≤ capDen`. -/
theorem mkWeight?_accepted_width {n d : Nat} {w : Weight} (h : mkWeight? n d = .ok w) :
    n ≤ d ∧ d ≤ capDen := by
  obtain ⟨hd, hn, hp, _⟩ := mkWeight?_ok_elim h
  exact ⟨hn, Nat.le_of_dvd capDen_pos (Nat.dvd_of_mod_eq_zero hp)⟩

/-- The complement denotes `1 − n / d` exactly. -/
theorem mkWeight?_complement {n d : Nat} {w : Weight} (h : mkWeight? n d = .ok w) :
    (capDen - w.val) * d = (d - n) * capDen := by
  have hden := mkWeight?_denotes h
  rw [Nat.sub_mul, Nat.sub_mul, hden, Nat.mul_comm capDen d]

/-- **The fit's two-decimal weight, accepted** (`mkWeight?_round2`): `9/10` is `9·10^17`. -/
theorem mkWeight?_round2 : (mkWeight? 9 10).map Subtype.val = .ok 900000000000000000 := by
  rfl

/-! ## The mixture (§13.2, D10-3) -/

/-- Whole minutes per level, one location, one day, **after** that location's budget limit. -/
abbrev Hist := Fin 6 → Nat

/-- **D10's mixture**: `w·lounge + (capDen − w)·home` at each level, numerators over
`capDen`. -/
def mix (w : Weight) (lounge home : Hist) : Hist := fun l =>
  w.val * lounge l + (capDen - w.val) * home l

/-- A future day's capacity. -/
def mixDay (d : Day) (w : Weight) (lounge home : Hist) : DayCapacity := ⟨d, mix w lounge home⟩

/-- A pure histogram over `capDen` (day 0 until L9: no mixture). -/
def ofHist (d : Day) (h : Hist) : DayCapacity := ⟨d, fun l => capDen * h l⟩

/-- A histogram from six levels, level `0` first (missing levels are `0`). -/
def histOf (ns : List Nat) : Hist := fun l => ns.getD l.val 0

private theorem convex_between (c w a b : Nat) (hw : w ≤ c) :
    c * min a b ≤ w * a + (c - w) * b ∧ w * a + (c - w) * b ≤ c * max a b := by
  have hc : c = w + (c - w) := by omega
  constructor
  · have h1 : w * min a b ≤ w * a := Nat.mul_le_mul_left _ (Nat.min_le_left a b)
    have h2 : (c - w) * min a b ≤ (c - w) * b := Nat.mul_le_mul_left _ (Nat.min_le_right a b)
    have h3 : c * min a b = w * min a b + (c - w) * min a b := by
      conv => lhs; rw [hc]
      rw [Nat.add_mul]
    omega
  · have h1 : w * a ≤ w * max a b := Nat.mul_le_mul_left _ (Nat.le_max_left a b)
    have h2 : (c - w) * b ≤ (c - w) * max a b := Nat.mul_le_mul_left _ (Nat.le_max_right a b)
    have h3 : c * max a b = w * max a b + (c - w) * max a b := by
      conv => lhs; rw [hc]
      rw [Nat.add_mul]
    omega

/-- **The mixture lies between the locations**, at every level. -/
theorem mix_between_the_locations (w : Weight) (L H : Hist) (l : Fin 6) :
    capDen * min (L l) (H l) ≤ mix w L H l ∧ mix w L H l ≤ capDen * max (L l) (H l) :=
  convex_between capDen w.val (L l) (H l) w.property

/-- **At weight 0 the day is home's.** -/
theorem mix_at_zero_is_home (w : Weight) (hw : w.val = 0) (L H : Hist) :
    mix w L H = fun l => capDen * H l := by
  funext l
  simp [mix, hw]

/-- **At weight `capDen` the day is the lounge's.** -/
theorem mix_at_one_is_lounge (w : Weight) (hw : w.val = capDen) (L H : Hist) :
    mix w L H = fun l => capDen * L l := by
  funext l
  simp [mix, hw]

/-- The certain weights, as days: `mixDay` is `ofHist` of the certain location. -/
theorem mixDay_at_a_certain_weight (d : Day) (L H : Hist) :
    mixDay d Weight.home L H = ofHist d H ∧ mixDay d Weight.lounge L H = ofHist d L := by
  refine ⟨?_, ?_⟩
  · simp only [mixDay, ofHist, mix_at_zero_is_home Weight.home rfl]
  · simp only [mixDay, ofHist, mix_at_one_is_lounge Weight.lounge rfl]

/-- **The mixture denotes `p·L + (1 − p)·H` exactly** for the decoded `p = n / d`. -/
theorem mix_denotes_the_weighted_sum {n d : Nat} {w : Weight} (h : mkWeight? n d = .ok w)
    (L H : Hist) (l : Fin 6) :
    mix w L H l * d = capDen * (n * L l + (d - n) * H l) := by
  have h1 := mkWeight?_denotes h
  have h2 := mkWeight?_complement h
  simp only [mix, Nat.add_mul]
  have e1 : w.val * L l * d = L l * (w.val * d) := by ac_rfl
  have e2 : (capDen - w.val) * H l * d = H l * ((capDen - w.val) * d) := by ac_rfl
  rw [e1, e2, h1, h2, Nat.mul_add]
  ac_rfl

/-- **The same, as step 3's rational minutes**: level `l` of the mixed day, read over
`capDenD`, is the rational `(n·L + (d − n)·H) / d`. -/
theorem mixDay_minutesAt_is_the_expectation {n d : Nat} {w : Weight}
    (h : mkWeight? n d = .ok w) (day : Day) (L H : Hist) (l : Fin 6) :
    Q.equiv ((mixDay day w L H).minutesAt capDenD l).val ⟨n * L l + (d - n) * H l, d⟩ = true := by
  simp only [Q.equiv, DayCapacity.minutesAt, mkPos_num, mkPos_den, mixDay, capDenD]
  apply decide_eq_true
  rw [mix_denotes_the_weighted_sum h]
  exact Nat.mul_comm _ _

/-- **R10's width of a mixed level.** -/
theorem mix_width (w : Weight) (L H : Hist) (l : Fin 6) (b : Nat) (hL : L l ≤ b) (hH : H l ≤ b) :
    mix w L H l ≤ capDen * b := by
  have h := (mix_between_the_locations w L H l).2
  have : capDen * max (L l) (H l) ≤ capDen * b := Nat.mul_le_mul_left _ (Nat.max_le.mpr ⟨hL, hH⟩)
  omega

/-! ### What a deadline sees: `DayCapacity::at_least` is linear -/

theorem topElig_lin (ci : Fin 6) (a b : Nat) (f g : Hist) :
    ∀ k, topElig ci (fun l => a * f l + b * g l) k = a * topElig ci f k + b * topElig ci g k := by
  intro k
  induction k with
  | zero => simp [topElig]
  | succ k ih =>
    simp only [topElig, ih]
    by_cases h : ci.val ≤ 5 - k
    · simp only [h, ↓reduceIte, Nat.mul_add]
      omega
    · simp only [h, ↓reduceIte, Nat.add_zero]

theorem eligAt_mix (ci : Fin 6) (w : Weight) (L H : Hist) :
    eligAt ci (mix w L H) = w.val * eligAt ci L + (capDen - w.val) * eligAt ci H :=
  topElig_lin ci _ _ L H 6

/-- **What an item of `ci` can use lies between the locations too.** -/
theorem mix_atLeast_between_the_locations (ci : Fin 6) (w : Weight) (L H : Hist) :
    capDen * min (eligAt ci L) (eligAt ci H) ≤ eligAt ci (mix w L H) ∧
      eligAt ci (mix w L H) ≤ capDen * max (eligAt ci L) (eligAt ci H) := by
  rw [eligAt_mix]
  exact convex_between capDen w.val _ _ w.property

/-! ## The budget limit, and why the mixture comes after it (D10-3)

Fork-point `limit_to_budget` sorts the slots by energy descending and takes
`budget × block_min` minutes greedily.  Over a histogram that is step 3's inner loop at
`ci = 0`: the highest level first, `min(cap, left)` at each (`dayTake`).  L4 proves the
per-slot sort equal to it (`limitSlots_is_limitHist`). -/

/-- **The budget limit over a histogram**: keep `B` minutes (numerator units), highest
level first. -/
def limitHist (B : Nat) (h : Hist) : Hist := dayTake ⟨0, by decide⟩ h B

/-- The limit keeps `min(B, the day)`. -/
theorem limitHist_keeps_the_min (B : Nat) (h : Hist) :
    sum6 (limitHist B h) = min B (sum6 h) := by
  have h1 := sum6_dayTake ⟨0, by decide⟩ h B
  have h2 := topTake_add_dayLeft ⟨0, by decide⟩ h B 6
  have h3 := day_gives_the_min ⟨0, by decide⟩ h B
  have h4 : eligAt ⟨0, by decide⟩ h = sum6 h := by
    simp [eligAt, topElig, stepLevel, sum6]
    omega
  simp only [limitHist, dayOut] at *
  omega

private theorem dayLeft_scale (k : Nat) (ci : Fin 6) (f : Hist) (left : Nat) :
    ∀ n, dayLeft ci (fun l => k * f l) (k * left) n = k * dayLeft ci f left n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [dayLeft, ih]
    by_cases h : ci.val ≤ 5 - n
    · simp only [h, ↓reduceIte, Nat.mul_sub]
    · simp only [h, ↓reduceIte, Nat.sub_zero]

theorem dayTake_scale (k : Nat) (ci : Fin 6) (f : Hist) (left : Nat) :
    dayTake ci (fun l => k * f l) (k * left) = fun l => k * dayTake ci f left l := by
  funext l
  simp only [dayTake, dayLeft_scale]
  split
  · exact (Nat.mul_min_mul_left k _ _)
  · simp

theorem dayRest_scale (k : Nat) (ci : Fin 6) (f : Hist) (left : Nat) :
    dayRest ci (fun l => k * f l) (k * left) = fun l => k * dayRest ci f left l := by
  funext l
  simp only [dayRest, dayLeft_scale]
  split
  · exact (Nat.mul_sub _ _ _).symm
  · rfl

theorem dayOut_scale (k : Nat) (ci : Fin 6) (f : Hist) (left : Nat) :
    dayOut ci (fun l => k * f l) (k * left) = k * dayOut ci f left :=
  dayLeft_scale k ci f left 6

/-- **At a certain weight the order does not matter**: limiting the pure location in
`capDen` units is `capDen` times limiting it in minutes. -/
theorem mixing_before_the_budget_agrees_at_a_certain_weight (B : Nat) (L H : Hist) :
    limitHist (B * capDen) (mix Weight.home L H) = mix Weight.home (limitHist B L) (limitHist B H) ∧
      limitHist (B * capDen) (mix Weight.lounge L H) =
        mix Weight.lounge (limitHist B L) (limitHist B H) := by
  rw [mix_at_zero_is_home Weight.home rfl, mix_at_zero_is_home Weight.home rfl,
    mix_at_one_is_lounge Weight.lounge rfl, mix_at_one_is_lounge Weight.lounge rfl]
  simp only [limitHist, Nat.mul_comm B capDen, dayTake_scale, and_self]

/-- The witness: budget 60 minutes; lounge 60 minutes at each of levels 5 and 4; home 120
minutes at level 3; `p = ½`. -/
def budgetWitnessL : Hist := histOf [0, 0, 0, 0, 60, 60]
def budgetWitnessH : Hist := histOf [0, 0, 0, 120, 0, 0]
def halfWeight : Weight := ⟨500000000000000000, by decide⟩

/-- **Mixing before the budget limit is not the expectation** (D10-3).  Each location's day
keeps 60 minutes: level 5 in the lounge, level 3 at home, so the expected day holds 30 at
level 5 and 30 at level 3.  Mixing first gives 30 at 5, 30 at 4 and 60 at 3, and the limit
then keeps 5 and 4 and drops level 3 altogether. -/
theorem mixing_before_the_budget_is_not_the_expectation :
    ∃ (w : Weight) (B : Nat) (L H : Hist) (l : Fin 6),
      mix w (limitHist B L) (limitHist B H) l ≠ limitHist (B * capDen) (mix w L H) l :=
  ⟨halfWeight, 60, budgetWitnessL, budgetWitnessH, 3, by decide⟩

/-- The witness's numbers, level by level (level `0` first), for the README. -/
theorem mixing_before_the_budget_on_the_witness :
    (List.finRange 6).map (mix halfWeight (limitHist 60 budgetWitnessL) (limitHist 60 budgetWitnessH))
        = [0, 0, 0, 30 * capDen, 0, 30 * capDen] ∧
      (List.finRange 6).map (limitHist (60 * capDen) (mix halfWeight budgetWitnessL budgetWitnessH))
        = [0, 0, 0, 0, 30 * capDen, 30 * capDen] := by
  decide

/-! ## The threshold twin (parity P1, step L7) -/

/-- **The fork point's location as a weight**: lounge iff `p ≥ ½`. -/
def twin (w : Weight) : Weight := if capDen ≤ 2 * w.val then Weight.lounge else Weight.home

/-- The twin's day is the fork point's chosen location, in `capDen` units. -/
theorem twin_is_the_forks_location (w : Weight) (L H : Hist) :
    mix (twin w) L H = fun l => capDen * (if capDen ≤ 2 * w.val then L l else H l) := by
  unfold twin
  by_cases h : capDen ≤ 2 * w.val
  · simp only [h, ↓reduceIte, mix_at_one_is_lounge Weight.lounge rfl]
  · simp only [h, ↓reduceIte, mix_at_zero_is_home Weight.home rfl]

/-- **The twin's test is the fork point's `p >= 0.5`** on the decoded pair: `2w ≥ capDen`
iff `2n ≥ d`.  Exact, because `0.5` is a double and the host's text round-trips. -/
theorem twin_is_the_forks_threshold {n d : Nat} {w : Weight} (h : mkWeight? n d = .ok w) :
    capDen ≤ 2 * w.val ↔ d ≤ 2 * n := by
  obtain ⟨hd, _, _, _⟩ := mkWeight?_ok_elim h
  have hden := mkWeight?_denotes h
  constructor
  · intro hle
    have : capDen * d ≤ 2 * w.val * d := Nat.mul_le_mul_right d hle
    have e : 2 * w.val * d = 2 * n * capDen := by rw [Nat.mul_assoc, hden, Nat.mul_assoc]
    rw [e, Nat.mul_comm capDen d] at this
    exact Nat.le_of_mul_le_mul_right this capDen_pos
  · intro hle
    have : d * capDen ≤ 2 * n * capDen := Nat.mul_le_mul_right capDen hle
    have e : 2 * n * capDen = 2 * w.val * d := by rw [Nat.mul_assoc, ← hden, Nat.mul_assoc]
    rw [e, Nat.mul_comm d capDen] at this
    exact Nat.le_of_mul_le_mul_right this hd

/-! ## `capDen` is unobservable (D17 is a one-line change) -/

/-- **The bin does not see `capDen`**: scaling an availability's numerator and denominator
by `k > 0` leaves §7.1's bin unchanged. -/
theorem the_bin_does_not_see_capDen (bins : List Q) (s : Pos) (rem a k : Nat) (hk : 0 < k) :
    binOfScaledQ bins s rem (mkPos (k * a) (k * capDen) (Nat.mul_pos hk capDen_pos))
      = binOfScaledQ bins s rem (mkPos a capDen capDen_pos) := by
  apply binOfScaledQ_congr
  simp only [Q.equiv, mkPos_num, mkPos_den]
  apply decide_eq_true
  ac_rfl

/-- A day with every numerator scaled by `k`. -/
def scaleDay (k : Nat) (c : DayCapacity) : DayCapacity := ⟨c.day, fun l => k * c.numAt l⟩

/-- A grant with its numerators scaled by `k`. -/
def scaleGrant (k : Nat) (g : Grant) : Grant := ⟨g.deadline, k * g.avail, k * g.reserved⟩

theorem availUntil_scale (k : Nat) (due : Day) (ci : Fin 6) :
    ∀ caps : List DayCapacity, availUntil due ci (caps.map (scaleDay k)) = k * availUntil due ci caps
  | [] => by simp [availUntil]
  | c :: cs => by
    simp only [List.map, availUntil, availUntil_scale k due ci cs, scaleDay]
    have : eligAt ci (fun l => k * c.numAt l) = k * eligAt ci c.numAt := by
      have := topElig_lin ci k 0 c.numAt c.numAt 6
      simpa [eligAt] using this
    split <;> simp [this, Nat.mul_add]

theorem reserveRest_scale (k : Nat) (due : Day) (ci : Fin 6) :
    ∀ (caps : List DayCapacity) (left : Nat),
      reserveRest due ci (caps.map (scaleDay k)) (k * left)
        = (reserveRest due ci caps left).map (scaleDay k)
  | [], _ => rfl
  | c :: cs, left => by
    simp only [List.map, reserveRest, scaleDay]
    split
    · rw [dayOut_scale, dayRest_scale]
      have ih := reserveRest_scale k due ci cs (dayOut ci c.numAt left)
      rw [ih]
      rfl
    · have ih := reserveRest_scale k due ci cs left
      rw [ih]
      rfl

theorem reserveOut_scale (k : Nat) (due : Day) (ci : Fin 6) (caps : List DayCapacity) (left : Nat) :
    reserveOut due ci (caps.map (scaleDay k)) (k * left) = k * reserveOut due ci caps left := by
  rw [reserveOut_eq, reserveOut_eq, availUntil_scale, Nat.mul_sub]

theorem edfCaps_scale (k den : Nat) :
    ∀ (caps : List DayCapacity) (ds : List Deadline),
      edfCaps (k * den) (caps.map (scaleDay k)) ds = (edfCaps den caps ds).map (scaleDay k)
  | _, [] => rfl
  | caps, d :: ds => by
    simp only [edfCaps]
    have e : d.need * (k * den) = k * (d.need * den) := by ac_rfl
    rw [e, reserveRest_scale, edfCaps_scale k den]

theorem edfGrantsGo_scale (k den : Nat) :
    ∀ (caps : List DayCapacity) (ds : List Deadline),
      edfGrantsGo (k * den) (caps.map (scaleDay k)) ds = (edfGrantsGo den caps ds).map (scaleGrant k)
  | _, [] => rfl
  | caps, d :: ds => by
    simp only [edfGrantsGo, List.map, grantOf, scaleGrant]
    have e : d.need * (k * den) = k * (d.need * den) := by ac_rfl
    rw [e, reserveRest_scale, edfGrantsGo_scale k den, availUntil_scale, reserveOut_scale,
      Nat.mul_sub]

/-- **Two runs (D5): the EDF pass commutes with scaling the unit.**  Run it over `k·den`
on every numerator scaled by `k`, and the days left are the first run's, scaled. -/
theorem edf_commutes_with_scaling (k : Nat) (hk : 0 < k) (den : Den) (caps : List DayCapacity)
    (ds : List Deadline) :
    edf ⟨k * den.val, Nat.mul_pos hk den.property⟩ (caps.map (scaleDay k)) ds
      = (edf den caps ds).map (scaleDay k) :=
  edfCaps_scale k den.val caps (sortDue ds)

/-- **The grants too**: each availability and reservation is the first run's, scaled. -/
theorem edfGrants_commute_with_scaling (k : Nat) (hk : 0 < k) (den : Den)
    (caps : List DayCapacity) (ds : List Deadline) :
    edfGrants ⟨k * den.val, Nat.mul_pos hk den.property⟩ (caps.map (scaleDay k)) ds
      = (edfGrants den caps ds).map (scaleGrant k) :=
  edfGrantsGo_scale k den.val caps (sortDue ds)

/-- **And no verdict sees the scale**: IMPOSSIBLE and §7.1's bin at the scaled grant are the
first run's. -/
theorem a_scaled_grant_keeps_its_verdicts (k : Nat) (hk : 0 < k) (den : Den) (g : Grant)
    (bins : List Q) (s : Pos) (rem : Nat) :
    (scaleGrant k g).impossible ⟨k * den.val, Nat.mul_pos hk den.property⟩ = g.impossible den ∧
      binOfScaledQ bins s rem ((scaleGrant k g).availQ ⟨k * den.val, Nat.mul_pos hk den.property⟩)
        = binOfScaledQ bins s rem (g.availQ den) := by
  constructor
  · simp only [Grant.impossible, scaleGrant]
    apply decide_eq_decide.mpr
    have e : g.deadline.need * (k * den.val) = k * (g.deadline.need * den.val) := by ac_rfl
    rw [e]
    exact ⟨fun h => Nat.lt_of_mul_lt_mul_left h, fun h => Nat.mul_lt_mul_of_pos_left h hk⟩
  · apply binOfScaledQ_congr
    simp only [Q.equiv, Grant.availQ, scaleGrant, mkPos_num, mkPos_den]
    apply decide_eq_true
    ac_rfl

/-! ## Both directions, decided witnesses -/

/-- **The weight decoder, both directions.**  Accepted: `0/1`, `1/1`, `1/2`, `9/10`, and 18
places.  Refused by name: a zero denominator, `3/2`, a third (`3 ∤ 10^18`), and 19 places. -/
theorem mkWeight?_on_witnesses :
    (mkWeight? 0 1).map Subtype.val = .ok 0 ∧
      (mkWeight? 1 1).map Subtype.val = .ok capDen ∧
      (mkWeight? 1 2).map Subtype.val = .ok 500000000000000000 ∧
      (mkWeight? 9 10).map Subtype.val = .ok 900000000000000000 ∧
      (mkWeight? 1 1000000000000000000).map Subtype.val = .ok 1 ∧
      (mkWeight? 1 0).map Subtype.val = .error .badWeight ∧
      (mkWeight? 3 2).map Subtype.val = .error .weightAboveOne ∧
      (mkWeight? 1 3).map Subtype.val = .error .weightPrecision ∧
      (mkWeight? 1 10000000000000000000).map Subtype.val = .error .weightPrecision := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The mixture on a witness**: `p = 9/10`, lounge 60 minutes at level 5, home 120 at
level 3.  The day holds 54 minutes at level 5 and 12 at level 3, over `capDen`; a `ci 4`
deadline sees 54, a `ci 3` one 66. -/
theorem mix_on_a_witness :
    (List.finRange 6).map (mix ⟨900000000000000000, by decide⟩ (histOf [0, 0, 0, 0, 0, 60])
        (histOf [0, 0, 0, 120, 0, 0])) = [0, 0, 0, 12 * capDen, 0, 54 * capDen] ∧
      eligAt 4 (mix ⟨900000000000000000, by decide⟩ (histOf [0, 0, 0, 0, 0, 60])
        (histOf [0, 0, 0, 120, 0, 0])) = 54 * capDen ∧
      eligAt 3 (mix ⟨900000000000000000, by decide⟩ (histOf [0, 0, 0, 0, 0, 60])
        (histOf [0, 0, 0, 120, 0, 0])) = 66 * capDen := by
  decide

/-! ############################################################################
## E7: the day's window (stage 5 D10 step L2; design §13.3, owner's D12)

Pulled forward from stage 6 by the owner's D12.  **Stage 6's `dayPlan` must reuse
`windowEnd`, `windowOn`, `wallIndex` and `wallsOn`, never a second copy** (design §2.3,
AGENTS §5.3).

### The fork point, read by name

`capacity::window_and_budget(arrival, walls_today, cfg)`:

1. `window_min = (window_hours × 60.0).round().max(0.0)` (site R3, `windowMinOf`);
2. `cap = local_dt(tz, arrival.date_naive(), window_cap)`;
3. `base_end = (arrival + window_min).min(cap).max(arrival)` (`windowBase`);
4. `walls_after(arrival, walls)`: each wall's start raised to the arrival, **no upper
   bound**, empty walls dropped (`clipWalls`), then `merge_walls`: sorted by start and
   merged, touching walls included (`sortByStart`, `mergeStep`, `mergeSorted`);
5. the walk: for each merged wall in order, `if a >= end { break }`, else
   `end += b − a` (`extendStep`).  The kernel's walk does not stop: once a merged wall
   starts at or after the end, every later one does too and the end no longer moves, so
   skipping them is the `break`.  `the_window_end_solves_the_equation` and
   `the_window_end_is_the_least_solution` pin the value whatever the walk looks like;
6. `budget_blocks = floor(window_hours × 60 / block_min × budget_ratio)` with
   `block_min.max(1)` (site R2, `budgetOf`).

### E7, in overlap semantics

`wallOverlap arrival stop walls` counts the units of `[arrival, stop)` under at least one
wall: clipped, merged and counted once, as the fork does.  It is a specification and is
never evaluated at run time.  `windowEnd` **solves** `end = windowBase + wallOverlap arrival
end walls` and is its **least** solution (the two E7 goals, moved here from `Goals.lean`'s
STAGE 6 under D12).  The proof goes through the merged walls, the route design risk K16
names: `mergeSorted_spec` (a sorted list merges into a chain of disjoint walls with the same
cover), then `extend_solves` and `extend_least` over the chain.

**Refuted as stage 6 wrote it.**  `Goals.lean` stated E7 over `wallsInside` (walls wholly
inside `[arrival, end]`) and the base `min(arrival + window, cap)`.  Both differ from the
fork: `the_window_end_is_not_the_least_solution_as_stage_6_wrote_it` (a wall straddling the
base end: 900 solves the old equation, and the fork gives 960) and
`the_window_end_does_not_solve_the_equation_as_stage_6_wrote_it` (an arrival after the cap:
the fork clamps the base to the arrival).  `a_wall_begun_before_the_arrival_extends_the_window`
is the third difference, the clip at the arrival.

### Real seconds (design §13.3)

`windowOn z d arrival cap windowMin walls` is `window_and_budget` for day `d` in zone `z`:
the arrival is `Cal.instantOf z d arrival` (fork `local_dt`), the cap is `instantOf` on the
arrival's local date, and every endpoint, wall and length is a count of **UTC seconds**.
`instantOf` returns whole seconds (`instantOf_ns`), so the seconds are the instants, and a
DST day's window counts real hours
(`the_window_counts_real_hours_across_the_spring_transition`).  Parity entry P28 (civil
minutes) is therefore never recorded.

### Walls from the plan (fork `Ctx::walls_on`, `Ctx::walls_by_date`)

For every item whose status is not settled (`State::is_closed` is Done or Dropped; a
demoted `[-]` line is not closed) and whose effective shape is `Interval { start, end }`:
the start moved back by `buffer:` **on the local clock** (`NaiveDateTime − Duration`,
`shiftBack`), then both ends through `local_dt`.  The wall belongs to every date from the
shifted start's date to the end's date.  `wallIndex` reads the plan **once per request**,
and `wallsOn` selects a date's walls from it.

**Quirk (e), ported faithfully (owner's Q6; gap 85).**  `walls_on` does not clip a wall to
its date and `walls_after` clips only at the arrival, so a Monday 09:00 to Wednesday 17:00
wall extends Tuesday's window to Thursday 01:00, and Wednesday evening lies inside both
Tuesday's and Wednesday's windows
(`a_multi_day_wall_puts_one_evening_in_two_windows`).

### The recursion rule (D9-21)

Over lists the wire can make large: `clipWalls` is core `map`/`filter` (tail-recursive by
core's `@[csimp]`); `mergeSorted` is a `foldl` then `reverse`; the walk is a `foldl`;
`wallIndex` and `wallsOn` are core `filterMap` (`filterMapTR`).  The sort is the one
exception: `sortByStart` is an insertion sort, quadratic and not tail-recursive, kept
because it reduces under `decide`.  **`windowEnd_eq_windowEndFast` is its `@[csimp]`
twin**: the compiled `windowEnd` runs core's `List.mergeSort`, and the two are equal
because both walks are the least solution of one equation.  `wallOverlap` is never run.
-/

/-- The units of `[arrival, stop)` under at least one wall.  **Specification only:** never
evaluated at run time (D9-21); decided witnesses stay below 1,440 units. -/
def wallOverlap (arrival stop : Nat) (walls : List (Nat × Nat)) : Nat :=
  ((List.range (stop - arrival)).map (· + arrival)).countP
    (fun t => walls.any (fun w => decide (w.1 ≤ t ∧ t < w.2)))

/-- Fork `base_end`: `(arrival + window).min(cap).max(arrival)`. -/
def windowBase (arrival windowMin windowCap : Nat) : Nat :=
  max arrival (min (arrival + windowMin) windowCap)

/-- Fork `walls_after`'s clip: each start raised to `lo`, no upper bound, empty walls
dropped. -/
def clipWalls (lo : Nat) (walls : List (Nat × Nat)) : List (Nat × Nat) :=
  (walls.map fun w => (max w.1 lo, w.2)).filter fun w => decide (w.1 < w.2)

/-- Insert by start, before the first wall that does not start earlier. -/
def insertByStart (w : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [w]
  | v :: vs => if w.1 ≤ v.1 then w :: v :: vs else v :: insertByStart w vs

/-- Sorted by start (fork `sort_by_key`).  The specification's sort: it reduces under
`decide`; the compiled code runs `List.mergeSort` (`windowEnd_eq_windowEndFast`). -/
def sortByStart : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | w :: ws => insertByStart w (sortByStart ws)

/-- One step of fork `merge_walls`, on an accumulator whose head is the last wall:
`Some(last) if a <= last.1 => last.1 = last.1.max(b)`, else push. -/
def mergeStep (acc : List (Nat × Nat)) (w : Nat × Nat) : List (Nat × Nat) :=
  match acc with
  | v :: vs => if w.1 ≤ v.2 then (v.1, max v.2 w.2) :: vs else w :: v :: vs
  | [] => [w]

/-- Fork `merge_walls` over a list already sorted by start. -/
def mergeSorted (s : List (Nat × Nat)) : List (Nat × Nat) := (s.foldl mergeStep []).reverse

/-- One step of the fork's walk: a wall that starts before the end extends it by its whole
length. -/
def extendStep (e : Nat) (w : Nat × Nat) : Nat := if w.1 < e then e + (w.2 - w.1) else e

/-- **§8.1's window end, E7** (fork `window_and_budget`'s `end`), in one unit throughout:
clip, sort, merge, extend. -/
def windowEnd (arrival windowMin windowCap : Nat) (walls : List (Nat × Nat)) : Nat :=
  (mergeSorted (sortByStart (clipWalls arrival walls))).foldl extendStep
    (windowBase arrival windowMin windowCap)

/-- `windowEnd` with core's merge sort, which is what the compiled code runs. -/
def windowEndFast (arrival windowMin windowCap : Nat) (walls : List (Nat × Nat)) : Nat :=
  (mergeSorted ((clipWalls arrival walls).mergeSort (fun v w => decide (v.1 ≤ w.1)))).foldl
    extendStep (windowBase arrival windowMin windowCap)

/-! ### Counting the units under the walls -/

/-- Some wall holds `t`. -/
def covered (L : List (Nat × Nat)) (t : Nat) : Bool := L.any (fun w => decide (w.1 ≤ t ∧ t < w.2))

/-- The units of `[a, x)` where `P` holds, in `wallOverlap`'s own form. -/
def countIn (P : Nat → Bool) (a x : Nat) : Nat := ((List.range (x - a)).map (· + a)).countP P

theorem wallOverlap_eq_countIn (a x : Nat) (ws : List (Nat × Nat)) :
    wallOverlap a x ws = countIn (covered ws) a x := rfl

theorem countIn_of_le (P : Nat → Bool) {a x : Nat} (h : x ≤ a) : countIn P a x = 0 := by
  simp [countIn, Nat.sub_eq_zero_of_le h]

theorem countIn_succ (P : Nat → Bool) {a x : Nat} (h : a ≤ x) :
    countIn P a (x + 1) = countIn P a x + if P x then 1 else 0 := by
  unfold countIn
  rw [show x + 1 - a = (x - a) + 1 by omega, List.range_succ, List.map_append, List.countP_append]
  simp only [List.map_cons, List.map_nil, List.countP_cons, List.countP_nil, Nat.zero_add]
  rw [show x - a + a = x by omega]

theorem countIn_congr {P Q : Nat → Bool} (a : Nat) : ∀ x, (∀ t, a ≤ t → t < x → P t = Q t) →
    countIn P a x = countIn Q a x
  | 0, _ => by simp [countIn]
  | x + 1, h => by
    by_cases hax : a ≤ x
    · rw [countIn_succ P hax, countIn_succ Q hax, countIn_congr a x (fun t h1 h2 => h t h1 (by omega)),
        h x hax (by omega)]
    · rw [countIn_of_le P (by omega), countIn_of_le Q (by omega)]

theorem countIn_or {P Q : Nat → Bool} (a : Nat) (hd : ∀ t, ¬ (P t = true ∧ Q t = true)) :
    ∀ x, countIn (fun t => P t || Q t) a x = countIn P a x + countIn Q a x
  | 0 => by simp [countIn]
  | x + 1 => by
    by_cases hax : a ≤ x
    · rw [countIn_succ _ hax, countIn_succ P hax, countIn_succ Q hax, countIn_or a hd x]
      have := hd x
      cases hp : P x <;> cases hq : Q x <;> simp_all <;> omega
    · rw [countIn_of_le _ (by omega), countIn_of_le P (by omega), countIn_of_le Q (by omega)]

/-- One wall that starts at or after `a` puts `min w.2 x − w.1` units under `[a, x)`. -/
theorem countIn_wall (w : Nat × Nat) {a : Nat} (hw : a ≤ w.1) :
    ∀ x, countIn (fun t => decide (w.1 ≤ t ∧ t < w.2)) a x = min w.2 x - w.1
  | 0 => by simp [countIn]
  | x + 1 => by
    by_cases hax : a ≤ x
    · rw [countIn_succ _ hax, countIn_wall w hw x]
      by_cases h1 : w.1 ≤ x <;> by_cases h2 : x < w.2 <;> simp [h1, h2] <;> omega
    · rw [countIn_of_le _ (by omega)]; omega

theorem countIn_zero (P : Nat → Bool) (a : Nat) : ∀ x, (∀ t, t < x → P t = false) → countIn P a x = 0
  | 0, _ => by simp [countIn]
  | x + 1, h => by
    by_cases hax : a ≤ x
    · rw [countIn_succ _ hax, countIn_zero P a x (fun t ht => h t (by omega)), h x (by omega)]; rfl
    · rw [countIn_of_le _ (by omega)]

theorem covered_cons (w : Nat × Nat) (L : List (Nat × Nat)) (t : Nat) :
    covered (w :: L) t = (decide (w.1 ≤ t ∧ t < w.2) || covered L t) := rfl

theorem covered_eq_true {L : List (Nat × Nat)} {t : Nat} :
    covered L t = true ↔ ∃ w ∈ L, w.1 ≤ t ∧ t < w.2 := by
  simp [covered, List.any_eq_true]

theorem countIn_covered_nil (a x : Nat) : countIn (covered []) a x = 0 :=
  countIn_zero _ a x (fun _ _ => rfl)

/-! ### The walk over a chain of disjoint walls -/

/-- Disjoint walls in order, each nonempty, none starting before `a`. -/
def WallChain (a : Nat) (L : List (Nat × Nat)) : Prop :=
  L.Pairwise (fun v w => v.2 < w.1) ∧ ∀ w ∈ L, a ≤ w.1 ∧ w.1 < w.2

theorem WallChain.tail {a : Nat} {w : Nat × Nat} {L : List (Nat × Nat)} (h : WallChain a (w :: L)) :
    WallChain a L :=
  ⟨(List.pairwise_cons.1 h.1).2, fun v hv => h.2 v (List.mem_cons_of_mem _ hv)⟩

theorem extend_ge : ∀ (L : List (Nat × Nat)) (e : Nat), e ≤ L.foldl extendStep e
  | [], _ => Nat.le_refl _
  | w :: L, e => by
    simp only [List.foldl_cons]
    refine Nat.le_trans ?_ (extend_ge L _)
    unfold extendStep; split <;> omega

theorem extendStep_pos {e : Nat} {w : Nat × Nat} (h : w.1 < e) : extendStep e w = e + (w.2 - w.1) :=
  if_pos h

theorem extendStep_neg {e : Nat} {w : Nat × Nat} (h : ¬ w.1 < e) : extendStep e w = e :=
  if_neg h

theorem countIn_covered_cons (a : Nat) (w : Nat × Nat) (L : List (Nat × Nat)) (h : WallChain a (w :: L))
    (x : Nat) : countIn (covered (w :: L)) a x = (min w.2 x - w.1) + countIn (covered L) a x := by
  have hw := h.2 w (by simp)
  rw [show covered (w :: L) = fun t => decide (w.1 ≤ t ∧ t < w.2) || covered L t from rfl]
  rw [countIn_or a, countIn_wall w hw.1]
  intro t ⟨h1, h2⟩
  simp only [decide_eq_true_eq] at h1
  obtain ⟨v, hv, hv1, hv2⟩ := covered_eq_true.1 h2
  have := List.rel_of_pairwise_cons h.1 hv
  omega

/-- Over a chain, the walk from `e` is at most every `m` with `e + overlap(m) ≤ m`. -/
theorem extend_least (a : Nat) : ∀ (L : List (Nat × Nat)), WallChain a L → ∀ e m,
    e + countIn (covered L) a m ≤ m → L.foldl extendStep e ≤ m
  | [], _, e, m, h => by rw [countIn_covered_nil] at h; simpa using h
  | w :: L, hc, e, m, h => by
    rw [countIn_covered_cons a w L hc] at h
    have hw := hc.2 w (by simp)
    rw [List.foldl_cons]
    by_cases hlt : w.1 < e
    · rw [extendStep_pos hlt]
      apply extend_least a L hc.tail
      have : w.2 ≤ m := by
        by_cases hm : w.2 ≤ m
        · exact hm
        · exfalso; omega
      omega
    · rw [extendStep_neg hlt]
      apply extend_least a L hc.tail; omega

/-- Over a chain, the walk from `e` solves `r = e + overlap(r)`. -/
theorem extend_solves (a : Nat) : ∀ (L : List (Nat × Nat)), WallChain a L → ∀ e,
    L.foldl extendStep e = e + countIn (covered L) a (L.foldl extendStep e)
  | [], _, e => by rw [countIn_covered_nil]; rfl
  | w :: L, hc, e => by
    have hw := hc.2 w (by simp)
    rw [List.foldl_cons]
    by_cases hlt : w.1 < e
    · rw [extendStep_pos hlt]
      have ih := extend_solves a L hc.tail (e + (w.2 - w.1))
      have hge := extend_ge L (e + (w.2 - w.1))
      rw [countIn_covered_cons a w L hc]
      have hmin : min w.2 (L.foldl extendStep (e + (w.2 - w.1))) = w.2 := by omega
      rw [hmin]
      omega
    · rw [extendStep_neg hlt]
      have z : countIn (covered L) a e = 0 := by
        apply countIn_zero
        intro t ht
        cases hct : covered L t
        · rfl
        · obtain ⟨v, hv, hv1, _⟩ := covered_eq_true.1 hct
          have := List.rel_of_pairwise_cons hc.1 hv
          omega
      have hle := extend_least a L hc.tail e e (by omega)
      have heq : L.foldl extendStep e = e := Nat.le_antisymm hle (extend_ge L e)
      rw [heq, countIn_covered_cons a w L hc, z]
      omega

/-! ### Merging a sorted list gives a chain with the same cover -/

/-- The merge's accumulator: a chain read last wall first. -/
def WallChainRev (a : Nat) (R : List (Nat × Nat)) : Prop :=
  R.Pairwise (fun v w => w.2 < v.1) ∧ ∀ w ∈ R, a ≤ w.1 ∧ w.1 < w.2

theorem mergeStep_spec (a : Nat) (R : List (Nat × Nat)) (w : Nat × Nat) (hR : WallChainRev a R)
    (hw : a ≤ w.1 ∧ w.1 < w.2) (hle : ∀ v ∈ R, v.1 ≤ w.1) :
    WallChainRev a (mergeStep R w) ∧ (∀ v ∈ mergeStep R w, v.1 ≤ w.1) ∧
      ∀ t, covered (mergeStep R w) t = (covered R t || decide (w.1 ≤ t ∧ t < w.2)) := by
  match R with
  | [] =>
    show WallChainRev a [w] ∧ (∀ v ∈ [w], v.1 ≤ w.1) ∧
      ∀ t, covered [w] t = (covered [] t || decide (w.1 ≤ t ∧ t < w.2))
    refine ⟨⟨by simp, by simpa using hw⟩, by simp, fun t => ?_⟩
    simp [covered]
  | v :: vs =>
    have hv := hR.2 v (by simp)
    have hvw := hle v (by simp)
    have hpw := List.pairwise_cons.1 hR.1
    by_cases hm : w.1 ≤ v.2
    · have e : mergeStep (v :: vs) w = (v.1, max v.2 w.2) :: vs := if_pos hm
      rw [e]
      refine ⟨⟨List.pairwise_cons.2 ⟨fun u hu => hpw.1 u hu, hpw.2⟩, ?_⟩, ?_, fun t => ?_⟩
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · simp; omega
        · exact hR.2 u (List.mem_cons_of_mem _ hu)
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · simpa using hvw
        · exact hle u (List.mem_cons_of_mem _ hu)
      · simp only [covered_cons]
        by_cases h1 : v.1 ≤ t <;> by_cases h2 : t < v.2 <;> by_cases h3 : w.1 ≤ t <;>
          by_cases h4 : t < w.2 <;> by_cases h5 : t < max v.2 w.2 <;>
          simp [h1, h2, h3, h4, h5] <;> omega
    · have e : mergeStep (v :: vs) w = w :: v :: vs := if_neg hm
      rw [e]
      refine ⟨⟨List.pairwise_cons.2 ⟨fun u hu => ?_, hR.1⟩, ?_⟩, ?_, fun t => ?_⟩
      · rcases List.mem_cons.1 hu with rfl | hu
        · omega
        · have := hpw.1 u hu
          have := hR.2 u (List.mem_cons_of_mem _ hu)
          omega
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact hw
        · exact hR.2 u hu
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact Nat.le_refl _
        · exact hle u hu
      · simp only [covered_cons]
        cases decide (v.1 ≤ t ∧ t < v.2) <;> cases covered vs t <;>
          cases decide (w.1 ≤ t ∧ t < w.2) <;> rfl

theorem foldl_mergeStep_spec (a : Nat) : ∀ (S R : List (Nat × Nat)),
    S.Pairwise (fun v w => v.1 ≤ w.1) → (∀ w ∈ S, a ≤ w.1 ∧ w.1 < w.2) → WallChainRev a R →
    (∀ v ∈ R, ∀ w ∈ S, v.1 ≤ w.1) →
    WallChainRev a (S.foldl mergeStep R) ∧
      ∀ t, covered (S.foldl mergeStep R) t = (covered R t || covered S t)
  | [], R, _, _, hR, _ => ⟨hR, fun t => by simp [covered]⟩
  | w :: S, R, hs, hm, hR, hle => by
    rw [List.foldl_cons]
    have hps := List.pairwise_cons.1 hs
    obtain ⟨h1, h2, h3⟩ :=
      mergeStep_spec a R w hR (hm w (by simp)) (fun v hv => hle v hv w (by simp))
    have ih := foldl_mergeStep_spec a S (mergeStep R w) hps.2
      (fun u hu => hm u (List.mem_cons_of_mem _ hu)) h1
      (fun v hv u hu => Nat.le_trans (h2 v hv) (hps.1 u hu))
    refine ⟨ih.1, fun t => ?_⟩
    rw [ih.2 t, h3 t, covered_cons]
    cases covered R t <;> cases decide (w.1 ≤ t ∧ t < w.2) <;> cases covered S t <;> rfl

theorem covered_reverse (L : List (Nat × Nat)) (t : Nat) : covered L.reverse t = covered L t := by
  simp [covered, List.any_reverse]

/-- **Fork `merge_walls`, specified**: a list sorted by start merges into a chain of
disjoint walls holding exactly the units the list held. -/
theorem mergeSorted_spec (a : Nat) (S : List (Nat × Nat)) (hs : S.Pairwise (fun v w => v.1 ≤ w.1))
    (hm : ∀ w ∈ S, a ≤ w.1 ∧ w.1 < w.2) :
    WallChain a (mergeSorted S) ∧ ∀ t, covered (mergeSorted S) t = covered S t := by
  obtain ⟨⟨hp, hmem⟩, hcov⟩ := foldl_mergeStep_spec a S [] hs hm ⟨by simp, by simp⟩ (by simp)
  refine ⟨⟨?_, fun w hw => hmem w (List.mem_reverse.1 hw)⟩, fun t => ?_⟩
  · unfold mergeSorted; rw [List.pairwise_reverse]; exact hp
  · unfold mergeSorted; rw [covered_reverse, hcov t]; simp [covered]

/-! ### Sorting and clipping -/

theorem insertByStart_perm (w : Nat × Nat) : ∀ L : List (Nat × Nat), (insertByStart w L).Perm (w :: L)
  | [] => List.Perm.refl _
  | v :: vs => by
    unfold insertByStart
    split
    · exact List.Perm.refl _
    · exact ((insertByStart_perm w vs).cons v).trans (List.Perm.swap w v vs)

theorem insertByStart_sorted (w : Nat × Nat) : ∀ L : List (Nat × Nat),
    L.Pairwise (fun v w => v.1 ≤ w.1) → (insertByStart w L).Pairwise (fun v w => v.1 ≤ w.1)
  | [], _ => by simp [insertByStart]
  | v :: vs, h => by
    have hp := List.pairwise_cons.1 h
    unfold insertByStart
    split
    · rename_i hle
      refine List.pairwise_cons.2 ⟨fun u hu => ?_, h⟩
      rcases List.mem_cons.1 hu with rfl | hu
      · exact hle
      · exact Nat.le_trans hle (hp.1 u hu)
    · rename_i hle
      refine List.pairwise_cons.2 ⟨fun u hu => ?_, insertByStart_sorted w vs hp.2⟩
      rcases List.mem_cons.1 ((insertByStart_perm w vs).mem_iff.1 hu) with rfl | hu
      · omega
      · exact hp.1 u hu

theorem sortByStart_perm : ∀ L : List (Nat × Nat), (sortByStart L).Perm L
  | [] => List.Perm.refl _
  | w :: ws => (insertByStart_perm w _).trans ((sortByStart_perm ws).cons w)

theorem sortByStart_sorted : ∀ L : List (Nat × Nat), (sortByStart L).Pairwise (fun v w => v.1 ≤ w.1)
  | [] => List.Pairwise.nil
  | w :: ws => insertByStart_sorted w _ (sortByStart_sorted ws)

theorem mergeSort_start_sorted (L : List (Nat × Nat)) :
    (L.mergeSort (fun v w => decide (v.1 ≤ w.1))).Pairwise (fun v w => v.1 ≤ w.1) := by
  have := List.pairwise_mergeSort (le := fun v w : Nat × Nat => decide (v.1 ≤ w.1))
    (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) L
  exact this.imp (fun h => by simpa using h)

theorem clipWalls_mem {lo : Nat} {ws : List (Nat × Nat)} {w : Nat × Nat} (h : w ∈ clipWalls lo ws) :
    lo ≤ w.1 ∧ w.1 < w.2 := by
  simp only [clipWalls, List.mem_filter, List.mem_map, decide_eq_true_eq] at h
  obtain ⟨⟨u, _, rfl⟩, h2⟩ := h
  exact ⟨Nat.le_max_right _ _, h2⟩

/-- At or after `lo`, clipping changes no unit's cover. -/
theorem covered_clipWalls (lo : Nat) (ws : List (Nat × Nat)) {t : Nat} (ht : lo ≤ t) :
    covered (clipWalls lo ws) t = covered ws t := by
  apply Bool.eq_iff_iff.2
  rw [covered_eq_true, covered_eq_true]
  simp only [clipWalls, List.mem_filter, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨⟨u, hu, rfl⟩, _⟩, h1, h2⟩
    exact ⟨u, hu, by simp at h1; omega, h2⟩
  · rintro ⟨u, hu, h1, h2⟩
    exact ⟨(max u.1 lo, u.2), ⟨⟨u, hu, rfl⟩, by simp; omega⟩, by simp; omega, h2⟩

theorem covered_perm {L M : List (Nat × Nat)} (h : L.Perm M) (t : Nat) : covered L t = covered M t := by
  apply Bool.eq_iff_iff.2
  rw [covered_eq_true, covered_eq_true]
  exact ⟨fun ⟨w, hw, hh⟩ => ⟨w, h.mem_iff.1 hw, hh⟩, fun ⟨w, hw, hh⟩ => ⟨w, h.mem_iff.2 hw, hh⟩⟩

/-! ### E7, discharged (moved from `Goals.lean`'s STAGE 6 under D12) -/

/-- The walk over **any** start-sorted arrangement of the clipped walls solves the
equation and is below every pre-fixed point.  Both sorts are instances. -/
theorem walk_is_the_least_solution (a wm wc : Nat) (ws S : List (Nat × Nat))
    (hperm : S.Perm (clipWalls a ws)) (hs : S.Pairwise (fun v w => v.1 ≤ w.1)) :
    (mergeSorted S).foldl extendStep (windowBase a wm wc)
        = windowBase a wm wc
          + wallOverlap a ((mergeSorted S).foldl extendStep (windowBase a wm wc)) ws ∧
      ∀ m, windowBase a wm wc + wallOverlap a m ws ≤ m →
        (mergeSorted S).foldl extendStep (windowBase a wm wc) ≤ m := by
  have hm : ∀ w ∈ S, a ≤ w.1 ∧ w.1 < w.2 := fun w hw => clipWalls_mem (hperm.mem_iff.1 hw)
  obtain ⟨hc, hcov⟩ := mergeSorted_spec a S hs hm
  have hov : ∀ x, wallOverlap a x ws = countIn (covered (mergeSorted S)) a x := by
    intro x
    rw [wallOverlap_eq_countIn]
    apply countIn_congr a x
    intro t hat _
    rw [hcov t, covered_perm hperm t, covered_clipWalls a ws hat]
  refine ⟨?_, fun m h => ?_⟩
  · rw [hov]; exact extend_solves a _ hc _
  · rw [hov] at h; exact extend_least a _ hc _ _ h

/-- **E7a**: the window end solves §8.1's equation, in the fork's overlap semantics. -/
theorem the_window_end_solves_the_equation (a wm wc : Nat) (ws : List (Nat × Nat)) :
    windowEnd a wm wc ws = windowBase a wm wc + wallOverlap a (windowEnd a wm wc ws) ws :=
  (walk_is_the_least_solution a wm wc ws _ (sortByStart_perm _) (sortByStart_sorted _)).1

/-- E7b's stronger form: below every pre-fixed point. -/
theorem windowEnd_le_of_prefixpoint (a wm wc m : Nat) (ws : List (Nat × Nat))
    (hm : windowBase a wm wc + wallOverlap a m ws ≤ m) : windowEnd a wm wc ws ≤ m :=
  (walk_is_the_least_solution a wm wc ws _ (sortByStart_perm _) (sortByStart_sorted _)).2 m hm

/-- **E7b**: the window end is the least solution, so it is a definition and not a choice
of how many rounds a loop ran. -/
theorem the_window_end_is_the_least_solution (a wm wc m : Nat) (ws : List (Nat × Nat))
    (hm : m = windowBase a wm wc + wallOverlap a m ws) :
    windowEnd a wm wc ws ≤ m :=
  windowEnd_le_of_prefixpoint a wm wc m ws (Nat.le_of_eq hm.symm)

/-- The compiled `windowEnd` runs core's merge sort: both walks are the least solution. -/
@[csimp] theorem windowEnd_eq_windowEndFast : @windowEnd = @windowEndFast := by
  funext a wm wc ws
  have f :=
    walk_is_the_least_solution a wm wc ws _ (List.mergeSort_perm _ _) (mergeSort_start_sorted _)
  have s := walk_is_the_least_solution a wm wc ws _ (sortByStart_perm _) (sortByStart_sorted _)
  exact Nat.le_antisymm (s.2 _ (Nat.le_of_eq f.1.symm)) (f.2 _ (Nat.le_of_eq s.1.symm))

theorem windowBase_le_windowEnd (a wm wc : Nat) (ws : List (Nat × Nat)) :
    windowBase a wm wc ≤ windowEnd a wm wc ws := extend_ge _ _

/-- The window never ends before the arrival (fork: "arriving after `window_cap` gives an
empty window rather than a negative one"). -/
theorem arrival_le_windowEnd (a wm wc : Nat) (ws : List (Nat × Nat)) : a ≤ windowEnd a wm wc ws :=
  Nat.le_trans (Nat.le_max_left _ _) (windowBase_le_windowEnd a wm wc ws)

theorem windowEnd_without_walls (a wm wc : Nat) : windowEnd a wm wc [] = windowBase a wm wc := rfl

/-! ### The stage-6 statement, refuted as written (§3.1 item 3) -/

/-- **`Goals.lean` STAGE 6's reading, kept only to refute it**: the length of every wall
wholly inside `[arrival, stop]`.  The fork clips at the arrival, merges, and counts
overlap (`wallOverlap`). -/
def wallsInside (arrival stop : Nat) (walls : List (Nat × Nat)) : Nat :=
  (walls.filter (fun w => decide (arrival ≤ w.1 ∧ w.2 ≤ stop))).foldl (fun a w => a + (w.2 - w.1)) 0

/-- Arrival 07:00, an eight-hour window, cap 19:00, a wall 14:50–15:50: 900 (15:00) solves
the stage-6 equation, because the wall is not wholly inside `[420, 900]`; the fork gives 960. -/
theorem the_window_end_is_not_the_least_solution_over_walls_wholly_inside :
    (900 = min (420 + 480) 1140 + wallsInside 420 900 [(890, 950)]) ∧
    windowEnd 420 480 1140 [(890, 950)] = 960 := by
  decide

/-- **E7b as `Goals.lean` STAGE 6 stated it is false** against the fork. -/
theorem the_window_end_is_not_the_least_solution_as_stage_6_wrote_it :
    ¬ ∀ (a wm wc m : Nat) (ws : List (Nat × Nat)),
      m = min (a + wm) wc + wallsInside a m ws → windowEnd a wm wc ws ≤ m := fun h => by
  have w := the_window_end_is_not_the_least_solution_over_walls_wholly_inside
  have := h 420 480 1140 900 [(890, 950)] w.1
  rw [w.2] at this
  omega

/-- The base clamp: arriving at 20:00 after a 19:00 cap gives an empty window ending at the
arrival, where the stage-6 equation's base is the cap. -/
theorem the_window_base_is_clamped_to_the_arrival :
    windowEnd 1200 480 1140 [] = 1200 ∧ min (1200 + 480) 1140 + wallsInside 1200 1200 [] = 1140 := by
  decide

/-- The clip: a wall 06:40–08:00 against a 07:00 arrival extends the window by its hour
after the arrival, and is not wholly inside it. -/
theorem a_wall_begun_before_the_arrival_extends_the_window :
    windowEnd 420 480 1140 [(400, 480)] = 960 ∧
    min (420 + 480) 1140 + wallsInside 420 960 [(400, 480)] = 900 := by
  decide

/-- **E7a as `Goals.lean` STAGE 6 stated it is false** against the fork. -/
theorem the_window_end_does_not_solve_the_equation_as_stage_6_wrote_it :
    ¬ ∀ (a wm wc : Nat) (ws : List (Nat × Nat)),
      windowEnd a wm wc ws = min (a + wm) wc + wallsInside a (windowEnd a wm wc ws) ws := fun h => by
  have w := the_window_base_is_clamped_to_the_arrival
  have := h 1200 480 1140 []
  rw [w.1, w.2] at this
  omega

/-- Two overlapping walls, 10:00–11:40 and 10:50–12:30 after a 07:00 arrival, count their
union once: 150 units, not 200 (fork `merge_walls`). -/
theorem overlapping_walls_count_once :
    windowEnd 420 480 1140 [(650, 750), (600, 700)] = 1050 := by
  decide

/-! ### The configured window: site R3 (reopened, D10-10) and site R2 -/

/-- **Site R3, reopened** (design D10-10): fork `(window_hours * 60.0).round().max(0.0)`,
half-up on the exact pair `window_hours = num/den`.  `f64::round` is half away from zero,
which is half-up on a positive value; where the double's product lands on the other side of
a tie than the exact pair does, the kernel differs by one minute (parity P27). -/
def windowMinOf (wh : Pos) : Nat := halfUpQ (scale wh 60)

/-- **Site R2 on the exact pairs**: fork `budget_blocks` =
`floor(window_hours × 60 / block_min.max(1) × budget_ratio)`, one division, through
`Arith.budgetBlocks`.  It reads the configured window, never the day's actual length (§8.1:
a late start keeps its budget), and never the rounded `windowMinOf`. -/
def budgetOf (wh : Pos) (blockMin : Nat) (br : Pos) : Nat :=
  budgetBlocks (60 * wh.val.num) (max 1 blockMin * wh.val.den)
    (Nat.mul_pos (by omega) (denPos wh)) br

theorem budgetOf_denotes (wh : Pos) (blockMin : Nat) (br : Pos) :
    budgetOf wh blockMin br
      = (60 * wh.val.num * br.val.num) / (max 1 blockMin * wh.val.den * br.val.den) := by
  simp [budgetOf, budgetBlocks, floorQ, mkPos, Nat.mul_assoc]

/-- Eight hours is 480 minutes and 6 blocks of 60 at 3/4; `7.33` h is 440 minutes; half a
minute rounds up; `block_min = 0` reads as 1 (360 blocks); `7.5` h at 50-minute blocks is
floor(6.75) = 6. -/
theorem window_and_budget_on_witnesses :
    windowMinOf (mkPos 8 1 (by decide)) = 480 ∧
    budgetOf (mkPos 8 1 (by decide)) 60 budgetRatio = 6 ∧
    windowMinOf (mkPos 733 100 (by decide)) = 440 ∧
    windowMinOf (mkPos 1 120 (by decide)) = 1 ∧
    budgetOf (mkPos 8 1 (by decide)) 0 budgetRatio = 360 ∧
    budgetOf (mkPos 15 2 (by decide)) 50 budgetRatio = 6 := by
  decide

/-! ### In real seconds, through the zone table -/

/-- `local_dt`'s instants are whole seconds, so a window in UTC seconds is exact. -/
theorem instantOf_ns (z : Cal.Tz) (d : Nat) (c : Fin 1440) : (Cal.instantOf z d c).ns = 0 := by
  unfold Cal.instantOf
  split
  · rfl
  · split <;> rfl

/-- **Fork `window_and_budget(local_dt(tz, d, arrival), walls, cfg)`'s window for day `d`**,
as UTC seconds `(start, end)`.  The walls are UTC seconds (`wallsOn`); `windowMin` is
`windowMinOf`'s minutes.  The cap is `window_cap` on the arrival's local date. -/
def windowOn (z : Cal.Tz) (d : Nat) (arrival windowCap : Field.Clock) (windowMin : Nat)
    (walls : List (Nat × Nat)) : Nat × Nat :=
  let a := (Cal.instantOf z d arrival).sec
  (a, windowEnd a (60 * windowMin) (Cal.instantOf z (Cal.localDate z ⟨a, 0⟩) windowCap).sec walls)

/-- E7 in real seconds, as `windowOn` runs it. -/
theorem windowOn_solves_E7 (z : Cal.Tz) (d : Nat) (arrival windowCap : Field.Clock) (windowMin : Nat)
    (walls : List (Nat × Nat)) :
    let w := windowOn z d arrival windowCap windowMin walls
    let base := windowBase w.1 (60 * windowMin)
      (Cal.instantOf z (Cal.localDate z ⟨w.1, 0⟩) windowCap).sec
    w.1 = (Cal.instantOf z d arrival).sec ∧ w.2 = base + wallOverlap w.1 w.2 walls ∧
      ∀ m, m = base + wallOverlap w.1 m walls → w.2 ≤ m :=
  ⟨rfl, the_window_end_solves_the_equation _ _ _ _, fun m hm => the_window_end_is_the_least_solution _ _ _ m _ hm⟩

/-- The witnesses' day numbers are the dates they name. -/
theorem the_witness_days_are_the_dates_they_name :
    Cal.toDay ⟨2026, 9, 7⟩ = 739865 ∧ Cal.weekdayOf 739865 = .monday ∧
    Cal.toDay ⟨2026, 3, 8⟩ = 739682 := by
  decide

/-- Fork test `budget_of_an_eight_hour_window` (Chicago, 2026-09-07): arriving at 07:00 with
no walls, the window ends at 15:00 and the budget is 6. -/
theorem budget_of_an_eight_hour_window :
    windowOn Cal.chicago 739865 420 1140 (windowMinOf (mkPos 8 1 (by decide))) []
      = ((Cal.instantOf Cal.chicago 739865 420).sec, (Cal.instantOf Cal.chicago 739865 900).sec) ∧
    budgetOf (mkPos 8 1 (by decide)) 60 budgetRatio = 6 := by
  decide

/-- Fork test `walls_extend_the_window`: the §4.3 meeting 12:50–13:50 moves the end from
15:00 to 16:00. -/
theorem walls_extend_the_window :
    windowOn Cal.chicago 739865 420 1140 480
        [((Cal.instantOf Cal.chicago 739865 770).sec, (Cal.instantOf Cal.chicago 739865 830).sec)]
      = ((Cal.instantOf Cal.chicago 739865 420).sec, (Cal.instantOf Cal.chicago 739865 960).sec) := by
  decide

/-- Fork test `the_cap_bounds_the_window`: arriving at 14:00, the eight hours would end at
22:00, and the cap ends the window at 19:00. -/
theorem the_cap_bounds_the_window :
    (windowOn Cal.chicago 739865 840 1140 480 []).2 = (Cal.instantOf Cal.chicago 739865 1140).sec := by
  decide

/-- Fork test `wall_extension_reaches_a_fixed_point` (`capacity_slots.rs`): 15:00 plus the
09:00 wall's hour is 16:00, which brings the 15:30 wall inside, so the end is 16:30. -/
theorem wall_extension_reaches_a_fixed_point :
    (windowOn Cal.chicago 739865 420 1140 480
        [((Cal.instantOf Cal.chicago 739865 540).sec, (Cal.instantOf Cal.chicago 739865 600).sec),
         ((Cal.instantOf Cal.chicago 739865 930).sec, (Cal.instantOf Cal.chicago 739865 960).sec)]).2
      = (Cal.instantOf Cal.chicago 739865 990).sec := by
  decide

/-- **A DST day counts real hours** (design §13.3, P28 not needed): on 2026-03-08, arriving
at 01:00 CST, eight hours end at 10:00 CDT on the clock, 28,800 seconds later. -/
theorem the_window_counts_real_hours_across_the_spring_transition :
    windowOn Cal.chicago 739682 60 1140 480 []
      = ((Cal.instantOf Cal.chicago 739682 60).sec, (Cal.instantOf Cal.chicago 739682 600).sec) ∧
    (Cal.instantOf Cal.chicago 739682 600).sec - (Cal.instantOf Cal.chicago 739682 60).sec
      = 480 * 60 := by
  decide

/-! ### Walls from the plan: fork `Ctx::walls_on`, indexed once per request -/

/-- One wall of the plan: the local dates it belongs to and its UTC seconds. -/
structure WallIx where
  fromDay : Nat
  toDay   : Nat
  lo      : Nat
  hi      : Nat
deriving DecidableEq, Repr

/-- `NaiveDateTime − Duration::minutes(m)`: the local clock moved back, as a date and a
clock (saturating at the origin). -/
def shiftBack (s : Field.DT) (m : Nat) : Nat × Field.Clock :=
  ((s.day * 1440 + s.time.val - m) / 1440,
    ⟨(s.day * 1440 + s.time.val - m) % 1440, Nat.mod_lt _ (by decide)⟩)

theorem shiftBack_zero (s : Field.DT) : shiftBack s 0 = (s.day, s.time) := by
  have h := s.time.isLt
  simp only [shiftBack, Nat.sub_zero, Prod.mk.injEq]
  refine ⟨by omega, Fin.ext ?_⟩
  simp only
  omega

/-- Fork `walls_on`'s wall for one item: none for a settled item or a shape that is not an
interval; otherwise the start moved back by `buffer:` on the local clock, the start's date
through the end's date, and both ends through `local_dt`. -/
def wallOfEntity (z : Cal.Tz) (bm : Nat) (p : PlanCore) (i : Id) (e : Entity) : Option WallIx :=
  match e.val.status with
  | .settled _ => none
  | _ =>
    match effectiveShape p i with
    | .interval s f =>
      let sb := shiftBack s ((e.val.buffer.map (Field.Dur.minutes bm)).getD 0)
      some ⟨sb.1, f.day, (Cal.instantOf z sb.1 sb.2).sec, (Cal.instantOf z f.day f.time).sec⟩
    | _ => none

/-- Every wall of the plan, read once per request (`bm` is `block_min`, for a `buffer:`
written in blocks). -/
def wallIndex (z : Cal.Tz) (bm : Nat) (p : PlanCore) : List WallIx :=
  p.store.dom.filterMap fun i =>
    match p.store.get i with
    | none => none
    | some e => wallOfEntity z bm p i e

/-- Fork `walls_on(date)`: the walls whose dates cover `d`, **not clipped to `d`** (quirk
(e), gap 85). -/
def wallsOn (ix : List WallIx) (d : Nat) : List (Nat × Nat) :=
  ix.filterMap fun w => if w.fromDay ≤ d ∧ d ≤ w.toDay then some (w.lo, w.hi) else none

theorem mem_wallsOn {ix : List WallIx} {d : Nat} {w : Nat × Nat} :
    w ∈ wallsOn ix d ↔ ∃ x ∈ ix, x.fromDay ≤ d ∧ d ≤ x.toDay ∧ w = (x.lo, x.hi) := by
  simp only [wallsOn, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, h⟩
    split at h
    · rename_i hd; simp only [Option.some.injEq] at h; exact ⟨x, hx, hd.1, hd.2, h.symm⟩
    · simp at h
  · rintro ⟨x, hx, h1, h2, rfl⟩
    exact ⟨x, hx, by simp [h1, h2]⟩

theorem mem_wallIndex {z : Cal.Tz} {bm : Nat} {p : PlanCore} {x : WallIx} :
    x ∈ wallIndex z bm p ↔ ∃ i e, p.store.get i = some e ∧ wallOfEntity z bm p i e = some x := by
  simp only [wallIndex, List.mem_filterMap]
  constructor
  · rintro ⟨i, _, h⟩
    split at h
    · simp at h
    · rename_i e he; exact ⟨i, e, he, h⟩
  · rintro ⟨i, e, he, h⟩
    refine ⟨i, (p.store.domSpec i).2 (by simp [he]), ?_⟩
    simp [he, h]

/-- A settled item is no wall. -/
theorem wallOfEntity_settled (z : Cal.Tz) (bm : Nat) (p : PlanCore) (i : Id) (e : Entity)
    (o : Outcome) (h : e.val.status = .settled o) : wallOfEntity z bm p i e = none := by
  simp [wallOfEntity, h]

/-- An unsettled interval item with no `buffer:` is the wall of its own ends. -/
theorem wallOfEntity_interval (z : Cal.Tz) (bm : Nat) (p : PlanCore) (i : Id) (e : Entity)
    (s f : Field.DT) (hst : ∀ o, e.val.status ≠ .settled o) (hsh : effectiveShape p i = .interval s f)
    (hb : e.val.buffer = none) :
    wallOfEntity z bm p i e
      = some ⟨s.day, f.day, (Cal.instantOf z s.day s.time).sec, (Cal.instantOf z f.day f.time).sec⟩ := by
  unfold wallOfEntity
  split
  · rename_i o ho; exact absurd ho (hst o)
  · simp [hsh, hb, shiftBack_zero]

/-- **The buffer comes off the local clock, not off the instant** (fork `walls_on`): an
03:30 interval with `buffer:60m` on 2026-03-08 starts its wall at the local time 02:30,
which Chicago skips, so the wall starts at 03:00 CDT; one hour before the 03:30 instant
would be half an hour earlier. -/
theorem the_buffer_is_taken_off_the_local_clock :
    shiftBack ⟨739682, 210⟩ 60 = (739682, 150) ∧
    (Cal.instantOf Cal.chicago 739682 150).sec
      = (Cal.instantOf Cal.chicago 739682 210).sec - 60 * 60 + 30 * 60 := by
  decide

/-- **Quirk (e), the multi-day wall** (owner's Q6, gap 85): a wall from Monday 09:00 to
Wednesday 17:00 (2026-09-07 to 09-09, Chicago) belongs to Tuesday and Wednesday unclipped.
Tuesday's window runs from 07:00 to Thursday 01:00 and Wednesday's from 07:00 to Thursday
01:00, so Wednesday 17:00 to Thursday 01:00, after the wall ends, lies in both.  Bounding a
window to its own date (the later fix Q6 names) would change Tuesday's end, so the fix is a
behaviour change with its own parity entry. -/
theorem a_multi_day_wall_puts_one_evening_in_two_windows :
    let ix : List WallIx := [⟨739865, 739867, (Cal.instantOf Cal.chicago 739865 540).sec,
      (Cal.instantOf Cal.chicago 739867 1020).sec⟩]
    windowOn Cal.chicago 739866 420 1140 480 (wallsOn ix 739866)
      = ((Cal.instantOf Cal.chicago 739866 420).sec, (Cal.instantOf Cal.chicago 739868 60).sec) ∧
    windowOn Cal.chicago 739867 420 1140 480 (wallsOn ix 739867)
      = ((Cal.instantOf Cal.chicago 739867 420).sec, (Cal.instantOf Cal.chicago 739868 60).sec) ∧
    (Cal.instantOf Cal.chicago 739867 1020).sec < (Cal.instantOf Cal.chicago 739868 60).sec := by
  decide

end Look
end Tm
