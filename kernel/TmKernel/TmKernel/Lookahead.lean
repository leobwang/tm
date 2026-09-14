import TmKernel.Capacity
/-!
# Lookahead — D10's exact mixture over step 3's EDF (stage 5, track L)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §13.  This module **produces** the
`List DayCapacity` that `Capacity.lean`'s `edf` consumes, and never restates it.  Step L1
(§13.2) builds the unit, the weight and the mixture; the histograms each location would
have on a day (the window E7, the slot cut, energy and the budget limit) are L2–L4's, and
are arguments here.

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

Nothing here recurses over a list the wire can make large: a histogram is `Fin 6 → Nat`, and
the scaling laws recurse over step 3's own `reserveRest`/`edfCaps` only inside proofs.

## Not here, by name

* `pureDay`, `lookahead`, `Input`, `mkInput?` (L5); the window, cut and energy (L2–L4).
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

end Look
end Tm
