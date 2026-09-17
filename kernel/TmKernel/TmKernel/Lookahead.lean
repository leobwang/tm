import TmKernel.Capacity
import TmKernel.Cal
/-!
# Lookahead — D10's exact mixture over step 3's EDF (stage 5, track L)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §13.  This module **produces** the
`List DayCapacity` that `Capacity.lean`'s `edf` consumes, and never restates it.  Step L1
(§13.2) builds the unit, the weight and the mixture.  Step L2 (§13.3, pulled from stage 6
by the owner's D12) builds the day's window, E7, in real seconds through `Cal`'s zone
table, and the plan's walls; its section below says what it ports and what it refutes.
Step L3 (§13.3, D12 likewise) cuts the window into slots and breaks around the walls and
rests (`freeIntervals`, `cutSlots`), exactly in whole seconds.  Step L4 (§13.3, D12
likewise) gives each slot its energy from the hours since wake in exact hundredths from
seconds (site R11, `hsw100`), the prior curve and the model's learned curves as data, and the
home cap (`futureEnergy`, `energize`), then limits the day to its budget (`limitSlots`, proved
equal to L1's `limitHist`), so one location's future day is `dayHist`.  Step L5 (§13.4)
runs the day range: `mkInput?` decodes the host's tables with the kernel's fallbacks, each
future day's wake is today's wake clock through `local_dt` at second resolution
(`wakeInstantOf`), and `lookahead` mixes the two locations' limited days at the weekday's
weight, day 0 being the host's histogram until L9.  Step L6 (§13.6) bounds every other value the
capacity wire carries (`mkDayCfg?`, `mkStep?`, `curveOk`, `priorOk`, `energyOk`, `homeMaxOk`),
each with its rejection theorems; the wire itself is `Boundary.lean`'s.  Step L8's kernel half (§13.6,
§13.8) answers fork `priority::compute` over the lookahead: which candidates enter step 3's EDF pass
(gap 80), the grants (gap 107), §7.1's bin at each grant's exact availability, and §7.2's `p` after
§7.4 (`priorities`).  Its host half adds §7.2's floor pass over the capacity the pass leaves
(`prioritiesWithFloors`, gap 79).
**Stage 6's `dayPlan` must reuse L2's `windowEnd`, `windowOn`, `wallIndex` and `wallsOn`,
L3's `freeIntervals` and `cutSlots`, and L4's `hsw100`, `predictAt`, `capForLocation` and
`energize`, never a second copy** (design §2.3).

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
(`windowEnd_eq_windowEndFast`; since L3 also `sortByStart_eq_sortByStartFast`, for every
caller).  L3's cut is listed in its section: `foldl`s, core's `append`, `map`, `filter` and
`any`, and a tail-recursive loop on structural fuel.  L4's energy and limit are listed in
theirs: core `map`, `foldl`s, and `limitSlots` compiled as its histogram form
(`limitSlots_eq_limitSlotsFast`).  L5's day range is a `foldl` over core's `List.range`,
then `reverse`, and each day is compiled with its histograms held
(`dayOf_eq_dayOfFast`).  L6's bounds walk nothing longer than their own guards allow: `curveOk`
checks a curve's length (core `length`, tail recursive) before `all` and `sortedFrom` walk its
at most 64 ranges, and `priorOk` checks the curve count before its walks over at most 16 curves.

## Not here, by name

* The wire (`capacity` and `lookahead`, digit strings, the refusal names): `Boundary.lean`'s L6
  section.
* Day 0's posterior correction, sleep-debt shift and `--allow-home` (L9).
* The zone table's refusal of a sub-minute offset (`badTz subMinuteOffset`, §13.6): not needed.
  L2's window, L3's cut and L4's hours since wake count whole seconds, so each is the fork's for
  every offset (the L6 section says so).
* Day 0 (`ofHist` over the host's histogram until L9, gap 93 of the design).
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
def windowFrom (z : Cal.Tz) (a windowMin : Nat) (windowCap : Field.Clock)
    (walls : List (Nat × Nat)) : Nat × Nat :=
  (a, windowEnd a (60 * windowMin) (Cal.instantOf z (Cal.localDate z ⟨a, 0⟩) windowCap).sec walls)

/-- **Fork `window_and_budget(local_dt(tz, d, arrival), walls, cfg)`'s window for day `d`**: the
same window, from an arrival named as a clock.  Step L9's day 0 arrives at an *instant* — `now`,
or `state.arrival` — so `windowFrom` is the definition and this is its whole-minute instance
(AGENTS §5.3: one window, not two). -/
def windowOn (z : Cal.Tz) (d : Nat) (arrival windowCap : Field.Clock) (windowMin : Nat)
    (walls : List (Nat × Nat)) : Nat × Nat :=
  windowFrom z (Cal.instantOf z d arrival).sec windowMin windowCap walls

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

/-! ############################################################################
## The slot cut (stage 5 D10 step L3; design §13.3, owner's D12)

Pulled forward from stage 6 by the owner's D12, beside L2's window.  **Stage 6's `dayPlan`
must reuse `freeIntervals` and `cutSlots`, never a second copy** (design §2.3, AGENTS §5.3):
the lookahead calls `cutSlots c arrival end walls [] 0`, and the planner's step 3 calls it
with its placed routines as `rests` and its blocks since the last break.

### The fork point, read by name

`capacity::cut_slots_around(from, end, walls, rests, cfg, blocks_since_break)` (spec §8.2
step 3); `cut_slots(from, end, walls, cfg)` is `cutSlots c from end walls [] 0` and
`cut_slots_from(…, k)` is `cutSlots c from end walls [] k`.

1. `block_min == 0` returns the empty cut (`cutSlots_without_a_block_length_is_empty`);
2. `min_last = min_last_block_min.min(block_min).max(1)` (`CutCfg.minLast`), and
   `breaks_on = break_after_blocks > 0 && break_min > 0`;
3. `free_intervals(from, end, walls ++ rests)` (`freeIntervals`): empty when `end ≤ from`;
   otherwise `normalize_walls` clips each wall to `[from, end)` **on both sides** (`clipTo`),
   drops the empty ones, sorts by start and merges touching walls (L2's `sortByStart` and
   `mergeSorted`), and the cursor walk (`freeStep`) emits the gaps;
4. for each free stretch `(start, stop)`, in order: `restful_end(start)` (a rest ending
   exactly at `start` and at least `break_min` long, `restfulEnd`) sets the counter to 0;
   then the `while t < stop` loop (`cutStretch`): a break that is due is placed only when
   `min_last` still fits after it, else the stretch ends; a full block when `block_min`
   fits; else a short block to `stop` when `min_last` fits; else the stretch ends.  The
   counter is carried from one stretch to the next: a wall is work.

### Exact in whole seconds, so no sub-minute refusal is needed

The fork compares `Duration::num_minutes()`, which truncates toward zero, against whole
minutes.  For whole seconds `x ≥ 0`, `num_minutes x ≥ m ⇔ x ≥ 60·m`; for a negative `x`,
`num_minutes x ≤ 0 < min_last`.  So every comparison is one inequality between UTC seconds:
`(stop − (t + brk)).num_minutes() < min_last ⇔ stop < t + 60·brk + 60·min_last`, a block
fits iff `t + 60·block_min ≤ stop`, and `restful_end`'s `(b − a).num_minutes() >= break_min`
is `60·break_min ≤ b − a ∧ a < b + 60` (the second conjunct is a reversed rest's truncation,
and it is unobservable: the counter is read only when breaks are on, which needs
`break_min > 0`).  L2's instants (`Cal.instantOf`) are whole seconds, so the cut is the
fork's for **any** zone offset, and design §13.6's `badTz subMinuteOffset` is not needed by
the window or the cut.  A fall-back day's cut counts real minutes
(`a_cut_counts_real_minutes_across_the_fall_transition`).

### What is proved

`freeIntervals_spec`: the free stretches lie in the window, come in order with a wall between
each two, and **hold exactly the units of `[from, end)` no wall or rest covers** (both
directions).  `cutSlots_spec`, and the named consequences below it: slots and breaks inside
the window, avoiding every wall and rest, in order, never overlapping one another; a block is
exactly `block_min`; a short block is at least `min_last` and shorter than a block; a break is
exactly `break_min`; **every break is followed by a slot that starts where it ends**, so no
stretch ends on a break; and the fuel is never the answer (`cutSlots_fuel_is_enough`).

### The recursion rule (D9-21)

Over lists the wire can make large: `clipTo` is core `map`/`filter`; `walls ++ rests` is core
`append` (`appendTR`); the sort is L2's `sortByStart`, now behind its own `@[csimp]` twin
**`sortByStart_eq_sortByStartFast`** (core's `List.mergeSort`, proved equal through
`List.mergeSort_cons`, so every caller, not only `windowEnd`, runs the merge sort);
`mergeSorted`, the free walk and the cut are `foldl`s; `Cut.slotMinutes` and
`Cut.breakMinutes` are `foldl`s.  `cutStretch` recurses on structural fuel `stop − start + 1`
with every recursive call in tail position, and runs once per slot or break, not once per
unit.  `restfulEnd` is core `any` over the rests (the planner's placed routines).
-/

/-- What a slot is (fork `SlotKind`): a full block, or the short last block of a stretch. -/
inductive SlotKind where
  | block
  | short
deriving DecidableEq, Repr

/-- One slot before `energize` (fork `Slot` without its `energy`): UTC seconds
`[start, stop)`. -/
structure Slot where
  start : Nat
  stop  : Nat
  kind  : SlotKind
deriving DecidableEq, Repr

/-- Fork `Slot::minutes`: `(end − start).num_minutes().max(0)`. -/
def Slot.minutes (s : Slot) : Nat := (s.stop - s.start) / 60

/-- Fork `Cut`: the slots and the breaks, each in time order. -/
structure Cut where
  slots  : List Slot
  breaks : List (Nat × Nat)
deriving DecidableEq, Repr

/-- Fork `Cut::slot_minutes`. -/
def Cut.slotMinutes (c : Cut) : Nat := c.slots.foldl (fun a s => a + s.minutes) 0

/-- Fork `Cut::break_minutes`. -/
def Cut.breakMinutes (c : Cut) : Nat := c.breaks.foldl (fun a b => a + (b.2 - b.1) / 60) 0

/-- The four `[day]` keys the cut reads, in minutes (fork `DayConfig`'s `u32`s).  L6's
`DayCfg` carries them with their R10 bounds. -/
structure CutCfg where
  blockMin        : Nat
  breakMin        : Nat
  breakAfter      : Nat
  minLastBlockMin : Nat
deriving DecidableEq, Repr

/-- Fork `cfg.day.min_last_block_min.min(block_min).max(1)`. -/
def CutCfg.minLast (c : CutCfg) : Nat := max 1 (min c.minLastBlockMin c.blockMin)

/-- The shipped `[day]` defaults: `block_min = 60`, `break_min = 20`,
`break_after_blocks = 2`, `min_last_block_min = 30`. -/
def CutCfg.shipped : CutCfg := ⟨60, 20, 2, 30⟩

/-! ### Sorting, compiled as core's merge sort -/

/-- `sortByStart` as the compiled code runs it. -/
def sortByStartFast (L : List (Nat × Nat)) : List (Nat × Nat) :=
  L.mergeSort (fun v w => decide (v.1 ≤ w.1))

theorem insertByStart_append (w : Nat × Nat) : ∀ (l₁ l₂ : List (Nat × Nat)),
    (∀ v ∈ l₁, ¬ w.1 ≤ v.1) → (∀ v ∈ l₂, w.1 ≤ v.1) → insertByStart w (l₁ ++ l₂) = l₁ ++ w :: l₂
  | [], [], _, _ => rfl
  | [], v :: vs, _, h2 => by
    simp only [List.nil_append]
    unfold insertByStart
    rw [if_pos (h2 v (by simp))]
  | v :: vs, l₂, h1, h2 => by
    simp only [List.cons_append]
    unfold insertByStart
    rw [if_neg (h1 v (by simp)), insertByStart_append w vs l₂ (fun u hu => h1 u (by simp [hu])) h2]

/-- **The insertion sort is core's merge sort**, list for list: both are stable, so a wall
lands after every earlier wall with its start (`List.mergeSort_cons`). -/
theorem sortByStart_eq_mergeSort : ∀ L : List (Nat × Nat), sortByStart L = sortByStartFast L
  | [] => by simp [sortByStart, sortByStartFast]
  | w :: ws => by
    have trans : ∀ a b c : Nat × Nat, decide (a.1 ≤ b.1) = true → decide (b.1 ≤ c.1) = true →
        decide (a.1 ≤ c.1) = true := fun a b c h1 h2 => by simp at *; omega
    have total : ∀ a b : Nat × Nat, (decide (a.1 ≤ b.1) || decide (b.1 ≤ a.1)) = true :=
      fun a b => by simp; omega
    obtain ⟨l₁, l₂, h1, h2, h3⟩ := List.mergeSort_cons trans total w ws
    have hs := mergeSort_start_sorted (w :: ws)
    rw [show List.mergeSort (w :: ws) (fun v w => decide (v.1 ≤ w.1)) = l₁ ++ w :: l₂ from h1] at hs
    have hl₂ : ∀ v ∈ l₂, w.1 ≤ v.1 :=
      fun v hv => List.rel_of_pairwise_cons (List.pairwise_append.1 hs).2.1 hv
    show insertByStart w (sortByStart ws) = sortByStartFast (w :: ws)
    rw [sortByStart_eq_mergeSort ws, sortByStartFast, sortByStartFast, h2, h1]
    exact insertByStart_append w l₁ l₂ (fun v hv => by simpa using h3 v hv) hl₂

/-- The compiled `sortByStart` is core's merge sort (D9-21). -/
@[csimp] theorem sortByStart_eq_sortByStartFast : @sortByStart = @sortByStartFast :=
  funext sortByStart_eq_mergeSort

/-! ### Free intervals: fork `free_intervals` -/

/-- Fork `normalize_walls`'s clip: each wall cut to `[lo, hi)`, empty walls dropped. -/
def clipTo (lo hi : Nat) (walls : List (Nat × Nat)) : List (Nat × Nat) :=
  (walls.map fun w => (max w.1 lo, min w.2 hi)).filter fun w => decide (w.1 < w.2)

/-- Fork `normalize_walls(lo, hi, walls)`: clipped, sorted by start, merged. -/
def freeChain (lo hi : Nat) (walls : List (Nat × Nat)) : List (Nat × Nat) :=
  mergeSorted (sortByStart (clipTo lo hi walls))

/-- One step of fork `free_intervals`' walk, on `(cursor, gaps newest first)`:
`if a > cursor { push (cursor, a) }; cursor = cursor.max(b)`. -/
def freeStep (acc : Nat × List (Nat × Nat)) (w : Nat × Nat) : Nat × List (Nat × Nat) :=
  (max acc.1 w.2, if acc.1 < w.1 then (acc.1, w.1) :: acc.2 else acc.2)

/-- **Fork `free_intervals(lo, hi, walls)`**: the free stretches of `[lo, hi)`, in order. -/
def freeIntervals (lo hi : Nat) (walls : List (Nat × Nat)) : List (Nat × Nat) :=
  if hi ≤ lo then [] else
    let r := (freeChain lo hi walls).foldl freeStep (lo, [])
    (if r.1 < hi then (r.1, hi) :: r.2 else r.2).reverse

/-! ### The cut: fork `cut_slots_around` -/

/-- The loop's slots and breaks, newest first. -/
abbrev CutAcc := List Slot × List (Nat × Nat)

/-- **Fork `cut_slots_around`'s `while t < stop` loop** over one free stretch ending at
`stop`, from `t` with `k` blocks since the last break, on structural fuel.  Returns the
counter and the accumulator. -/
def cutStretch (c : CutCfg) (stop : Nat) : Nat → Nat → Nat → CutAcc → Nat × CutAcc
  | 0, _, k, acc => (k, acc)
  | fuel + 1, t, k, acc =>
    if t < stop then
      if (0 < c.breakAfter ∧ 0 < c.breakMin) ∧ c.breakAfter ≤ k then
        if stop < t + 60 * c.breakMin + 60 * c.minLast then (k, acc)
        else cutStretch c stop fuel (t + 60 * c.breakMin) 0 (acc.1, (t, t + 60 * c.breakMin) :: acc.2)
      else if t + 60 * c.blockMin ≤ stop then
        cutStretch c stop fuel (t + 60 * c.blockMin) (k + 1)
          (⟨t, t + 60 * c.blockMin, .block⟩ :: acc.1, acc.2)
      else if t + 60 * c.minLast ≤ stop then
        cutStretch c stop fuel stop (k + 1) (⟨t, stop, .short⟩ :: acc.1, acc.2)
      else (k, acc)
    else (k, acc)

/-- Fork `restful_end(t)`: a rest ending exactly at `t` whose `num_minutes()` is at least
`break_min`, in whole seconds. -/
def restfulEnd (c : CutCfg) (rests : List (Nat × Nat)) (t : Nat) : Bool :=
  rests.any fun r => decide (r.2 = t ∧ 60 * c.breakMin ≤ r.2 - r.1 ∧ r.1 < r.2 + 60)

/-- One free stretch of the cut: the counter reset by a restful end, then the loop on fuel
`stop − start + 1`. -/
def cutStep (c : CutCfg) (rests : List (Nat × Nat)) (acc : Nat × CutAcc) (iv : Nat × Nat) :
    Nat × CutAcc :=
  cutStretch c iv.2 (iv.2 - iv.1 + 1) iv.1 (if restfulEnd c rests iv.1 then 0 else acc.1) acc.2

/-- **§8.2 step 3's cut** (fork `cut_slots_around(lo, hi, walls, rests, cfg, k)`), in UTC
seconds: `[lo, hi)` around the walls and the rests, into blocks and breaks. -/
def cutSlots (c : CutCfg) (lo hi : Nat) (walls rests : List (Nat × Nat)) (sinceBreak : Nat) : Cut :=
  if c.blockMin = 0 then ⟨[], []⟩ else
    let r := (freeIntervals lo hi (walls ++ rests)).foldl (cutStep c rests) (sinceBreak, ([], []))
    ⟨r.2.1.reverse, r.2.2.reverse⟩

/-! ### Free intervals, specified -/

theorem clipTo_mem {lo hi : Nat} {ws : List (Nat × Nat)} {w : Nat × Nat} (h : w ∈ clipTo lo hi ws) :
    lo ≤ w.1 ∧ w.1 < w.2 ∧ w.2 ≤ hi := by
  simp only [clipTo, List.mem_filter, List.mem_map, decide_eq_true_eq] at h
  obtain ⟨⟨u, _, rfl⟩, h2⟩ := h
  exact ⟨Nat.le_max_right _ _, h2, Nat.min_le_right _ _⟩

/-- Clipping keeps a unit's cover inside `[lo, hi)` and removes it outside. -/
theorem covered_clipTo (lo hi : Nat) (ws : List (Nat × Nat)) (t : Nat) :
    covered (clipTo lo hi ws) t = (decide (lo ≤ t ∧ t < hi) && covered ws t) := by
  apply Bool.eq_iff_iff.2
  rw [covered_eq_true, Bool.and_eq_true, covered_eq_true, decide_eq_true_eq]
  simp only [clipTo, List.mem_filter, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨⟨u, hu, rfl⟩, _⟩, h1, h2⟩
    simp only at h1 h2
    exact ⟨⟨by omega, by omega⟩, u, hu, by omega, by omega⟩
  · rintro ⟨⟨h1, h2⟩, u, hu, h3, h4⟩
    exact ⟨(max u.1 lo, min u.2 hi), ⟨⟨u, hu, rfl⟩, by simp; omega⟩, by simp; omega, by simp; omega⟩

/-- The merged walls form a chain inside `[lo, hi]` with the walls' cover there. -/
theorem freeChain_spec (lo hi : Nat) (ws : List (Nat × Nat)) :
    WallChain lo (freeChain lo hi ws) ∧ (∀ w ∈ freeChain lo hi ws, w.2 ≤ hi) ∧
      ∀ t, covered (freeChain lo hi ws) t = (decide (lo ≤ t ∧ t < hi) && covered ws t) := by
  obtain ⟨hc, hcov⟩ := mergeSorted_spec lo (sortByStart (clipTo lo hi ws)) (sortByStart_sorted _)
    (fun w hw => (clipTo_mem ((sortByStart_perm _).mem_iff.1 hw)).imp_right (fun h => h.1))
  have hcov' : ∀ t, covered (freeChain lo hi ws) t = (decide (lo ≤ t ∧ t < hi) && covered ws t) :=
    fun t => by rw [freeChain, hcov t, covered_perm (sortByStart_perm _) t, covered_clipTo]
  refine ⟨hc, fun w hw => ?_, hcov'⟩
  have hw' := hc.2 w hw
  have h := hcov' (w.2 - 1)
  have hin : covered (freeChain lo hi ws) (w.2 - 1) = true :=
    covered_eq_true.2 ⟨w, hw, by omega, by omega⟩
  rw [hin] at h
  have := h.symm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  omega

/-- The free walk over a chain of walls starting at or after the cursor: the gaps it emits
are ordered, lie between the cursor and the final cursor, and hold exactly the uncovered
units there. -/
theorem freeFold_spec : ∀ (L : List (Nat × Nat)), L.Pairwise (fun v w => v.2 < w.1) →
    ∀ (c : Nat) (R : List (Nat × Nat)), (∀ w ∈ L, c ≤ w.1 ∧ w.1 < w.2) →
    (∀ iv ∈ R, iv.1 < iv.2 ∧ iv.2 < c) → R.Pairwise (fun a b => b.2 < a.1) →
    c ≤ (L.foldl freeStep (c, R)).1 ∧
    (∀ B, c ≤ B → (∀ w ∈ L, w.2 ≤ B) → (L.foldl freeStep (c, R)).1 ≤ B) ∧
    (∀ w ∈ L, w.2 ≤ (L.foldl freeStep (c, R)).1) ∧
    (∀ iv ∈ (L.foldl freeStep (c, R)).2, iv.1 < iv.2 ∧ iv.2 < (L.foldl freeStep (c, R)).1) ∧
    (L.foldl freeStep (c, R)).2.Pairwise (fun a b => b.2 < a.1) ∧
    (∀ iv ∈ (L.foldl freeStep (c, R)).2, iv ∈ R ∨ c ≤ iv.1) ∧
    ∀ t, (∃ iv ∈ (L.foldl freeStep (c, R)).2, iv.1 ≤ t ∧ t < iv.2) ↔
      ((∃ iv ∈ R, iv.1 ≤ t ∧ t < iv.2) ∨
        (c ≤ t ∧ t < (L.foldl freeStep (c, R)).1 ∧ covered L t = false))
  | [], _, c, R, _, hR, hRp => by
    simp only [List.foldl_nil]
    refine ⟨Nat.le_refl _, fun _ h _ => h, by simp, hR, hRp, fun iv h => .inl h, fun t => ?_⟩
    constructor
    · exact fun h => .inl h
    · rintro (h | ⟨h1, h2, _⟩)
      · exact h
      · omega
  | w :: L, hp, c, R, hm, hR, hRp => by
    have hw := hm w (by simp)
    have hpw := List.pairwise_cons.1 hp
    have hstep : freeStep (c, R) w = (w.2, if c < w.1 then (c, w.1) :: R else R) := by
      simp only [freeStep]; congr 1; omega
    rw [List.foldl_cons, hstep]
    have hm' : ∀ u ∈ L, w.2 ≤ u.1 ∧ u.1 < u.2 := fun u hu =>
      ⟨Nat.le_of_lt (hpw.1 u hu), (hm u (List.mem_cons_of_mem _ hu)).2⟩
    have hR' : ∀ iv ∈ (if c < w.1 then (c, w.1) :: R else R), iv.1 < iv.2 ∧ iv.2 < w.2 := by
      intro iv hiv
      split at hiv
      · rcases List.mem_cons.1 hiv with rfl | hiv
        · simp only; omega
        · have := hR iv hiv; omega
      · have := hR iv hiv; omega
    have hRp' : (if c < w.1 then (c, w.1) :: R else R).Pairwise (fun a b => b.2 < a.1) := by
      split
      · exact List.pairwise_cons.2 ⟨fun iv hiv => (hR iv hiv).2, hRp⟩
      · exact hRp
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := freeFold_spec L hpw.2 w.2 _ hm' hR' hRp'
    refine ⟨by omega, fun B hB hL => i2 B (hL w (by simp)) (fun u hu => hL u (by simp [hu])),
      fun u hu => ?_, i4, i5, fun iv hiv => ?_, fun t => ?_⟩
    · rcases List.mem_cons.1 hu with rfl | hu
      · exact i1
      · exact i3 u hu
    · rcases i6 iv hiv with h | h
      · split at h
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inr (Nat.le_refl _)
          · exact .inl h
        · exact .inl h
      · exact .inr (by omega)
    · rw [i7 t, covered_cons]
      constructor
      · rintro (⟨iv, hiv, h1, h2⟩ | ⟨h1, h2, h3⟩)
        · split at hiv
          · rcases List.mem_cons.1 hiv with rfl | hiv
            · refine .inr ⟨h1, by omega, ?_⟩
              simp only at h1 h2
              have : covered L t = false := by
                cases hct : covered L t
                · rfl
                · obtain ⟨u, hu, hu1, _⟩ := covered_eq_true.1 hct
                  have := hm' u hu; omega
              simp [this]; omega
            · exact .inl ⟨iv, hiv, h1, h2⟩
          · exact .inl ⟨iv, hiv, h1, h2⟩
        · refine .inr ⟨by omega, h2, ?_⟩
          simp only [h3, Bool.or_false, decide_eq_false_iff_not]
          omega
      · rintro (⟨iv, hiv, h1, h2⟩ | ⟨h1, h2, h3⟩)
        · refine .inl ⟨iv, ?_, h1, h2⟩
          split
          · exact List.mem_cons_of_mem _ hiv
          · exact hiv
        · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h3
          by_cases htw : t < w.1
          · refine .inl ⟨(c, w.1), ?_, h1, htw⟩
            rw [if_pos (by omega)]; simp
          · exact .inr ⟨by omega, h2, h3.2⟩


theorem mem_ite_cons {p : Prop} [Decidable p] {x iv : Nat × Nat} {R : List (Nat × Nat)} :
    iv ∈ (if p then x :: R else R) ↔ (p ∧ iv = x) ∨ iv ∈ R := by
  split <;> simp_all

/-- **Fork `free_intervals`, specified**: the stretches lie in `[lo, hi]`, are nonempty,
come in order with a wall between each two, and hold **exactly** the units of `[lo, hi)`
that no wall covers. -/
theorem freeIntervals_spec (lo hi : Nat) (ws : List (Nat × Nat)) :
    (∀ iv ∈ freeIntervals lo hi ws, lo ≤ iv.1 ∧ iv.1 < iv.2 ∧ iv.2 ≤ hi) ∧
    (freeIntervals lo hi ws).Pairwise (fun a b => a.2 < b.1) ∧
    ∀ t, (∃ iv ∈ freeIntervals lo hi ws, iv.1 ≤ t ∧ t < iv.2) ↔
      (lo ≤ t ∧ t < hi ∧ covered ws t = false) := by
  unfold freeIntervals
  by_cases hlh : hi ≤ lo
  · rw [if_pos hlh]
    refine ⟨by simp, by simp, fun t => ?_⟩
    simp only [List.not_mem_nil, false_and, exists_false, false_iff]
    omega
  · rw [if_neg hlh]
    obtain ⟨hc, hhi, hcov⟩ := freeChain_spec lo hi ws
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ :=
      freeFold_spec (freeChain lo hi ws) hc.1 lo [] (fun w hw => hc.2 w hw) (by simp) (by simp)
    have hr : ((freeChain lo hi ws).foldl freeStep (lo, [])).1 ≤ hi := i2 hi (by omega) hhi
    have hc1 : ∀ t, lo ≤ t → t < hi → covered (freeChain lo hi ws) t = covered ws t := by
      intro t h1 h2; rw [hcov t]; simp [h1, h2]
    generalize (freeChain lo hi ws).foldl freeStep (lo, []) = r at i1 i3 i4 i5 i6 i7 hr
    refine ⟨fun iv hiv => ?_, ?_, fun t => ?_⟩
    · rw [List.mem_reverse, mem_ite_cons] at hiv
      rcases hiv with ⟨h1, rfl⟩ | hiv
      · exact ⟨i1, h1, Nat.le_refl _⟩
      · have := i4 iv hiv
        rcases i6 iv hiv with h | h
        · simp at h
        · exact ⟨h, this.1, by omega⟩
    · rw [List.pairwise_reverse]
      split
      · exact List.pairwise_cons.2 ⟨fun iv hiv => (i4 iv hiv).2, i5⟩
      · exact i5
    · constructor
      · rintro ⟨iv, hiv, h1, h2⟩
        rw [List.mem_reverse, mem_ite_cons] at hiv
        rcases hiv with ⟨h3, rfl⟩ | hiv
        · simp only at h1 h2
          refine ⟨by omega, h2, ?_⟩
          have hz : covered (freeChain lo hi ws) t = false := by
            cases hct : covered (freeChain lo hi ws) t
            · rfl
            · obtain ⟨u, hu, _, hu2⟩ := covered_eq_true.1 hct
              have := i3 u hu; omega
          rw [← hc1 t (by omega) h2]; exact hz
        · obtain ⟨h0, h4, h5⟩ := (i7 t).1 ⟨iv, hiv, h1, h2⟩ |>.resolve_left (by simp)
          refine ⟨h0, by omega, ?_⟩
          rw [← hc1 t h0 (by omega)]; exact h5
      · rintro ⟨h1, h2, h3⟩
        by_cases htr : t < r.1
        · obtain ⟨iv, hiv, hh⟩ := (i7 t).2 (.inr ⟨h1, htr, by rw [hc1 t h1 h2]; exact h3⟩)
          exact ⟨iv, by rw [List.mem_reverse, mem_ite_cons]; exact .inr hiv, hh⟩
        · exact ⟨(r.1, hi), by rw [List.mem_reverse, mem_ite_cons]; exact .inl ⟨by omega, rfl⟩,
            by simp only; omega, h2⟩

theorem freeIntervals_inside_the_window {lo hi : Nat} {ws : List (Nat × Nat)} {iv : Nat × Nat}
    (h : iv ∈ freeIntervals lo hi ws) : lo ≤ iv.1 ∧ iv.1 < iv.2 ∧ iv.2 ≤ hi :=
  (freeIntervals_spec lo hi ws).1 iv h

theorem freeIntervals_are_in_order (lo hi : Nat) (ws : List (Nat × Nat)) :
    (freeIntervals lo hi ws).Pairwise (fun a b => a.2 < b.1) :=
  (freeIntervals_spec lo hi ws).2.1

/-- **Both directions**: a unit is in a free stretch exactly when it is in the window and no
wall holds it. -/
theorem freeIntervals_are_the_free_units (lo hi : Nat) (ws : List (Nat × Nat)) (t : Nat) :
    (∃ iv ∈ freeIntervals lo hi ws, iv.1 ≤ t ∧ t < iv.2) ↔
      (lo ≤ t ∧ t < hi ∧ ∀ w ∈ ws, ¬ (w.1 ≤ t ∧ t < w.2)) := by
  rw [(freeIntervals_spec lo hi ws).2.2 t]
  have : covered ws t = false ↔ ∀ w ∈ ws, ¬ (w.1 ≤ t ∧ t < w.2) := by
    rw [← Bool.not_eq_true, covered_eq_true]; simp
  rw [this]

/-! ### The stretch loop -/

/-- Two fuels above the stretch's remaining length give the same loop result, when
`block_min ≥ 1` (which `cutSlots` checks first, as the fork does). -/
theorem cutStretch_fuel (c : CutCfg) (hb : 0 < c.blockMin) (stop : Nat) :
    ∀ f g t k (acc : CutAcc), stop - t < f → stop - t < g →
      cutStretch c stop f t k acc = cutStretch c stop g t k acc
  | 0, _, _, _, _, hf, _ => absurd hf (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, _, _, hg => absurd hg (Nat.not_lt_zero _)
  | f + 1, g + 1, t, k, acc, hf, hg => by
    simp only [cutStretch]
    by_cases ht : t < stop
    · rw [if_pos ht, if_pos ht]
      by_cases hd : (0 < c.breakAfter ∧ 0 < c.breakMin) ∧ c.breakAfter ≤ k
      · rw [if_pos hd, if_pos hd]
        by_cases hg' : stop < t + 60 * c.breakMin + 60 * c.minLast
        · rw [if_pos hg', if_pos hg']
        · rw [if_neg hg', if_neg hg']
          exact cutStretch_fuel c hb stop f g _ _ _ (by omega) (by omega)
      · rw [if_neg hd, if_neg hd]
        by_cases h1 : t + 60 * c.blockMin ≤ stop
        · rw [if_pos h1, if_pos h1]
          exact cutStretch_fuel c hb stop f g _ _ _ (by omega) (by omega)
        · rw [if_neg h1, if_neg h1]
          by_cases h2 : t + 60 * c.minLast ≤ stop
          · rw [if_pos h2, if_pos h2]
            exact cutStretch_fuel c hb stop f g _ _ _ (by omega) (by omega)
          · rw [if_neg h2, if_neg h2]
    · rw [if_neg ht, if_neg ht]

/-- **The fuel is never the answer** (design §13.3): any fuel above the stretch's length gives
the cut `cutStep` computes on `stop − t + 1`.  Every loop turn advances `t` by at least
60 seconds, or ends the stretch. -/
theorem cutSlots_fuel_is_enough (c : CutCfg) (hb : 0 < c.blockMin) (stop f t k : Nat) (acc : CutAcc)
    (hf : stop - t < f) :
    cutStretch c stop f t k acc = cutStretch c stop (stop - t + 1) t k acc :=
  cutStretch_fuel c hb stop f _ t k acc hf (by omega)

/-- The stretch loop's induction principle: a property of the loop state that every push
keeps and every exit turns into `Q`. -/
theorem cutStretch_rec (c : CutCfg) (stop : Nat) (P : Nat → Nat → Nat → CutAcc → Prop)
    (Q : Nat × CutAcc → Prop)
    (hexit : ∀ f t k acc, P f t k acc →
      (f = 0 ∨ stop ≤ t ∨
        ((0 < c.breakAfter ∧ 0 < c.breakMin) ∧ c.breakAfter ≤ k ∧
          stop < t + 60 * c.breakMin + 60 * c.minLast) ∨
        (¬ ((0 < c.breakAfter ∧ 0 < c.breakMin) ∧ c.breakAfter ≤ k) ∧
          stop < t + 60 * c.blockMin ∧ stop < t + 60 * c.minLast)) →
      Q (k, acc))
    (hbrk : ∀ f t k acc, P (f + 1) t k acc → t < stop → (0 < c.breakAfter ∧ 0 < c.breakMin) →
      c.breakAfter ≤ k → t + 60 * c.breakMin + 60 * c.minLast ≤ stop →
      P f (t + 60 * c.breakMin) 0 (acc.1, (t, t + 60 * c.breakMin) :: acc.2))
    (hblk : ∀ f t k acc, P (f + 1) t k acc → t < stop →
      ¬ ((0 < c.breakAfter ∧ 0 < c.breakMin) ∧ c.breakAfter ≤ k) → t + 60 * c.blockMin ≤ stop →
      P f (t + 60 * c.blockMin) (k + 1) (⟨t, t + 60 * c.blockMin, .block⟩ :: acc.1, acc.2))
    (hsht : ∀ f t k acc, P (f + 1) t k acc → t < stop →
      ¬ ((0 < c.breakAfter ∧ 0 < c.breakMin) ∧ c.breakAfter ≤ k) → stop < t + 60 * c.blockMin →
      t + 60 * c.minLast ≤ stop →
      P f stop (k + 1) (⟨t, stop, .short⟩ :: acc.1, acc.2)) :
    ∀ f t k acc, P f t k acc → Q (cutStretch c stop f t k acc)
  | 0, t, k, acc, h => hexit 0 t k acc h (.inl rfl)
  | f + 1, t, k, acc, h => by
    simp only [cutStretch]
    by_cases ht : t < stop
    · rw [if_pos ht]
      by_cases hd : (0 < c.breakAfter ∧ 0 < c.breakMin) ∧ c.breakAfter ≤ k
      · rw [if_pos hd]
        by_cases hg : stop < t + 60 * c.breakMin + 60 * c.minLast
        · rw [if_pos hg]; exact hexit _ t k acc h (.inr (.inr (.inl ⟨hd.1, hd.2, hg⟩)))
        · rw [if_neg hg]
          exact cutStretch_rec c stop P Q hexit hbrk hblk hsht f _ _ _
            (hbrk f t k acc h ht hd.1 hd.2 (by omega))
      · rw [if_neg hd]
        by_cases h1 : t + 60 * c.blockMin ≤ stop
        · rw [if_pos h1]
          exact cutStretch_rec c stop P Q hexit hbrk hblk hsht f _ _ _ (hblk f t k acc h ht hd h1)
        · rw [if_neg h1]
          by_cases h2 : t + 60 * c.minLast ≤ stop
          · rw [if_pos h2]
            exact cutStretch_rec c stop P Q hexit hbrk hblk hsht f _ _ _
              (hsht f t k acc h ht hd (by omega) h2)
          · rw [if_neg h2]
            exact hexit _ t k acc h (.inr (.inr (.inr ⟨hd, by omega, by omega⟩)))
    · rw [if_neg ht]; exact hexit _ t k acc h (.inr (.inl (by omega)))

theorem minLast_pos (c : CutCfg) : 0 < c.minLast := by
  unfold CutCfg.minLast; omega

/-- A slot as the fork cuts it. -/
def SlotShape (c : CutCfg) (s : Slot) : Prop :=
  s.start < s.stop ∧
    (s.kind = .block → s.stop = s.start + 60 * c.blockMin) ∧
    (s.kind = .short → s.start + 60 * c.minLast ≤ s.stop ∧ s.stop < s.start + 60 * c.blockMin)

/-- The loop's accumulator (both lists newest first) is ordered, disjoint and shaped, and
nothing in it ends after `t`. -/
def AccInv (c : CutCfg) (t : Nat) (acc : CutAcc) : Prop :=
  (∀ s ∈ acc.1, s.stop ≤ t) ∧ (∀ b ∈ acc.2, b.2 ≤ t) ∧
    acc.1.Pairwise (fun x y => y.stop ≤ x.start) ∧ acc.2.Pairwise (fun x y => y.2 ≤ x.1) ∧
    (∀ s ∈ acc.1, ∀ b ∈ acc.2, s.stop ≤ b.1 ∨ b.2 ≤ s.start) ∧
    (∀ s ∈ acc.1, SlotShape c s) ∧ (∀ b ∈ acc.2, b.2 = b.1 + 60 * c.breakMin ∧ 0 < c.breakMin)

theorem AccInv.mono {c : CutCfg} {t t' : Nat} {acc : CutAcc} (h : AccInv c t acc) (ht : t ≤ t') :
    AccInv c t' acc :=
  ⟨fun s hs => Nat.le_trans (h.1 s hs) ht, fun b hb => Nat.le_trans (h.2.1 b hb) ht, h.2.2⟩

theorem AccInv.nil (c : CutCfg) (t : Nat) : AccInv c t ([], []) := by
  simp [AccInv]

/-- Every break has a slot starting where it ends. -/
def Followed (acc : CutAcc) : Prop := ∀ b ∈ acc.2, ∃ s ∈ acc.1, s.start = b.2

/-- **One stretch** keeps the invariant, puts every new item inside `[t₀, stop]`, and
leaves no break without its slot. -/
theorem cutStretch_spec (c : CutCfg) (hb : 0 < c.blockMin) (stop t₀ f k : Nat) (acc : CutAcc)
    (ht : t₀ ≤ stop) (hf : stop - t₀ < f) (hi : AccInv c t₀ acc) (hfo : Followed acc) :
    AccInv c stop (cutStretch c stop f t₀ k acc).2 ∧ Followed (cutStretch c stop f t₀ k acc).2 ∧
    (∀ s ∈ (cutStretch c stop f t₀ k acc).2.1, s ∈ acc.1 ∨ (t₀ ≤ s.start ∧ s.stop ≤ stop)) ∧
    (∀ b ∈ (cutStretch c stop f t₀ k acc).2.2, b ∈ acc.2 ∨ (t₀ ≤ b.1 ∧ b.2 ≤ stop)) := by
  have hml := minLast_pos c
  apply cutStretch_rec c stop
    (fun f t k a => t₀ ≤ t ∧ t ≤ stop ∧ stop - t < f ∧ AccInv c t a ∧
      (∀ b ∈ a.2, (∃ s ∈ a.1, s.start = b.2) ∨ (b.2 = t ∧ k = 0 ∧ t + 60 * c.minLast ≤ stop)) ∧
      (∀ s ∈ a.1, s ∈ acc.1 ∨ (t₀ ≤ s.start ∧ s.stop ≤ stop)) ∧
      (∀ b ∈ a.2, b ∈ acc.2 ∨ (t₀ ≤ b.1 ∧ b.2 ≤ stop)))
    (fun r => AccInv c stop r.2 ∧ Followed r.2 ∧
      (∀ s ∈ r.2.1, s ∈ acc.1 ∨ (t₀ ≤ s.start ∧ s.stop ≤ stop)) ∧
      (∀ b ∈ r.2.2, b ∈ acc.2 ∨ (t₀ ≤ b.1 ∧ b.2 ≤ stop)))
  · -- exits
    rintro f t k a ⟨_, h2, h3, h4, h5, h6, h7⟩ hx
    refine ⟨h4.mono h2, fun b hb => ?_, h6, h7⟩
    rcases h5 b hb with h | ⟨_, hk, hs⟩
    · exact h
    · exfalso
      rcases hx with hx | hx | ⟨⟨ha, _⟩, hk', _⟩ | ⟨_, _, hx⟩ <;> omega
  · -- a break
    rintro f t k a ⟨h1, h2, h3, h4, h5, h6, h7⟩ ht hon hdue hg
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := h4
    refine ⟨by omega, by omega, by omega, ⟨fun s hs => by have := i1 s hs; omega, ?_, i3, ?_, ?_, i6, ?_⟩,
      ?_, h6, ?_⟩
    · intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact Nat.le_refl _
      · have := i2 b hb; omega
    · exact List.pairwise_cons.2 ⟨fun y hy => i2 y hy, i4⟩
    · intro s hs b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact .inl (i1 s hs)
      · exact i5 s hs b hb
    · intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨rfl, hon.2⟩
      · exact i7 b hb
    · intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact .inr ⟨rfl, rfl, show t + 60 * c.breakMin + 60 * c.minLast ≤ stop by omega⟩
      · rcases h5 b hb with h | ⟨_, hk, _⟩
        · exact .inl h
        · omega
    · intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact .inr ⟨h1, by simp only; omega⟩
      · exact h7 b hb
  · -- a full block
    rintro f t k a ⟨h1, h2, h3, h4, h5, h6, h7⟩ ht hnd hfit
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := h4
    refine ⟨by omega, hfit, by omega, ⟨?_, fun b hb => by have := i2 b hb; omega, ?_, i4, ?_, ?_, i7⟩,
      ?_, ?_, h7⟩
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact Nat.le_refl _
      · have := i1 s hs; omega
    · exact List.pairwise_cons.2 ⟨fun y hy => i1 y hy, i3⟩
    · intro s hs b hb
      rcases List.mem_cons.1 hs with rfl | hs
      · exact .inr (i2 b hb)
      · exact i5 s hs b hb
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact ⟨show t < t + 60 * c.blockMin by omega, fun _ => rfl, (fun h => by cases h)⟩
      · exact i6 s hs
    · intro b hb
      rcases h5 b hb with ⟨s, hs, hse⟩ | ⟨hbt, _, _⟩
      · exact .inl ⟨s, List.mem_cons_of_mem _ hs, hse⟩
      · exact .inl ⟨_, List.mem_cons_self, hbt.symm⟩
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact .inr ⟨h1, hfit⟩
      · exact h6 s hs
  · -- the short block
    rintro f t k a ⟨h1, h2, h3, h4, h5, h6, h7⟩ ht hnd hlt hfit
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := h4
    refine ⟨by omega, Nat.le_refl _, by omega, ⟨?_, fun b hb => by have := i2 b hb; omega, ?_, i4, ?_, ?_, i7⟩,
      ?_, ?_, h7⟩
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact Nat.le_refl _
      · have := i1 s hs; omega
    · exact List.pairwise_cons.2 ⟨fun y hy => i1 y hy, i3⟩
    · intro s hs b hb
      rcases List.mem_cons.1 hs with rfl | hs
      · exact .inr (i2 b hb)
      · exact i5 s hs b hb
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact ⟨show t < stop by omega, (fun h => by cases h), fun _ => ⟨hfit, hlt⟩⟩
      · exact i6 s hs
    · intro b hb
      rcases h5 b hb with ⟨s, hs, hse⟩ | ⟨hbt, _, _⟩
      · exact .inl ⟨s, List.mem_cons_of_mem _ hs, hse⟩
      · exact .inl ⟨_, List.mem_cons_self, hbt.symm⟩
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact .inr ⟨h1, Nat.le_refl _⟩
      · exact h6 s hs
  · exact ⟨Nat.le_refl _, ht, hf, hi, fun b hb => .inl (hfo b hb), fun s hs => .inl hs,
      fun b hb => .inl hb⟩

theorem cutFold_spec (c : CutCfg) (hb : 0 < c.blockMin) (rests FI : List (Nat × Nat)) :
    ∀ (L : List (Nat × Nat)) (acc : Nat × CutAcc) (x : Nat),
      (∀ iv ∈ L, iv ∈ FI ∧ x ≤ iv.1 ∧ iv.1 < iv.2) → L.Pairwise (fun a b => a.2 < b.1) →
      AccInv c x acc.2 → Followed acc.2 →
      (∀ s ∈ acc.2.1, ∃ iv ∈ FI, iv.1 ≤ s.start ∧ s.stop ≤ iv.2) →
      (∀ b ∈ acc.2.2, ∃ iv ∈ FI, iv.1 ≤ b.1 ∧ b.2 ≤ iv.2) →
      ∃ y, AccInv c y (L.foldl (cutStep c rests) acc).2 ∧ Followed (L.foldl (cutStep c rests) acc).2 ∧
        (∀ s ∈ (L.foldl (cutStep c rests) acc).2.1, ∃ iv ∈ FI, iv.1 ≤ s.start ∧ s.stop ≤ iv.2) ∧
        (∀ b ∈ (L.foldl (cutStep c rests) acc).2.2, ∃ iv ∈ FI, iv.1 ≤ b.1 ∧ b.2 ≤ iv.2)
  | [], acc, x, _, _, hi, hfo, hs, hbk => ⟨x, hi, hfo, hs, hbk⟩
  | iv :: L, acc, x, hm, hp, hi, hfo, hs, hbk => by
    obtain ⟨hivF, hx, hiv⟩ := hm iv (by simp)
    have hpc := List.pairwise_cons.1 hp
    rw [List.foldl_cons]
    obtain ⟨j1, j2, j3, j4⟩ := cutStretch_spec c hb iv.2 iv.1 (iv.2 - iv.1 + 1)
      (if restfulEnd c rests iv.1 then 0 else acc.1) acc.2 (Nat.le_of_lt hiv) (by omega)
      (hi.mono hx) hfo
    apply cutFold_spec c hb rests FI L _ iv.2
      (fun u hu => ⟨(hm u (by simp [hu])).1, Nat.le_of_lt (hpc.1 u hu), (hm u (by simp [hu])).2.2⟩)
      hpc.2 j1 j2
    · intro s hsm
      rcases j3 s hsm with h | ⟨h1, h2⟩
      · exact hs s h
      · exact ⟨iv, hivF, h1, h2⟩
    · intro b hbm
      rcases j4 b hbm with h | ⟨h1, h2⟩
      · exact hbk b h
      · exact ⟨iv, hivF, h1, h2⟩

theorem cutSlots_spec (c : CutCfg) (lo hi : Nat) (walls rests : List (Nat × Nat)) (k : Nat) :
    (cutSlots c lo hi walls rests k).slots.Pairwise (fun x y => x.stop ≤ y.start) ∧
    (cutSlots c lo hi walls rests k).breaks.Pairwise (fun x y => x.2 ≤ y.1) ∧
    (∀ s ∈ (cutSlots c lo hi walls rests k).slots, ∀ b ∈ (cutSlots c lo hi walls rests k).breaks,
      s.stop ≤ b.1 ∨ b.2 ≤ s.start) ∧
    (∀ s ∈ (cutSlots c lo hi walls rests k).slots, SlotShape c s ∧ 0 < c.blockMin) ∧
    (∀ b ∈ (cutSlots c lo hi walls rests k).breaks, b.2 = b.1 + 60 * c.breakMin ∧ 0 < c.breakMin) ∧
    (∀ b ∈ (cutSlots c lo hi walls rests k).breaks,
      ∃ s ∈ (cutSlots c lo hi walls rests k).slots, s.start = b.2) ∧
    (∀ s ∈ (cutSlots c lo hi walls rests k).slots,
      ∃ iv ∈ freeIntervals lo hi (walls ++ rests), iv.1 ≤ s.start ∧ s.stop ≤ iv.2) ∧
    (∀ b ∈ (cutSlots c lo hi walls rests k).breaks,
      ∃ iv ∈ freeIntervals lo hi (walls ++ rests), iv.1 ≤ b.1 ∧ b.2 ≤ iv.2) := by
  unfold cutSlots
  by_cases hb : c.blockMin = 0
  · rw [if_pos hb]; simp
  · rw [if_neg hb]
    obtain ⟨f1, f2, _⟩ := freeIntervals_spec lo hi (walls ++ rests)
    obtain ⟨y, ⟨_, _, i3, i4, i5, i6, i7⟩, hfo, hs, hbk⟩ :=
      cutFold_spec c (by omega) rests (freeIntervals lo hi (walls ++ rests))
        (freeIntervals lo hi (walls ++ rests)) (k, ([], [])) lo
        (fun iv hiv => ⟨hiv, (f1 iv hiv).1, (f1 iv hiv).2.1⟩) f2 (AccInv.nil c lo) (by simp [Followed])
        (by simp) (by simp)
    simp only [List.pairwise_reverse, List.mem_reverse]
    exact ⟨i3, i4, i5, fun s hs => ⟨i6 s hs, by omega⟩, i7, hfo, hs, hbk⟩


/-! ### The cut's laws, by name -/

/-- Fork: `if block_min == 0 { return cut; }`. -/
theorem cutSlots_without_a_block_length_is_empty (c : CutCfg) (h : c.blockMin = 0) (lo hi : Nat)
    (walls rests : List (Nat × Nat)) (k : Nat) : cutSlots c lo hi walls rests k = ⟨[], []⟩ := by
  simp [cutSlots, h]

/-- **Every slot lies inside the window**, and is nonempty. -/
theorem cutSlots_inside_the_window (c : CutCfg) (lo hi : Nat) (walls rests : List (Nat × Nat))
    (k : Nat) {s : Slot} (hs : s ∈ (cutSlots c lo hi walls rests k).slots) :
    lo ≤ s.start ∧ s.start < s.stop ∧ s.stop ≤ hi := by
  obtain ⟨_, _, _, h4, _, _, h7, _⟩ := cutSlots_spec c lo hi walls rests k
  obtain ⟨iv, hiv, h1, h2⟩ := h7 s hs
  have := freeIntervals_inside_the_window hiv
  exact ⟨by omega, (h4 s hs).1.1, by omega⟩

/-- Every break lies inside the window, and is nonempty. -/
theorem cutSlots_breaks_inside_the_window (c : CutCfg) (lo hi : Nat) (walls rests : List (Nat × Nat))
    (k : Nat) {b : Nat × Nat} (hb : b ∈ (cutSlots c lo hi walls rests k).breaks) :
    lo ≤ b.1 ∧ b.1 < b.2 ∧ b.2 ≤ hi := by
  obtain ⟨_, _, _, _, h5, _, _, h8⟩ := cutSlots_spec c lo hi walls rests k
  obtain ⟨iv, hiv, h1, h2⟩ := h8 b hb
  have := freeIntervals_inside_the_window hiv
  have := h5 b hb
  exact ⟨by omega, by omega, by omega⟩

/-- **No slot unit is inside a wall or a rest.** -/
theorem cutSlots_avoid_the_walls (c : CutCfg) (lo hi : Nat) (walls rests : List (Nat × Nat))
    (k : Nat) {s : Slot} (hs : s ∈ (cutSlots c lo hi walls rests k).slots)
    {w : Nat × Nat} (hw : w ∈ walls ++ rests) {t : Nat} (h1 : s.start ≤ t) (h2 : t < s.stop) :
    ¬ (w.1 ≤ t ∧ t < w.2) := by
  obtain ⟨_, _, _, _, _, _, h7, _⟩ := cutSlots_spec c lo hi walls rests k
  obtain ⟨iv, hiv, h3, h4⟩ := h7 s hs
  exact ((freeIntervals_are_the_free_units lo hi (walls ++ rests) t).1
    ⟨iv, hiv, by omega, by omega⟩).2.2 w hw

/-- No break unit is inside a wall or a rest. -/
theorem cutSlots_breaks_avoid_the_walls (c : CutCfg) (lo hi : Nat) (walls rests : List (Nat × Nat))
    (k : Nat) {b : Nat × Nat} (hb : b ∈ (cutSlots c lo hi walls rests k).breaks)
    {w : Nat × Nat} (hw : w ∈ walls ++ rests) {t : Nat} (h1 : b.1 ≤ t) (h2 : t < b.2) :
    ¬ (w.1 ≤ t ∧ t < w.2) := by
  obtain ⟨_, _, _, _, _, _, _, h8⟩ := cutSlots_spec c lo hi walls rests k
  obtain ⟨iv, hiv, h3, h4⟩ := h8 b hb
  exact ((freeIntervals_are_the_free_units lo hi (walls ++ rests) t).1
    ⟨iv, hiv, by omega, by omega⟩).2.2 w hw

/-- A full block is exactly `block_min` minutes. -/
theorem cutSlots_block_is_block_min (c : CutCfg) (lo hi : Nat) (walls rests : List (Nat × Nat))
    (k : Nat) {s : Slot} (hs : s ∈ (cutSlots c lo hi walls rests k).slots) (hk : s.kind = .block) :
    s.stop = s.start + 60 * c.blockMin ∧ s.minutes = c.blockMin ∧ 0 < c.blockMin := by
  obtain ⟨_, _, _, h4, _, _, _, _⟩ := cutSlots_spec c lo hi walls rests k
  have h := (h4 s hs).1.2.1 hk
  refine ⟨h, ?_, (h4 s hs).2⟩
  simp only [Slot.minutes, h]
  omega

/-- **A short block is at least `min_last`** (never dropped at `min_last`, never below it)
and shorter than a full block. -/
theorem cutSlots_short_block_is_at_least_min_last (c : CutCfg) (lo hi : Nat)
    (walls rests : List (Nat × Nat)) (k : Nat) {s : Slot}
    (hs : s ∈ (cutSlots c lo hi walls rests k).slots) (hk : s.kind = .short) :
    s.start + 60 * c.minLast ≤ s.stop ∧ s.stop < s.start + 60 * c.blockMin ∧
      c.minLast ≤ s.minutes ∧ s.minutes < c.blockMin := by
  obtain ⟨_, _, _, h4, _, _, _, _⟩ := cutSlots_spec c lo hi walls rests k
  obtain ⟨h1, h2⟩ := (h4 s hs).1.2.2 hk
  refine ⟨h1, h2, ?_, ?_⟩ <;> simp only [Slot.minutes] <;> omega

/-- A break is exactly `break_min` minutes, and breaks happen only with `break_min > 0`. -/
theorem cutSlots_break_is_break_min (c : CutCfg) (lo hi : Nat) (walls rests : List (Nat × Nat))
    (k : Nat) {b : Nat × Nat} (hb : b ∈ (cutSlots c lo hi walls rests k).breaks) :
    b.2 = b.1 + 60 * c.breakMin ∧ 0 < c.breakMin :=
  (cutSlots_spec c lo hi walls rests k).2.2.2.2.1 b hb

/-- The slots come in time order, each ending before the next starts. -/
theorem cutSlots_slots_are_in_order (c : CutCfg) (lo hi : Nat) (walls rests : List (Nat × Nat))
    (k : Nat) : (cutSlots c lo hi walls rests k).slots.Pairwise (fun x y => x.stop ≤ y.start) :=
  (cutSlots_spec c lo hi walls rests k).1

/-- The breaks come in time order. -/
theorem cutSlots_breaks_are_in_order (c : CutCfg) (lo hi : Nat) (walls rests : List (Nat × Nat))
    (k : Nat) : (cutSlots c lo hi walls rests k).breaks.Pairwise (fun x y => x.2 ≤ y.1) :=
  (cutSlots_spec c lo hi walls rests k).2.1

/-- **No slot overlaps a break** (what stage 6's `plan_places_no_block_over_a_break` needs of
the cut). -/
theorem cutSlots_no_slot_overlaps_a_break (c : CutCfg) (lo hi : Nat) (walls rests : List (Nat × Nat))
    (k : Nat) {s : Slot} (hs : s ∈ (cutSlots c lo hi walls rests k).slots)
    {b : Nat × Nat} (hb : b ∈ (cutSlots c lo hi walls rests k).breaks) :
    s.stop ≤ b.1 ∨ b.2 ≤ s.start :=
  (cutSlots_spec c lo hi walls rests k).2.2.1 s hs b hb

/-- **No stretch ends on a break**: every break is followed by a slot starting where it ends
(fork: "only rest when work still follows"). -/
theorem every_break_is_followed_by_a_slot (c : CutCfg) (lo hi : Nat) (walls rests : List (Nat × Nat))
    (k : Nat) {b : Nat × Nat} (hb : b ∈ (cutSlots c lo hi walls rests k).breaks) :
    ∃ s ∈ (cutSlots c lo hi walls rests k).slots, s.start = b.2 :=
  (cutSlots_spec c lo hi walls rests k).2.2.2.2.2.1 b hb

/-! ### The fork's tests, as witnesses (Chicago's 2026 table) -/

/-- A clock time on the §4.3 day, 2026-09-07 in Chicago, as UTC seconds. -/
def onTheSpecDay (c : Field.Clock) : Nat := (Cal.instantOf Cal.chicago 739865 c).sec

/-- **Capacity.rs's documented §4.3 cut** (fork test `cut_slots_on_the_spec_day`): 07:00 to
16:00 around the 12:50–13:50 meeting is 07:00, 08:00, break 09:00, 09:20, 10:20, break 11:20,
11:40 (the 10 minutes before the meeting dropped), 13:50, break 14:50, and 15:10–16:00
short: 410 slot minutes and 60 of breaks. -/
theorem cut_slots_on_the_spec_day :
    cutSlots CutCfg.shipped (onTheSpecDay 420) (onTheSpecDay 960)
        [(onTheSpecDay 770, onTheSpecDay 830)] [] 0
      = ⟨[⟨onTheSpecDay 420, onTheSpecDay 480, .block⟩, ⟨onTheSpecDay 480, onTheSpecDay 540, .block⟩,
          ⟨onTheSpecDay 560, onTheSpecDay 620, .block⟩, ⟨onTheSpecDay 620, onTheSpecDay 680, .block⟩,
          ⟨onTheSpecDay 700, onTheSpecDay 760, .block⟩, ⟨onTheSpecDay 830, onTheSpecDay 890, .block⟩,
          ⟨onTheSpecDay 910, onTheSpecDay 960, .short⟩],
         [(onTheSpecDay 540, onTheSpecDay 560), (onTheSpecDay 680, onTheSpecDay 700),
          (onTheSpecDay 890, onTheSpecDay 910)]⟩ ∧
    (cutSlots CutCfg.shipped (onTheSpecDay 420) (onTheSpecDay 960)
      [(onTheSpecDay 770, onTheSpecDay 830)] [] 0).slotMinutes = 410 ∧
    (cutSlots CutCfg.shipped (onTheSpecDay 420) (onTheSpecDay 960)
      [(onTheSpecDay 770, onTheSpecDay 830)] [] 0).breakMinutes = 60 := by
  decide

/-- Fork test `a_routine_passed_as_a_wall_does_not_pay_off_the_break`: lunch 11:20–11:50 as a
wall is work, so the break due at 11:20 lands at 11:50 and the pre-meeting block is 40
minutes. -/
theorem a_routine_passed_as_a_wall_does_not_pay_off_the_break :
    cutSlots CutCfg.shipped (onTheSpecDay 420) (onTheSpecDay 960)
        [(onTheSpecDay 680, onTheSpecDay 710), (onTheSpecDay 770, onTheSpecDay 830)] [] 0
      = ⟨[⟨onTheSpecDay 420, onTheSpecDay 480, .block⟩, ⟨onTheSpecDay 480, onTheSpecDay 540, .block⟩,
          ⟨onTheSpecDay 560, onTheSpecDay 620, .block⟩, ⟨onTheSpecDay 620, onTheSpecDay 680, .block⟩,
          ⟨onTheSpecDay 730, onTheSpecDay 770, .short⟩, ⟨onTheSpecDay 830, onTheSpecDay 890, .block⟩,
          ⟨onTheSpecDay 910, onTheSpecDay 960, .short⟩],
         [(onTheSpecDay 540, onTheSpecDay 560), (onTheSpecDay 710, onTheSpecDay 730),
          (onTheSpecDay 890, onTheSpecDay 910)]⟩ := by
  decide

/-- Fork test `cut_slots_around_a_placed_routine`: lunch 11:20–11:50 as a **rest** pays off
the break due at 11:20, so a full block follows at 11:50; a 10-minute rest (11:20–11:30) is
shorter than `break_min` and the break still lands, at 11:30. -/
theorem cut_slots_around_a_placed_routine :
    cutSlots CutCfg.shipped (onTheSpecDay 420) (onTheSpecDay 960)
        [(onTheSpecDay 770, onTheSpecDay 830)] [(onTheSpecDay 680, onTheSpecDay 710)] 0
      = ⟨[⟨onTheSpecDay 420, onTheSpecDay 480, .block⟩, ⟨onTheSpecDay 480, onTheSpecDay 540, .block⟩,
          ⟨onTheSpecDay 560, onTheSpecDay 620, .block⟩, ⟨onTheSpecDay 620, onTheSpecDay 680, .block⟩,
          ⟨onTheSpecDay 710, onTheSpecDay 770, .block⟩, ⟨onTheSpecDay 830, onTheSpecDay 890, .block⟩,
          ⟨onTheSpecDay 910, onTheSpecDay 960, .short⟩],
         [(onTheSpecDay 540, onTheSpecDay 560), (onTheSpecDay 890, onTheSpecDay 910)]⟩ ∧
    (onTheSpecDay 690, onTheSpecDay 710) ∈ (cutSlots CutCfg.shipped (onTheSpecDay 420) (onTheSpecDay 960)
        [(onTheSpecDay 770, onTheSpecDay 830)] [(onTheSpecDay 680, onTheSpecDay 690)] 0).breaks := by
  decide

/-- Fork test `cut_slots_from_a_pending_break`: two blocks already worked, 09:00 to 12:00 opens
with the break; the second break due at 11:20 would leave 20 minutes, below `min_last`, so it
is dropped with the tail.  With `min_last_block_min = 20` the tail is a short block, so the
break is placed. -/
theorem cut_slots_from_a_pending_break :
    cutSlots CutCfg.shipped (onTheSpecDay 540) (onTheSpecDay 720) [] [] 2
      = ⟨[⟨onTheSpecDay 560, onTheSpecDay 620, .block⟩, ⟨onTheSpecDay 620, onTheSpecDay 680, .block⟩],
         [(onTheSpecDay 540, onTheSpecDay 560)]⟩ ∧
    cutSlots ⟨60, 20, 2, 20⟩ (onTheSpecDay 540) (onTheSpecDay 720) [] [] 2
      = ⟨[⟨onTheSpecDay 560, onTheSpecDay 620, .block⟩, ⟨onTheSpecDay 620, onTheSpecDay 680, .block⟩,
          ⟨onTheSpecDay 700, onTheSpecDay 720, .short⟩],
         [(onTheSpecDay 540, onTheSpecDay 560), (onTheSpecDay 680, onTheSpecDay 700)]⟩ := by
  decide

/-- Fork test `a_cut_never_ends_on_a_break`: a window to 09:45 leaves 25 minutes after the
break due at 09:00, so neither is placed; to 09:50 the break is placed and a 30-minute short
block, exactly `min_last`, follows it.  (`every_break_is_followed_by_a_slot` is the law.) -/
theorem a_cut_never_ends_on_a_break :
    cutSlots CutCfg.shipped (onTheSpecDay 420) (onTheSpecDay 585) [] [] 0
      = ⟨[⟨onTheSpecDay 420, onTheSpecDay 480, .block⟩, ⟨onTheSpecDay 480, onTheSpecDay 540, .block⟩], []⟩ ∧
    cutSlots CutCfg.shipped (onTheSpecDay 420) (onTheSpecDay 590) [] [] 0
      = ⟨[⟨onTheSpecDay 420, onTheSpecDay 480, .block⟩, ⟨onTheSpecDay 480, onTheSpecDay 540, .block⟩,
          ⟨onTheSpecDay 560, onTheSpecDay 590, .short⟩], [(onTheSpecDay 540, onTheSpecDay 560)]⟩ := by
  decide

/-- Fork test `a_long_wall_extends_the_window_by_its_whole_duration`'s cut: five back-to-back
meetings 14:30–19:30 inside a window to 20:00 leave eight hours, cut into 420 minutes of slots
and 60 of breaks. -/
theorem a_long_wall_leaves_eight_hours_to_cut :
    (cutSlots CutCfg.shipped (onTheSpecDay 420) (onTheSpecDay 1200)
        [(onTheSpecDay 870, onTheSpecDay 930), (onTheSpecDay 930, onTheSpecDay 990),
         (onTheSpecDay 990, onTheSpecDay 1050), (onTheSpecDay 1050, onTheSpecDay 1110),
         (onTheSpecDay 1110, onTheSpecDay 1170)] [] 0).slotMinutes = 420 ∧
    (cutSlots CutCfg.shipped (onTheSpecDay 420) (onTheSpecDay 1200)
        [(onTheSpecDay 870, onTheSpecDay 930), (onTheSpecDay 930, onTheSpecDay 990),
         (onTheSpecDay 990, onTheSpecDay 1050), (onTheSpecDay 1050, onTheSpecDay 1110),
         (onTheSpecDay 1110, onTheSpecDay 1170)] [] 0).breakMinutes = 60 := by
  decide

/-- Fork test `the_window_cap_bounds_a_late_arrival`'s cut: arriving at 20:00, after the cap,
the window is empty and so is the cut. -/
theorem a_late_arrival_cuts_nothing :
    cutSlots CutCfg.shipped (onTheSpecDay 1200) (onTheSpecDay 1200) [] [] 0 = ⟨[], []⟩ := by
  decide

/-- Fork unit test `free_intervals_merge_overlapping_walls`. -/
theorem free_intervals_merge_overlapping_walls :
    freeIntervals (onTheSpecDay 420) (onTheSpecDay 780)
        [(onTheSpecDay 540, onTheSpecDay 600), (onTheSpecDay 570, onTheSpecDay 660)]
      = [(onTheSpecDay 420, onTheSpecDay 540), (onTheSpecDay 660, onTheSpecDay 780)] := by
  decide

/-- **A fall-back day's cut counts real minutes**: on 2026-11-01 in Chicago the clock runs
00:00 to 03:00 in four real hours, and the cut is two blocks, a break, a block and a
40-minute short block (civil minutes would give 180 minutes and a different cut). -/
theorem a_cut_counts_real_minutes_across_the_fall_transition :
    Cal.toDay ⟨2026, 11, 1⟩ = 739920 ∧
    cutSlots CutCfg.shipped (Cal.instantOf Cal.chicago 739920 0).sec
        (Cal.instantOf Cal.chicago 739920 180).sec [] [] 0
      = ⟨[⟨(Cal.instantOf Cal.chicago 739920 0).sec, (Cal.instantOf Cal.chicago 739920 0).sec + 3600, .block⟩,
          ⟨(Cal.instantOf Cal.chicago 739920 0).sec + 3600,
            (Cal.instantOf Cal.chicago 739920 0).sec + 7200, .block⟩,
          ⟨(Cal.instantOf Cal.chicago 739920 0).sec + 8400,
            (Cal.instantOf Cal.chicago 739920 0).sec + 12000, .block⟩,
          ⟨(Cal.instantOf Cal.chicago 739920 0).sec + 12000,
            (Cal.instantOf Cal.chicago 739920 180).sec, .short⟩],
         [((Cal.instantOf Cal.chicago 739920 0).sec + 7200,
           (Cal.instantOf Cal.chicago 739920 0).sec + 8400)]⟩ ∧
    (Cal.instantOf Cal.chicago 739920 180).sec - (Cal.instantOf Cal.chicago 739920 0).sec = 4 * 3600 := by
  decide


/-! ############################################################################
## Energy and the budget limit (stage 5 D10 step L4; design §13.3, owner's D12)

Pulled forward from stage 6 by the owner's D12, beside L2's window and L3's cut.  **Stage 6's
`dayPlan` must reuse `hsw100`, `bucket`, `stepAt`, `priorLevel`, `learnedLevel`, `predictAt`,
`capForLocation` and `energize`, never a second copy** (design §2.3, AGENTS §5.3).  A future
day at one location is `dayHist`: L3's slots, each given its energy, then the budget limit.
L5's `pureDay` is `dayHist` over `windowOn` and `cutSlots … [] 0`.

### The fork point, read by name

`capacity::lookahead`'s future day is `energize(&cut.slots, &EnergyCtx::new(model, cfg,
&Posterior::none(cfg), wake, loc))` then `limit_to_budget(&slots, budget, block_min)`.

1. `EnergyCtx::energy_at(t)` is `cap_for_location(posterior.correct(t, predict(model, cfg,
   &Features::at(t, wake, loc))))` (`futureEnergy`).  On a future day the posterior is
   `Posterior::none`, whose `correct` returns the prediction unchanged (no report, so the
   adjustment is `0.0` and `round` of a whole level is that level), `slept_min` is `None`, so
   the sleep-debt shift is `0`, and `allow_home` is `false`.  Day 0's posterior, shift and
   `--allow-home` are L9's (design §13.5).
2. `Features::at` → `log::hours_since_wake(t, wake)`: `secs =
   t.signed_duration_since(wake).num_seconds()`, then `(secs / 36.0).round() / 100.0`
   (`hsw100` of `Cal.secondsBetween`, **site R11**; `hswAt`).
3. `energy::predict`: `curve_key` is `"lounge"` or `"home"` (`Loc.curve`); the base is
   `model.energy_at(curve, hsw)` (`learnedLevel`: the curve's entry at `bucket(hsw)`, if the
   model has the curve and the curve has the entry), else `prior_level(cfg, curve, hsw)`
   (`priorLevel`: the curve's own prior when the config has it or has no `home` curve, else
   the `home` prior), each through `Config::prior_energy` (`priorEnergy`: the named curve,
   else `lounge`, else the first curve in the map's key order, else `3`) and `StepFn::at`
   (`stepAt`: before the first step its level; else the first step containing the hours;
   else, in a gap, the last step starting at or before them; `3` for an empty curve); then
   `(base − 0).clamp(0, 5)` (`predictAt`).
4. `cap_for_location`: `min(energy, home_max_ci)` at home unless `--allow-home`
   (`capForLocation`).
5. `energize` maps every slot to its energy at its start (`energize`; the progress features it
   also computes are v2's and change no level).
6. `limit_to_budget`: the slots sorted by energy descending, then start ascending (a stable
   sort), each taking `min(minutes, left)` from `left = budget × block_min`, summed per level
   (`limitSlots`).  **`limitSlots_is_limitHist`: that is L1's per-level greedy `limitHist` over
   the slots' histogram `histOf'`**, so the sort is unobservable, and D10-3's "mix after the
   limit" is stated over the fork's own limit.

### Exact against the fork's doubles (design §13.3, D10-11)

* `s / 36.0` is correctly rounded.  A tie `s = 36k + 18` has the exact quotient `k + ½`, and a
  non-tie lies at least `1/36` from `k + ½`, far beyond an ulp for `|s| < 2^40`.  So `round`
  sees the true side, ties go away from zero, and `hsw100` is its value
  (`hsw100_is_round_half_away`, `hsw100_nearest`).
* `bucket` floors `n / 100.0`, correctly rounded, which never reaches the next integer for
  `|n| < 2^40`, because `(100m − 1)/100` is `1/100` below `m`; negative and zero hours are
  bucket `0`, and the index is clamped to `0..11`.
* A range key `num/den` (the decimal text of the TOML key, `den ≤ 10^6` under L6's R10
  bounds) against `n / 100.0`: unequal rationals differ by at least `1/(100·den)`, beyond the
  ulp at these magnitudes, and equal rationals give the same double.  So `hours ≥ from` is
  `100·num ≤ n·den` and `hours < to` is `n·den < 100·num`, exactly (`Step.reached`,
  `Step.before`); input design LOOK's range-key exception (its P8) is not needed.
* Seconds, not minutes: today's wake keeps its seconds, and wake 06:05:40 against a slot at
  07:05:00 is 3,560 s, `hsw` 0.99 and bucket 0, where whole minutes would say 1.00 and bucket 1
  (`the_bucket_reads_seconds`, `the_bucket_reads_seconds_on_the_spec_day`).  Real seconds
  across a DST transition too (`hours_since_wake_count_real_hours_across_the_fall_transition`).

### Data, and what L6 owes it

`Curves` holds `[energy.prior]` as `(key, steps)` pairs in the config's map and `model.json`'s
`energy` likewise, keys as `List Char`.  `stepAt` reads a curve in `StepFn`'s order, sorted by
`from` (fork `StepFn::from_pairs`).  L6's decoder owes that sort, one entry per key, and the
§13.6 bounds (`den ∈ [1, 10^6]`, `num ≤ 48·den`, levels `≤ 5`, `≤ 64` ranges, 12-entry curves
of levels `< 256`, `homeMaxCi ≤ 5`) with their rejection theorems.  It also owes every prior
curve, not only `lounge` and `home`: with neither, `Config::prior_energy` reads the least key
(`curveLeast`; `a_curve_falls_back_as_the_config_does`).  Nothing here crosses the wire yet, so
no smart constructor is owed by this step.

### The recursion rule (D9-21)

Over lists the wire can make large: `energize` is core `map` (`mapTR`); `histOf'` is a `foldl`
per level; `slotMinutesOf` is a `foldl`.  `limitSlots`' fold builds one closure per slot, so
it is **never run**: `@[csimp] limitSlots_eq_limitSlotsFast` compiles it as `limitHist` over
`histOf'` (the step's own theorem).  `stepAt` walks one curve (core `find?` and `reverse`, at most
64 ranges under L6), `curveLookup` and `curveLeast` walk the curve map (`find?`, `foldl`), and
`curveKeyLt` recurses over one key's characters, which L6 bounds.
-/

/-! ### Hours since wake: site R11 -/

/-- **Site R11** (design D10-11): fork `(s / 36.0).round()` for whole seconds `s`, the hours
since wake in hundredths, rounded half away from zero. -/
def hsw100 (s : Int) : Int :=
  if s < 0 then -(((((-s).toNat + 18) / 36 : Nat)) : Int) else (((s.toNat + 18) / 36 : Nat) : Int)

/-- **`hsw100` is `f64::round` of `s / 36`**: the nearest whole number, a tie `s + 18 = 36k`
going up, and odd in `s`, so a negative tie goes down (away from zero). -/
theorem hsw100_is_round_half_away (s : Nat) :
    36 * (hsw100 s).toNat ≤ s + 18 ∧ s + 18 < 36 * ((hsw100 s).toNat + 1) ∧
    hsw100 (-(s : Int)) = -(hsw100 s) := by
  unfold hsw100
  refine ⟨?_, ?_, ?_⟩
  · simp only [show ¬ ((s : Int) < 0) by omega, if_false]
    omega
  · simp only [show ¬ ((s : Int) < 0) by omega, if_false]
    omega
  · by_cases h : s = 0
    · subst h; simp
    · simp only [show (-(s : Int)) < 0 by omega, show ¬ ((s : Int) < 0) by omega, if_true, if_false]
      omega

/-- **The rational specification, both signs**: `|h − s/36| ≤ ½`, and at a tie `h` lies on the
side away from zero.  The two conditions determine `h`. -/
theorem hsw100_nearest (s : Int) :
    -36 ≤ 72 * hsw100 s - 2 * s ∧ 72 * hsw100 s - 2 * s ≤ 36 ∧
      (72 * hsw100 s - 2 * s = 36 → 0 < s) ∧ (72 * hsw100 s - 2 * s = -36 → s < 0) := by
  unfold hsw100
  split <;> omega

/-- Site R11 is monotone (`Arith.lean`'s `*_mono` convention). -/
theorem hsw100_mono {a b : Int} (h : a ≤ b) : hsw100 a ≤ hsw100 b := by
  unfold hsw100
  split <;> split <;> omega

/-- Site R11 is within half a hundredth of the exact hours (`*_withinOne`: 18 of 36 seconds). -/
theorem hsw100_withinOne (s : Int) : -18 ≤ 36 * hsw100 s - s ∧ 36 * hsw100 s - s ≤ 18 := by
  have := hsw100_nearest s
  omega

/-- Fork `energy::bucket`: `floor(hsw)` clamped to `0..HSW_BUCKETS − 1`, `0` for `hsw ≤ 0`, on
the hundredths. -/
def bucket (h : Int) : Fin 12 := if h ≤ 0 then 0 else ⟨min 11 (h.toNat / 100), by omega⟩

theorem bucket_mono {a b : Int} (h : a ≤ b) : (bucket a).val ≤ (bucket b).val := by
  unfold bucket
  split <;> split <;> simp <;> omega

/-- Fork `Features::at`'s `hsw`: `hours_since_wake(t, wake)` in hundredths, from chrono's
`num_seconds` of `t − wake` (`Cal.secondsBetween`, leap seconds and nanoseconds included). -/
def hswAt (wake t : Cal.Instant) : Int := hsw100 (Cal.secondsBetween wake t)

/-! ### The curves: fork `StepFn::at`, `Config::prior_energy`, `prior_level`, `Model::energy_at` -/

/-- One range of a prior curve (fork `Step`): `from = fromNum / fromDen` hours, `to` the same
or `none` for an open `N+` key, and the level. -/
structure Step where
  fromNum : Nat
  fromDen : Nat
  toKey   : Option (Nat × Nat)
  level   : Nat
deriving DecidableEq, Repr

/-- `hours >= s.from` for `hours = h / 100`, cross-multiplied. -/
def Step.reached (h : Int) (s : Step) : Bool := decide (100 * (s.fromNum : Int) ≤ h * (s.fromDen : Int))

/-- `s.to.is_none_or(|to| hours < to)`, cross-multiplied. -/
def Step.before (h : Int) (s : Step) : Bool :=
  match s.toKey with
  | none => true
  | some (n, d) => decide (h * (d : Int) < 100 * (n : Int))

/-- **Fork `StepFn::at`** on hundredths of an hour: `3` for an empty curve; before the first
step, its level; else the first step containing the hours; else (a gap between ranges) the
last step starting at or before them. -/
def stepAt (steps : List Step) (h : Int) : Nat :=
  match steps with
  | [] => 3
  | first :: _ =>
    if first.reached h then
      match steps.find? (fun s => s.reached h && s.before h) with
      | some s => s.level
      | none =>
        match steps.reverse.find? (Step.reached h) with
        | some s => s.level
        | none => first.level
    else first.level

/-- `BTreeMap<String, _>`'s key order: bytes of UTF-8, which is code-point order. -/
def curveKeyLt : List Char → List Char → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a.toNat < b.toNat then true else if a = b then curveKeyLt as bs else false

/-- `map.get(key)`. -/
def curveLookup {α : Type} (m : List (List Char × α)) (k : List Char) : Option α :=
  (m.find? (fun e => e.1 == k)).map (·.2)

def curveLeastStep {α : Type} (acc : Option (List Char × α)) (e : List Char × α) :
    Option (List Char × α) :=
  match acc with
  | none => some e
  | some a => if curveKeyLt e.1 a.1 then some e else some a

/-- `map.values().next()`'s entry: the least key. -/
def curveLeast {α : Type} (m : List (List Char × α)) : Option (List Char × α) :=
  m.foldl curveLeastStep none

def loungeKey : List Char := ['l', 'o', 'u', 'n', 'g', 'e']
def homeKey : List Char := ['h', 'o', 'm', 'e']

/-- **Fork `Config::prior_energy(loc, hsw)`**: the named curve, else `lounge`, else the first
curve in key order, else `3`. -/
def priorEnergy (prior : List (List Char × List Step)) (loc : List Char) (h : Int) : Nat :=
  match curveLookup prior loc with
  | some c => stepAt c h
  | none =>
    match curveLookup prior loungeKey with
    | some c => stepAt c h
    | none =>
      match curveLeast prior with
      | some e => stepAt e.2 h
      | none => 3

/-- **Fork `energy::prior_level(cfg, curve, hsw)`**: the curve's own prior when the config
has it or has no `home` curve, else `home`'s. -/
def priorLevel (prior : List (List Char × List Step)) (curve : List Char) (h : Int) : Nat :=
  if (curveLookup prior curve).isSome || (curveLookup prior homeKey).isNone then priorEnergy prior curve h
  else priorEnergy prior homeKey h

/-- **Fork `Model::energy_at(curve, hsw)`**: the learned level at `bucket(hsw)`, if the model
has the curve and the curve has that entry. -/
def learnedLevel (energy : List (List Char × List Nat)) (curve : List Char) (h : Int) : Option Nat :=
  (curveLookup energy curve).bind (fun c => c[(bucket h).val]?)

/-- The curves `predict` reads: `config.toml`'s `[energy.prior]` and `model.json`'s `energy`,
as data. -/
structure Curves where
  prior  : List (List Char × List Step)
  energy : List (List Char × List Nat)
deriving DecidableEq, Repr

/-- The two locations of a future day (fork `Loc::Lounge`, `Loc::Home`). -/
inductive Loc where
  | lounge
  | home
deriving DecidableEq, Repr

/-- Fork `curve_key`: a lounge day reads `"lounge"`, a home day `"home"`. -/
def Loc.curve : Loc → List Char
  | .lounge => loungeKey
  | .home => homeKey

/-- The key `any` names: fork `Loc::Any`, which `curve_key` reads as `home`. -/
def anyKey : List Char := ['a', 'n', 'y']

/-- **Fork `energy::curve_key(loc, cfg, model)`**: `lounge` and `home` are their own curves,
`any` reads `home`, and any other name (`out`, `zoom`, …) reads its own curve when the model or
the config has one and `home` otherwise.  A future day is always one of the two locations, so
only step L9's day 0 — which reads `state.loc` — can reach the last two branches. -/
def curveKeyOf (c : Curves) (name : List Char) : List Char :=
  if name = loungeKey then loungeKey
  else if name = homeKey then homeKey
  else if name = anyKey then homeKey
  else if (curveLookup c.energy name).isSome || (curveLookup c.prior name).isSome then name
  else homeKey

/-- **Fork `energy::predict`'s base level**: the learned level at the hour's bucket, else the
config prior — **before** the sleep-debt shift and before the `0..5` clamp, because the fork
subtracts the shift from the raw base and clamps once.  The distinction is observable: the wire
bounds a learned curve entry below 256, so a base above 5 with a shift of 1 clamps to 5, where
clamping first would give 4. -/
def baseLevel (c : Curves) (curve : List Char) (h : Int) : Nat :=
  (learnedLevel c.energy curve h).getD (priorLevel c.prior curve h)

/-- **Fork `energy::predict`**: `(base − shift).clamp(0, 5)`, the shift site R10's
(`Arith.roundAway`) and zero unless the night was short. -/
def predictShift (c : Curves) (curve : List Char) (h : Int) (shift : Int) : Fin 6 :=
  ⟨min 5 ((baseLevel c curve h : Int) - shift).toNat, by omega⟩

/-- **Fork `energy::predict` with no sleep-debt shift**: a future day, whose `EnergyCtx` carries
no `slept_min`, so `under_slept` is false and the shift is zero. -/
def predictAt (c : Curves) (curve : List Char) (h : Int) : Fin 6 := predictShift c curve h 0

theorem predictAt_val (c : Curves) (curve : List Char) (h : Int) :
    (predictAt c curve h).val = min 5 (baseLevel c curve h) := by
  simp only [predictAt, predictShift, Int.sub_zero, Int.toNat_natCast]

/-- **Fork `EnergyCtx::cap_for_location`**: `min(energy, home_max_ci)` at home unless
`--allow-home`. -/
def capForLocation (homeMax : Nat) (allowHome : Bool) (loc : Loc) (e : Fin 6) : Fin 6 :=
  match loc, allowHome with
  | .home, false => ⟨min e.val homeMax, by omega⟩
  | _, _ => e

/-- The location the **cap** sees.  Fork `cap_for_location` compares `self.loc == Loc::Home` and
nothing else, so only "is it home" crosses; the curve is chosen separately (`curveKeyOf`), because
`curve_key` reads the location's *name*.  Step L9's day 0 is the only caller with a location that
is neither `lounge` nor `home`. -/
def capLoc (name : List Char) : Loc := if name = homeKey then .home else .lounge

/-- **A future day's slot energy** (fork `EnergyCtx::energy_at` under `EnergyCtx::new` and
`Posterior::none`): predicted from the hours since `wake` at `t`, then the home cap. -/
def futureEnergy (c : Curves) (homeMax : Nat) (loc : Loc) (wake t : Cal.Instant) : Fin 6 :=
  capForLocation homeMax false loc (predictAt c loc.curve (hswAt wake t))

/-- **The home cap holds on every future home day**, and it is the only change to the
prediction there. -/
theorem futureEnergy_home_is_capped (c : Curves) (homeMax : Nat) (wake t : Cal.Instant) :
    (futureEnergy c homeMax .home wake t).val ≤ homeMax ∧
      (futureEnergy c homeMax .home wake t).val = min homeMax (predictAt c homeKey (hswAt wake t)).val := by
  simp only [futureEnergy, capForLocation, Loc.curve]
  omega

/-- A lounge day is not capped. -/
theorem futureEnergy_lounge_is_the_prediction (c : Curves) (homeMax : Nat) (wake t : Cal.Instant) :
    futureEnergy c homeMax .lounge wake t = predictAt c loungeKey (hswAt wake t) := rfl

/-- **Fork `capacity::energize`** on a future day: each slot with its energy at its start. -/
def energize (c : Curves) (homeMax : Nat) (loc : Loc) (wake : Cal.Instant) (slots : List Slot) :
    List (Fin 6 × Slot) :=
  slots.map fun s => (futureEnergy c homeMax loc wake ⟨s.start, 0⟩, s)

/-! ### The budget limit: fork `limit_to_budget`, and why it is L1's `limitHist` -/

def levelStep (l : Fin 6) (a : Nat) (x : Fin 6 × Slot) : Nat := if x.1 = l then a + x.2.minutes else a

/-- **Fork `DayCapacity::from_slots`**: the slots' minutes (`Slot.minutes`) at each level. -/
def histOf' (slots : List (Fin 6 × Slot)) : Hist := fun l => slots.foldl (levelStep l) 0

/-- Fork `limit_to_budget`'s order, `b.energy.cmp(&a.energy).then(a.start.cmp(&b.start))`, as
"`a` may come first". -/
def slotLe (a b : Fin 6 × Slot) : Bool :=
  decide (b.1.val < a.1.val) || (decide (a.1 = b.1) && decide (a.2.start ≤ b.2.start))

/-- One turn of `limit_to_budget`'s loop: `take = min(minutes, left)`, `left −= take`, and
`minutes_at_level[energy] += take` (a slot after `left` reaches `0` takes `0`, as the fork's
`break` does). -/
def takeStep (acc : Nat × Hist) (x : Fin 6 × Slot) : Nat × Hist :=
  (acc.1 - min x.2.minutes acc.1,
    fun l => if l = x.1 then acc.2 l + min x.2.minutes acc.1 else acc.2 l)

/-- **Fork `limit_to_budget(slots, budget, block_min)`** summed per level, with
`budgetMin = budget × block_min`: the slots merge-sorted by energy descending then start
ascending, each taking what is left.  Compiled as `limitSlotsFast` (`@[csimp]`). -/
def limitSlots (budgetMin : Nat) (slots : List (Fin 6 × Slot)) : Hist :=
  ((slots.mergeSort slotLe).foldl takeStep (budgetMin, fun _ => 0)).2

theorem foldl_levelStep (l : Fin 6) : ∀ (L : List (Fin 6 × Slot)) (a : Nat),
    L.foldl (levelStep l) a = a + L.foldl (levelStep l) 0
  | [], a => by simp
  | x :: xs, a => by
    simp only [List.foldl_cons]
    rw [foldl_levelStep l xs (levelStep l a x), foldl_levelStep l xs (levelStep l 0 x)]
    unfold levelStep
    split <;> omega

theorem histOf'_cons (x : Fin 6 × Slot) (xs : List (Fin 6 × Slot)) (l : Fin 6) :
    histOf' (x :: xs) l = (if l = x.1 then histOf' xs l + x.2.minutes else histOf' xs l) := by
  simp only [histOf', List.foldl_cons]
  rw [foldl_levelStep]
  unfold levelStep
  by_cases h : l = x.1
  · subst h; simp; omega
  · simp [h, Ne.symm h]

theorem histOf'_of_below (xs : List (Fin 6 × Slot)) (l : Fin 6) (h : ∀ x ∈ xs, x.1.val < l.val) :
    histOf' xs l = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [histOf'_cons, ih (fun y hy => h y (by simp [hy]))]
    have := h x (by simp)
    have : l ≠ x.1 := fun e => by subst e; omega
    simp [this]

/-- The histogram does not see the slots' order. -/
theorem histOf'_perm {L M : List (Fin 6 × Slot)} (p : L.Perm M) : histOf' L = histOf' M := by
  funext l
  unfold histOf'
  apply p.foldl_eq'
  intro x _ y _ z
  unfold levelStep
  split <;> split <;> omega

theorem topElig_bump (f : Hist) (k : Fin 6) (m : Nat) : ∀ n, n ≤ 6 →
    topElig ⟨0, by decide⟩ (fun l => if l = k then f l + m else f l) n
      = topElig ⟨0, by decide⟩ f n + (if 5 < k.val + n then m else 0) := by
  intro n
  induction n with
  | zero => intro _; have := k.isLt; simp [topElig]; omega
  | succ n ih =>
    intro hn
    have ih' := ih (by omega)
    have hk := k.isLt
    show topElig ⟨0, by decide⟩ (fun l => if l = k then f l + m else f l) n
        + (if 0 ≤ 5 - n then (if stepLevel n = k then f (stepLevel n) + m else f (stepLevel n)) else 0)
      = topElig ⟨0, by decide⟩ f n + (if 0 ≤ 5 - n then f (stepLevel n) else 0)
        + (if 5 < k.val + (n + 1) then m else 0)
    rw [ih']
    simp only [Nat.zero_le, if_true]
    by_cases h : stepLevel n = k
    · have hv : k.val = 5 - n := by rw [← h, stepLevel_val]
      rw [if_pos h]
      split <;> split <;> omega
    · have hv : k.val ≠ 5 - n := fun e => h (Fin.ext (by rw [stepLevel_val]; omega))
      rw [if_neg h]
      split <;> split <;> omega

theorem topElig_of_zero_above (f : Hist) (k : Fin 6) (h : ∀ l : Fin 6, k.val < l.val → f l = 0) :
    ∀ n, n ≤ 5 - k.val → topElig ⟨0, by decide⟩ f n = 0 := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    simp only [topElig, ih (by omega), Nat.zero_le, if_true]
    rw [h (stepLevel n) (by rw [stepLevel_val]; omega)]

/-- L1's limit at one level: what is left after every higher level, capped by the level. -/
theorem limitHist_eq (B : Nat) (h : Hist) (l : Fin 6) :
    limitHist B h l = min (h l) (B - topElig ⟨0, by decide⟩ h (5 - l.val)) := by
  simp only [limitHist, dayTake, Nat.zero_le, if_true, dayLeft_eq_sub]

/-- **The greedy over slots in non-increasing energy** gives each level the minimum of its
minutes and what the higher levels left. -/
theorem greedy_spec : ∀ (L : List (Fin 6 × Slot)) (left : Nat) (h₀ : Hist) (l : Fin 6),
    L.Pairwise (fun a b => b.1.val ≤ a.1.val) →
    (L.foldl takeStep (left, h₀)).2 l
      = h₀ l + min (histOf' L l) (left - topElig ⟨0, by decide⟩ (histOf' L) (5 - l.val))
  | [], left, h₀, l, _ => by simp [histOf']
  | x :: xs, left, h₀, l, hp => by
    have hxs := (List.pairwise_cons.1 hp)
    simp only [List.foldl_cons]
    rw [greedy_spec xs _ _ l hxs.2]
    simp only [takeStep]
    have hb : histOf' (x :: xs) = fun l => if l = x.1 then histOf' xs l + x.2.minutes else histOf' xs l :=
      funext (histOf'_cons x xs)
    rw [hb, topElig_bump _ _ _ _ (by omega)]
    have hz : ∀ l' : Fin 6, x.1.val < l'.val → histOf' xs l' = 0 :=
      fun l' hl' => histOf'_of_below xs l' (fun y hy => by have := hxs.1 y hy; omega)
    have := l.isLt
    have := x.1.isLt
    by_cases hk : l = x.1
    · have h0 := topElig_of_zero_above (histOf' xs) x.1 hz (5 - l.val) (by rw [hk]; exact Nat.le_refl _)
      simp only [if_pos hk, h0]
      split <;> omega
    · have hk' : l.val ≠ x.1.val := fun e => hk (Fin.ext e)
      simp only [hk, if_false]
      by_cases hlt : x.1.val < l.val
      · rw [hz l hlt]; simp
      · split <;> omega

/-- **The fork's per-slot sort is L1's per-level greedy** (design D10-6): sorting by energy
and taking what is left gives exactly `limitHist` over the slots' histogram, whatever the
slots' order and however ties are broken. -/
theorem limitSlots_is_limitHist (budgetMin : Nat) (slots : List (Fin 6 × Slot)) :
    limitSlots budgetMin slots = limitHist budgetMin (histOf' slots) := by
  funext l
  have trans : ∀ a b c : Fin 6 × Slot, slotLe a b = true → slotLe b c = true → slotLe a c = true := by
    intro a b c h1 h2
    simp only [slotLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Fin.ext_iff] at *
    omega
  have total : ∀ a b : Fin 6 × Slot, (slotLe a b || slotLe b a) = true := by
    intro a b
    simp only [slotLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Fin.ext_iff]
    omega
  have hs := List.pairwise_mergeSort trans total slots
  have hs' : (slots.mergeSort slotLe).Pairwise (fun a b => b.1.val ≤ a.1.val) := by
    refine hs.imp ?_
    intro a b h
    simp only [slotLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Fin.ext_iff] at h
    omega
  simp only [limitSlots]
  rw [greedy_spec _ _ _ l hs', histOf'_perm (List.mergeSort_perm slots slotLe), limitHist_eq]
  simp

/-- `limitSlots` as the compiled code runs it: no sort, no closure per slot. -/
def limitSlotsFast (budgetMin : Nat) (slots : List (Fin 6 × Slot)) : Hist :=
  limitHist budgetMin (histOf' slots)

/-- The compiled `limitSlots` is the histogram's greedy (D9-21). -/
@[csimp] theorem limitSlots_eq_limitSlotsFast : @limitSlots = @limitSlotsFast := by
  funext B slots
  exact limitSlots_is_limitHist B slots

/-- Fork `Cut::slot_minutes` over energised slots. -/
def slotMinutesOf (slots : List (Fin 6 × Slot)) : Nat := slots.foldl (fun a x => a + x.2.minutes) 0

theorem sum6_bump (g : Hist) (k : Fin 6) (m : Nat) :
    sum6 (fun l => if l = k then g l + m else g l) = sum6 g + m := by
  obtain ⟨k, hk⟩ := k
  simp only [sum6, Fin.ext_iff]
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := { decide := true }) <;> omega

theorem foldl_add_minutes : ∀ (L : List (Fin 6 × Slot)) (a : Nat),
    L.foldl (fun a x => a + x.2.minutes) a = a + L.foldl (fun a x => a + x.2.minutes) 0
  | [], a => by simp
  | x :: xs, a => by
    simp only [List.foldl_cons]
    rw [foldl_add_minutes xs (a + _), foldl_add_minutes xs (0 + _)]
    omega

/-- The histogram holds every slot minute. -/
theorem sum6_histOf' : ∀ (L : List (Fin 6 × Slot)), sum6 (histOf' L) = slotMinutesOf L
  | [] => rfl
  | x :: xs => by
    have hb : histOf' (x :: xs) = fun l => if l = x.1 then histOf' xs l + x.2.minutes else histOf' xs l :=
      funext (histOf'_cons x xs)
    rw [hb, sum6_bump, sum6_histOf' xs]
    simp only [slotMinutesOf, List.foldl_cons]
    rw [foldl_add_minutes xs (0 + _)]
    omega

/-- **One location's future day** (fork `lookahead`'s loop body after the cut): the slots
energised at `loc`, limited to `budgetMin = budget × block_min` minutes.  L5's mixture reads
two of these, lounge and home. -/
def dayHist (c : Curves) (homeMax : Nat) (loc : Loc) (wake : Cal.Instant) (budgetMin : Nat)
    (slots : List Slot) : Hist :=
  limitSlots budgetMin (energize c homeMax loc wake slots)

theorem dayHist_eq (c : Curves) (homeMax : Nat) (loc : Loc) (wake : Cal.Instant) (budgetMin : Nat)
    (slots : List Slot) :
    dayHist c homeMax loc wake budgetMin slots
      = limitHist budgetMin (histOf' (energize c homeMax loc wake slots)) :=
  limitSlots_is_limitHist _ _

/-- **A future day keeps `min(budget × block_min, the cut's slot minutes)`.** -/
theorem dayHist_keeps_the_min (c : Curves) (homeMax : Nat) (loc : Loc) (wake : Cal.Instant)
    (budgetMin : Nat) (cut : Cut) :
    sum6 (dayHist c homeMax loc wake budgetMin cut.slots) = min budgetMin cut.slotMinutes := by
  rw [dayHist_eq, limitHist_keeps_the_min, sum6_histOf']
  simp only [slotMinutesOf, energize, List.foldl_map, Cut.slotMinutes]

/-- A home day's histogram holds nothing above `home_max_ci`. -/
theorem dayHist_home_is_capped (c : Curves) (homeMax : Nat) (wake : Cal.Instant) (budgetMin : Nat)
    (slots : List Slot) (l : Fin 6) (hl : homeMax < l.val) :
    dayHist c homeMax .home wake budgetMin slots l = 0 := by
  rw [dayHist_eq, limitHist_eq, histOf'_of_below]
  · simp
  · intro x hx
    simp only [energize, List.mem_map] at hx
    obtain ⟨s, _, rfl⟩ := hx
    have := (futureEnergy_home_is_capped c homeMax wake ⟨s.start, 0⟩).1
    show (futureEnergy c homeMax .home wake ⟨s.start, 0⟩).val < l.val
    omega

/-! ### The shipped curves and the fork's fixture model -/

def Step.range (a b level : Nat) : Step := ⟨a, 1, some (b, 1), level⟩
def Step.from (a level : Nat) : Step := ⟨a, 1, none, level⟩

/-- `[energy.prior.lounge]`: `0-1` 4, `1-5` 5, `5-8` 4, `8-10` 3, `10+` 2. -/
def shippedLounge : List Step := [.range 0 1 4, .range 1 5 5, .range 5 8 4, .range 8 10 3, .from 10 2]
/-- `[energy.prior.home]`: `0-1` 3, `1-4` 4, `4-8` 3, `8+` 2. -/
def shippedHome : List Step := [.range 0 1 3, .range 1 4 4, .range 4 8 3, .from 8 2]
/-- The shipped `[energy.prior]`, in key order. -/
def shippedPrior : List (List Char × List Step) := [(homeKey, shippedHome), (loungeKey, shippedLounge)]
/-- `Config::default()` with `Model::default()` (no learned curve). -/
def Curves.shipped : Curves := ⟨shippedPrior, []⟩
/-- `tm-core/tests/fixtures/model.json`'s `energy`. -/
def fixtureEnergy : List (List Char × List Nat) :=
  [(homeKey, [3, 4, 4, 4, 3, 3, 3, 2, 2, 2, 2, 2]), (loungeKey, [4, 5, 5, 5, 5, 4, 4, 4, 3, 3, 2, 2])]
/-- `Config::default()` with the fixture model. -/
def Curves.fixture : Curves := ⟨shippedPrior, fixtureEnergy⟩

/-! ### The fork's tests, as witnesses (Chicago's 2026 table) -/

/-- Rounding at the ties, both signs. -/
theorem hsw100_on_witnesses :
    hsw100 17 = 0 ∧ hsw100 18 = 1 ∧ hsw100 (-17) = 0 ∧ hsw100 (-18) = -1 ∧
    hsw100 3560 = 99 ∧ hsw100 3600 = 100 ∧ hsw100 (-3600) = -100 := by
  decide

/-- **Hours since wake read seconds** (design §15, CRIT 6): 3,560 s is 0.99 h and bucket 0;
3,600 s is 1.00 h and bucket 1. -/
theorem the_bucket_reads_seconds :
    bucket (hsw100 3560) = 0 ∧ bucket (hsw100 3600) = 1 := by
  decide

/-- The same on instants: wake 06:05:40 against a slot at 07:05:00 on the spec day predicts
the lounge's `0-1` level 4; a wake at 06:05:00 predicts `1-5`'s 5. -/
theorem the_bucket_reads_seconds_on_the_spec_day :
    Cal.secondsBetween ⟨onTheSpecDay 365 + 40, 0⟩ ⟨onTheSpecDay 425, 0⟩ = 3560 ∧
    hswAt ⟨onTheSpecDay 365 + 40, 0⟩ ⟨onTheSpecDay 425, 0⟩ = 99 ∧
    (futureEnergy Curves.shipped 3 .lounge ⟨onTheSpecDay 365 + 40, 0⟩ ⟨onTheSpecDay 425, 0⟩).val = 4 ∧
    hswAt ⟨onTheSpecDay 365, 0⟩ ⟨onTheSpecDay 425, 0⟩ = 100 ∧
    (futureEnergy Curves.shipped 3 .lounge ⟨onTheSpecDay 365, 0⟩ ⟨onTheSpecDay 425, 0⟩).val = 5 := by
  decide

/-- Fork test `buckets_clamp` (`energy.rs`), on hundredths. -/
theorem buckets_clamp :
    bucket (-100) = 0 ∧ bucket 0 = 0 ∧ bucket 99 = 0 ∧ bucket 100 = 1 ∧ bucket 1190 = 11 ∧
    bucket 3000 = 11 := by
  decide

/-- Fork test `prior_energy_lookup` (`config.rs`), all 13 assertions. -/
theorem prior_energy_lookup :
    priorEnergy shippedPrior loungeKey 0 = 4 ∧ priorEnergy shippedPrior loungeKey 50 = 4 ∧
    priorEnergy shippedPrior loungeKey 100 = 5 ∧ priorEnergy shippedPrior loungeKey 499 = 5 ∧
    priorEnergy shippedPrior loungeKey 500 = 4 ∧ priorEnergy shippedPrior loungeKey 900 = 3 ∧
    priorEnergy shippedPrior loungeKey 1000 = 2 ∧ priorEnergy shippedPrior loungeKey 3000 = 2 ∧
    priorEnergy shippedPrior loungeKey (-100) = 4 ∧ priorEnergy shippedPrior homeKey 200 = 4 ∧
    priorEnergy shippedPrior homeKey 800 = 2 ∧ priorEnergy shippedPrior ['z', 'o', 'o', 'm'] 200 = 5 ∧
    priorEnergy [] loungeKey 200 = 3 := by
  decide

/-- Fork test `predict_matches_the_prior_tables_at_boundaries` (`energy_model.rs`), all 15. -/
theorem predict_matches_the_prior_tables_at_boundaries :
    ([0, 99, 100, 499, 500, 799, 800, 999, 1000, 2300].map fun h => (predictAt Curves.shipped loungeKey h).val)
      = [4, 4, 5, 5, 4, 4, 3, 3, 2, 2] ∧
    ([99, 100, 399, 400, 800].map fun h => (predictAt Curves.shipped homeKey h).val) = [3, 4, 4, 3, 2] := by
  decide

/-- Fork test `predict_falls_back_to_the_prior` (`energy.rs`): its lounge and home assertions.
Its three `Out`/`Any`/`Named` assertions read `curve_key`'s `"home"`, so they are the home one;
no future day has those locations. -/
theorem predict_falls_back_to_the_prior :
    (predictAt Curves.shipped Loc.lounge.curve 99).val = 4 ∧
    (predictAt Curves.shipped Loc.lounge.curve 100).val = 5 ∧
    (predictAt Curves.shipped Loc.home.curve 200).val = 4 := by
  decide

/-- Fork test `predict_uses_the_learned_curve` (`energy_model.rs`): the learned curve wins,
the bucket floors, and past the last bucket the last learned level holds. -/
theorem predict_uses_the_learned_curve :
    ([99, 100, 500, 800, 1000, 3000].map fun h => (predictAt Curves.fixture loungeKey h).val)
      = [4, 5, 4, 3, 2, 2] ∧
    (predictAt Curves.fixture homeKey 700).val = 2 ∧ (predictAt Curves.shipped homeKey 700).val = 3 := by
  decide

/-- `Config::prior_energy`'s and `prior_level`'s fallbacks, and `StepFn::at` in a gap and
before the first step: a lounge day with only a `home` prior reads it; with neither, the least
key (`cafe` before `zoo`, whatever the list order); fork `unknown_keys_are_errors`' extra
curve. -/
theorem a_curve_falls_back_as_the_config_does :
    priorLevel [(homeKey, shippedHome)] loungeKey 50 = 3 ∧
    priorLevel [(['z', 'o', 'o'], [Step.from 0 1]), (['c', 'a', 'f', 'e'], [Step.from 0 2])] loungeKey 50 = 2 ∧
    priorLevel [(['c', 'a', 'f', 'e'], [Step.range 0 4 3, Step.from 4 2])] ['c', 'a', 'f', 'e'] 500 = 2 ∧
    stepAt [Step.range 0 1 4, Step.range 2 3 5] 150 = 4 ∧ stepAt [Step.range 0 1 4, Step.range 2 3 5] 350 = 5 ∧
    stepAt [Step.range 1 2 4, Step.range 2 3 5] 50 = 4 ∧ stepAt [] 50 = 3 := by
  decide

/-- Fork test `energize_follows_the_prior_curve` (`capacity_slots.rs`): the §4.3 cut, lounge,
wake 06:05. -/
theorem energize_follows_the_prior_curve :
    (energize Curves.shipped 3 .lounge ⟨onTheSpecDay 365, 0⟩
        (cutSlots CutCfg.shipped (onTheSpecDay 420) (onTheSpecDay 960)
          [(onTheSpecDay 770, onTheSpecDay 830)] [] 0).slots).map (·.1.val)
      = [4, 5, 5, 5, 4, 4, 3] := by
  decide

/-- Fork test `energize_applies_the_home_cap_and_the_posterior` (`capacity_slots.rs`): its
lounge, home-cap and `--allow-home` assertions (the posterior and sleep-debt ones are day 0's,
L9). -/
theorem energize_applies_the_home_cap :
    (energize Curves.shipped 3 .lounge ⟨onTheSpecDay 365, 0⟩
        [⟨onTheSpecDay 480, onTheSpecDay 540, .block⟩, ⟨onTheSpecDay 720, onTheSpecDay 780, .block⟩]).map (·.1.val)
      = [5, 4] ∧
    (energize Curves.shipped 3 .home ⟨onTheSpecDay 365, 0⟩
        [⟨onTheSpecDay 480, onTheSpecDay 540, .block⟩, ⟨onTheSpecDay 720, onTheSpecDay 780, .block⟩]).map (·.1.val)
      = [3, 3] ∧
    ([onTheSpecDay 480, onTheSpecDay 720].map fun t =>
        (capForLocation 3 true .home (predictAt Curves.shipped homeKey (hswAt ⟨onTheSpecDay 365, 0⟩ ⟨t, 0⟩))).val)
      = [4, 3] := by
  decide

/-- Fork test `lookahead_follows_the_learned_arrival_and_location`'s Tuesday (2026-09-08,
`capacity_lookahead.rs`), window 07:00–15:00, wake 06:05: the cut holds 420 minutes, more than
the 6-block budget, and the limit keeps three 5s and three 4s. -/
theorem a_future_tuesday_keeps_its_budget :
    Cal.toDay ⟨2026, 9, 8⟩ = 739866 ∧
    slotMinutesOf (energize Curves.shipped 3 .lounge ⟨(Cal.instantOf Cal.chicago 739866 365).sec, 0⟩
        (cutSlots CutCfg.shipped (Cal.instantOf Cal.chicago 739866 420).sec
          (Cal.instantOf Cal.chicago 739866 900).sec [] [] 0).slots) = 420 ∧
    (List.finRange 6).map (limitHist 360 (histOf' (energize Curves.shipped 3 .lounge
        ⟨(Cal.instantOf Cal.chicago 739866 365).sec, 0⟩
        (cutSlots CutCfg.shipped (Cal.instantOf Cal.chicago 739866 420).sec
          (Cal.instantOf Cal.chicago 739866 900).sec [] [] 0).slots)))
      = [0, 0, 0, 0, 180, 180] := by
  decide

/-- Fork test `lookahead_uses_the_learned_energy_curve`'s Sunday (2026-09-13, a home day,
window 10:00–18:00, wake 06:05): the prior gives 4 h at 3 and 2 h at 2 (the week-grid
snapshot's Sunday); the fixture model's learned home curve moves one hour from 3 to 2. -/
theorem the_learned_curve_moves_an_hour_on_sunday :
    Cal.toDay ⟨2026, 9, 13⟩ = 739871 ∧
    (List.finRange 6).map (limitHist 360 (histOf' (energize Curves.shipped 3 .home
        ⟨(Cal.instantOf Cal.chicago 739871 365).sec, 0⟩
        (cutSlots CutCfg.shipped (Cal.instantOf Cal.chicago 739871 600).sec
          (Cal.instantOf Cal.chicago 739871 1080).sec [] [] 0).slots)))
      = [0, 0, 120, 240, 0, 0] ∧
    (List.finRange 6).map (limitHist 360 (histOf' (energize Curves.fixture 3 .home
        ⟨(Cal.instantOf Cal.chicago 739871 365).sec, 0⟩
        (cutSlots CutCfg.shipped (Cal.instantOf Cal.chicago 739871 600).sec
          (Cal.instantOf Cal.chicago 739871 1080).sec [] [] 0).slots)))
      = [0, 0, 180, 180, 0, 0] := by
  decide

/-- **Hours since wake count real hours across a DST transition**: on 2026-11-01 in Chicago a
wake at 00:00 and a slot at 03:30 are 4.5 hours apart, so a home day predicts `4-8`'s 3, where
the civil 3.5 hours would predict `1-4`'s 4. -/
theorem hours_since_wake_count_real_hours_across_the_fall_transition :
    hswAt ⟨(Cal.instantOf Cal.chicago 739920 0).sec, 0⟩ ⟨(Cal.instantOf Cal.chicago 739920 210).sec, 0⟩ = 450 ∧
    (futureEnergy Curves.shipped 5 .home ⟨(Cal.instantOf Cal.chicago 739920 0).sec, 0⟩
        ⟨(Cal.instantOf Cal.chicago 739920 210).sec, 0⟩).val = 3 ∧
    (predictAt Curves.shipped homeKey 350).val = 4 := by
  decide


/-! ############################################################################
## The lookahead (stage 5 D10 step L5; design §13.4)

The day range and the mixture.  Fork-point `capacity::lookahead(walls_by_date, cfg, model,
today_slots, from, days, wake_default)` produces the `List DayCapacity` that step 3's `edf`
consumes; `lookahead` produces it over `capDen` (`lookahead_is_a_lookahead`), and L2–L4's
window, cut, energy and limit are reused, never copied.

### The fork point, read by name

For `i` in `0..days`, `date = from + i`:

1. `i == 0`: `DayCapacity::from_slots(date, today_slots)`, the host's histogram until L9
   (design §13.5): `ofHist today day0`;
2. otherwise, with `wd = date.weekday()`: `arrival = local_dt(tz, date,
   model.expected_arrival_on(wd, cfg))` (`arrivalOn`: learned, else the config's),
   `wake = local_dt(tz, date, wake_default)` (`wakeOn`, `wakeInstantOf`), the walls of the date
   (L2's `wallsOn` over the plan indexed once), `window_and_budget` (L2's `windowOn`,
   `windowMinOf`, `budgetOf`), `cut_slots(arrival, end, walls, cfg)` (L3's `cutSlots … [] 0`),
   `energize` at the location and `limit_to_budget(slots, budget, block_min)` (L4's `dayHist`,
   here `pureDay`, `pureDay_is_dayHist`);
3. the location: `lounge` iff `model.p_lounge_on(wd, cfg) >= 0.5`.  **Under D10 both locations
   are computed and mixed at the weekday's exact weight** (`dayOf`, `mixDay`), after each
   location's budget limit (D10-3).  With every weight forced to the fork's threshold
   (`Input.twin`), a day is the fork's location in `capDen` units
   (`the_twin_forces_the_forks_location`): that is P1 (refined), the one recorded difference.

`wake_default` is `Ctx::wake_time()`: `state.json`'s logged wake, else the replay's `wake` of
today, else **today's** weekday's expected arrival (`Model::wake_or_expected`), a `NaiveTime`
with seconds and nanoseconds.  Every future date reuses that clock.  `wakeInstantOf` is
`local_dt` at second resolution: chrono-tz reads the local clock's whole seconds against its
spans, the nanoseconds ride along, and in a spring-forward gap `naive + Duration::minutes(m)`
keeps the seconds and leaves a leap second (`leapFold`).  Its whole-minute instance is B1's
`Cal.instantOf` (`wakeInstantOf_ofClock`), so no second definition of `local_dt` exists.

### The input (R10, D10-4)

`InputIn` is what the host has: both readings of every weekday table, today's logged wake if
any, **`Today`** (step L9: the `at` instant, `state.json`'s runtime facts, `--allow-home`, and
the two facts the seam carries), the curves, the `[day]` keys and the walls indexed once.
`mkInput?` is the smart constructor.  It refuses `lookaheadTooLong` first (more than 3,660 days,
D10-13), then a weight by weekday (`weight wd e`, L1's `WErr`), then a wake chrono could not hold
(`badWake`), then an `at` stamp whose local date is not `today` (`nowDisagrees`, step L9, where
`badDay0` used to be); each
refusal has its theorem, and every other input is accepted (`mkInput?_accepts`).  The kernel
applies the model-then-config fallbacks and the wake fallback itself
(`mkInput?_weight_is_the_model_then_config`, `mkInput?_arrival_and_wake`).  The curves' and
`[day]`'s own bounds, the zone's, and the wire are L6's (design §13.6).

### Held once (L4's note)

A `Hist` is a function, so every read of a level re-runs what built it, and step 3's pass reads
each day's levels once per deadline.  **`@[csimp] dayOf_eq_dayOfFast`**: the compiled code cuts
each day once, lists each location's energised slots once, and holds its histogram, its limited
day and the mixed numerators as `Six`, six numbers read in constant time.

### The recursion rule (D9-21)

Over lists the wire can make large: the day range is core's `List.range` (`range.loop`, tail
recursive) folded by `foldl` and reversed; each day's walls, window, cut, energy and limit are
L2–L4's, listed in their sections; `Cal.localHits` and `Cal.gapHit` are B1's (a `foldl` over the
zone table; structural fuel 180).  Day 0's own recursions are the same ones (step L9: `day0Cut`
is L3's `cutSlots`, `day0Slots` a `map`, `day0Hist` L4's `histOf'`), plus `latestBefore`, a
`foldl` over the day's energy reports, which the replay bounds.  `weightsOf?` and `Six` recurse
over nothing large.  Proof-only recursions:
`foldl_cons_map`, `daysAscending_range'`.
-/

/-! ### A future day's wake: fork `local_dt(tz, date, wake_default)` at second resolution -/

/-- chrono's `NaiveTime`: seconds of the day and nanoseconds. -/
structure WakeClock where
  sec : Nat
  ns  : Nat
deriving DecidableEq, Repr

/-- chrono's representable times of day (R10): a second below 86,400, a nanosecond count below
two seconds, at or above one second only on second 59 of a minute (a leap second). -/
def WakeClock.wf (w : WakeClock) : Bool :=
  decide (w.sec < 86400) && decide (w.ns < 2000000000) && (decide (w.ns < 1000000000) || w.sec % 60 == 59)

/-- A whole-minute clock as a time of day (fork `wake_or_expected`'s fallback, an expected
arrival). -/
def WakeClock.ofClock (c : Field.Clock) : WakeClock := ⟨c.val * 60, 0⟩

theorem WakeClock.ofClock_wf (c : Field.Clock) : (WakeClock.ofClock c).wf = true := by
  have := c.isLt
  simp only [WakeClock.wf, WakeClock.ofClock, Bool.and_eq_true]
  exact ⟨⟨decide_eq_true (by omega), rfl⟩, rfl⟩

/-- chrono's `NaiveDateTime + Duration::minutes(m)`, `m ≥ 1`, on the nanoseconds: a leap
second is left, the minutes land on the next whole second's count. -/
def leapFold (ns : Nat) : Nat := if 1000000000 ≤ ns then ns - 1000000000 else ns

/-- **Fork `local_dt(tz, date, time)` for a time with seconds and nanoseconds**, as
`capacity::lookahead` builds `wake = local_dt(tz, date, wake_default)` for every future date:
chrono-tz reads the local clock's whole seconds against its spans; `Single` gives that instant
and `Ambiguous` the earliest, each with the time's nanoseconds; `None` tries the local time plus
1 to 180 minutes (the seconds kept, a leap second left); failing that, the local time read as
UTC.  `Cal.instantOf` is its whole-minute instance (`wakeInstantOf_ofClock`). -/
def wakeInstantOf (z : Cal.Tz) (d : Nat) (w : WakeClock) : Cal.Instant :=
  match Cal.localHits z (d * 86400 + w.sec) with
  | s :: _ => ⟨s, w.ns⟩
  | [] =>
      match Cal.gapHit z (d * 86400 + w.sec) 180 1 with
      | some s => ⟨s, leapFold w.ns⟩
      | none => ⟨d * 86400 + w.sec, w.ns⟩

theorem wakeInstantOf_ofClock (z : Cal.Tz) (d : Nat) (c : Field.Clock) :
    wakeInstantOf z d (WakeClock.ofClock c) = Cal.instantOf z d c := by
  simp only [wakeInstantOf, WakeClock.ofClock, Cal.instantOf, leapFold]
  rfl

/-- **`wakeInstantOf` is `local_dt` on an unambiguous time**: when exactly one instant has the
local second, the wake is that second with the time's nanoseconds. -/
theorem wakeInstantOf_on_an_unambiguous_time (z : Cal.Tz) (d : Nat) (w : WakeClock) (t : Cal.Instant)
    (hu : (Cal.localHits z (d * 86400 + w.sec)).length = 1) (hpos : 0 < d * 86400 + w.sec)
    (hns : t.ns = w.ns) (ht : Cal.localSec z t = d * 86400 + w.sec) :
    wakeInstantOf z d w = t := by
  have hmem := Cal.mem_localHits_of_localSec z t _ hpos ht
  unfold wakeInstantOf
  cases hh : Cal.localHits z (d * 86400 + w.sec) with
  | nil => rw [hh] at hu; simp at hu
  | cons s rest =>
    rw [hh] at hu hmem
    have hr : rest = [] := by simpa using hu
    subst hr
    simp only [List.mem_singleton] at hmem
    cases t
    simp_all

/-! ### The input: fork `capacity::lookahead`'s arguments, with the kernel's fallbacks -/

/-- The lookahead's R10 bound (D10-13): at most 3,660 days, else `lookaheadTooLong`. -/
def maxLookaheadDays : Nat := 3660

/-! ### Today's posterior, its sleep debt, and what else today is (step L9; design §13.5)

Day 0 is not a histogram the host hands in any more (gap 93).  Everything a **future** day reads
is a table; everything **today** reads that a future day does not is here: the instant the
request was made, `state.json`'s window, budget, arrival, date and location, `--allow-home`, and
the two facts the kernel derives from its own replay through D24's seam — last night's minutes
and today's energy reports.

Fork `Ctx::today_slots(allow_home)` is the whole of it, and `DayCapacity::from_slots` is what it
becomes.  Note what is *not* here: `blocks_done` and `since_break_min` reach `Features` and no
further — `energy::predict` reads `loc`, `hsw` and `slept_min` only (they are §8.5's v2 features),
so they cannot move a slot's energy and day 0 does not carry them.  Nor is there a budget limit:
`from_slots` sums the energised slots and `limit_to_budget` is a *future* day's (`pureDay`). -/

/-- One of today's energy reports as the posterior reads it (fork `Report`): the instant, what was
predicted then, and what was reported.  `Posterior::from_observations` maps the day's
`EnergyObs` to exactly this triple. -/
structure Report where
  t    : Cal.Instant
  pred : Nat
  rep  : Nat
deriving DecidableEq, Repr

/-- **Fork `Posterior::latest_before(t)`**: `reports.iter().rev().find(|r| r.t <= t)` over the
**stably sorted** reports — the newest report at or before `t`, and the last of the day's own
order among any that share that instant.  Written as one left fold, which needs no sort: it keeps
the last reading that is both at or before `t` and no earlier than the one held, which is that
element for a list in any order (fork `sort_by_key` is stable, so on the sorted list the two
agree; the fold does not depend on the list arriving sorted). -/
def keepsIt (t : Cal.Instant) (acc : Option Report) (r : Report) : Bool :=
  decide (r.t ≤ t) && (match acc with | none => true | some a => decide (a.t ≤ r.t))

theorem keepsIt_le {t : Cal.Instant} {acc : Option Report} {r : Report}
    (h : keepsIt t acc r = true) : r.t ≤ t := by
  unfold keepsIt at h
  rw [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

def latestStep (t : Cal.Instant) (acc : Option Report) (r : Report) : Option Report :=
  if keepsIt t acc r then some r else acc

def latestBefore (l : List Report) (t : Cal.Instant) : Option Report :=
  l.foldl (latestStep t) none

theorem latestBefore_nil (t : Cal.Instant) : latestBefore [] t = none := rfl

/-- The fold keeps a report of the list, at or before `t`, or what it was handed. -/
theorem latestBefore_go : ∀ (l : List Report) (t : Cal.Instant) (acc : Option Report) (r : Report),
    l.foldl (latestStep t) acc = some r → (r ∈ l ∧ r.t ≤ t) ∨ acc = some r
  | [], _, _, _, h => Or.inr h
  | x :: xs, t, acc, r, h => by
    rcases latestBefore_go xs t (latestStep t acc x) r h with h' | h'
    · exact Or.inl ⟨List.mem_cons_of_mem _ h'.1, h'.2⟩
    · unfold latestStep at h'
      by_cases hc : keepsIt t acc x = true
      · rw [if_pos hc] at h'
        have hx : x = r := Option.some.inj h'
        subst hx
        exact Or.inl ⟨List.mem_cons_self .., keepsIt_le hc⟩
      · rw [if_neg hc] at h'
        exact Or.inr h'

/-- What the fold keeps is one of the reports, at or before `t`. -/
theorem latestBefore_sound (l : List Report) (t : Cal.Instant) (r : Report)
    (h : latestBefore l t = some r) : r ∈ l ∧ r.t ≤ t := by
  rcases latestBefore_go l t none r h with h' | h'
  · exact h'
  · cases h'

/-- No report at or before `t` and the fold keeps nothing. -/
theorem latestBefore_none_of_all_after {l : List Report} {t : Cal.Instant}
    (h : ∀ r ∈ l, ¬ r.t ≤ t) : latestBefore l t = none := by
  rcases hl : latestBefore l t with _ | r
  · rfl
  · exact absurd (latestBefore_sound l t r hl).2 (h r (latestBefore_sound l t r hl).1)

/-- §16's `[energy] posterior_full_hours` and `posterior_zero_hours`, as the exact decimals their
file writes.  **Nothing converts them to minutes.**  §13.5 says day 0's posterior goes through
`Arith.ramp` "over minutes", and the repo says otherwise: `posterior_weight` compares
`hours = seconds/3600` against two `f64` hours, and both comparisons are exact on the pair, so
the weight is taken over the common unit `1/(3600·fd·zd)` hours — an exact scaling with nothing
rounded, and therefore no rounding site to add. -/
structure PostCfg where
  full : Arith.Pos
  zero : Arith.Pos

/-- **Fork `posterior_weight(hours, full_hours, zero_hours)`** for a report `dt` **seconds** old,
exactly: `1` up to `full`, falling linearly to `0` at `zero`, and `0` at or past it.  The three
values are put over one exact unit and the ramp is then `Arith.ramp`'s — §8.5's one definition
(AGENTS §5.3).

**The order of the fork's tests is load-bearing** and this was found by measurement, not by
reading: `hours <= full_hours` is tested **before** `zero_hours <= full_hours`, so a report inside
`full` weighs one *even when the pair is degenerate* (`zero ≤ full`).  Taking the degenerate case
first — which this definition did until the L9 parity run reached `full = 3, zero = 2` — weighs
such a report nothing, and a whole day's levels move.  `hours < 0` is the fork's first test and is
unreachable here: `latestBefore` only ever returns a report at or before `t`. -/
def weightAt (c : PostCfg) (dt : Nat) : Arith.Pos :=
  let fu := 3600 * c.full.val.num * c.zero.val.den
  let zu := 3600 * c.zero.val.num * c.full.val.den
  let du := dt * (c.full.val.den * c.zero.val.den)
  if du ≤ fu then Arith.posOfNat 1
  else if h : fu < zu then Arith.ramp fu zu h du
  else Arith.mkPos 0 1 (by omega)

/-- A report no older than `posterior_full_hours` weighs one — whatever `zero` is. -/
theorem weightAt_full (c : PostCfg) {dt : Nat}
    (h : dt * (c.full.val.den * c.zero.val.den) ≤ 3600 * c.full.val.num * c.zero.val.den) :
    Arith.Q.equiv (weightAt c dt).val (Arith.ofNat 1) = true := by
  simp only [weightAt, if_pos h]
  rfl

/-- A report **past** `posterior_full_hours` and at or past `posterior_zero_hours` weighs nothing,
and so does one past `full` under a degenerate pair. -/
theorem weightAt_zero (c : PostCfg) {dt : Nat}
    (hf : 3600 * c.full.val.num * c.zero.val.den < dt * (c.full.val.den * c.zero.val.den))
    (hz : 3600 * c.zero.val.num * c.full.val.den ≤ dt * (c.full.val.den * c.zero.val.den)) :
    (weightAt c dt).val.num = 0 := by
  simp only [weightAt, if_neg (by omega : ¬ dt * (c.full.val.den * c.zero.val.den) ≤ 3600 * c.full.val.num * c.zero.val.den)]
  split
  · exact Arith.ramp_zero _ _ _ hz
  · rfl

/-- **A staler report weighs less** (fork's falling ramp; `Arith.ramp_antitone`). -/
theorem weightAt_antitone (c : PostCfg) {d₁ d₂ : Nat} (h : d₁ ≤ d₂) :
    Arith.Q.le (weightAt c d₂).val (weightAt c d₁).val = true := by
  have hm : d₁ * (c.full.val.den * c.zero.val.den) ≤ d₂ * (c.full.val.den * c.zero.val.den) :=
    Nat.mul_le_mul_right _ h
  simp only [weightAt]
  by_cases h2 : d₂ * (c.full.val.den * c.zero.val.den) ≤ 3600 * c.full.val.num * c.zero.val.den
  · rw [if_pos h2, if_pos (by omega)]
    exact Arith.Q.le_refl _
  · rw [if_neg h2]
    by_cases h1 : d₁ * (c.full.val.den * c.zero.val.den) ≤ 3600 * c.full.val.num * c.zero.val.den
    · rw [if_pos h1]
      split
      · rename_i hfz
        have hd : (Arith.ofNat 1).defined = true := by decide
        exact Arith.Q.le_trans hd (Arith.ramp_le_one _ _ hfz _) (Arith.Q.le_refl _)
      · exact Arith.Q.le_of (by simp [Arith.mkPos, Arith.posOfNat])
    · rw [if_neg h1]
      split
      · exact Arith.ramp_antitone _ _ _ hm
      · exact Arith.Q.le_refl _

/-- **Fork `Posterior::correct(t, pred)`**: the prediction at `t` plus `δ·w` of the newest report
at or before `t`, rounded and clamped to `0..5` — site R5's `Arith.energyAfter`.  With no report
the adjustment is `0` and the answer is the prediction (`Arith.energyAfter_no_report`).

`f64::round` is half **away from zero** where `energyAfter` is half **up**; the two rules differ
only strictly below zero, and there the fork's own `clamp(0.0, 5.0)` answers `0` while
`energyAfter`'s non-positive branch answers `0` as well
(`the_posterior_rounds_a_half_the_way_the_fork_does`). -/
def correctAt (c : PostCfg) (l : List Report) (t : Cal.Instant) (pred : Nat) : Fin 6 :=
  match latestBefore l t with
  | none => Arith.energyAfter pred 0 (Arith.posOfNat 1)
  | some r => Arith.energyAfter pred ((r.rep : Int) - (r.pred : Int))
      (weightAt c (Cal.secondsBetween r.t t).toNat)

/-- **No report, no correction.** -/
theorem correctAt_without_a_report (c : PostCfg) {l : List Report} {t : Cal.Instant}
    (h : latestBefore l t = none) (pred : Nat) : (correctAt c l t pred).val = min 5 pred := by
  simp only [correctAt, h]
  exact Arith.energyAfter_no_report _ _

/-- **The half that decides the two rounding rules agree.**  A corrected value of exactly `−0.5`
is `round`ed to `−1` by the fork and clamped to `0`; `+0.5` is rounded to `1` by both.  These are
the two points at which half-away-from-zero and half-up could part company on this domain, and
they do not. -/
theorem the_posterior_rounds_a_half_the_way_the_fork_does :
    (Arith.energyAfter 1 (-3) (Arith.mkPos 1 2 (by omega))).val = 0 ∧
    (Arith.energyAfter 2 (-3) (Arith.mkPos 1 2 (by omega))).val = 1 ∧
    (Arith.energyAfter 3 (-3) (Arith.mkPos 1 2 (by omega))).val = 2 := by decide

/-- §16's `[energy.sleep_debt]` and `.tm/model.json`'s fitted `sleep_debt_shift`: the host sends
both shifts and the kernel picks (D10-4), beside the hours a night must reach not to count as
debt. -/
structure SleepCfg where
  shiftModel  : Option Arith.Signed
  shiftConfig : Arith.Signed
  underHours  : Arith.Pos

/-- **Fork `Model::sleep_shift(cfg)`**: the model's shift, else the config's. -/
def SleepCfg.shift (s : SleepCfg) : Arith.Signed := s.shiftModel.getD s.shiftConfig

/-- **Fork `Features::under_slept(cfg)`**: `slept_min / 60 < under_hours`.  A **comparison**, so
it cross-multiplies and nothing rounds (`Arith.lean`'s note).  No sleep reading is no debt. -/
def SleepCfg.underSlept (s : SleepCfg) : Option Nat → Bool
  | none => false
  | some m => Arith.Q.lt ⟨m, 60⟩ s.underHours.val

/-- **Fork `energy::predict`'s shift**: site R10's rounding of the chosen shift under debt, and
nothing otherwise. -/
def SleepCfg.shiftOf (s : SleepCfg) (slept : Option Nat) : Int :=
  if s.underSlept slept then Arith.roundAway s.shift else 0

theorem SleepCfg.shiftOf_without_sleep (s : SleepCfg) : s.shiftOf none = 0 := rfl

/-- **What today is, beside the tables every day reads** (step L9; design §13.5).  `now` is the
request's own instant — the `at` stamp, whose local date `mkInput?` checks against `now`
(`nowDisagrees`); `date`, `window`, `budget`, `arrival` and `loc` are `state.json`'s, which is
the host's file (AGENTS §8.4, "runtime state that lives in Rust"); `allowHome` is
`tm plan --allow-home`; and `slept` and `reports` are the kernel's own, read off this call's
replay through D24's seam. -/
structure Today where
  now       : Cal.Instant
  date      : Option Nat
  window    : Option (Field.Clock × Field.Clock)
  budget    : Option Nat
  arrival   : Option Field.Clock
  loc       : List Char
  allowHome : Bool
  slept     : Option Nat
  reports   : List Report
  post      : PostCfg
  sleep     : SleepCfg

/-- **Fork `Ctx::window`'s stored branch**: `state.window` counts only with `state.budget` beside
it and only when `state.date` is today — a window stored on an earlier day belongs to that day. -/
def Today.storedWindow (T : Today) (today : Nat) : Option (Field.Clock × Field.Clock) :=
  if T.date = some today then
    (match T.window, T.budget with
     | some w, some _ => some w
     | _, _ => none)
  else none

/-- **Fork `Ctx::window`'s formula branch**: `state.arrival` when it is today's, else `now`. -/
def Today.arrivalSec (T : Today) (today : Nat) (z : Cal.Tz) : Nat :=
  if T.date = some today then
    (match T.arrival with
     | some c => (Cal.instantOf z today c).sec
     | none => T.now.sec)
  else T.now.sec

/-- The `[day]` keys the window, the budget and the cut read.  L6 decodes it with §13.6's
bounds (`badDay <key>`); `CutCfg` is L3's, contained, not copied. -/
structure DayCfg where
  cut         : CutCfg
  windowHours : Pos
  windowCap   : Field.Clock
  budgetRatio : Pos

/-- What the host hands the lookahead, raw: both readings of every weekday table (D10-4: the
kernel picks, AGENTS §5.6), today's logged wake if the day has one, and the plan's walls indexed
once (`wallIndex`). -/
structure InputIn where
  today     : Nat
  days      : Nat
  today0    : Today
  pModel    : Cal.Weekday → Option (Nat × Nat)
  pConfig   : Cal.Weekday → Nat × Nat
  arrModel  : Cal.Weekday → Option Field.Clock
  arrConfig : Cal.Weekday → Field.Clock
  wake      : Option WakeClock
  curves    : Curves
  homeMax   : Nat
  day       : DayCfg
  tz        : Cal.Tz
  walls     : List WallIx

/-- The lookahead's input, decoded (`mkInput?`). -/
structure Input where
  today   : Nat
  days    : Nat
  today0  : Today
  weight  : Cal.Weekday → Weight
  arrival : Cal.Weekday → Field.Clock
  wake    : WakeClock
  curves  : Curves
  homeMax : Nat
  day     : DayCfg
  tz      : Cal.Tz
  walls   : List WallIx

/-- Why the capacity input is refused, by name (AGENTS §5.7). -/
inductive CapErr where
  | lookaheadTooLong
  | weight (wd : Cal.Weekday) (e : WErr)
  | badWake
  | nowDisagrees
deriving DecidableEq, Repr

/-- **Fork `Model::p_lounge_on(wd, cfg)`**: the learned pair, else the config's, decoded
exactly or refused with the weekday's name. -/
def weightOn? (x : InputIn) (wd : Cal.Weekday) : Except CapErr Weight :=
  match mkWeight? ((x.pModel wd).getD (x.pConfig wd)).1 ((x.pModel wd).getD (x.pConfig wd)).2 with
  | .ok w => .ok w
  | .error e => .error (.weight wd e)

/-- The seven weights, Monday first; the first refusal is returned. -/
def weightsOf? (x : InputIn) : Except CapErr (Cal.Weekday → Weight) :=
  match weightOn? x .monday, weightOn? x .tuesday, weightOn? x .wednesday, weightOn? x .thursday,
      weightOn? x .friday, weightOn? x .saturday, weightOn? x .sunday with
  | .ok mo, .ok tu, .ok we, .ok th, .ok fr, .ok sa, .ok su =>
    .ok fun
      | .monday => mo | .tuesday => tu | .wednesday => we | .thursday => th
      | .friday => fr | .saturday => sa | .sunday => su
  | .error e, _, _, _, _, _, _ => .error e
  | _, .error e, _, _, _, _, _ => .error e
  | _, _, .error e, _, _, _, _ => .error e
  | _, _, _, .error e, _, _, _ => .error e
  | _, _, _, _, .error e, _, _ => .error e
  | _, _, _, _, _, .error e, _ => .error e
  | _, _, _, _, _, _, .error e => .error e

/-- **Fork `Model::expected_arrival_on(wd, cfg)`**: learned, else the config's. -/
def arrivalOn (x : InputIn) (wd : Cal.Weekday) : Field.Clock := (x.arrModel wd).getD (x.arrConfig wd)

/-- **Fork `Ctx::wake_time()`** (`Model::wake_or_expected(logged, today.weekday())`): the
logged wake, else today's weekday's expected arrival.  Every future day reuses it. -/
def wakeOf (x : InputIn) : WakeClock := x.wake.getD (WakeClock.ofClock (arrivalOn x (Cal.weekdayOf x.today)))

/-- **The `at` stamp names today** (step L9; design §13.5): `Ctx::now_tz` and `Ctx::today` are
one instant read two ways, so a request whose `at` falls on another local date would cut day 0
from an instant outside the day it is planning.  R10: it is refused by name, never adjusted. -/
def nowAgrees (x : InputIn) : Bool := Cal.localDate x.tz x.today0.now == x.today

/-- **The smart constructor** (R10).  Checked in the order `lookaheadTooLong`, the weights
Monday first, `badWake`, `nowDisagrees`. -/
def mkInput? (x : InputIn) : Except CapErr Input :=
  if maxLookaheadDays < x.days then .error .lookaheadTooLong else
  match weightsOf? x with
  | .error e => .error e
  | .ok ws =>
    if (wakeOf x).wf = false then .error .badWake
    else if nowAgrees x = false then .error .nowDisagrees
    else .ok ⟨x.today, x.days, x.today0, ws, arrivalOn x, wakeOf x, x.curves, x.homeMax, x.day,
      x.tz, x.walls⟩

theorem mkInput?_refuses_too_many_days (x : Look.InputIn) (h : Look.maxLookaheadDays < x.days) :
    Look.mkInput? x = .error .lookaheadTooLong := by
  simp [mkInput?, h]

/-- **R10 at L5's constructor** (stage 6 D24): every accepted input's wake is a clock chrono can
represent.  `mkInput?` is the only constructor of an `Input`, so a wake the `NaiveTime` bound
rejects — off the wire, or derived from the kernel's own replay through D24's seam
(`CapWire.wakeClockOf`) — never reaches a day's hours-since-wake: it is refused `badWake` by name
(AGENTS §5.7), never rounded into a representable one. -/
theorem mkInput?_ok_wake_wf (x : Look.InputIn) (I : Look.Input) (h : Look.mkInput? x = .ok I) :
    I.wake.wf = true := by
  unfold mkInput? at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hw _
  cases h
  simpa using hw

/-! ### One future day: window, cut, energy and limit at each location, then the mixture -/

/-- Fork `limit_to_budget`'s `budget.saturating_mul(block_min)`, `budget` from `budget_blocks`. -/
def budgetMinOf (c : DayCfg) : Nat := budgetOf c.windowHours c.cut.blockMin c.budgetRatio * c.cut.blockMin

/-- Fork `lookahead`'s day `d` up to the cut: the arrival on `d`'s weekday through `local_dt`,
`window_and_budget` over the walls of `d`, and `cut_slots(arrival, end, walls, cfg)`. -/
def dayCut (I : Input) (d : Nat) : Cut :=
  let walls := wallsOn I.walls d
  let w := windowOn I.tz d (I.arrival (Cal.weekdayOf d)) I.day.windowCap (windowMinOf I.day.windowHours) walls
  cutSlots I.day.cut w.1 w.2 walls [] 0

/-- Fork `local_dt(tz, date, wake_default)`: today's wake clock on day `d`. -/
def wakeOn (I : Input) (d : Nat) : Cal.Instant := wakeInstantOf I.tz d I.wake

/-- **One location's future day** (design §13.4): the window, the cut, each slot's energy at
`loc`, and the budget limit.  Written as the limit over the energised histogram, which reduces
under `decide`; it is L4's `dayHist`, the fork's per-slot sort, by `pureDay_is_dayHist`. -/
def pureDay (I : Input) (loc : Loc) (d : Nat) : Hist :=
  limitHist (budgetMinOf I.day) (histOf' (energize I.curves I.homeMax loc (wakeOn I d) (dayCut I d).slots))

/-- **`pureDay` is L4's `dayHist`**: fork `lookahead`'s loop body after the cut,
`limit_to_budget(energize(cut.slots, ctx), budget, block_min)`. -/
theorem pureDay_is_dayHist (I : Input) (loc : Loc) (d : Nat) :
    pureDay I loc d = dayHist I.curves I.homeMax loc (wakeOn I d) (budgetMinOf I.day) (dayCut I d).slots :=
  (dayHist_eq _ _ _ _ _ _).symm

/-! ### Day 0: today, derived in the kernel (step L9, gap 93; design §13.5) -/

/-- **Fork `Ctx::window`**: the window `tm arrive` stored *for today*, else §8.1's formula from
the stored arrival (or `now`) over today's walls — the same `windowFrom` every future day uses.
The budget is not read: day 0 has no budget limit (`from_slots` sums the slots), and
`state.budget` only decides whether the stored window counts at all. -/
def day0Window (I : Input) : Nat × Nat :=
  match I.today0.storedWindow I.today with
  | some w => ((Cal.instantOf I.tz I.today w.1).sec, (Cal.instantOf I.tz I.today w.2).sec)
  | none =>
    windowFrom I.tz (I.today0.arrivalSec I.today I.tz) (windowMinOf I.day.windowHours)
      I.day.windowCap (wallsOn I.walls I.today)

/-- **Fork `Ctx::today_slots`'s cut**: from `max(window.start, now)` to the window's end, around
today's walls, with no placed rest and no block worked since a break — and nothing at all when
the window has already ended (`if end <= from { return Vec::new() }`). -/
def day0Cut (I : Input) : Cut :=
  let w := day0Window I
  let lo := max w.1 I.today0.now.sec
  if w.2 ≤ lo then ⟨[], []⟩ else cutSlots I.day.cut lo w.2 (wallsOn I.walls I.today) [] 0

theorem day0Cut_eq (I : Input) :
    day0Cut I =
      (if (day0Window I).2 ≤ max (day0Window I).1 I.today0.now.sec then ⟨[], []⟩
       else cutSlots I.day.cut (max (day0Window I).1 I.today0.now.sec) (day0Window I).2
         (wallsOn I.walls I.today) [] 0) := rfl

/-- **Fork `EnergyCtx::energy_at` on today**: the prediction at the hours since wake, less the
sleep-debt shift (site R10), corrected by today's posterior (site R5), then the home cap.  The
order is the fork's and it is load-bearing — cheat 118 is the posterior applied *after* the
cap. -/
def todayEnergy (I : Input) (t : Cal.Instant) : Fin 6 :=
  capForLocation I.homeMax I.today0.allowHome (capLoc I.today0.loc)
    (correctAt I.today0.post I.today0.reports t
      (predictShift I.curves (curveKeyOf I.curves I.today0.loc) (hswAt (wakeOn I I.today) t)
        (I.today0.sleep.shiftOf I.today0.slept)).val)

/-- **Fork `capacity::energize(cut.slots, ectx)`** on today: each slot with its energy at its
start.  (`blocks_done` and `since_break_min` count up in the fork and reach `Features` only;
`energy::predict` reads `loc`, `hsw` and `slept_min`, so neither can move a level.) -/
def day0Slots (I : Input) : List (Fin 6 × Slot) :=
  (day0Cut I).slots.map fun s => (todayEnergy I ⟨s.start, 0⟩, s)

/-- **Fork `DayCapacity::from_slots(ctx.today, &ctx.today_slots(allow_home))`** — day 0, derived
from the kernel's own replay instead of handed in (gap 93). -/
def day0Hist (I : Input) : Hist := histOf' (day0Slots I)

/-- **Entry `i` of the lookahead**: day 0 is today, cut from `now` and energised through today's
posterior and sleep debt (step L9); a later day mixes the two locations' limited days at its
weekday's weight (D10-3). -/
def dayOf (I : Input) (i : Nat) : DayCapacity :=
  if i = 0 then ofHist I.today (day0Hist I)
  else mixDay (I.today + i) (I.weight (Cal.weekdayOf (I.today + i)))
    (pureDay I .lounge (I.today + i)) (pureDay I .home (I.today + i))

/-! ### Held once: six numbers per histogram (what the compiled code runs) -/

/-- Six levels, held.  A `Hist` is a function, so a level read re-runs what built it; a
`Six` is built once and read in constant time. -/
structure Six where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  l4 : Nat
  l5 : Nat

def Six.of (h : Hist) : Six := ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩

def Six.get (s : Six) (l : Fin 6) : Nat :=
  if l.val = 0 then s.l0 else if l.val = 1 then s.l1 else if l.val = 2 then s.l2
  else if l.val = 3 then s.l3 else if l.val = 4 then s.l4 else s.l5

theorem Six.get_of (h : Hist) : (Six.of h).get = h := by
  funext l
  obtain ⟨n, hn⟩ := l
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- One location's day, held: the energised slots listed once, their histogram held, the limit
held. -/
def locSix (c : Curves) (homeMax : Nat) (loc : Loc) (wake : Cal.Instant) (budgetMin : Nat)
    (slots : List Slot) : Six :=
  let e := energize c homeMax loc wake slots
  let h := Six.of (histOf' e)
  Six.of (limitHist budgetMin h.get)

theorem locSix_get (c : Curves) (homeMax : Nat) (loc : Loc) (wake : Cal.Instant) (budgetMin : Nat)
    (slots : List Slot) :
    (locSix c homeMax loc wake budgetMin slots).get = limitHist budgetMin (histOf' (energize c homeMax loc wake slots)) := by
  simp only [locSix, Six.get_of]

/-- Day 0's six levels, held (L4's note): the cut and the energising run once per call. -/
def day0Six (I : Input) : Six :=
  let sl := day0Slots I
  Six.of (histOf' sl)

theorem day0Six_get (I : Input) : (day0Six I).get = day0Hist I := by
  simp only [day0Six, day0Hist, Six.get_of]

/-- `dayOf` as the compiled code runs it: the cut once per day, each location's day held, the
mixed numerators held. -/
def dayOfFast (I : Input) (i : Nat) : DayCapacity :=
  if i = 0 then
    let s := day0Six I
    ⟨I.today, (Six.of (fun l => capDen * s.get l)).get⟩
  else
    let d := I.today + i
    let slots := (dayCut I d).slots
    let wake := wakeOn I d
    let B := budgetMinOf I.day
    let L := locSix I.curves I.homeMax .lounge wake B slots
    let H := locSix I.curves I.homeMax .home wake B slots
    ⟨d, (Six.of (mix (I.weight (Cal.weekdayOf d)) L.get H.get)).get⟩

/-- The compiled `dayOf` holds every histogram once (L4's note; D9-21). -/
@[csimp] theorem dayOf_eq_dayOfFast : @dayOf = @dayOfFast := by
  funext I i
  unfold dayOf dayOfFast
  split
  · simp only [Six.get_of, day0Six_get, ofHist]
  · simp only [locSix_get, Six.get_of, pureDay]; rfl

/-- **Fork `capacity::lookahead`, under D10** (design §13.4): `days` entries from `today`, a
`foldl` over the day range, then `reverse` (D9-21).  Declared after `dayOf_eq_dayOfFast`, so its
compiled fold calls `dayOfFast`. -/
def lookahead (I : Input) : List DayCapacity :=
  ((List.range I.days).foldl (fun acc i => dayOf I i :: acc) []).reverse

/-! ### The laws (in-step; design §15) -/

theorem foldl_cons_map {α β : Type} (f : α → β) : ∀ (L : List α) (acc : List β),
    L.foldl (fun acc i => f i :: acc) acc = (L.map f).reverse ++ acc
  | [], acc => rfl
  | x :: xs, acc => by
    simp only [List.foldl_cons, List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    exact foldl_cons_map f xs (f x :: acc)

/-- **The lookahead is its entries, in order.** -/
theorem lookahead_eq_map (I : Input) : lookahead I = (List.range I.days).map (dayOf I) := by
  simp [lookahead]

theorem dayOf_day (I : Input) (i : Nat) : (dayOf I i).day = I.today + i := by
  unfold dayOf
  split
  · rename_i h; subst h; rfl
  · rfl

theorem lookahead_keeps_the_days (I : Look.Input) : (Look.lookahead I).length = I.days := by
  simp [lookahead_eq_map]

/-- **The days are `today`, `today + 1`, … in order** (fork `from.checked_add_signed(i)`). -/
theorem lookahead_dates (I : Input) : (lookahead I).map (·.day) = (List.range I.days).map (I.today + ·) := by
  rw [lookahead_eq_map, List.map_map]
  congr 1
  funext i
  exact dayOf_day I i

theorem lookahead_getElem? (I : Input) (i : Nat) :
    (lookahead I)[i]? = if i < I.days then some (dayOf I i) else none := by
  by_cases h : i < I.days <;> simp [h, lookahead_eq_map]

theorem daysAscending_range' (g : Nat → DayCapacity) (c : Nat) (hg : ∀ j, (g j).day = c + j) :
    ∀ n s, daysAscending ((List.range' s n).map g) = true
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, s => by
    have ih := daysAscending_range' g c hg (n + 1) (s + 1)
    simp only [List.range'_succ, List.map_cons] at ih ⊢
    simp only [daysAscending, ih, Bool.and_true]
    simp [hg]

theorem lookahead_is_a_lookahead (I : Look.Input) : (lookaheadOf? Look.capDen (Look.lookahead I)).isSome = true := by
  have h : daysAscending (lookahead I) = true := by
    rw [lookahead_eq_map, List.range_eq_range']
    exact daysAscending_range' (dayOf I) I.today (dayOf_day I) I.days 0
  simp [lookaheadOf?, denOf?, capDen_pos, h]

theorem lookahead_entry {I : Input} {i : Nat} {c : DayCapacity} (h : (lookahead I)[i]? = some c) :
    i < I.days ∧ c = dayOf I i := by
  rw [lookahead_getElem?] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · cases h

/-- **Day 0 is the kernel's own** (step L9, gap 93): today's cut from `now`, energised through
today's posterior and sleep debt, summed as `from_slots` sums it — not a histogram the host
handed in.  (Until L9 this theorem read `some (ofHist I.today I.day0)`, and `I.day0` no longer
exists.) -/
theorem lookahead_day_zero_is_the_kernels (I : Input) (h : 0 < I.days) :
    (lookahead I)[0]? = some (ofHist I.today (day0Hist I)) := by
  rw [lookahead_getElem?, if_pos h]
  rfl

/-- **A future day is the mixture of the two locations' limited days** (D10-3), at the weight
of its own weekday. -/
theorem lookahead_future_day_is_the_mixture {I : Input} {i : Nat} {c : DayCapacity}
    (h : (lookahead I)[i]? = some c) (hi : 0 < i) :
    c = mixDay c.day (I.weight (Cal.weekdayOf c.day)) (pureDay I .lounge c.day) (pureDay I .home c.day) := by
  obtain ⟨_, rfl⟩ := lookahead_entry h
  rw [dayOf_day]
  unfold dayOf
  rw [if_neg (by omega)]

theorem lookahead_between_the_locations (I : Look.Input) (i : Nat) (c : DayCapacity) (l : Fin 6)
    (h : (Look.lookahead I)[i]? = some c) (hi : 0 < i) :
    Look.capDen * min (Look.pureDay I .lounge c.day l) (Look.pureDay I .home c.day l) ≤ c.numAt l ∧
    c.numAt l ≤ Look.capDen * max (Look.pureDay I .lounge c.day l) (Look.pureDay I .home c.day l) := by
  have e := lookahead_future_day_is_the_mixture h hi
  have hn : c.numAt = mix (I.weight (Cal.weekdayOf c.day)) (pureDay I .lounge c.day) (pureDay I .home c.day) := by
    conv => lhs; rw [e]
    rfl
  rw [hn]
  exact mix_between_the_locations _ _ _ l

/-- **At a certain weight the day is the pure location's** (D10's mixture meets the fork's
forced location). -/
theorem lookahead_at_a_certain_weight_is_the_pure_location {I : Input} {i : Nat} {c : DayCapacity}
    (h : (lookahead I)[i]? = some c) (hi : 0 < i) :
    ((I.weight (Cal.weekdayOf c.day)).val = capDen → c = ofHist c.day (pureDay I .lounge c.day)) ∧
    ((I.weight (Cal.weekdayOf c.day)).val = 0 → c = ofHist c.day (pureDay I .home c.day)) := by
  have e := lookahead_future_day_is_the_mixture h hi
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · conv => lhs; rw [e]
    simp only [mixDay, ofHist, mix_at_one_is_lounge _ hw]
  · conv => lhs; rw [e]
    simp only [mixDay, ofHist, mix_at_zero_is_home _ hw]

/-- **Day 0's slots lie inside today's window and start no earlier than `now`** — the cut's laws
at day 0's arguments (an ended window cuts nothing at all). -/
theorem day0_slots_are_inside_the_window (I : Input) :
    ∀ s ∈ (day0Cut I).slots,
      max (day0Window I).1 I.today0.now.sec ≤ s.start ∧ s.start < s.stop ∧ s.stop ≤ (day0Window I).2 := by
  rw [day0Cut_eq]
  split
  · intro s hs; cases hs
  · intro s hs; exact cutSlots_inside_the_window _ _ _ _ _ _ hs

/-- **No unit of a day-0 slot is inside a wall of today's.** -/
theorem day0_slots_avoid_the_walls (I : Input) :
    ∀ s ∈ (day0Cut I).slots, ∀ w ∈ wallsOn I.walls I.today, ∀ t,
      s.start ≤ t → t < s.stop → ¬ (w.1 ≤ t ∧ t < w.2) := by
  rw [day0Cut_eq]
  split
  · intro s hs; cases hs
  · intro s hs w hw t h1 h2
    exact cutSlots_avoid_the_walls _ _ _ _ _ _ hs (by simpa using hw) h1 h2

/-- **A window that has already ended leaves day 0 empty** (fork's
`if end <= from { return Vec::new() }`). -/
theorem day0_after_the_window_is_empty (I : Input)
    (h : (day0Window I).2 ≤ max (day0Window I).1 I.today0.now.sec) (l : Fin 6) :
    day0Hist I l = 0 := by
  simp only [day0Hist, day0Slots, day0Cut_eq, if_pos h, histOf']
  rfl

/-- The lookahead with every weight replaced by the fork's threshold (step L7's twin). -/
def Input.twin (I : Input) : Input := { I with weight := fun wd => Look.twin (I.weight wd) }

/-- **The twin is the fork's `capacity::lookahead` with the location forced per day**, in
`capDen` units: lounge iff `p ≥ ½` (`twin_is_the_forks_threshold`), day 0 unchanged. -/
theorem the_twin_forces_the_forks_location {I : Input} {i : Nat} {c : DayCapacity}
    (h : (lookahead I.twin)[i]? = some c) (hi : 0 < i) :
    c = ofHist c.day (if capDen ≤ 2 * (I.weight (Cal.weekdayOf c.day)).val
      then pureDay I .lounge c.day else pureDay I .home c.day) := by
  have e := lookahead_future_day_is_the_mixture h hi
  conv => lhs; rw [e]
  have hp : ∀ loc d, pureDay I.twin loc d = pureDay I loc d := fun _ _ => rfl
  simp only [hp, mixDay, ofHist]
  show DayCapacity.mk c.day (mix (Look.twin (I.weight (Cal.weekdayOf c.day))) _ _) = _
  rw [twin_is_the_forks_location]
  congr 1
  funext l
  split <;> rfl

/-- R10's width of a future day: no level holds more than the day's budget, in `capDen` units. -/
theorem pureDay_le_budget (I : Input) (loc : Loc) (d : Nat) (l : Fin 6) :
    pureDay I loc d l ≤ budgetMinOf I.day := by
  unfold pureDay
  rw [limitHist_eq]
  omega

theorem lookahead_future_day_width {I : Input} {i : Nat} {c : DayCapacity}
    (h : (lookahead I)[i]? = some c) (hi : 0 < i) (l : Fin 6) :
    c.numAt l ≤ capDen * budgetMinOf I.day :=
  have hb := lookahead_between_the_locations I i c l h hi
  Nat.le_trans hb.2 (Nat.mul_le_mul_left _ (Nat.max_le.mpr ⟨pureDay_le_budget I _ _ l, pureDay_le_budget I _ _ l⟩))

/-! ### The smart constructor's laws (R10, D10-4) -/

theorem weightsOf?_ok {x : InputIn} {ws : Cal.Weekday → Weight} (h : weightsOf? x = .ok ws) :
    ∀ wd, weightOn? x wd = .ok (ws wd) := by
  unfold weightsOf? at h
  split at h
  · rename_i mo tu we th fr sa su h1 h2 h3 h4 h5 h6 h7
    cases h
    intro wd
    cases wd <;> assumption
  all_goals cases h

theorem weightsOf?_of_ok {x : InputIn} (h : ∀ wd, ∃ w, weightOn? x wd = .ok w) :
    ∃ ws, weightsOf? x = .ok ws := by
  obtain ⟨mo, h1⟩ := h .monday
  obtain ⟨tu, h2⟩ := h .tuesday
  obtain ⟨we, h3⟩ := h .wednesday
  obtain ⟨th, h4⟩ := h .thursday
  obtain ⟨fr, h5⟩ := h .friday
  obtain ⟨sa, h6⟩ := h .saturday
  obtain ⟨su, h7⟩ := h .sunday
  exact ⟨_, by simp only [weightsOf?, h1, h2, h3, h4, h5, h6, h7]; rfl⟩

/-- What an accepted input satisfied, and what it holds. -/
theorem mkInput?_ok_elim {x : InputIn} {I : Input} (h : mkInput? x = .ok I) :
    x.days ≤ maxLookaheadDays ∧ (∀ wd, weightOn? x wd = .ok (I.weight wd)) ∧
      (wakeOf x).wf = true ∧ nowAgrees x = true ∧
      I.today = x.today ∧ I.days = x.days ∧ I.today0 = x.today0 ∧ I.arrival = arrivalOn x ∧
      I.wake = wakeOf x ∧ I.curves = x.curves ∧ I.homeMax = x.homeMax ∧ I.day = x.day ∧ I.tz = x.tz ∧
      I.walls = x.walls := by
  unfold mkInput? at h
  by_cases hd : maxLookaheadDays < x.days
  · rw [if_pos hd] at h; cases h
  · rw [if_neg hd] at h
    split at h
    · cases h
    · rename_i ws hws
      by_cases hw : (wakeOf x).wf = false
      · rw [if_pos hw] at h; cases h
      · rw [if_neg hw] at h
        by_cases h0 : nowAgrees x = false
        · rw [if_pos h0] at h; cases h
        · rw [if_neg h0] at h
          cases h
          exact ⟨by omega, weightsOf?_ok hws, by simpa using hw, by simpa using h0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The weight is the model's, else the config's, decoded exactly** (fork
`Model::p_lounge_on`; D10-4). -/
theorem mkInput?_weight_is_the_model_then_config {x : InputIn} {I : Input} (h : mkInput? x = .ok I)
    (wd : Cal.Weekday) :
    mkWeight? ((x.pModel wd).getD (x.pConfig wd)).1 ((x.pModel wd).getD (x.pConfig wd)).2 = .ok (I.weight wd) := by
  have hw := (mkInput?_ok_elim h).2.1 wd
  unfold weightOn? at hw
  split at hw
  · rename_i w hm; cases hw; exact hm
  · cases hw

/-- **The arrival is the model's, else the config's; the wake is today's logged wake, else
today's expected arrival** (fork `Model::expected_arrival_on`, `Ctx::wake_time`). -/
theorem mkInput?_arrival_and_wake {x : InputIn} {I : Input} (h : mkInput? x = .ok I) :
    (∀ wd, I.arrival wd = (x.arrModel wd).getD (x.arrConfig wd)) ∧
      I.wake = x.wake.getD (WakeClock.ofClock ((x.arrModel (Cal.weekdayOf x.today)).getD
        (x.arrConfig (Cal.weekdayOf x.today)))) := by
  obtain ⟨-, -, -, -, -, -, -, ha, hw, -⟩ := mkInput?_ok_elim h
  exact ⟨fun wd => by rw [ha]; rfl, by rw [hw]; rfl⟩

/-- R10's width: an accepted lookahead has at most 3,660 days. -/
theorem mkInput?_days_le {x : InputIn} {I : Input} (h : mkInput? x = .ok I) : I.days ≤ maxLookaheadDays := by
  obtain ⟨hd, -, -, -, -, he, -⟩ := mkInput?_ok_elim h
  rw [he]; exact hd

theorem mkInput?_refuses_a_bad_weight {x : InputIn} {wd : Cal.Weekday} {e : CapErr}
    (h : weightOn? x wd = .error e) (I : Input) : mkInput? x ≠ .ok I := fun hI => by
  have := (mkInput?_ok_elim hI).2.1 wd
  rw [h] at this
  cases this

theorem mkInput?_refuses_a_bad_wake {x : InputIn} (h : (wakeOf x).wf = false) (I : Input) :
    mkInput? x ≠ .ok I := fun hI => by
  have := (mkInput?_ok_elim hI).2.2.1
  rw [h] at this
  cases this

/-- An `at` stamp on another local date is refused by name (design §13.5's `nowDisagrees`),
never planned against. -/
theorem mkInput?_refuses_a_now_that_disagrees {x : InputIn} (h : nowAgrees x = false) (I : Input) :
    mkInput? x ≠ .ok I := fun hI => by
  have := (mkInput?_ok_elim hI).2.2.2.1
  rw [h] at this
  cases this

/-- **Both directions**: every other input is accepted. -/
theorem mkInput?_accepts {x : InputIn} (hd : x.days ≤ maxLookaheadDays)
    (hws : ∀ wd, ∃ w, weightOn? x wd = .ok w) (hw : (wakeOf x).wf = true) (h0 : nowAgrees x = true) :
    ∃ I, mkInput? x = .ok I := by
  obtain ⟨ws, hws⟩ := weightsOf?_of_ok hws
  refine ⟨⟨x.today, x.days, x.today0, ws, arrivalOn x, wakeOf x, x.curves, x.homeMax, x.day, x.tz,
    x.walls⟩, ?_⟩
  simp only [mkInput?, if_neg (Nat.not_lt.mpr hd), hws, hw, h0]
  rfl

/-- A logged wake is refused by name only when chrono could not hold it; the fallback, an
expected arrival, never is. -/
theorem wakeOf_without_a_logged_wake_is_wf (x : InputIn) (h : x.wake = none) : (wakeOf x).wf = true := by
  simp only [wakeOf, h, Option.getD_none]
  exact WakeClock.ofClock_wf _

/-- **End to end from the host's pair**: an accepted input's future day, read over `capDenD`, is
the rational `(n·lounge + (d − n)·home) / d` for the model-then-config pair `n / d` of its
weekday, each location's day limited to its budget first (D10, D10-3, D10-4). -/
theorem lookahead_is_the_expected_minutes {x : InputIn} {I : Input} (hI : mkInput? x = .ok I)
    {i : Nat} {c : DayCapacity} (h : (lookahead I)[i]? = some c) (hi : 0 < i) (l : Fin 6) :
    Q.equiv (c.minutesAt capDenD l).val
      ⟨((x.pModel (Cal.weekdayOf c.day)).getD (x.pConfig (Cal.weekdayOf c.day))).1 * pureDay I .lounge c.day l
        + (((x.pModel (Cal.weekdayOf c.day)).getD (x.pConfig (Cal.weekdayOf c.day))).2
          - ((x.pModel (Cal.weekdayOf c.day)).getD (x.pConfig (Cal.weekdayOf c.day))).1) * pureDay I .home c.day l,
        ((x.pModel (Cal.weekdayOf c.day)).getD (x.pConfig (Cal.weekdayOf c.day))).2⟩ = true := by
  have e := lookahead_future_day_is_the_mixture h hi
  have hw := mkInput?_weight_is_the_model_then_config hI (Cal.weekdayOf c.day)
  rw [e]
  exact mixDay_minutesAt_is_the_expectation hw c.day _ _ l

/-! ### Witnesses (Chicago's 2026 table; the shipped `config.toml`) -/

/-- The wake witnesses on Chicago's 2026 table: seconds and nanoseconds kept on an unambiguous
time; the spring gap moves 02:30:40 to 03:00:40 CDT, and a leap second there is left; the fall
fold takes the earlier 01:30:40. -/
theorem wakeInstantOf_on_witnesses :
    wakeInstantOf Cal.chicago 739865 ⟨6 * 3600 + 5 * 60 + 40, 250000000⟩
      = ⟨(Cal.instantOf Cal.chicago 739865 365).sec + 40, 250000000⟩ ∧
    wakeInstantOf Cal.chicago 739682 ⟨2 * 3600 + 30 * 60 + 40, 0⟩ = ⟨63908553600 + 40, 0⟩ ∧
    wakeInstantOf Cal.chicago 739682 ⟨2 * 3600 + 30 * 60 + 59, 1500000000⟩ = ⟨63908553600 + 59, 500000000⟩ ∧
    wakeInstantOf Cal.chicago 739920 ⟨1 * 3600 + 30 * 60 + 40, 0⟩ = ⟨63929111400 + 40, 0⟩ := by
  decide

/-- The shipped `[day]`: 60-minute blocks, a 20-minute break after 2, a 30-minute last block,
8 hours, a 19:00 cap, `budget_ratio` 0.75. -/
def DayCfg.shipped : DayCfg := ⟨CutCfg.shipped, mkPos 8 1 (by decide), 1140, Arith.budgetRatio⟩

/-- The shipped `[expected] p_lounge`, as exact weights: 0.9 Monday to Thursday, 0.8 Friday,
0.5 Saturday, 0.4 Sunday. -/
def shippedWeight : Cal.Weekday → Weight
  | .friday => ⟨800000000000000000, by decide⟩
  | .saturday => ⟨500000000000000000, by decide⟩
  | .sunday => ⟨400000000000000000, by decide⟩
  | _ => ⟨900000000000000000, by decide⟩

/-- The shipped `[expected] arrival`: 07:00 on weekdays, 10:00 at weekends. -/
def shippedArrival : Cal.Weekday → Field.Clock
  | .saturday => 600
  | .sunday => 600
  | _ => 420

/-- The §4.3 Monday as `Ctx` describes it at 07:00: nothing stored in `state.json` (so §8.1's
formula runs from `now`), at the lounge, the home cap in force, no sleep reading and no energy
report yet, and §16's `[energy]` decimals — `posterior_full_hours = 3`, `posterior_zero_hours = 6`,
`sleep_debt.under_hours = 7`, `sleep_debt.shift = 1`. -/
def specToday : Today :=
  ⟨⟨(Cal.instantOf Cal.chicago 739865 420).sec, 0⟩, none, none, none, none, loungeKey, false, none, [],
    ⟨Arith.mkPos 3 1 (by decide), Arith.mkPos 6 1 (by decide)⟩,
    ⟨none, Arith.defaultShift, Arith.mkPos 7 1 (by decide)⟩⟩

/-- The fork's `capacity_lookahead.rs` week, from Monday 2026-09-07 in Chicago: the shipped
config, no learned model, no walls, woken at 06:05; day 0 is today, derived (step L9). -/
def specInput : Input :=
  ⟨739865, 3, specToday, shippedWeight, shippedArrival, ⟨6 * 3600 + 5 * 60, 0⟩,
    Curves.shipped, 3, DayCfg.shipped, Cal.chicago, []⟩

/-- **A future day reuses today's wake clock to the second** (fork `Ctx::wake_time`, then
`local_dt` per date): on Tuesday 2026-09-08 with a 07:05 arrival, a wake at 06:05:00 puts the
07:05 block at 1.00 h, the lounge's `1-5` level 5, and the day keeps 240 minutes at 5; a wake at
06:05:40 puts it at 0.99 h, level 4, and the day keeps 180 at 5 and 180 at 4. -/
theorem a_future_day_reads_todays_wake_to_the_second :
    (List.finRange 6).map (pureDay { specInput with arrival := fun _ => 425 } .lounge 739866)
      = [0, 0, 0, 0, 120, 240] ∧
    (List.finRange 6).map (pureDay { specInput with arrival := fun _ => 425, wake := ⟨6 * 3600 + 5 * 60 + 40, 0⟩ }
        .lounge 739866) = [0, 0, 0, 0, 180, 180] := by
  decide

/-- Fork test `lookahead_follows_the_learned_arrival_and_location`, through the twin: the
learned Tuesday arrival 12:00 and the learned Wednesday `P(lounge)` 0.2 (a home day).  With the
location forced as the fork forces it, the kernel's three days are the fork's minutes times
`capDen`: day 0 **derived** (step L9 — arriving at 07:00 with nothing stored and no walls, the
window runs to 15:00 and its seven blocks hold 240 minutes at level 4 and 180 at 5), Tuesday
`[0, 0, 120, 120, 120, 0]` (the fork's assertion) and Wednesday at home, capped at level 3. -/
theorem the_twin_follows_the_learned_arrival_and_location :
    (lookahead { specInput with
        arrival := fun wd => if wd = Cal.Weekday.tuesday then 720 else shippedArrival wd,
        weight := fun wd => if wd = Cal.Weekday.wednesday then ⟨200000000000000000, by decide⟩ else shippedWeight wd }.twin).map
        (fun c => (c.day, (List.finRange 6).map c.numAt))
      = [(739865, [0, 0, 0, 0, 240 * capDen, 180 * capDen]),
         (739866, [0, 0, 120 * capDen, 120 * capDen, 120 * capDen, 0]),
         (739867, [0, 0, 0, 360 * capDen, 0, 0])] := by
  decide

/-- **D10's Tuesday**: `p = 0.9`.  The lounge keeps 180 minutes at 5 and 180 at 4; home caps
every slot at 3 and keeps 360 there.  The expected day holds 162, 162 and 36 minutes, where the
fork's lounge day holds 180, 180 and 0. -/
theorem the_expected_tuesday :
    (List.finRange 6).map (pureDay specInput .lounge 739866) = [0, 0, 0, 0, 180, 180] ∧
    (List.finRange 6).map (pureDay specInput .home 739866) = [0, 0, 0, 360, 0, 0] ∧
    ((lookahead specInput)[1]?).map (fun c => (List.finRange 6).map c.numAt)
      = some [0, 0, 0, 36 * capDen, 162 * capDen, 162 * capDen] := by
  decide

/-- `specInput`'s raw form: the shipped tables as the host sends them, nothing learned, no
logged wake. -/
def specIn : InputIn :=
  ⟨739865, 3, specToday, fun _ => none,
    fun wd => match wd with | .friday => (8, 10) | .saturday => (5, 10) | .sunday => (4, 10) | _ => (9, 10),
    fun _ => none, shippedArrival, none, Curves.shipped, 3, DayCfg.shipped, Cal.chicago, []⟩

/-- **The decoder, both directions.**  Accepted: the shipped tables, with today's expected
arrival (Monday 07:00) as the wake; a learned Sunday weight 0.8 over the config's 0.4; 3,660
days; a leap second on second 59.  Refused by name: 3,661 days; a config weight 3/2 on
Saturday; a learned third on Wednesday, whatever the config says; a wake at 24:00; a leap
second off second 59; an `at` stamp on yesterday, and one on tomorrow. -/
theorem mkInput?_on_witnesses :
    (mkInput? specIn).map (fun I => (I.days, (I.weight .sunday).val, I.wake)) = .ok (3, 400000000000000000, ⟨25200, 0⟩) ∧
    (mkInput? { specIn with pModel := fun wd => if wd = Cal.Weekday.sunday then some (8, 10) else none }).map
      (fun I => (I.weight .sunday).val) = .ok 800000000000000000 ∧
    (mkInput? { specIn with days := 3660 }).map (fun I => I.days) = .ok 3660 ∧
    (mkInput? { specIn with wake := some ⟨7 * 3600 + 59, 1500000000⟩ }).map (fun I => I.wake.ns) = .ok 1500000000 ∧
    (mkInput? { specIn with days := 3661 }).map (fun _ => ()) = .error .lookaheadTooLong ∧
    (mkInput? { specIn with pConfig := fun wd => if wd = Cal.Weekday.saturday then (3, 2) else (9, 10) }).map
      (fun _ => ()) = .error (.weight .saturday .weightAboveOne) ∧
    (mkInput? { specIn with pModel := fun wd => if wd = Cal.Weekday.wednesday then some (1, 3) else none }).map
      (fun _ => ()) = .error (.weight .wednesday .weightPrecision) ∧
    (mkInput? { specIn with wake := some ⟨86400, 0⟩ }).map (fun _ => ()) = .error .badWake ∧
    (mkInput? { specIn with wake := some ⟨7 * 3600 + 58, 1500000000⟩ }).map (fun _ => ()) = .error .badWake ∧
    (mkInput? { specIn with today0 := { specToday with now := ⟨(Cal.instantOf Cal.chicago 739864 420).sec, 0⟩ } }).map
      (fun _ => ()) = .error .nowDisagrees ∧
    (mkInput? { specIn with today0 := { specToday with now := ⟨(Cal.instantOf Cal.chicago 739866 420).sec, 0⟩ } }).map
      (fun _ => ()) = .error .nowDisagrees :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Sunday mixes at its own weekday's weight** (fork `p_lounge_on(date.weekday())`): the
shipped 0.4.  The lounge keeps 120 minutes at each of 5, 4 and 3; home keeps 240 at 3 and 120 at
2; the expected Sunday holds 48, 48, 192 and 72. -/
theorem sunday_mixes_at_its_own_weight :
    (List.finRange 6).map (pureDay specInput .lounge 739871) = [0, 0, 0, 120, 120, 120] ∧
    (List.finRange 6).map (pureDay specInput .home 739871) = [0, 0, 120, 240, 0, 0] ∧
    (List.finRange 6).map (dayOf specInput 6).numAt = [0, 0, 72 * capDen, 192 * capDen, 48 * capDen, 48 * capDen] := by
  decide

/-! ### Day 0's witnesses (step L9): the §4.3 day, derived -/

/-- The §4.3 meeting moved onto the Monday, 12:50–13:50 in Chicago — so that day 0's own window
and cut are the ones `cut_slots_on_the_spec_day` documents. -/
def mondayWall : List WallIx :=
  [⟨739865, 739865, (Cal.instantOf Cal.chicago 739865 770).sec, (Cal.instantOf Cal.chicago 739865 830).sec⟩]

/-- `specInput` with that wall: the §4.3 day as day 0. -/
def specWalled : Input := { specInput with walls := mondayWall }

/-- An instant on the §4.3 day. -/
def atSpec (c : Field.Clock) : Cal.Instant := ⟨(Cal.instantOf Cal.chicago 739865 c).sec, 0⟩

/-- **Day 0 *is* the §4.3 day, derived** (gap 93).  Arriving at 07:00 with the 12:50–13:50
meeting, §8.1's window runs to 16:00 and `cut_slots_on_the_spec_day`'s seven blocks hold 410
minutes; at the lounge, woken at 06:05, they energise to 180 minutes at level 5 (08:00, 09:20,
10:20), 180 at 4 (07:00, 11:40, 13:50) and the 50-minute short block at 3 (15:10).  Nothing is
handed in: this is `Ctx::today_slots` then `DayCapacity::from_slots`, in the kernel. -/
theorem day_zero_is_the_spec_day_energised :
    (day0Window specWalled).2 = (Cal.instantOf Cal.chicago 739865 960).sec ∧
    (day0Cut specWalled).slotMinutes = 410 ∧
    (List.finRange 6).map (day0Hist specWalled) = [0, 0, 0, 50, 180, 180] := by
  decide

/-- **Day 0 is not limited to the budget**, and a future day is (D10-3).  The §4.3 Monday holds
420 minutes where `budget_blocks × block_min` is 360: `from_slots` sums the energised slots and
`limit_to_budget` is `pureDay`'s. -/
theorem the_day_zero_histogram_is_not_limited_to_the_budget :
    budgetMinOf specInput.day = 360 ∧
    (List.finRange 6).map (day0Hist specInput) = [0, 0, 0, 0, 240, 180] ∧
    (List.finRange 6).map (pureDay specInput .lounge 739866) = [0, 0, 0, 0, 180, 180] := by
  decide

/-- **Day 0 is cut from `now`, not from the arrival** (fork `from = start.max(self.now_tz)`):
with 07:00 stored as today's arrival and `now` at 10:00, the window is unchanged and the day
holds what is left of it — 260 minutes. -/
theorem day_zero_is_cut_from_now :
    (List.finRange 6).map (day0Hist { specWalled with today0 :=
        { specToday with date := some 739865, arrival := some 420, now := atSpec 600 } })
      = [0, 0, 0, 50, 90, 120] := by
  decide

/-- **The stored window counts only with its budget, and only on its own day** (fork
`Ctx::window`): `state.window = 09:00–12:00` with `state.budget` is today's window; the same
window with no budget, or dated yesterday, falls back to §8.1's formula. -/
theorem day_zero_reads_the_stored_window :
    day0Window { specWalled with today0 :=
        { specToday with date := some 739865, window := some (540, 720), budget := some 6 } }
      = ((Cal.instantOf Cal.chicago 739865 540).sec, (Cal.instantOf Cal.chicago 739865 720).sec) ∧
    day0Window { specWalled with today0 :=
        { specToday with date := some 739865, window := some (540, 720), budget := none } }
      = day0Window specWalled ∧
    day0Window { specWalled with today0 :=
        { specToday with date := some 739864, window := some (540, 720), budget := some 6 } }
      = day0Window specWalled := by
  decide

/-- **Today's posterior moves today's levels** (§8.5, site R5): a 09:00 report of 2 against a
prediction of 5 is a residual of −3, at full weight for three hours and fading to nothing at
six, so the day's levels fall and then recover.  A report from last night at 23:00 is past
`posterior_zero_hours` and weighs nothing. -/
theorem todays_posterior_moves_todays_levels :
    (List.finRange 6).map (day0Hist { specWalled with today0 :=
        { specToday with reports := [⟨atSpec 540, 5, 2⟩] } })
      = [0, 60, 120, 110, 60, 60] ∧
    (List.finRange 6).map (day0Hist { specWalled with today0 :=
        { specToday with reports := [⟨⟨(Cal.instantOf Cal.chicago 739864 1380).sec, 0⟩, 5, 2⟩] } })
      = [0, 0, 0, 50, 180, 180] := by
  decide

/-- **A short night shifts every level** (site R10): five hours is below `under_hours = 7`, so
the shift of 1 comes off each base level; eight hours is not, and nothing moves. -/
theorem a_short_night_shifts_every_level :
    (List.finRange 6).map (day0Hist { specWalled with today0 := { specToday with slept := some 300 } })
      = [0, 0, 50, 180, 180, 0] ∧
    (List.finRange 6).map (day0Hist { specWalled with today0 := { specToday with slept := some 480 } })
      = [0, 0, 0, 50, 180, 180] := by
  decide

/-- **Today's location is read, and `--allow-home` lifts the cap** (fork `Ctx::loc`,
`EnergyCtx::cap_for_location`): at home the day reads the home curve and every level is capped
at `home_max_ci = 3`; with `--allow-home` the same curve is uncapped.  A location the curves do
not name — `zoom` — reads the home curve and is **not** capped, because `cap_for_location`
compares `Loc::Home` and nothing else. -/
theorem day_zero_reads_todays_location :
    (List.finRange 6).map (day0Hist { specWalled with today0 := { specToday with loc := homeKey } })
      = [0, 0, 50, 360, 0, 0] ∧
    (List.finRange 6).map (day0Hist { specWalled with today0 :=
        { specToday with loc := homeKey, allowHome := true } })
      = [0, 0, 50, 240, 120, 0] ∧
    (List.finRange 6).map (day0Hist { specWalled with today0 :=
        { specToday with loc := ['z', 'o', 'o', 'm'] } })
      = [0, 0, 50, 240, 120, 0] ∧
    curveKeyOf Curves.shipped ['z', 'o', 'o', 'm'] = homeKey ∧
    curveKeyOf Curves.shipped anyKey = homeKey ∧
    curveKeyOf Curves.shipped loungeKey = loungeKey := by
  decide

/-- The §4.3 meeting on Wednesday 2026-09-09, 12:50–13:50 in Chicago, as `wallIndex` lists it. -/
def wednesdayWall : List WallIx :=
  [⟨739867, 739867, (Cal.instantOf Cal.chicago 739867 770).sec, (Cal.instantOf Cal.chicago 739867 830).sec⟩]

/-- **The Wednesday wall, end to end** (design §13.4's loaded-plan witness; `Boundary.lean`
reaches it from a loaded calendar through `wallIndex`).  Without walls Wednesday's window ends
at 15:00; the meeting moves it to 16:00 and the §4.3 cut holds 410 minutes; the lounge day, the
fork's forced location at `p = 0.9`, keeps its 360-minute budget, 180 at 5 and 180 at 4: the
fork's `[0, 0, 0, 0, 180, 180]`, written out by hand, times `capDen`. -/
theorem a_wednesday_wall_moves_the_window_and_keeps_the_budget :
    (windowOn Cal.chicago 739867 420 1140 480 []).2 = (Cal.instantOf Cal.chicago 739867 900).sec ∧
    (windowOn Cal.chicago 739867 420 1140 480 (wallsOn wednesdayWall 739867)).2
      = (Cal.instantOf Cal.chicago 739867 960).sec ∧
    (dayCut { specInput with walls := wednesdayWall } 739867).slotMinutes = 410 ∧
    ((lookahead { specInput with walls := wednesdayWall }.twin)[2]?).map
        (fun c => (c.day, (List.finRange 6).map c.numAt))
      = some (739867, [0, 0, 0, 0, 180 * capDen, 180 * capDen]) := by
  decide

/-! ############################################################################
## The capacity input's bounds (stage 5 D10 step L6; design §13.6, §10.4)

Step L5's `mkInput?` checks the day count, the weights, the wake and day 0.  This section gives
every other value the capacity wire carries its R10 bound, a smart constructor the wire decoder
(`Boundary.lean`, section "Stage 5 D10 L6") actually uses, and a rejection theorem, with the names
of design §13.6's table:

| value | bound | constructor | refusal |
|---|---|---|---|
| `[day]` `block_min`, `min_last_block_min` | `1..=1440` | `mkDayCfg?` | `badDay <key>` |
| `[day]` `break_min` | `0..=1440` | `mkDayCfg?` | `badDay breakMin` |
| `[day]` `break_after_blocks` | `≤ 64` | `mkDayCfg?` | `badDay breakAfterBlocks` |
| `[day]` `window_hours` | a pair, `den ∈ [1, 10^6]`, `0 < num ≤ 24·den` | `mkDayCfg?` | `badDay windowHours` |
| `[day]` `budget_ratio` | a pair, `den ∈ [1, 10^6]`, `num ≤ den` | `mkDayCfg?` | `badDay budgetRatio` |
| a prior range | keys `den ∈ [1, 10^6]`, `num ≤ 48·den`, `from < to`; level `≤ 5` | `mkStep?` | `badStep`, `badLevel` |
| a prior curve | `≤ 64` ranges, each well formed, sorted by `from` as `StepFn::from_pairs` sorts | `curveOk` | `badStep` |
| the prior curves | `≤ 16` curves, keys `≤ 64` characters, no key twice, **every** curve (L4's disagreement 8) | `priorOk` | `badPrior <key>` |
| a learned curve (`lounge`, `home`) | exactly 12 entries, each `< 256` | `energyOk` | `badCurve <loc>` |
| `home_max_ci` | `≤ 5` | `homeMaxOk` | `badCap homeMaxCi` |

**Why these bounds and not wider ones.**  A range key with `den ≤ 10^6` is where L4 proved the
kernel's exact comparison is the fork's `f64` one, so a wider key is parity entry P26's, refused.
A level above 5, a learned entry of 256 or more, or a curve not of 12 entries is P26's too: the
fork clamps or reads past the end, and the kernel refuses by name.  `curveKeyLt` recurses over one
key's characters and `stepAt` over one curve, so the key length and the range count are R10's
widths for rule D9-21.  The bounds the fork cannot violate (a `u32` minute count above 1,440, a
`window_hours` above a day) are refused as host defects.

**`badTz subMinuteOffset` is not needed** (design §13.6's last row, left to L6 by L2 and L3).
L2's window and L3's cut count whole UTC seconds and are the fork's for every offset (L3's block,
"Exact in whole seconds"), and L4's hours since wake read seconds (site R11).  So no zone table is
refused for a sub-minute offset.
-/

/-! ### `[day]`: fork `DayConfig`, every key bounded -/

/-- The `[day]` key a bound refused (design §13.6's `badDay <key>`). -/
inductive DayKey where
  | blockMin
  | breakMin
  | breakAfterBlocks
  | minLastBlockMin
  | windowHours
  | budgetRatio
deriving DecidableEq, Repr

/-- A day's minutes: the widest `block_min`, `break_min` and `min_last_block_min`. -/
def maxDayMin : Nat := 1440

/-- The widest denominator of a `[day]` ratio or a prior range key: six decimal places. -/
def maxKeyDen : Nat := 1000000

/-- The most blocks between breaks. -/
def maxBreakAfter : Nat := 64

/-- **The smart constructor for `[day]`** (R10).  Checked in the order of §13.6's table:
`blockMin`, `breakMin`, `breakAfterBlocks`, `minLastBlockMin`, `windowHours`, `budgetRatio`.
`window_cap` is a `Field.Clock`, bounded by its type and read by the clock grammar. -/
def mkDayCfg? (blockMin breakMin breakAfter minLast whNum whDen : Nat) (windowCap : Field.Clock)
    (brNum brDen : Nat) : Except DayKey DayCfg :=
  if ¬ (1 ≤ blockMin ∧ blockMin ≤ maxDayMin) then .error .blockMin
  else if ¬ breakMin ≤ maxDayMin then .error .breakMin
  else if ¬ breakAfter ≤ maxBreakAfter then .error .breakAfterBlocks
  else if ¬ (1 ≤ minLast ∧ minLast ≤ maxDayMin) then .error .minLastBlockMin
  else if hw : 1 ≤ whDen ∧ whDen ≤ maxKeyDen ∧ 0 < whNum ∧ whNum ≤ 24 * whDen then
    if hb : 1 ≤ brDen ∧ brDen ≤ maxKeyDen ∧ brNum ≤ brDen then
      .ok ⟨⟨blockMin, breakMin, breakAfter, minLast⟩, mkPos whNum whDen (by omega), windowCap,
        mkPos brNum brDen (by omega)⟩
    else .error .budgetRatio
  else .error .windowHours

/-- What an accepted `[day]` satisfies. -/
def DayCfg.wf (c : DayCfg) : Bool :=
  decide (1 ≤ c.cut.blockMin ∧ c.cut.blockMin ≤ maxDayMin) && decide (c.cut.breakMin ≤ maxDayMin) &&
  decide (c.cut.breakAfter ≤ maxBreakAfter) &&
  decide (1 ≤ c.cut.minLastBlockMin ∧ c.cut.minLastBlockMin ≤ maxDayMin) &&
  decide (c.windowHours.val.den ≤ maxKeyDen ∧ 0 < c.windowHours.val.num ∧
    c.windowHours.val.num ≤ 24 * c.windowHours.val.den) &&
  decide (c.budgetRatio.val.den ≤ maxKeyDen ∧ c.budgetRatio.val.num ≤ c.budgetRatio.val.den)

theorem mkDayCfg?_wf {bm br ba ml wn wd : Nat} {cap : Field.Clock} {rn rd : Nat} {c : DayCfg}
    (h : mkDayCfg? bm br ba ml wn wd cap rn rd = .ok c) : c.wf = true := by
  unfold mkDayCfg? at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · rename_i h1 h2 h3 h4 hw hb
      cases h
      simp only [Decidable.not_not] at h1 h2 h3 h4
      simp [DayCfg.wf, mkPos, h1, h2, h3, h4, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, hb.1, hb.2.1, hb.2.2]
    · cases h
  · cases h

/-- **Both directions**: every well-formed `[day]` is accepted, as itself. -/
theorem mkDayCfg?_of_wf (c : DayCfg) (h : c.wf = true) :
    mkDayCfg? c.cut.blockMin c.cut.breakMin c.cut.breakAfter c.cut.minLastBlockMin
      c.windowHours.val.num c.windowHours.val.den c.windowCap c.budgetRatio.val.num
      c.budgetRatio.val.den = .ok c := by
  simp only [DayCfg.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  have hwd := denPos c.windowHours
  have hbd := denPos c.budgetRatio
  unfold mkDayCfg?
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    dif_pos (by omega), dif_pos (by omega)]
  obtain ⟨⟨a, b, c', d⟩, ⟨⟨wn, wd⟩, hw⟩, cap, ⟨⟨rn, rd⟩, hr⟩⟩ := c
  rfl

theorem mkDayCfg?_refuses_blockMin {bm : Nat} (h : bm = 0 ∨ maxDayMin < bm) (br ba ml wn wd : Nat)
    (cap : Field.Clock) (rn rd : Nat) : mkDayCfg? bm br ba ml wn wd cap rn rd = .error .blockMin := by
  unfold mkDayCfg?; rw [if_pos (by omega)]

theorem mkDayCfg?_refuses_breakMin {bm br : Nat} (h0 : 1 ≤ bm ∧ bm ≤ maxDayMin) (h : maxDayMin < br)
    (ba ml wn wd : Nat) (cap : Field.Clock) (rn rd : Nat) :
    mkDayCfg? bm br ba ml wn wd cap rn rd = .error .breakMin := by
  unfold mkDayCfg?; rw [if_neg (by omega), if_pos (by omega)]

theorem mkDayCfg?_refuses_breakAfterBlocks {bm br ba : Nat} (h0 : 1 ≤ bm ∧ bm ≤ maxDayMin)
    (h1 : br ≤ maxDayMin) (h : maxBreakAfter < ba) (ml wn wd : Nat) (cap : Field.Clock) (rn rd : Nat) :
    mkDayCfg? bm br ba ml wn wd cap rn rd = .error .breakAfterBlocks := by
  unfold mkDayCfg?; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem mkDayCfg?_refuses_minLastBlockMin {bm br ba ml : Nat} (h0 : 1 ≤ bm ∧ bm ≤ maxDayMin)
    (h1 : br ≤ maxDayMin) (h2 : ba ≤ maxBreakAfter) (h : ml = 0 ∨ maxDayMin < ml) (wn wd : Nat)
    (cap : Field.Clock) (rn rd : Nat) :
    mkDayCfg? bm br ba ml wn wd cap rn rd = .error .minLastBlockMin := by
  unfold mkDayCfg?; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem mkDayCfg?_refuses_windowHours {bm br ba ml wn wd : Nat} (h0 : 1 ≤ bm ∧ bm ≤ maxDayMin)
    (h1 : br ≤ maxDayMin) (h2 : ba ≤ maxBreakAfter) (h3 : 1 ≤ ml ∧ ml ≤ maxDayMin)
    (h : ¬ (1 ≤ wd ∧ wd ≤ maxKeyDen ∧ 0 < wn ∧ wn ≤ 24 * wd)) (cap : Field.Clock) (rn rd : Nat) :
    mkDayCfg? bm br ba ml wn wd cap rn rd = .error .windowHours := by
  unfold mkDayCfg?; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    dif_neg h]

theorem mkDayCfg?_refuses_budgetRatio {bm br ba ml wn wd rn rd : Nat} (h0 : 1 ≤ bm ∧ bm ≤ maxDayMin)
    (h1 : br ≤ maxDayMin) (h2 : ba ≤ maxBreakAfter) (h3 : 1 ≤ ml ∧ ml ≤ maxDayMin)
    (h4 : 1 ≤ wd ∧ wd ≤ maxKeyDen ∧ 0 < wn ∧ wn ≤ 24 * wd) (h : ¬ (1 ≤ rd ∧ rd ≤ maxKeyDen ∧ rn ≤ rd))
    (cap : Field.Clock) : mkDayCfg? bm br ba ml wn wd cap rn rd = .error .budgetRatio := by
  unfold mkDayCfg?; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    dif_pos h4, dif_neg h]

/-- R10's width of an accepted `[day]`: the configured window is at most a day, and the budget at
most the window. -/
theorem DayCfg.wf_window_le_a_day {c : DayCfg} (h : c.wf = true) : windowMinOf c.windowHours ≤ 1440 := by
  simp only [DayCfg.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  have hd := denPos c.windowHours
  simp only [windowMinOf, halfUpQ, scale_num, scale_den]
  have hlt : (2 * (c.windowHours.val.num * 60) + c.windowHours.val.den) / (2 * c.windowHours.val.den) < 1441 :=
    Nat.div_lt_of_lt_mul (by omega)
  omega

/-! ### The prior curves: fork `StepFn`, `EnergyConfig::prior` -/

/-- Why a prior range is refused (design §13.6's `badStep`, `badLevel`). -/
inductive StepErr where
  | badStep
  | badLevel
deriving DecidableEq, Repr

/-- A range key `num / den` hours inside the exact domain: `den ∈ [1, 10^6]`, at most 48 hours. -/
def keyOk (n d : Nat) : Bool := decide (1 ≤ d ∧ d ≤ maxKeyDen ∧ n ≤ 48 * d)

/-- The range part of a step: both keys in the domain, and `from < to` for a closed range. -/
def rangeOk (fromNum fromDen : Nat) : Option (Nat × Nat) → Bool
  | none => keyOk fromNum fromDen
  | some (n, d) => keyOk fromNum fromDen && keyOk n d && decide (fromNum * d < n * fromDen)

/-- A well-formed prior range. -/
def Step.wf (s : Step) : Bool := rangeOk s.fromNum s.fromDen s.toKey && decide (s.level ≤ 5)

/-- **The smart constructor for a prior range** (R10): `badStep` for the keys, then `badLevel`. -/
def mkStep? (fromNum fromDen : Nat) (toKey : Option (Nat × Nat)) (level : Nat) : Except StepErr Step :=
  if rangeOk fromNum fromDen toKey = false then .error .badStep
  else if level ≤ 5 then .ok ⟨fromNum, fromDen, toKey, level⟩
  else .error .badLevel

theorem mkStep?_ok_iff {fn fd : Nat} {t : Option (Nat × Nat)} {l : Nat} {s : Step} :
    mkStep? fn fd t l = .ok s ↔ s = ⟨fn, fd, t, l⟩ ∧ s.wf = true := by
  unfold mkStep?
  constructor
  · intro h
    split at h
    · cases h
    · split at h
      · cases h
        rename_i h1 h2
        refine ⟨rfl, ?_⟩
        simp only [Step.wf, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by simpa using h1, h2⟩
      · cases h
  · rintro ⟨rfl, hw⟩
    simp only [Step.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    rw [if_neg (by simp [hw.1]), if_pos hw.2]

theorem mkStep?_refuses_a_zero_denominator (fn : Nat) (t : Option (Nat × Nat)) (l : Nat) :
    mkStep? fn 0 t l = .error .badStep := by
  cases t <;> simp [mkStep?, rangeOk, keyOk]

theorem mkStep?_refuses_a_wide_denominator {fd : Nat} (h : maxKeyDen < fd) (fn : Nat)
    (t : Option (Nat × Nat)) (l : Nat) : mkStep? fn fd t l = .error .badStep := by
  have : keyOk fn fd = false := by simp [keyOk]; omega
  cases t with
  | none => simp [mkStep?, rangeOk, this]
  | some p => obtain ⟨n, d⟩ := p; simp [mkStep?, rangeOk, this]

theorem mkStep?_refuses_past_48_hours {fn fd : Nat} (h : 48 * fd < fn) (t : Option (Nat × Nat)) (l : Nat) :
    mkStep? fn fd t l = .error .badStep := by
  have : keyOk fn fd = false := by simp [keyOk]; omega
  cases t with
  | none => simp [mkStep?, rangeOk, this]
  | some p => obtain ⟨n, d⟩ := p; simp [mkStep?, rangeOk, this]

theorem mkStep?_refuses_an_empty_range {fn fd tn td : Nat} (h : tn * fd ≤ fn * td) (l : Nat) :
    mkStep? fn fd (some (tn, td)) l = .error .badStep := by
  have : decide (fn * td < tn * fd) = false := by simp; omega
  simp [mkStep?, rangeOk, this]

theorem mkStep?_refuses_a_level_above_five {fn fd : Nat} {t : Option (Nat × Nat)} {l : Nat}
    (hr : rangeOk fn fd t = true) (h : 5 < l) : mkStep? fn fd t l = .error .badLevel := by
  simp only [mkStep?, hr]
  rw [if_neg (by simp), if_neg (by omega)]

/-- The most ranges in one curve, the most curves, and the longest curve key. -/
def maxCurveSteps : Nat := 64
def maxCurves : Nat := 16
def maxCurveKey : Nat := 64

/-- `a.from ≤ b.from`, cross-multiplied. -/
def fromLe (a b : Step) : Bool := decide (a.fromNum * b.fromDen ≤ b.fromNum * a.fromDen)

/-- Sorted by `from`, as fork `StepFn::from_pairs` leaves a curve (its sort is stable, so equal
starts keep the order given). -/
def sortedFrom : List Step → Bool
  | a :: b :: t => fromLe a b && sortedFrom (b :: t)
  | _ => true

/-- **A prior curve on the wire**: at most 64 ranges, each well formed, sorted by `from`.  The
length is checked first, so the walks below it never run over a longer list. -/
def curveOk (steps : List Step) : Bool :=
  decide (steps.length ≤ maxCurveSteps) && steps.all Step.wf && sortedFrom steps

/-- **The prior curves on the wire**: at most 16, keys of at most 64 characters, no key twice,
each curve `curveOk`. -/
def priorOk (p : List (List Char × List Step)) : Bool :=
  decide (p.length ≤ maxCurves) && p.all (fun e => decide (e.1.length ≤ maxCurveKey)) &&
    decide (p.map Prod.fst).Nodup && p.all (fun e => curveOk e.2)

/-- **A learned curve on the wire** (fork `model.json` `energy.<loc>`): exactly 12 entries, each a
`u8`. -/
def energyOk (c : List Nat) : Bool := c.length == 12 && c.all (fun n => decide (n < 256))

/-- `[location] home_max_ci`: a level. -/
def homeMaxOk (n : Nat) : Bool := decide (n ≤ 5)

/-- The curves `predict` reads, as the wire may carry them: the prior curves `priorOk`, and the
learned curves at most one `lounge` and one `home`, each `energyOk`. -/
def Curves.wf (c : Curves) : Bool :=
  priorOk c.prior && decide (c.energy.map Prod.fst).Nodup &&
    c.energy.all (fun e => (e.1 == loungeKey || e.1 == homeKey) && energyOk e.2)

/-- Every §13.6 bound `mkInput?` does not check. -/
def InputIn.boundsWf (x : InputIn) : Bool := x.curves.wf && homeMaxOk x.homeMax && x.day.wf

theorem curveOk_refuses_too_many_ranges {steps : List Step} (h : maxCurveSteps < steps.length) :
    curveOk steps = false := by
  simp [curveOk]; omega

theorem curveOk_refuses_a_bad_range {steps : List Step} {s : Step} (hs : s ∈ steps) (h : s.wf = false) :
    curveOk steps = false := by
  have : steps.all Step.wf = false := by
    rw [List.all_eq_false]; exact ⟨s, hs, by simp [h]⟩
  simp [curveOk, this]

theorem curveOk_refuses_an_unsorted_curve {a b : Step} {t : List Step} (h : fromLe a b = false) :
    curveOk (a :: b :: t) = false := by
  simp [curveOk, sortedFrom, h]

theorem priorOk_refuses_too_many_curves {p : List (List Char × List Step)} (h : maxCurves < p.length) :
    priorOk p = false := by
  simp [priorOk]; omega

theorem priorOk_refuses_a_long_key {p : List (List Char × List Step)} {e : List Char × List Step}
    (he : e ∈ p) (h : maxCurveKey < e.1.length) : priorOk p = false := by
  have : p.all (fun e => decide (e.1.length ≤ maxCurveKey)) = false := by
    rw [List.all_eq_false]; exact ⟨e, he, by simp; omega⟩
  simp [priorOk, this]

theorem priorOk_refuses_a_key_twice {p : List (List Char × List Step)} (h : ¬ (p.map Prod.fst).Nodup) :
    priorOk p = false := by
  simp [priorOk, h]

theorem priorOk_refuses_a_bad_curve {p : List (List Char × List Step)} {e : List Char × List Step}
    (he : e ∈ p) (h : curveOk e.2 = false) : priorOk p = false := by
  have : p.all (fun e => curveOk e.2) = false := by
    rw [List.all_eq_false]; exact ⟨e, he, by simp [h]⟩
  simp [priorOk, this]

theorem energyOk_refuses_a_curve_not_of_12 {c : List Nat} (h : c.length ≠ 12) : energyOk c = false := by
  simp [energyOk, h]

theorem energyOk_refuses_an_entry_past_a_byte {c : List Nat} {n : Nat} (hn : n ∈ c) (h : 256 ≤ n) :
    energyOk c = false := by
  have : c.all (fun n => decide (n < 256)) = false := by
    rw [List.all_eq_false]; exact ⟨n, hn, by simp; omega⟩
  simp [energyOk, this]

theorem homeMaxOk_iff (n : Nat) : homeMaxOk n = true ↔ n ≤ 5 := by simp [homeMaxOk]

/-- **R10's width for `stepAt` and `curveKeyLt`** (rule D9-21): an accepted prior's walks are over
at most 16 curves, 64 ranges and 64 key characters. -/
theorem priorOk_widths {p : List (List Char × List Step)} (h : priorOk p = true) :
    p.length ≤ maxCurves ∧ ∀ e ∈ p, e.1.length ≤ maxCurveKey ∧ e.2.length ≤ maxCurveSteps := by
  simp only [priorOk, curveOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, fun e he => ⟨h.1.1.2 e he, (h.2 e he).1.1⟩⟩

/-- **Exact against the fork on an accepted curve** (L4's domain): every key of every accepted
range has a denominator of at most `10^6`, where L4's range comparisons are the fork's `f64` ones. -/
theorem priorOk_keys_in_the_exact_domain {p : List (List Char × List Step)} (h : priorOk p = true)
    {e : List Char × List Step} (he : e ∈ p) {s : Step} (hs : s ∈ e.2) :
    s.fromDen ≤ maxKeyDen ∧ ∀ n d, s.toKey = some (n, d) → d ≤ maxKeyDen := by
  simp only [priorOk, curveOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have hw := (h.2 e he).1.2 s hs
  obtain ⟨fn, fd, t, l⟩ := s
  cases t with
  | none =>
    simp only [Step.wf, rangeOk, keyOk, Bool.and_eq_true, decide_eq_true_eq] at hw
    exact ⟨hw.1.2.1, fun _ _ h => by cases h⟩
  | some p =>
    obtain ⟨n, d⟩ := p
    simp only [Step.wf, rangeOk, keyOk, Bool.and_eq_true, decide_eq_true_eq] at hw
    refine ⟨hw.1.1.1.2.1, fun n' d' h' => ?_⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨-, rfl⟩ := h'
    exact hw.1.1.2.2.1

/-- The shipped `[day]`, curves and `home_max_ci` are accepted. -/
theorem the_shipped_bounds_hold :
    DayCfg.shipped.wf = true ∧ Curves.shipped.wf = true ∧ Curves.fixture.wf = true ∧ homeMaxOk 3 = true := by
  decide

/-! ############################################################################
## The grants (stage 5 D10 step L8, kernel half; design §13.6, §13.8; gaps 80 and 107)

Fork-point `priority::compute` over the lookahead: which candidates enter §7.3's EDF pass (gap 80),
step 3's pass over their deadlines at `capDen` (gap 107), §7.1's bin at each grant's exact
availability, and §7.2's row and `p` after §7.4's hysteresis, one answer per candidate in request
order.  The configuration decoded at L6 is used here: the ladder (`binAt`), the safety (R1's `needMin`
and the bin's scaled need) and `default_priority` (`Cand.kOf`).

* **Which enter** (`Cand.enters`, `entering`): not a wall, not optional, no placement window, and an
  effective due; overdue candidates included.  `grantAt_none_of_not_enters` and
  `grantAt_some_of_enters` are the two directions.
* **The served order** (`sortDueIx`) is step 3's `sortDue` with each deadline's position carried
  alongside (`sortDueIx_snd`), so the grants are `edfGrants` itself (`servedGrants_are_the_pass`), and
  every EDF theorem of `Capacity.lean` applies to them unchanged.  Ties on one date keep request order
  (parity P12: the fork orders a date's deadlines by time of day, then line).
* **The bin** is `binOfScaledQ` of `remaining × safety` against the grant's availability over `capDen`
  (P7), HOT (`u ≥ 1`) at the bin; the reported shortfall is the grant's `need − avail` when HOT, as fork
  `shortfall_min` is, and IMPOSSIBLE is HOT with a shortfall.
* **Not here, by name**: the floor pass (gap 79), and the candidates' facts, which the host collects
  (gap 113).

The recursion rule (D9-21): the candidates are at most 1,024 (the wire's guard); `entering` is core's
`zipIdx` and `filterMap`, `sortDueIx` an insertion sort over the guarded list, `grantAt` core's
`find?`, and the pass is step 3's `edfGrantsGo`, compiled as a `foldl` (`edfGrantsGo_eq_edfGrantsGoFast`).
-/

open Arith

/-! ### A candidate, and which enter the pass (gap 80) -/

/-- **§7's inputs of one candidate**: fork `priority::Candidate`, the fields `priority::compute`
reads, as the host collected them (gap 113).  `rootPrio` is the root's written `!k` (fork
`Item::priority` on `Tree::root`), so `default_priority` is applied here (`Cand.kOf`);
`remaining` is the candidate's minutes (fork `remaining_min`), and the need is R1's ceiling of
`remaining × safety` (P3); `due` is the local date of the effective due (fork
`effective_due.date_naive()`); `window` is fork `window.is_some()`, and `optional` fork
`is_optional`. -/
structure Cand where
  id        : List Char
  ci        : Fin 6
  rootPrio  : Option (Fin 4)
  remaining : Nat
  due       : Option Day
  window    : Bool
  wall      : Bool
  optional  : Bool
  overdue   : Bool
  mandatory : Bool
  hot       : Bool
  yesterday : Option (Fin 8)
deriving DecidableEq, Repr

/-- **Gap 80, fork `priority::compute`'s filter**: a candidate enters the EDF pass when it is not a
wall, not optional, has no placement window, and has an effective due; overdue candidates
included. -/
def Cand.enters (c : Cand) : Bool := !c.wall && !c.optional && !c.window && c.due.isSome

/-- The deadline an entering candidate reserves for: R1's ceiling of its remaining × safety, its
`ci`, its due date. -/
def Cand.deadlineAt (s : Pos) (c : Cand) (due : Day) : Deadline := ⟨needMin s c.remaining, c.ci, due⟩

/-- One candidate, with its position in the request, as the pass sees it. -/
def enterOf (s : Pos) (x : Cand × Nat) : Option (Nat × Deadline) :=
  if !x.1.wall && !x.1.optional && !x.1.window then x.1.due.map (fun d => (x.2, x.1.deadlineAt s d))
  else none

/-- The entering candidates' deadlines, in request order, each with its position. -/
def entering (s : Pos) (cs : List Cand) : List (Nat × Deadline) := cs.zipIdx.filterMap (enterOf s)

theorem enterOf_eq_some {s : Pos} {c : Cand} {i j : Nat} {d : Deadline} :
    enterOf s (c, j) = some (i, d) ↔ j = i ∧ c.enters = true ∧ ∃ due, c.due = some due ∧ d = c.deadlineAt s due := by
  unfold enterOf Cand.enters
  cases hd : c.due with
  | none => simp
  | some due =>
    by_cases hf : (!c.wall && !c.optional && !c.window) = true
    · simp only [hf, ↓reduceIte, Option.map_some, Option.some.injEq, Prod.mk.injEq, Option.isSome_some,
        Bool.and_true, true_and]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, due, rfl, h2.symm⟩
      · rintro ⟨h1, _, rfl, h4⟩; exact ⟨h1, h4.symm⟩
    · simp only [Bool.not_eq_true] at hf
      simp [hf]

/-- **Who is in the pass**: a position and a deadline are entering exactly when the candidate at that
position enters and the deadline is its own. -/
theorem mem_entering {s : Pos} {cs : List Cand} {i : Nat} {d : Deadline} :
    (i, d) ∈ entering s cs ↔
      ∃ c due, cs[i]? = some c ∧ c.enters = true ∧ c.due = some due ∧ d = c.deadlineAt s due := by
  unfold entering
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨c, j⟩, hm, he⟩
    obtain ⟨rfl, hen, due, hdue, rfl⟩ := enterOf_eq_some.mp he
    exact ⟨c, due, List.mem_zipIdx_iff_getElem?.mp hm, hen, hdue, rfl⟩
  · rintro ⟨c, due, hc, hen, hdue, rfl⟩
    exact ⟨(c, i), List.mem_zipIdx_iff_getElem?.mpr hc, enterOf_eq_some.mpr ⟨rfl, hen, due, hdue, rfl⟩⟩

/-! ### The served order: `sortDue`, carrying each deadline's position -/

/-- `insertDue`, on positioned deadlines. -/
def insertDueIx (x : Nat × Deadline) : List (Nat × Deadline) → List (Nat × Deadline)
  | []      => [x]
  | y :: ys => if x.2.due ≤ y.2.due then x :: y :: ys else y :: insertDueIx x ys

/-- `sortDue`, on positioned deadlines: by due, stable. -/
def sortDueIx : List (Nat × Deadline) → List (Nat × Deadline)
  | []      => []
  | x :: xs => insertDueIx x (sortDueIx xs)

theorem insertDueIx_snd (x : Nat × Deadline) :
    ∀ ys : List (Nat × Deadline), (insertDueIx x ys).map Prod.snd = insertDue x.2 (ys.map Prod.snd)
  | [] => rfl
  | y :: ys => by
    have ih := insertDueIx_snd x ys
    by_cases h : x.2.due ≤ y.2.due
    · simp [insertDueIx, insertDue, h]
    · simp [insertDueIx, insertDue, h, ih]

/-- **The served order is step 3's `sortDue`**, positions carried alongside. -/
theorem sortDueIx_snd : ∀ xs : List (Nat × Deadline), (sortDueIx xs).map Prod.snd = sortDue (xs.map Prod.snd)
  | [] => rfl
  | x :: xs => by
    simp only [sortDueIx, List.map_cons, sortDue, insertDueIx_snd, sortDueIx_snd xs]

theorem perm_insertDueIx (x : Nat × Deadline) :
    ∀ ys : List (Nat × Deadline), List.Perm (insertDueIx x ys) (x :: ys)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertDueIx
    split
    · exact List.Perm.refl _
    · exact ((perm_insertDueIx x ys).cons y).trans (List.Perm.swap x y ys)

theorem sortDueIx_perm : ∀ xs : List (Nat × Deadline), List.Perm (sortDueIx xs) xs
  | [] => List.Perm.refl _
  | x :: xs => (perm_insertDueIx x (sortDueIx xs)).trans ((sortDueIx_perm xs).cons x)

/-- The served order of a request's candidates. -/
def servedOrder (s : Pos) (cs : List Cand) : List (Nat × Deadline) := sortDueIx (entering s cs)

/-- Step 3's grants over a served order, each tagged with its candidate's position. -/
def tagGrants (caps : List DayCapacity) (srv : List (Nat × Deadline)) : List (Nat × Grant) :=
  (srv.map Prod.fst).zip (edfGrantsGo capDen caps (srv.map Prod.snd))

/-- **The pass over a request's candidates** (gap 107): step 3's `edfGrants` over the entering
candidates' deadlines, each grant tagged with its candidate's position. -/
def servedGrants (s : Pos) (caps : List DayCapacity) (cs : List Cand) : List (Nat × Grant) :=
  tagGrants caps (servedOrder s cs)

theorem edfGrantsGo_length (den : Nat) (caps : List DayCapacity) (ds : List Deadline) :
    (edfGrantsGo den caps ds).length = ds.length := by
  have := congrArg List.length (edfGrantsGo_deadlines den caps ds)
  rwa [List.length_map] at this

theorem tagGrants_snd (caps : List DayCapacity) (srv : List (Nat × Deadline)) :
    (tagGrants caps srv).map Prod.snd = edfGrantsGo capDen caps (srv.map Prod.snd) := by
  unfold tagGrants
  apply List.map_snd_zip
  simp [edfGrantsGo_length]

/-- **The grants are step 3's pass** (gap 107): in served order, the grants the response carries
are `edfGrants` at `capDen` over the entering candidates' deadlines, listed in request order. -/
theorem servedGrants_are_the_pass (s : Pos) (caps : List DayCapacity) (cs : List Cand) :
    (servedGrants s caps cs).map Prod.snd = edfGrants capDenD caps ((entering s cs).map Prod.snd) := by
  unfold servedGrants servedOrder
  rw [tagGrants_snd, sortDueIx_snd]
  rfl

/-- A candidate's grant: the one tagged with its position. -/
def grantAt (served : List (Nat × Grant)) (i : Nat) : Option Grant :=
  (served.find? (fun p => p.1 == i)).map Prod.snd

/-- **The grant a candidate carries is the pass's grant at the position its deadline is served**,
and that grant is for the deadline served there. -/
theorem grantAt_servedGrants {s : Pos} {caps : List DayCapacity} {cs : List Cand} {i : Nat} {g : Grant}
    (h : grantAt (servedGrants s caps cs) i = some g) :
    ∃ (j : Nat) (d : Deadline), (servedOrder s cs)[j]? = some (i, d) ∧
      (edfGrants capDenD caps ((entering s cs).map Prod.snd))[j]? = some g ∧ g.deadline = d := by
  unfold grantAt at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hpi, j, hj, hjp, -⟩ := List.find?_eq_some_iff_getElem.mp hp
  have hz : (servedGrants s caps cs)[j]? = some p := by rw [List.getElem?_eq_getElem hj, hjp]
  unfold servedGrants tagGrants at hz
  obtain ⟨h1, h2⟩ := List.getElem?_zip_eq_some.mp hz
  rw [List.getElem?_map] at h1
  obtain ⟨⟨i', d⟩, hsrv, hi'⟩ := Option.map_eq_some_iff.mp h1
  simp only [beq_iff_eq] at hpi
  simp only at hi'
  subst hi'
  have hg : (edfGrants capDenD caps ((entering s cs).map Prod.snd))[j]? = some p.2 := by
    have e : edfGrants capDenD caps ((entering s cs).map Prod.snd)
        = edfGrantsGo capDen caps ((servedOrder s cs).map Prod.snd) := by
      unfold servedOrder; rw [sortDueIx_snd]; rfl
    rw [e]; exact h2
  refine ⟨j, d, by rw [hsrv, hpi], hg, ?_⟩
  have hd := congrArg (fun l => l[j]?) (edfGrantsGo_deadlines capDen caps ((servedOrder s cs).map Prod.snd))
  simp only [List.getElem?_map, h2, hsrv, Option.map_some] at hd
  exact Option.some.inj hd

/-- **Gap 80, one direction: a candidate that does not enter reserves nothing** (a wall, an
optional, a window instance, an undated candidate). -/
theorem grantAt_none_of_not_enters {s : Pos} {caps : List DayCapacity} {cs : List Cand} {i : Nat}
    {c : Cand} (hc : cs[i]? = some c) (hn : c.enters = false) :
    grantAt (servedGrants s caps cs) i = none := by
  cases hg : grantAt (servedGrants s caps cs) i with
  | none => rfl
  | some g =>
    obtain ⟨j, d, hsrv, -, -⟩ := grantAt_servedGrants hg
    have hm : (i, d) ∈ entering s cs :=
      (sortDueIx_perm _).mem_iff.mp (List.mem_of_getElem? hsrv)
    obtain ⟨c', _, hc', hen, -⟩ := mem_entering.mp hm
    rw [hc] at hc'
    cases hc'
    rw [hn] at hen
    cases hen

/-- **Gap 80, the other direction: a candidate that enters carries a grant**, and it is the grant
for its own deadline. -/
theorem grantAt_some_of_enters {s : Pos} {caps : List DayCapacity} {cs : List Cand} {i : Nat}
    {c : Cand} (hc : cs[i]? = some c) (he : c.enters = true) :
    ∃ g due, grantAt (servedGrants s caps cs) i = some g ∧ c.due = some due ∧ g.deadline = c.deadlineAt s due := by
  obtain ⟨due, hdue⟩ : ∃ due, c.due = some due := by
    unfold Cand.enters at he
    simp only [Bool.and_eq_true] at he
    exact Option.isSome_iff_exists.mp he.2
  have hm : (i, c.deadlineAt s due) ∈ servedOrder s cs :=
    (sortDueIx_perm _).mem_iff.mpr (mem_entering.mpr ⟨c, due, hc, he, hdue, rfl⟩)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  have hlen : j < (edfGrantsGo capDen caps ((servedOrder s cs).map Prod.snd)).length := by
    rw [edfGrantsGo_length, List.length_map]
    exact (List.getElem?_eq_some_iff.mp hj).1
  have hz : (servedGrants s caps cs)[j]? =
      some (i, (edfGrantsGo capDen caps ((servedOrder s cs).map Prod.snd))[j]) := by
    unfold servedGrants tagGrants
    rw [List.getElem?_zip_eq_some]
    exact ⟨by rw [List.getElem?_map, hj]; rfl, List.getElem?_eq_getElem hlen⟩
  have hsome : (grantAt (servedGrants s caps cs) i).isSome = true := by
    unfold grantAt
    rw [Option.isSome_map, List.find?_isSome]
    exact ⟨_, List.mem_of_getElem? hz, by simp⟩
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨j', d, hsrv, -, hgd⟩ := grantAt_servedGrants hg
  have hm' : (i, d) ∈ entering s cs := (sortDueIx_perm _).mem_iff.mp (List.mem_of_getElem? hsrv)
  obtain ⟨c', due', hc', -, hdue', rfl⟩ := mem_entering.mp hm'
  rw [hc] at hc'
  cases hc'
  rw [hdue] at hdue'
  cases hdue'
  exact ⟨g, due, hg, hdue, hgd⟩

/-! ### Each candidate's answer: the grant, §7.1's bin, §7.2's row and `p` -/

/-- `k`: the root's written `!k`, else `default_priority` (fork `Tree::root_priority`), `1..4`. -/
def Cand.kOf (dflt : Fin 4) (c : Cand) : Nat := (c.rootPrio.getD dflt).val + 1

/-- What §7.2 reads off a candidate, with the pass's bin. -/
def Cand.rule (c : Cand) (pass : Option Bin) : RuleIn :=
  ⟨c.wall, c.optional, c.overdue, c.mandatory, c.hot, pass⟩

/-- **§7.1's bin at a grant** (design §13.1): `remaining × safety` against the grant's exact
availability over `capDen`, never rounded (P7). -/
def binAt (bins : Bins) (s : Pos) (c : Cand) (g : Grant) : Bin :=
  binOfScaledQ bins.val s c.remaining (g.availQ capDenD)

/-- One candidate's answer. -/
structure CandOut where
  cand  : Cand
  k     : Nat
  need  : Nat
  grant : Option Grant
  bin   : Option Bin
  row   : PrioRow
  raw   : Option Nat
  p     : Option Nat

/-- The answer for the candidate at position `x.2`. -/
def candOut (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool) (served : List (Nat × Grant))
    (x : Cand × Nat) : CandOut :=
  let g := grantAt served x.2
  let b := g.map (binAt bins s x.1)
  ⟨x.1, x.1.kOf dflt, if x.1.wall then 0 else needMin s x.1.remaining, g, b, rowOf (x.1.rule b),
    rawPrio (x.1.kOf dflt) (x.1.rule b), finalPrio hyst x.1.yesterday (x.1.kOf dflt) (x.1.rule b)⟩

/-- **Fork `priority::compute`, without the floor pass (gap 79)**: one answer per candidate, in
request order, over the lookahead `caps`. -/
def priorities (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool) (caps : List DayCapacity)
    (cs : List Cand) : List CandOut :=
  cs.zipIdx.map (candOut bins s dflt hyst (servedGrants s caps cs))

/-- The shortfall a candidate reports: fork `shortfall_min`, set only when the pass is HOT. -/
def CandOut.shortfall (o : CandOut) : Nat :=
  match o.grant, o.bin with
  | some g, some .hot => g.shortfall capDen
  | _, _ => 0

/-- Fork `PrioClass`, without `floor` (gap 79). -/
inductive PClass where
  | wall | hot | impossible | overdue | mandatory | hotFlag | dated | rank | optional
deriving DecidableEq, Repr

/-- Which line of §7.2 answered, HOT split by its shortfall (fork `priority::compute`). -/
def CandOut.cls (o : CandOut) : PClass :=
  match o.row with
  | .wall => .wall
  | .optional => .optional
  | .overdue => .overdue
  | .mandatory => .mandatory
  | .hotFlag => .hotFlag
  | .pressure .hot => if 0 < o.shortfall then .impossible else .hot
  | .pressure (.plus _) => .dated
  | .rank => .rank

theorem priorities_length (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool) (caps : List DayCapacity)
    (cs : List Cand) : (priorities bins s dflt hyst caps cs).length = cs.length := by
  simp [priorities]

theorem priorities_getElem? (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool) (caps : List DayCapacity)
    (cs : List Cand) (i : Nat) :
    (priorities bins s dflt hyst caps cs)[i]? = cs[i]?.map (fun c => candOut bins s dflt hyst (servedGrants s caps cs) (c, i)) := by
  simp [priorities, List.getElem?_zipIdx, Function.comp_def]

/-- **Gap 80 on the answer, both directions**: the answer at a position carries a grant exactly when
its candidate enters the pass, and then the grant is for the candidate's own deadline, its bin is
§7.1's at the grant's availability, and its row reads that bin. -/
theorem an_answer_carries_a_grant_iff_its_candidate_enters (bins : Bins) (s : Pos) (dflt : Fin 4)
    (hyst : Bool) (caps : List DayCapacity) (cs : List Cand) {i : Nat} {c : Cand} {o : CandOut}
    (hc : cs[i]? = some c) (ho : (priorities bins s dflt hyst caps cs)[i]? = some o) :
    o.cand = c ∧ (o.grant.isSome = c.enters) ∧
      (∀ g, o.grant = some g → ∃ due, c.due = some due ∧ g.deadline = c.deadlineAt s due ∧
        o.bin = some (binAt bins s c g) ∧ o.row = rowOf (c.rule (some (binAt bins s c g)))) := by
  rw [priorities_getElem?, hc, Option.map_some, Option.some.injEq] at ho
  subst ho
  refine ⟨rfl, ?_, ?_⟩
  · cases he : c.enters
    · simp [candOut, grantAt_none_of_not_enters hc he]
    · obtain ⟨g, _, hg, -⟩ := grantAt_some_of_enters (s := s) (caps := caps) hc he
      simp [candOut, hg]
  · intro g hg
    simp only [candOut] at hg
    cases he : c.enters
    · rw [grantAt_none_of_not_enters hc he] at hg; cases hg
    · obtain ⟨g', due, hg', hdue, hd⟩ := grantAt_some_of_enters (s := s) (caps := caps) hc he
      rw [hg'] at hg
      cases hg
      exact ⟨due, hdue, hd, by simp [candOut, hg'], by simp [candOut, hg']⟩

/-- **Every grant on the answer is §7.3's**: it reserved `min(need, avail)` in units over `capDen`,
and the shortfall it reports is `need − avail` (fork `shortfall_min`), whenever the pass is HOT. -/
theorem an_answers_grant_reserves_the_min (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool)
    (caps : List DayCapacity) (cs : List Cand) {i : Nat} {o : CandOut} {g : Grant}
    (ho : (priorities bins s dflt hyst caps cs)[i]? = some o) (hg : o.grant = some g) :
    g.reserved = min (g.deadline.need * capDen) g.avail ∧
      o.shortfall = (if o.bin = some .hot then g.deadline.need * capDen - g.avail else 0) := by
  rw [priorities_getElem?] at ho
  obtain ⟨c, _, rfl⟩ := Option.map_eq_some_iff.mp ho
  simp only [candOut] at hg
  obtain ⟨j, d, -, hj, -⟩ := grantAt_servedGrants hg
  have hmem := List.mem_of_getElem? hj
  have hmin := edf_reserves_the_min capDenD caps _ g hmem
  have hsh : g.shortfall capDen = g.deadline.need * capDen - g.avail :=
    edf_shortfall_is_need_minus_avail capDenD caps _ g hmem
  refine ⟨hmin, ?_⟩
  unfold CandOut.shortfall
  simp only [candOut, hg, Option.map_some]
  split <;> simp_all

/-- **A wall is off the scale, and only a wall**: `p` is absent exactly for walls (fork `Prio::wall`). -/
theorem an_answer_is_off_the_scale_iff_a_wall (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool)
    (caps : List DayCapacity) (cs : List Cand) {i : Nat} {o : CandOut}
    (ho : (priorities bins s dflt hyst caps cs)[i]? = some o) : o.p = none ↔ o.cand.wall = true := by
  rw [priorities_getElem?] at ho
  obtain ⟨c, _, rfl⟩ := Option.map_eq_some_iff.mp ho
  simp only [candOut, finalPrio, Option.map_eq_none_iff]
  exact rawPrio_isNone_iff _ _

/-- §7.2's HOT row is `p = 0` after §7.4. -/
theorem finalPrio_of_pressure_hot (en : Bool) (y : Option (Fin 8)) (k : Nat) (r : RuleIn)
    (h : rowOf r = .pressure .hot) : finalPrio en y k r = some 0 := by
  simp only [finalPrio, rawPrio, h, rowTable, PVal.eval, Option.map_some, prio_of_hot_is_zero,
    applyHysteresis_zero, ite_self]

/-- **HOT and IMPOSSIBLE are `p = 0`, whatever yesterday was** (§7.2, §7.4's exception), and an
IMPOSSIBLE answer reports a shortfall. -/
theorem a_hot_answer_is_zero (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool) (caps : List DayCapacity)
    (cs : List Cand) {i : Nat} {o : CandOut} (ho : (priorities bins s dflt hyst caps cs)[i]? = some o)
    (hh : o.cls = .hot ∨ o.cls = .impossible) :
    o.p = some 0 ∧ (o.cls = .impossible → 0 < o.shortfall) := by
  rw [priorities_getElem?] at ho
  obtain ⟨c, _, rfl⟩ := Option.map_eq_some_iff.mp ho
  unfold CandOut.cls at hh ⊢
  split at hh
  · simp at hh
  · simp at hh
  · simp at hh
  · simp at hh
  · simp at hh
  · rename_i hrow
    refine ⟨finalPrio_of_pressure_hot _ _ _ _ hrow, ?_⟩
    intro himp
    by_cases h0 : 0 < (candOut bins s dflt hyst (servedGrants s caps cs) (c, i)).shortfall
    · exact h0
    · simp [h0] at himp
  · simp at hh
  · simp at hh

/-! ### A witness (decided; probed under the 8 GB cap) -/

/-- What a witness pins of an answer: `p`, the class, the need, the grant's availability and
reservation, and the shortfall. -/
structure CandView where
  p         : Option Nat
  cls       : PClass
  need      : Nat
  grant     : Option (Nat × Nat)
  shortfall : Nat
deriving DecidableEq, Repr

def CandOut.view (o : CandOut) : CandView :=
  ⟨o.p, o.cls, o.need, o.grant.map (fun g => (g.avail, g.reserved)), o.shortfall⟩

/-- §16's default ladder, accepted. -/
def defaultBinsV : Bins := ⟨Arith.defaultBins, by decide⟩

/-- Step 3's loaded-plan witness over `capDen`: 60 minutes at level 3 on day 1, 30 on day 2. -/
def witnessCaps : List DayCapacity := [ofHist 1 (histOf [0, 0, 0, 60, 0, 0]), ofHist 2 (histOf [0, 0, 0, 30, 0, 0])]

/-- Five candidates: a wall, `^a2` (45 minutes, due day 2) listed before `^a1` (30 minutes, due
day 1, yesterday at 6), an optional, and an undated one. -/
def witnessCands : List Cand :=
  [⟨['w'], 3, none, 60, some 1, false, true, false, false, false, false, none⟩,
   ⟨['a', '2'], 3, none, 45, some 2, false, false, false, false, false, false, none⟩,
   ⟨['a', '1'], 3, none, 30, some 1, false, false, false, false, false, false, some 6⟩,
   ⟨['o'], 3, none, 20, some 1, false, false, true, false, false, false, none⟩,
   ⟨['r'], 2, some 0, 50, none, false, false, false, false, false, false, none⟩]

/-- **The grants on a witness, in request order.**  The wall and the optional enter nothing; `^a1`
is served first though listed after `^a2`: 60 minutes available, 39 reserved (R1's ceiling of
`30 × 1.3`), `u = 0.65` in the `+0` bin, `p = k + 0 = 3` held at 5 by yesterday's 6.  `^a2` then
sees 51 minutes against a need of 59: IMPOSSIBLE, `p = 0`, 8 minutes short.  The undated one is pure
rank, `k + 2` with its written `!1`. -/
theorem priorities_on_a_witness :
    (priorities defaultBinsV Arith.safety specDefaultPrio true witnessCaps witnessCands).map
        CandOut.view =
      [⟨none, .wall, 0, none, 0⟩,
       ⟨some 0, .impossible, 59, some (51 * capDen, 51 * capDen), 8 * capDen⟩,
       ⟨some 5, .dated, 39, some (60 * capDen, 39 * capDen), 0⟩,
       ⟨some 5, .optional, 26, none, 0⟩,
       ⟨some 3, .rank, 65, none, 0⟩] := by
  decide

/-! ############################################################################
## The floor pass (stage 5 D10 step L8, host half; gap 79)

Fork-point `priority::floor_pass`: a candidate with a `min:` floor that does not enter §7.3's pass is
ranked by §7.2's floor line.  Its need is `(floor − done_this_period) × safety`, and its capacity is
what the pass **left**, at levels `≥ ci`, on every day up to the last date of the floor's period.  A
floor reserves nothing (the fork's deviation 4: two floors of one period are independent claims), and
a candidate that enters the pass is answered by its grant whatever its floor (fork
`edf[i].or(floor)`).  A wall has no floor answer (fork `compute` answers a wall before the floor).

The floor's facts are the host's (gap 113): `left`, the floor's minutes less those done this period
(fork `floor.amount − floor_done_min`, saturating), and `until`, the period's last date (fork
`period_range(per, today).1`).  The need is R1's ceiling (P3), the bin is exact against the capacity
left over `capDen` (P7), and `0/0` is HOT (P2), as for a grant.

* `prioritiesWithFloors` is `priorities` with each answer that has no grant and a floor replaced by
  the floor's answer; `prioritiesWithFloors_without_floors` carries every law of `priorities` to a
  request without floors, and the host's wire answers through it.
* `passLeft_is_edf`: the capacity a floor reads is step 3's `edf` over the entering deadlines.
* `a_floor_reserves_nothing`, `the_pass_wins_over_a_floor`,
  `a_floor_answer_reads_what_the_pass_left` and `an_ungranted_floor_is_answered_at_its_floor` are the
  laws; `a_hot_floor_answer_is_zero` is §7.2's HOT row for a floor.

The recursion rule (D9-21): `prioritiesWithFloors` is core's `map` and `zip` over the guarded
candidate list; `passLeft` is step 3's `edfCaps` (compiled as a `foldl`, gap 106) and the floor's
availability `availUntil` (compiled as a `foldl`).
-/

/-- **A candidate's floor**, as the host collected it (gap 113): the floor's minutes still owed this
period, and the period's last date. -/
structure Floor where
  left : Nat
  last : Day
deriving DecidableEq, Repr

/-- **The capacity the pass leaves**: step 3's pass over the served order of the entering
candidates. -/
def passLeft (s : Pos) (caps : List DayCapacity) (cs : List Cand) : List DayCapacity :=
  edfCaps capDen caps ((servedOrder s cs).map Prod.snd)

/-- **What a floor reads is step 3's `edf`** over the entering candidates' deadlines, in request
order: every `edf` law of `Capacity.lean` describes it. -/
theorem passLeft_is_edf (s : Pos) (caps : List DayCapacity) (cs : List Cand) :
    passLeft s caps cs = edf capDenD caps ((entering s cs).map Prod.snd) := by
  unfold passLeft servedOrder
  rw [sortDueIx_snd]
  rfl

/-- One floor's reading: the floor, R1's ceiling of `left × safety`, and what the pass left up to
`until` at levels `≥ ci`, in units over `capDen`. -/
structure FloorGrant where
  floor : Floor
  need  : Nat
  avail : Nat
deriving DecidableEq, Repr

/-- A floor, read against the capacity the pass left. -/
def floorGrantOf (s : Pos) (left : List DayCapacity) (ci : Fin 6) (f : Floor) : FloorGrant :=
  ⟨f, needMin s f.left, availUntil f.last ci left⟩

/-- **§7.1's bin at a floor**: `left × safety` against the exact availability over `capDen`, never
rounded (P7), as `binAt` is for a grant. -/
def floorBin (bins : Bins) (s : Pos) (g : FloorGrant) : Bin :=
  binOfScaledQ bins.val s g.floor.left (mkPos g.avail capDen capDenD.property)

/-- One answer, with the floor it was answered at when it was. -/
structure FloorOut where
  out   : CandOut
  floor : Option FloorGrant

/-- **An answer and its candidate's floor**: an answer without a grant, not a wall, whose candidate
has a floor is answered at the floor's bin; every other answer is `priorities`' own.  The capacity the
pass left is a `Thunk`, forced only by a floor answer and then once for the whole request (an
argument evaluated per candidate cost 1,024 passes over 3,660 days: 705 s of `stack.rs`). -/
def withFloor (bins : Bins) (s : Pos) (hyst : Bool) (left : Thunk (List DayCapacity)) (o : CandOut)
    (f : Option Floor) : FloorOut :=
  match o.grant, f with
  | none, some fl =>
    if o.cand.wall then ⟨o, none⟩
    else
      let g := floorGrantOf s left.get o.cand.ci fl
      let b := floorBin bins s g
      ⟨⟨o.cand, o.k, g.need, none, some b, rowOf (o.cand.rule (some b)),
        rawPrio o.k (o.cand.rule (some b)), finalPrio hyst o.cand.yesterday o.k (o.cand.rule (some b))⟩,
        some g⟩
  | _, _ => ⟨o, none⟩

/-- **Fork `priority::compute`, the floor pass included** (gap 79): one answer per candidate, in
request order, each candidate carrying its floor.  The pass is `priorities`' over the candidates;
a floor reads what it left. -/
def floorAll (bins : Bins) (s : Pos) (hyst : Bool) (left : Thunk (List DayCapacity))
    (ps : List (CandOut × Option Floor)) : List FloorOut :=
  ps.map (fun p => withFloor bins s hyst left p.1 p.2)

def prioritiesWithFloors (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool) (caps : List DayCapacity)
    (cfs : List (Cand × Option Floor)) : List FloorOut :=
  floorAll bins s hyst (Thunk.mk (fun _ => passLeft s caps (cfs.map Prod.fst)))
    ((priorities bins s dflt hyst caps (cfs.map Prod.fst)).zip (cfs.map Prod.snd))

/-- The shortfall an answer reports: a grant's (`CandOut.shortfall`), or a HOT floor's
`need − avail` (fork `shortfall_min` over the floor pass). -/
def FloorOut.shortfall (o : FloorOut) : Nat :=
  match o.floor, o.out.bin with
  | none, _ => o.out.shortfall
  | some g, some .hot => g.need * capDen - g.avail
  | some _, _ => 0

/-- Which line of §7.2 answered, HOT split by the answer's shortfall; a floor's `+n` row is still
`dated` here, and the wire names it `floor` (fork `PrioClass::Floor`). -/
def FloorOut.cls (o : FloorOut) : PClass :=
  match o.floor, o.out.row with
  | some _, .pressure .hot => if 0 < o.shortfall then .impossible else .hot
  | _, _ => o.out.cls

theorem prioritiesWithFloors_length (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool)
    (caps : List DayCapacity) (cfs : List (Cand × Option Floor)) :
    (prioritiesWithFloors bins s dflt hyst caps cfs).length = cfs.length := by
  simp [prioritiesWithFloors, floorAll, priorities_length]

theorem prioritiesWithFloors_getElem? (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool)
    (caps : List DayCapacity) (cfs : List (Cand × Option Floor)) (i : Nat) :
    (prioritiesWithFloors bins s dflt hyst caps cfs)[i]? =
      ((priorities bins s dflt hyst caps (cfs.map Prod.fst))[i]?).bind (fun o =>
        (cfs[i]?).map (fun cf => withFloor bins s hyst (Thunk.mk (fun _ => passLeft s caps (cfs.map Prod.fst))) o cf.2)) := by
  unfold prioritiesWithFloors floorAll
  rw [List.getElem?_map, List.zip_eq_zipWith, List.getElem?_zipWith, List.getElem?_map]
  cases (priorities bins s dflt hyst caps (cfs.map Prod.fst))[i]? <;> cases cfs[i]? <;> rfl

/-- The candidate list is as long as the answers. -/
theorem lt_of_priorities_getElem? {bins : Bins} {s : Pos} {dflt : Fin 4} {hyst : Bool}
    {caps : List DayCapacity} {cfs : List (Cand × Option Floor)} {i : Nat} {o : CandOut}
    (ho : (priorities bins s dflt hyst caps (cfs.map Prod.fst))[i]? = some o) : i < cfs.length := by
  have := (List.getElem?_eq_some_iff.mp ho).1
  simpa [priorities_length] using this

/-- **Without floors, the answers are `priorities`' own**: every law of `priorities` holds of the wire's
answers to a request whose candidates carry no floor. -/
theorem prioritiesWithFloors_without_floors (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool)
    (caps : List DayCapacity) (cfs : List (Cand × Option Floor)) (h : ∀ cf ∈ cfs, cf.2 = none) :
    prioritiesWithFloors bins s dflt hyst caps cfs =
      (priorities bins s dflt hyst caps (cfs.map Prod.fst)).map (fun o => ⟨o, none⟩) := by
  apply List.ext_getElem?
  intro i
  rw [prioritiesWithFloors_getElem?, List.getElem?_map]
  cases ho : (priorities bins s dflt hyst caps (cfs.map Prod.fst))[i]? with
  | none => rfl
  | some o =>
    have hl : i < cfs.length := by
      have := (List.getElem?_eq_some_iff.mp ho).1
      simpa [priorities_length] using this
    have hn : cfs[i].2 = none := h _ (List.getElem_mem hl)
    simp only [Option.bind_some, List.getElem?_eq_getElem hl, Option.map_some]
    unfold withFloor
    rw [hn]
    cases o.grant <;> rfl

/-- **A floor reserves nothing** (the fork's deviation 4): every candidate's grant, floors or not, is
the grant `priorities` gives it over the same candidates. -/
theorem a_floor_reserves_nothing (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool)
    (caps : List DayCapacity) (cfs : List (Cand × Option Floor)) :
    (prioritiesWithFloors bins s dflt hyst caps cfs).map (·.out.grant) =
      (priorities bins s dflt hyst caps (cfs.map Prod.fst)).map (·.grant) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, List.getElem?_map, prioritiesWithFloors_getElem?]
  cases ho : (priorities bins s dflt hyst caps (cfs.map Prod.fst))[i]? with
  | none => rfl
  | some o =>
    have hl := lt_of_priorities_getElem? ho
    rw [List.getElem?_eq_getElem hl]
    simp only [Option.bind_some, Option.map_some, Option.some.injEq]
    unfold withFloor
    cases hg : o.grant with
    | some g => simp [hg]
    | none =>
      cases cfs[i].2 with
      | none => simp [hg]
      | some fl => by_cases hw : o.cand.wall <;> simp [hg, hw]

/-- **The pass wins over a floor**: a candidate that enters the pass is answered by its grant, exactly
as `priorities` answers it, and carries no floor answer. -/
theorem the_pass_wins_over_a_floor (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool)
    (caps : List DayCapacity) (cfs : List (Cand × Option Floor)) {i : Nat} {c : Cand} {f : Option Floor}
    (hc : cfs[i]? = some (c, f)) (he : c.enters = true) :
    (prioritiesWithFloors bins s dflt hyst caps cfs)[i]? =
      ((priorities bins s dflt hyst caps (cfs.map Prod.fst))[i]?).map (fun o => ⟨o, none⟩) := by
  have hc' : (cfs.map Prod.fst)[i]? = some c := by rw [List.getElem?_map, hc]; rfl
  obtain ⟨g, _, hg, -⟩ := grantAt_some_of_enters (s := s) (caps := caps) hc' he
  rw [prioritiesWithFloors_getElem?, priorities_getElem?, hc', hc]
  simp only [Option.map_some, Option.bind_some, Option.some.injEq]
  unfold withFloor
  simp only [candOut, hg]

/-- **An ungranted floor is answered at its floor** (the other direction): a candidate that does not
enter the pass, is not a wall and has a floor is answered at that floor. -/
theorem an_ungranted_floor_is_answered_at_its_floor (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool)
    (caps : List DayCapacity) (cfs : List (Cand × Option Floor)) {i : Nat} {c : Cand} {fl : Floor}
    (hc : cfs[i]? = some (c, some fl)) (hn : c.enters = false) (hw : c.wall = false) :
    ∃ o, (prioritiesWithFloors bins s dflt hyst caps cfs)[i]? = some o ∧
      o.floor = some (floorGrantOf s (passLeft s caps (cfs.map Prod.fst)) c.ci fl) := by
  have hc' : (cfs.map Prod.fst)[i]? = some c := by rw [List.getElem?_map, hc]; rfl
  have hg := grantAt_none_of_not_enters (s := s) (caps := caps) hc' hn
  rw [prioritiesWithFloors_getElem?, priorities_getElem?, hc', hc]
  refine ⟨_, rfl, ?_⟩
  unfold withFloor
  simp [candOut, hg, hw] <;> rfl

/-- **A floor answer reads what the pass left**: an answer at a floor is for a candidate that did not
enter the pass and is not a wall; its availability is `availUntil` over step 3's `edf` of the entering
deadlines, up to the floor's last date at the candidate's levels; its need is R1's ceiling of the
floor's remainder; and its bin, row and `p` are §7.1, §7.2 and §7.4 at that availability. -/
theorem a_floor_answer_reads_what_the_pass_left (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool)
    (caps : List DayCapacity) (cfs : List (Cand × Option Floor)) {i : Nat} {o : FloorOut} {g : FloorGrant}
    (ho : (prioritiesWithFloors bins s dflt hyst caps cfs)[i]? = some o) (hg : o.floor = some g) :
    ∃ c, cfs[i]? = some (c, some g.floor) ∧ c.enters = false ∧ c.wall = false ∧
      g.avail = availUntil g.floor.last c.ci (edf capDenD caps ((entering s (cfs.map Prod.fst)).map Prod.snd)) ∧
      g.need = needMin s g.floor.left ∧ o.out.need = g.need ∧ o.out.grant = none ∧
      o.out.bin = some (floorBin bins s g) ∧ o.out.row = rowOf (c.rule (some (floorBin bins s g))) ∧
      o.out.p = finalPrio hyst c.yesterday (c.kOf dflt) (c.rule (some (floorBin bins s g))) := by
  rw [prioritiesWithFloors_getElem?, priorities_getElem?] at ho
  cases hc : cfs[i]? with
  | none =>
    have h0 : (cfs.map Prod.fst)[i]? = none := by rw [List.getElem?_map, hc]; rfl
    rw [h0] at ho; cases ho
  | some cf =>
    obtain ⟨c, f⟩ := cf
    have hc' : (cfs.map Prod.fst)[i]? = some c := by rw [List.getElem?_map, hc]; rfl
    rw [hc', hc] at ho
    simp only [Option.map_some, Option.bind_some, Option.some.injEq] at ho
    subst ho
    cases he : c.enters with
    | true =>
      obtain ⟨g', _, hg', -⟩ := grantAt_some_of_enters (s := s) (caps := caps) hc' he
      simp [withFloor, candOut, hg'] at hg
    | false =>
      have hga := grantAt_none_of_not_enters (s := s) (caps := caps) hc' he
      cases f with
      | none => simp [withFloor, candOut, hga] at hg
      | some fl =>
        cases hw : c.wall with
        | true => simp [withFloor, candOut, hga, hw] at hg
        | false =>
          simp only [withFloor, candOut, hga, hw, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hg
          subst hg
          refine ⟨c, rfl, he, hw, ?_, rfl, ?_⟩
          · simp [floorGrantOf, passLeft_is_edf] <;> rfl
          · simp [withFloor, candOut, hga, hw]

/-- **A HOT floor answer is `p = 0`**, whatever yesterday was, and an IMPOSSIBLE one reports a
shortfall. -/
theorem a_hot_floor_answer_is_zero (bins : Bins) (s : Pos) (dflt : Fin 4) (hyst : Bool)
    (caps : List DayCapacity) (cfs : List (Cand × Option Floor)) {i : Nat} {o : FloorOut}
    (ho : (prioritiesWithFloors bins s dflt hyst caps cfs)[i]? = some o)
    (hh : o.cls = .hot ∨ o.cls = .impossible) :
    o.out.p = some 0 ∧ (o.cls = .impossible → 0 < o.shortfall) := by
  cases hf : o.floor with
  | none =>
    have hcls : o.cls = o.out.cls := by unfold FloorOut.cls; rw [hf]
    have hsh : o.shortfall = o.out.shortfall := by unfold FloorOut.shortfall; rw [hf]
    rw [prioritiesWithFloors_getElem?] at ho
    cases hp : (priorities bins s dflt hyst caps (cfs.map Prod.fst))[i]? with
    | none => rw [hp] at ho; cases ho
    | some o' =>
      rw [hp] at ho
      cases hc : cfs[i]? with
      | none => rw [hc] at ho; cases ho
      | some cf =>
        rw [hc] at ho
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at ho
        have heq : o.out = o' := by
          subst ho
          unfold withFloor at hf ⊢
          revert hf
          cases o'.grant <;> cases cf.2 <;> simp
          all_goals (intro h; split at h <;> simp_all)
        rw [hcls, heq] at hh
        rw [hcls, hsh, heq]
        exact a_hot_answer_is_zero bins s dflt hyst caps (cfs.map Prod.fst) hp hh
  | some g =>
    obtain ⟨c, -, -, -, -, -, -, -, -, hrow, hp⟩ :=
      a_floor_answer_reads_what_the_pass_left bins s dflt hyst caps cfs ho hf
    have hrow' : o.out.row = .pressure .hot := by
      unfold FloorOut.cls at hh
      rw [hf] at hh
      revert hh
      cases hr : o.out.row with
      | pressure b =>
        cases b with
        | hot => intro _; rfl
        | plus n => intro hh; simp [CandOut.cls, hr] at hh
      | _ => intro hh; simp [CandOut.cls, hr] at hh
    refine ⟨?_, ?_⟩
    · rw [hp]
      exact finalPrio_of_pressure_hot _ _ _ _ (by rw [← hrow]; exact hrow')
    · intro himp
      unfold FloorOut.cls at himp
      rw [hf, hrow'] at himp
      by_cases h0 : 0 < o.shortfall
      · exact h0
      · simp [h0] at himp

/-! ### A witness (decided; probed under the 8 GB cap) -/

/-- What a witness pins of an answer with its floor: `p`, the class, the need, the availability and
reservation of the grant or the floor (a floor's allocation is `min(need, avail)` and reserves nothing),
and the shortfall. -/
def FloorOut.view (o : FloorOut) : CandView :=
  ⟨o.out.p, o.cls, o.out.need,
    (o.floor.map (fun g => (g.avail, min (g.need * capDen) g.avail))).or (o.out.grant.map (fun g => (g.avail, g.reserved))),
    o.shortfall⟩

/-- `witnessCands` with floors: on the wall, on `^a1` (which enters the pass), on the optional and on
the undated `^r` (20 minutes owed by day 2). -/
def witnessFloors : List (Cand × Option Floor) :=
  witnessCands.zip [some ⟨10, 2⟩, none, some ⟨30, 1⟩, some ⟨10, 2⟩, some ⟨20, 2⟩]

/-- The witness days with 120 minutes on day 2. -/
def witnessFloorCaps : List DayCapacity :=
  [ofHist 1 (histOf [0, 0, 0, 60, 0, 0]), ofHist 2 (histOf [0, 0, 0, 120, 0, 0])]

/-- **The floor pass over `witnessCaps`**: the pass leaves nothing, so the optional's floor sees 0 (still
`p = 5`, 13 minutes short) and `^r`'s floor of 20 minutes is IMPOSSIBLE, `p = 0`, 26 short; the wall and
`^a1` ignore their floors, and `^a1` and `^a2` keep `priorities_on_a_witness`'s grants.  (Stated as two
projections of `FloorOut.view`: `decide` over the whole `CandView` of a floor answer loops in the
elaborator at any `maxRecDepth`, while each projection decides in well under a second.) -/
theorem prioritiesWithFloors_on_a_witness :
    (prioritiesWithFloors defaultBinsV Arith.safety specDefaultPrio true witnessCaps witnessFloors).map (fun o => (o.view.p, o.view.cls, o.view.need)) =
      [(none, .wall, 0), (some 0, .impossible, 59), (some 5, .dated, 39), (some 5, .optional, 13),
       (some 0, .impossible, 26)] ∧
    (prioritiesWithFloors defaultBinsV Arith.safety specDefaultPrio true witnessCaps witnessFloors).map (fun o => (o.view.grant, o.view.shortfall)) =
      [(none, 0), (some (51 * capDen, 51 * capDen), 8 * capDen), (some (60 * capDen, 39 * capDen), 0),
       (some (0, 0), 13 * capDen), (some (0, 0), 26 * capDen)] := by
  constructor <;> decide

/-- **The floor pass over `witnessFloorCaps`**: `^a2` sees 141 minutes and reserves 59, leaving 82 on
day 2; the optional's floor fits, and `^r`'s need of 26 against 82 is `u ≈ 0.32`, the `+1` bin,
`p = !1 + 1 = 2` (against the 180 minutes before the pass it would be the `+2` bin, `p = 3`; cheat
141). -/
theorem prioritiesWithFloors_on_a_roomier_witness :
    (prioritiesWithFloors defaultBinsV Arith.safety specDefaultPrio true witnessFloorCaps witnessFloors).map (fun o => (o.view.p, o.view.cls, o.view.need)) =
      [(none, .wall, 0), (some 4, .dated, 59), (some 5, .dated, 39), (some 5, .optional, 13), (some 2, .dated, 26)] ∧
    (prioritiesWithFloors defaultBinsV Arith.safety specDefaultPrio true witnessFloorCaps witnessFloors).map (fun o => (o.view.grant, o.view.shortfall)) =
      [(none, 0), (some (141 * capDen, 59 * capDen), 0), (some (60 * capDen, 39 * capDen), 0),
       (some (82 * capDen, 13 * capDen), 0), (some (82 * capDen, 26 * capDen), 0)] := by
  constructor <;> decide

end Look
end Tm
