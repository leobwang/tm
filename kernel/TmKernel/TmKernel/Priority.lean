import TmKernel.Plan
import TmKernel.Arith
/-!
# Priority — §7.1's `p`, §7.2's rule table and §7.4's hysteresis

Fork-point `tm-core/src/priority.rs` is the oracle, read by function name:
`priority::compute` (the §7.2 cascade), `priority::clamp_p`,
`priority::apply_hysteresis`, `priority::bin_of`, `priority::utilization`, and
`Tree::root_priority` for `k`.  Everything here is a function of plain arguments:
no log, no clock, no configuration file.

## What is built

* **`k`** — `rootK p dflt i`: `Tree::root_priority`, the root's written `!k` (`rootPrio`,
  live since D6), else §16's `default_priority`, as a number in `1..4`.  The default
  enters as a `Fin 4` through `defaultPrioOf?`, which refuses `0` and anything above
  `4` (R10).
* **`prio k b`** — §7.2's arithmetic: HOT is `0`, `+n` is `min (k + n) 7`
  (`priority::clamp_p`).  Proved antitone in utilisation on top of Arith's
  `binOf_antitone`.
* **The ladder at a rational availability (D10).**  Capacity is an exact mixture, so
  availability until a deadline is an `Arith.Pos`, never a `Nat`.  `binOfQ` and
  `binOfScaledQ` put a `Nat` need (or `remaining × safety`, R1) against it by
  cross-multiplication: `u ≥ p/q` at `avail = a/b` is `p·a ≤ q·need·b`.  On whole
  minutes they *are* the existing `Nat` forms (`binOfQ_on_whole_minutes`,
  `binOfScaledQ_on_whole_minutes`); they cannot see how the availability was written
  (`binOfQ_congr`, `binOfScaledQ_congr`), which is the fact a later normalisation of the
  EDF pass's growing pairs needs; and gap 25's decision stands: capacity `0` is HOT at
  any need, `0` included (`zero_need_on_zero_capacity_is_hot`).
  `flooring_the_mixture_changes_the_bin` is why nothing is rounded.
* **§7.2's rule table** (`rowOf`, `rowTable`, `rawPrio`, `finalPrio`) — tabulated
  (AGENTS §5.5): which line applies is the fork point's cascade order, derived; what
  each line makes of `p`, and whether hysteresis may hold it, is data, one row per
  constructor so the compiler checks the table is complete.  The bridge theorems
  `rawPrio_of_*` state each row over the inputs, never over the table.
* **§7.4's hysteresis** (`hysteresis`, `applyHysteresis`, `hysteresisDays`).
* **Gap 27's loader check** (`binsOk`, `Bins`, `binsOf?`, `binsOfPairs?`) and the
  configured safety (`safetyOf?`): config rationals arrive as numerator/denominator
  `Nat` pairs through `Arith.ofPair?` (README "Stage 5 step 1"); no `Float`.

## Tiers

`prio`, the table and the ladder are **function laws** (tier: one run, one answer).
**Hysteresis is a relational-ish law and is not in L1..L27** (AGENTS §8.3's named
trap).  Its tier: `hysteresis yesterday raw` is a function of two numbers, where
`yesterday` is a *given input* — the host's `state.json` `priorities_yesterday`
(§10.2), filled by the host from yesterday's output, bounded to `Fin 8` by
`yesterdayOf?` — so its three goals are function laws.  The day-over-day reading
(today's output is tomorrow's `yesterday`) holds only under the host's contract to
store today's `p`, and is stated as a law over iterated days with that contract made
explicit as the recursion (`hysteresisDays`): a steady raw `p` is reached within the gap
and then held (`hysteresis_settles_on_a_steady_priority`), and not a day sooner
(`hysteresis_holds_every_day_of_the_gap`).  One "bin" in §7.4's sentence is one step
of `p`, as in `priority::apply_hysteresis`: while `k` is fixed and nothing clamps, the
two are the same.

## Not here, by name

* **Log-derived inputs are plain arguments** (the owner's D9): `RuleIn.overdue`
  (§5.3's persist), `RuleIn.mandatory` (§5.2's instance, which needs the replayed
  instance status) and `RuleIn.pass` (the EDF or floor pass's bin, which needs the
  lookahead of D10 and, for a floor, the replayed `done_this_period`) are `Bool`s and an
  `Option Bin` the D9/D10 tranche will compute.  No Rust summary format enters.
* **§7.3's EDF pass** — stage 5's next step, over rational minutes.
* **§7.5's batching** needs the sorted candidates, planned minutes (R4, from the
  duration fit) and `block_min`: stage 6's (README gap 76).
-/

namespace Tm

open Arith

/-! ## `k`: §7.1's root priority -/

/-- §16 `default_priority`, decoded: `1..4`, held zero-based like a written `!k`
(`Field.parsePrio`). -/
def defaultPrioOf? (n : Nat) : Option (Fin 4) :=
  if h : 1 ≤ n ∧ n ≤ 4 then some ⟨n - 1, by omega⟩ else none

theorem defaultPrioOf?_refuses_zero : defaultPrioOf? 0 = none := by decide

theorem defaultPrioOf?_refuses_above_four (n : Nat) (h : 4 < n) : defaultPrioOf? n = none := by
  unfold defaultPrioOf?
  rw [dif_neg (by omega)]

/-- The other direction: every `k` §7.1 allows is accepted, and means itself. -/
theorem defaultPrioOf?_accepts (n : Nat) (h1 : 1 ≤ n) (h4 : n ≤ 4) :
    (defaultPrioOf? n).map (fun k => k.val + 1) = some n := by
  unfold defaultPrioOf?
  rw [dif_pos ⟨h1, h4⟩]
  show some (n - 1 + 1) = some n
  congr 1
  omega

/-- §16's shipped `default_priority = 3`. -/
def specDefaultPrio : Fin 4 := ⟨2, by decide⟩

theorem specDefaultPrio_is_three : defaultPrioOf? 3 = some specDefaultPrio := by decide

/-- **§7.1's `k`** — fork-point `Tree::root_priority`: the root's `!k`, else the
configured default, in `1..4`. -/
def rootK (p : PlanCore) (dflt : Fin 4) (i : Id) : Nat := ((rootPrio p i).getD dflt).val + 1

theorem rootK_pos (p : PlanCore) (dflt : Fin 4) (i : Id) : 0 < rootK p dflt i :=
  Nat.succ_pos _

theorem rootK_le_four (p : PlanCore) (dflt : Fin 4) (i : Id) : rootK p dflt i ≤ 4 := by
  have := ((rootPrio p i).getD dflt).isLt
  unfold rootK
  omega

/-- A root's own `!k` is its `k` (`Core.priorityK`, the one-based reading). -/
theorem rootK_of_a_root_with_k (p : PlanCore) (dflt : Fin 4) (i : Id) (e : Entity) (n : Nat)
    (hget : p.store.get i = some e) (hpar : e.val.parent = none)
    (hk : e.val.priorityK = some n) : rootK p dflt i = n := by
  unfold rootK
  rw [rootPrio_of_a_root p i e hget hpar]
  unfold Core.priorityK at hk
  cases hp : e.val.prio with
  | none => rw [hp] at hk; cases hk
  | some k => rw [hp] at hk; cases hk; rfl

/-- A root with no `!k` takes the default. -/
theorem rootK_of_a_root_without_k (p : PlanCore) (dflt : Fin 4) (i : Id) (e : Entity)
    (hget : p.store.get i = some e) (hpar : e.val.parent = none)
    (hk : e.val.prio = none) : rootK p dflt i = dflt.val + 1 := by
  unfold rootK
  rw [rootPrio_of_a_root p i e hget hpar, hk]
  rfl

/-! ## §7.2's arithmetic: `p = k + bin`, HOT at zero, clamped -/

/-- `p = 0` for HOT, else `k + n` clamped to `0..=7` (`priority::clamp_p`). -/
def prio (k : Nat) (b : Arith.Bin) : Nat :=
  match b with
  | .hot    => 0
  | .plus n => min (k + n) 7

theorem prio_plus (k n : Nat) : prio k (.plus n) = min (k + n) 7 := rfl

/-- **§7.2: HOT is `p = 0`, whatever the root priority says.** -/
theorem prio_of_hot_is_zero (k : Nat) : prio k Arith.Bin.hot = 0 := rfl

/-- **§7.2: "clamp p to 0..=7".** -/
theorem prio_is_clamped (k : Nat) (b : Arith.Bin) : prio k b ≤ 7 := by
  cases b with
  | hot => exact Nat.zero_le _
  | plus n => exact Nat.min_le_right _ _

/-- `prio` never undoes the bin's order. -/
theorem prio_mono_ix (k : Nat) {b₁ b₂ : Bin} (h : b₂.ix ≤ b₁.ix) : prio k b₂ ≤ prio k b₁ := by
  cases b₂ with
  | hot => exact Nat.zero_le _
  | plus m =>
    cases b₁ with
    | hot => simp [Bin.ix] at h
    | plus n =>
      simp only [Bin.ix] at h
      simp only [prio]
      omega

/-- **§7.1–7.2: more pressure is never lower priority.** -/
theorem prio_is_antitone_in_utilisation (bins : List Arith.Q) (k n₁ a₁ n₂ a₂ : Nat)
    (hd : Arith.utilDefined n₁ a₁ = true)
    (h : Arith.Q.le (Arith.util n₁ a₁) (Arith.util n₂ a₂) = true) :
    prio k (Arith.binOf bins n₂ a₂) ≤ prio k (Arith.binOf bins n₁ a₁) :=
  prio_mono_ix k (binOf_antitone bins hd h)

/-- **Both directions of the zero:** with `k` in §7.1's `1..4`, `p = 0` is HOT and
nothing else — a `+0` bin never collides with HOT. -/
theorem prio_eq_zero_iff_hot {k : Nat} (hk : 0 < k) (b : Bin) : prio k b = 0 ↔ b = .hot := by
  cases b with
  | hot => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | plus n =>
    constructor
    · intro h
      simp only [prio] at h
      exact absurd h (by omega)
    · intro h
      cases h

/-- With §16's shipped edges and `k ≤ 4` the clamp never fires (`k + 3 ≤ 7`). -/
theorem prio_clamp_is_silent_on_the_default_ladder {k need avail n : Nat} (hk : k ≤ 4)
    (h : binOf defaultBins need avail = .plus n) : prio k (.plus n) = k + n := by
  have := default_bin_le_three need avail n h
  simp only [prio]
  omega

/-- …and it does fire on a longer configured ladder: five edges, `k = 4`, `u = 1/100`
lands on `+5`, and `4 + 5` is held at `7`. -/
theorem prio_clamp_fires_on_a_long_ladder :
    binOf [⟨1, 2⟩, ⟨1, 4⟩, ⟨1, 10⟩, ⟨1, 20⟩, ⟨1, 50⟩] 1 100 = .plus 5 ∧
      prio 4 (.plus 5) = 7 := by decide

/-! ## D10: the ladder at a rational availability

Availability until a deadline is an exact mixture of capacities, so it is an
`Arith.Pos`.  The need stays a `Nat` (or `remaining × safety`, folded in).  Nothing is
divided and nothing rounded: `u = need / (a/b)` is the pair `⟨need·b, a⟩`. -/

/-- §7.1's `u` at a rational availability, as a pair.  Never divided. -/
def utilQ (need : Nat) (avail : Pos) : Q := ⟨need * avail.val.den, avail.val.num⟩

/-- `u ≥ e` at `avail = a/b`: `e.num·a ≤ e.den·need·b`. -/
def utilQGe (need : Nat) (avail : Pos) (e : Q) : Bool :=
  utilGe (need * avail.val.den) avail.val.num e

theorem utilQGe_cross (need : Nat) (avail : Pos) (e : Q) :
    utilQGe need avail e = decide (e.num * avail.val.num ≤ e.den * need * avail.val.den) := by
  simp only [utilQGe, utilGe, Nat.mul_assoc]

theorem utilQGe_eq_le (need : Nat) (avail : Pos) (e : Q) :
    utilQGe need avail e = Q.le e (utilQ need avail) :=
  utilGe_eq_le _ _ _

/-- **Faithfulness.**  The cross-multiplied test is the comparison against
`need / avail` formed for real. -/
theorem utilQGe_is_division (need : Nat) (avail : Pos) (e : Q) :
    utilQGe need avail e = Q.le e (Q.div (ofNat need) avail.val) := by
  simp only [utilQGe, utilGe, Q.le, Q.div, ofNat, Nat.one_mul]
  rw [Nat.mul_comm e.den]

/-- **On whole minutes it is the existing `Nat` form.** -/
theorem utilQGe_on_whole_minutes (need a : Nat) (e : Q) :
    utilQGe need (posOfNat a) e = utilGe need a e := by
  simp only [utilQGe, posOfNat, mkPos_num, mkPos_den, Nat.mul_one]

/-- One cross-multiplied inequality carried from one spelling of a rational to
another. -/
theorem cross_transfer {x y n₁ d₁ n₂ d₂ : Nat} (hd₁ : 0 < d₁) (h : n₁ * d₂ = n₂ * d₁)
    (hle : x * n₁ ≤ y * d₁) : x * n₂ ≤ y * d₂ := by
  refine Nat.le_of_mul_le_mul_right ?_ hd₁
  calc x * n₂ * d₁ = x * (n₁ * d₂) := by rw [Nat.mul_assoc, ← h]
    _ = x * n₁ * d₂ := by rw [Nat.mul_assoc]
    _ ≤ y * d₁ * d₂ := Nat.mul_le_mul_right _ hle
    _ = y * d₂ * d₁ := by rw [Nat.mul_right_comm]

/-- **The comparison cannot see how the availability was written.** -/
theorem utilQGe_congr (need : Nat) {a₁ a₂ : Pos} (h : Q.equiv a₁.val a₂.val = true) (e : Q) :
    utilQGe need a₁ e = utilQGe need a₂ e := by
  simp only [Q.equiv, decide_eq_true_eq] at h
  rw [utilQGe_cross, utilQGe_cross]
  exact decide_eq_decide.mpr
    ⟨cross_transfer (denPos a₁) h, cross_transfer (denPos a₂) h.symm⟩

/-- The same, for a scaled need over a rational availability. -/
theorem utilGe_scaled_pair_congr (x y : Nat) {a₁ a₂ : Pos} (h : Q.equiv a₁.val a₂.val = true)
    (e : Q) :
    utilGe (y * a₁.val.den) (x * a₁.val.num) e = utilGe (y * a₂.val.den) (x * a₂.val.num) e := by
  simp only [Q.equiv, decide_eq_true_eq] at h
  simp only [utilGe, ← Nat.mul_assoc]
  exact decide_eq_decide.mpr
    ⟨cross_transfer (denPos a₁) h, cross_transfer (denPos a₂) h.symm⟩

/-- Two need/availability pairs that reach the same edges sit on the same rung. -/
theorem rungs_eq_of_utilGe_eq (bins : List Q) {n₁ a₁ n₂ a₂ : Nat}
    (h : ∀ e, utilGe n₁ a₁ e = utilGe n₂ a₂ e) : rungs bins n₁ a₁ = rungs bins n₂ a₂ := by
  simp only [rungs, h]

/-- **§7.1's bin at a rational availability.** -/
def binOfQ (bins : List Q) (need : Nat) (avail : Pos) : Bin :=
  binOf bins (need * avail.val.den) avail.val.num

/-- **§7.1's bin for the ordering path (R1): `remaining × safety` against a rational
availability**, the scale folded into the cross-multiplication and never rounded
first. -/
def binOfScaledQ (bins : List Q) (s : Pos) (rem : Nat) (avail : Pos) : Bin :=
  binOf bins (s.val.num * rem * avail.val.den) (s.val.den * avail.val.num)

/-- The scaled test at a rational availability. -/
def utilScaledQGe (s : Pos) (rem : Nat) (avail : Pos) (e : Q) : Bool :=
  utilGe (s.val.num * rem * avail.val.den) (s.val.den * avail.val.num) e

/-- The ladder counts exactly the edges `utilQGe` misses. -/
theorem binOfQ_ix (bins : List Q) (need : Nat) (avail : Pos) :
    (binOfQ bins need avail).ix = (hotEdge :: bins).countP (fun e => ! utilQGe need avail e) :=
  binOf_ix _ _ _

theorem binOfScaledQ_ix (bins : List Q) (s : Pos) (rem : Nat) (avail : Pos) :
    (binOfScaledQ bins s rem avail).ix
      = (hotEdge :: bins).countP (fun e => ! utilScaledQGe s rem avail e) :=
  binOf_ix _ _ _

theorem binOfQ_on_whole_minutes (bins : List Q) (need a : Nat) :
    binOfQ bins need (posOfNat a) = binOf bins need a := by
  simp only [binOfQ, posOfNat, mkPos_num, mkPos_den, Nat.mul_one]

theorem utilScaledQGe_on_whole_minutes (s : Pos) (rem a : Nat) (e : Q) :
    utilScaledQGe s rem (posOfNat a) e = utilScaledGe s rem a e := by
  simp only [utilScaledQGe, utilScaledGe, posOfNat, mkPos_num, mkPos_den, Nat.mul_one]

/-- **On whole minutes the ordering path is Arith's `utilScaledGe` ladder.** -/
theorem binOfScaledQ_on_whole_minutes (bins : List Q) (s : Pos) (rem a : Nat) :
    binOfScaledQ bins s rem (posOfNat a) = binOf bins (s.val.num * rem) (s.val.den * a) := by
  simp only [binOfScaledQ, posOfNat, mkPos_num, mkPos_den, Nat.mul_one]

theorem utilScaledQGe_is_division (s : Pos) (rem : Nat) (avail : Pos) (e : Q) :
    utilScaledQGe s rem avail e = Q.le e (Q.div (Q.mul (ofNat rem) s.val) avail.val) := by
  simp only [utilScaledQGe, utilGe, Q.le, Q.div, Q.mul, ofNat, Nat.one_mul]
  have : e.den * (s.val.num * rem * avail.val.den) = rem * s.val.num * avail.val.den * e.den := by
    ac_rfl
  rw [this]

theorem binOfQ_congr (bins : List Q) (need : Nat) {a₁ a₂ : Pos}
    (h : Q.equiv a₁.val a₂.val = true) : binOfQ bins need a₁ = binOfQ bins need a₂ := by
  have hq : ∀ e, utilGe (need * a₁.val.den) a₁.val.num e = utilGe (need * a₂.val.den) a₂.val.num e :=
    fun e => utilQGe_congr need h e
  unfold binOfQ binOf
  rw [rungs_eq_of_utilGe_eq bins hq]

theorem binOfScaledQ_congr (bins : List Q) (s : Pos) (rem : Nat) {a₁ a₂ : Pos}
    (h : Q.equiv a₁.val a₂.val = true) :
    binOfScaledQ bins s rem a₁ = binOfScaledQ bins s rem a₂ := by
  have hq := utilGe_scaled_pair_congr s.val.den (s.val.num * rem) h
  unfold binOfScaledQ binOf
  rw [rungs_eq_of_utilGe_eq bins hq]

/-- **Gap 25, kept at a rational availability.**  No capacity is HOT at any need. -/
theorem binOfQ_capacity_zero (bins : List Q) (need : Nat) {avail : Pos}
    (h : avail.val.num = 0) : binOfQ bins need avail = .hot := by
  unfold binOfQ
  rw [h]
  exact binOf_capacity_zero _ _

theorem binOfScaledQ_capacity_zero (bins : List Q) (s : Pos) (rem : Nat) {avail : Pos}
    (h : avail.val.num = 0) : binOfScaledQ bins s rem avail = .hot := by
  unfold binOfScaledQ
  rw [h, Nat.mul_zero]
  exact binOf_capacity_zero _ _

/-- **Gap 25's decided disagreement, as a theorem (parity entry P2).**  Nothing left
to do and no capacity to do it in is `0/0`; §7.1's "capacity 0 → `u = ∞`" has no
exception for zero need, so it is HOT and `p = 0`.  Fork-point
`priority::utilization` returns `0.0` for a zero need and `bin_of` puts it in the
lowest bin. -/
theorem zero_need_on_zero_capacity_is_hot (bins : List Q) (k d : Nat) (hd : 0 < d) :
    binOfQ bins 0 (mkPos 0 d hd) = .hot ∧ prio k (binOfQ bins 0 (mkPos 0 d hd)) = 0 :=
  ⟨binOfQ_capacity_zero bins 0 rfl, by rw [binOfQ_capacity_zero bins 0 rfl]; rfl⟩

/-- **More availability never worsens the bin.** -/
theorem binOfQ_anti_avail (bins : List Q) {need : Nat} {a₁ a₂ : Pos} (hne : 0 < need)
    (h : Q.le a₁.val a₂.val = true) : (binOfQ bins need a₁).ix ≤ (binOfQ bins need a₂).ix := by
  have hd : utilDefined (need * a₂.val.den) a₂.val.num = true :=
    (utilDefined_iff _ _).mpr (Or.inr (Nat.mul_pos hne (denPos a₂)))
  have h' := Q.le_elim h
  have hq : Q.le (util (need * a₂.val.den) a₂.val.num) (util (need * a₁.val.den) a₁.val.num) = true := by
    apply Q.le_of
    show need * a₂.val.den * a₁.val.num ≤ need * a₁.val.den * a₂.val.num
    calc need * a₂.val.den * a₁.val.num = need * (a₁.val.num * a₂.val.den) := by ac_rfl
      _ ≤ need * (a₂.val.num * a₁.val.den) := Nat.mul_le_mul_left _ h'
      _ = need * a₁.val.den * a₂.val.num := by ac_rfl
  unfold binOfQ
  rw [binOf_ix, binOf_ix]
  exact rungs_antitone bins hd hq

/-- **`prio` is antitone in utilisation at a rational availability.** -/
theorem prio_is_antitone_in_rational_utilisation (bins : List Q) (k : Nat) {n₁ n₂ : Nat}
    {a₁ a₂ : Pos} (hd : (utilQ n₁ a₁).defined = true)
    (h : Q.le (utilQ n₁ a₁) (utilQ n₂ a₂) = true) :
    prio k (binOfQ bins n₂ a₂) ≤ prio k (binOfQ bins n₁ a₁) :=
  prio_is_antitone_in_utilisation bins k _ _ _ _ hd h

/-- **Why D10 carries the mixture exact.**  A need of `60 × 13/10 = 78` minutes
against a mixture of `½·200 + ½·113 = 156½` minutes is `u ≈ 0.498`, bin `+1`; floor the
mixture to `156` and `u = ½` exactly, bin `+0`.  A rounding anywhere between the
mixture and the bin moves an item's priority. -/
theorem flooring_the_mixture_changes_the_bin :
    binOfScaledQ defaultBins safety 60 (mkPos 313 2 (by decide)) = .plus 1 ∧
      binOfScaledQ defaultBins safety 60 (posOfNat 156) = .plus 0 := by decide

/-! ## Gap 27: the bins a loader accepts -/

/-- **The loader's check** (gap 27): every edge a rational, and the ladder descending
from HOT's edge `1`.  `ladder_eq_rungs` needs exactly this. -/
def binsOk (bins : List Q) : Bool := binsWf bins && descending (hotEdge :: bins)

/-- A configured ladder that passed the check. -/
abbrev Bins := { l : List Q // binsOk l = true }

/-- The smart constructor. -/
def binsOf? (l : List Q) : Option Bins := if h : binsOk l = true then some ⟨l, h⟩ else none

/-- Decode a list of numerator/denominator pairs through `ofPair?`. -/
def pairsQ? : List (Nat × Nat) → Option (List Q)
  | [] => some []
  | (n, d) :: t =>
    match ofPair? n d, pairsQ? t with
    | some q, some qs => some (q.val :: qs)
    | _, _ => none

/-- **§16 `priority.bins` off the wire**: pairs, `ofPair?`, then the check. -/
def binsOfPairs? (ps : List (Nat × Nat)) : Option Bins :=
  match pairsQ? ps with
  | some l => binsOf? l
  | none => none

/-- **What the check guarantees**: a configured ladder is §7.1's ladder as written. -/
theorem Bins.ladder_eq_rungs (b : Bins) (need avail : Nat) :
    ladderIx b.val need avail = rungs b.val need avail := by
  have h := b.property
  simp only [binsOk, Bool.and_eq_true] at h
  exact Arith.ladder_eq_rungs _ _ _ h.1 h.2

/-- Both directions: accepted exactly when the check passes. -/
theorem binsOf?_isSome_iff (l : List Q) : (binsOf? l).isSome = true ↔ binsOk l = true := by
  unfold binsOf?
  split
  · exact ⟨fun _ => (by assumption), fun _ => rfl⟩
  · exact ⟨fun h => (by cases h), fun h => (by contradiction)⟩

theorem binsOf?_val {l : List Q} {b : Bins} (h : binsOf? l = some b) : b.val = l := by
  unfold binsOf? at h
  split at h
  · cases h; rfl
  · cases h

theorem binsOf?_accepts_the_default : (binsOf? defaultBins).map Subtype.val = some defaultBins := by
  decide

theorem binsOf?_refuses_unsorted_edges : binsOf? [⟨1, 10⟩, ⟨1, 2⟩] = none := by decide

theorem binsOf?_refuses_an_edge_above_hot : binsOf? [⟨2, 1⟩] = none := by decide

theorem binsOf?_refuses_an_infinite_edge : binsOf? [⟨1, 0⟩] = none := by decide

theorem binsOfPairs?_refuses_a_zero_denominator : binsOfPairs? [(1, 2), (1, 0)] = none := by
  decide

/-- **§16's decimals, sent as pairs, are §7.1's ladder**: `0.5 = 5/10`,
`0.25 = 25/100`, `0.1 = 1/10` give the same bin as `defaultBins` at every need and
availability. -/
theorem the_spec_decimals_are_the_default_ladder (need avail : Nat) :
    (binsOfPairs? [(5, 10), (25, 100), (1, 10)]).map (fun b => binOf b.val need avail)
      = some (binOf defaultBins need avail) := by
  have hb : (binsOfPairs? [(5, 10), (25, 100), (1, 10)]).map Subtype.val
      = some [⟨5, 10⟩, ⟨25, 100⟩, ⟨1, 10⟩] := by decide
  cases hq : binsOfPairs? [(5, 10), (25, 100), (1, 10)] with
  | none => rw [hq] at hb; cases hb
  | some b =>
    rw [hq] at hb
    simp only [Option.map_some, Option.some.injEq] at hb ⊢
    rw [hb]
    have e1 : utilGe need avail ⟨5, 10⟩ = utilGe need avail ⟨1, 2⟩ := by
      simp only [utilGe]; exact decide_eq_decide.mpr (by omega)
    have e2 : utilGe need avail ⟨25, 100⟩ = utilGe need avail ⟨1, 4⟩ := by
      simp only [utilGe]; exact decide_eq_decide.mpr (by omega)
    simp only [binOf, rungs, defaultBins, List.countP_cons, e1, e2]

/-- **Gap 27, exhibited.**  Swapped edges fail the check, still give an antitone bin
(`binOf_antitone` needs no sorting), and that bin is not §7.1's ladder: at
`u = 3/10` the ladder as written stops at `1/10` (rung 1) while the count also misses
`1/2` (rung 2). -/
theorem a_misconfigured_ladder_is_antitone_but_not_the_ladder :
    binsOk [⟨1, 10⟩, ⟨1, 2⟩] = false ∧
      (∀ n₁ a₁ n₂ a₂ : Nat, utilDefined n₁ a₁ = true → Q.le (util n₁ a₁) (util n₂ a₂) = true →
        (binOf [⟨1, 10⟩, ⟨1, 2⟩] n₂ a₂).ix ≤ (binOf [⟨1, 10⟩, ⟨1, 2⟩] n₁ a₁).ix) ∧
      ladderIx [⟨1, 10⟩, ⟨1, 2⟩] 3 10 ≠ rungs [⟨1, 10⟩, ⟨1, 2⟩] 3 10 :=
  ⟨by decide, fun _ _ _ _ hd h => binOf_antitone _ hd h, by decide⟩

/-- §16 `priority.safety`, off the wire: a positive rational.  Fork-point
`priority::safety_minutes` silently uses `1.0` for a non-positive safety; the kernel
refuses it (parity entry P8). -/
def safetyOf? (n d : Nat) : Option Pos := if 0 < n then ofPair? n d else none

theorem safetyOf?_refuses_zero (d : Nat) : safetyOf? 0 d = none := rfl

theorem safetyOf?_refuses_a_zero_denominator (n : Nat) : safetyOf? n 0 = none := by
  unfold safetyOf?
  split <;> rfl

theorem safetyOf?_reads_the_spec : safetyOf? 13 10 = some safety := by decide

/-! ## §7.4's hysteresis

"`p` may improve (decrease) by at most one bin per day relative to yesterday's stored
`p` (in `state.json`) unless the new value is 0.  It may worsen freely."  Fork-point
`priority::apply_hysteresis`: a raw `0` passes; otherwise `raw + 1 < y` gives `y − 1`;
otherwise `raw`.  Absent yesterday, or `hysteresis = false` in the config, `raw`
passes (`applyHysteresis`). -/

/-- §7.4 on two numbers. -/
def hysteresis (yesterday raw : Nat) : Nat :=
  if raw = 0 then 0 else if raw + 1 < yesterday then yesterday - 1 else raw

theorem hysteresis_cases (y r : Nat) :
    (r = 0 ∧ hysteresis y r = 0) ∨ (0 < r ∧ r + 1 < y ∧ hysteresis y r = y - 1) ∨
      (0 < r ∧ y ≤ r + 1 ∧ hysteresis y r = r) := by
  unfold hysteresis
  by_cases h0 : r = 0
  · left; rw [if_pos h0]; exact ⟨h0, rfl⟩
  · by_cases h1 : r + 1 < y
    · right; left; rw [if_neg h0, if_pos h1]; exact ⟨by omega, h1, rfl⟩
    · right; right; rw [if_neg h0, if_neg h1]; exact ⟨by omega, by omega, rfl⟩

/-- **§7.4: improvement is capped at one step.** -/
theorem hysteresis_improves_by_at_most_one_bin (y r : Nat) (h : 0 < hysteresis y r) :
    y ≤ hysteresis y r + 1 := by
  rcases hysteresis_cases y r with ⟨_, he⟩ | ⟨_, h1, he⟩ | ⟨_, h1, he⟩ <;> omega

/-- **§7.4: worsening is free.** -/
theorem hysteresis_worsens_freely (y r : Nat) (h : y ≤ r) : hysteresis y r = r := by
  rcases hysteresis_cases y r with ⟨h0, he⟩ | ⟨_, h1, he⟩ | ⟨_, h1, he⟩ <;> omega

/-- **§7.4's exception: `p = 0` is never delayed.** -/
theorem hysteresis_never_delays_hot (y : Nat) : hysteresis y 0 = 0 := by
  unfold hysteresis
  rw [if_pos rfl]

/-- The damping never makes an item *more* urgent than its raw `p`. -/
theorem hysteresis_never_raises_urgency (y r : Nat) : r ≤ hysteresis y r := by
  rcases hysteresis_cases y r with ⟨_, he⟩ | ⟨_, h1, he⟩ | ⟨_, h1, he⟩ <;> omega

/-- **The other direction: the damping bites.**  A raw improvement of two or more steps
is held at one step better than yesterday. -/
theorem hysteresis_holds_one_step_back (y r : Nat) (hr : 0 < r) (h : r + 1 < y) :
    hysteresis y r = y - 1 := by
  rcases hysteresis_cases y r with ⟨h0, _⟩ | ⟨_, _, he⟩ | ⟨_, h1, _⟩ <;> omega

/-- Held, the answer is never worse than the larger of today's raw and yesterday. -/
theorem hysteresis_le_max (y r : Nat) : hysteresis y r ≤ max r y := by
  rcases hysteresis_cases y r with ⟨_, he⟩ | ⟨_, h1, he⟩ | ⟨_, h1, he⟩ <;> omega

/-- `state.json`'s `priorities_yesterday` value, decoded: a stored `p` is `0..7`. -/
def yesterdayOf? (n : Nat) : Option (Fin 8) := if h : n < 8 then some ⟨n, h⟩ else none

theorem yesterdayOf?_refuses_eight (n : Nat) (h : 8 ≤ n) : yesterdayOf? n = none := by
  unfold yesterdayOf?
  rw [dif_neg (by omega)]

theorem yesterdayOf?_accepts (n : Nat) (h : n < 8) : (yesterdayOf? n).map Fin.val = some n := by
  unfold yesterdayOf?
  rw [dif_pos h]
  rfl

/-- `priority::apply_hysteresis`: the config switch and an absent yesterday both pass
`raw`. -/
def applyHysteresis (enabled : Bool) (yesterday : Option (Fin 8)) (raw : Nat) : Nat :=
  match enabled, yesterday with
  | true, some y => hysteresis y.val raw
  | _,    _      => raw

theorem applyHysteresis_without_yesterday (enabled : Bool) (raw : Nat) :
    applyHysteresis enabled none raw = raw := by
  cases enabled <;> rfl

theorem applyHysteresis_disabled (yesterday : Option (Fin 8)) (raw : Nat) :
    applyHysteresis false yesterday raw = raw := by
  cases yesterday <;> rfl

theorem applyHysteresis_enabled (y : Fin 8) (raw : Nat) :
    applyHysteresis true (some y) raw = hysteresis y.val raw := rfl

theorem applyHysteresis_zero (enabled : Bool) (yesterday : Option (Fin 8)) :
    applyHysteresis enabled yesterday 0 = 0 := by
  cases enabled <;> cases yesterday <;> first | rfl | exact hysteresis_never_delays_hot _

theorem applyHysteresis_cases (enabled : Bool) (yesterday : Option (Fin 8)) (raw : Nat) :
    applyHysteresis enabled yesterday raw = raw ∨
      ∃ y : Fin 8, yesterday = some y ∧ applyHysteresis enabled yesterday raw = hysteresis y.val raw := by
  cases enabled <;> cases yesterday <;> first | exact Or.inl rfl | exact Or.inr ⟨_, rfl, rfl⟩

/-! ### The day-over-day reading, under the host's contract

`hysteresisDays y raw n` is day `n + 1`'s `p` when yesterday stored `y`, the raw `p`
stays `raw`, and the host stores each day's answer as the next day's yesterday. -/

def hysteresisDays (y raw : Nat) : Nat → Nat
  | 0     => hysteresis y raw
  | n + 1 => hysteresis (hysteresisDays y raw n) raw

theorem hysteresisDays_closed_form {raw : Nat} (hr : 0 < raw) (y : Nat) :
    ∀ n, hysteresisDays y raw n = max raw (y - (n + 1)) := by
  intro n
  induction n with
  | zero =>
    simp only [hysteresisDays]
    rcases hysteresis_cases y raw with ⟨_, he⟩ | ⟨_, h1, he⟩ | ⟨_, h1, he⟩ <;> omega
  | succ m ih =>
    simp only [hysteresisDays]
    rw [ih]
    rcases hysteresis_cases (max raw (y - (m + 1))) raw with ⟨_, he⟩ | ⟨_, h1, he⟩ | ⟨_, h1, he⟩ <;>
      omega

/-- **A steady raw `p` is reached within the gap, and held.** -/
theorem hysteresis_settles_on_a_steady_priority {raw : Nat} (hr : 0 < raw) (y n : Nat)
    (h : y ≤ raw + n + 1) : hysteresisDays y raw n = raw := by
  rw [hysteresisDays_closed_form hr]
  omega

/-- **…and not a day sooner**: each day of the gap is exactly one step better. -/
theorem hysteresis_holds_every_day_of_the_gap {raw : Nat} (hr : 0 < raw) (y n : Nat)
    (h : raw + n + 1 < y) : hysteresisDays y raw n = y - (n + 1) ∧ raw < hysteresisDays y raw n := by
  rw [hysteresisDays_closed_form hr]
  omega

/-- A HOT item is `0` every day. -/
theorem hysteresisDays_of_hot (y : Nat) : ∀ n, hysteresisDays y 0 n = 0 := by
  intro n
  induction n with
  | zero => exact hysteresis_never_delays_hot y
  | succ m _ => exact hysteresis_never_delays_hot _

/-! ## §7.2's rule table

```
walls    : off the scale
p = 0    : HOT (u ≥ 1) · overdue with on_miss = persist · mandatory window instance · `hot` flag
p = k + bin(u)         : Finite with a due — after the EDF pass
p = k + bin(u_floor)   : Open with a floor
p = k + 2              : Finite, no due, no floor (pure rank)
p = 5                  : optional.md items
clamp p to 0..=7
```

Which row applies is `priority::compute`'s cascade, in its order — wall, optional,
overdue, mandatory, `hot` flag, a pass (EDF or floor), rank — and is derived
(`rowOf`).  What each row makes of `p`, and whether §7.4 may hold it, is data
(`rowTable`).  `priority::compute`'s deviation 5 is the second column: every row is
damped except `optional.md` (pinned at `5`) and walls (off the scale); the `p = 0` rows
are damped and exempt by the hysteresis rule's own "unless the new value is 0". -/

/-- One line of §7.2.  `pressure` carries the pass's bin: `.hot` is §7.3's HOT/IMPOSSIBLE
(`p = 0`), `.plus n` is `k + n`. -/
inductive PrioRow where
  | wall
  | optional
  | overdue
  | mandatory
  | hotFlag
  | pressure (b : Bin)
  | rank
deriving DecidableEq, Repr

/-- What §7.2 reads off one candidate.  Every field is a plain argument: `overdue`,
`mandatory` and `pass` are the D9/D10 tranche's to compute. -/
structure RuleIn where
  wall      : Bool
  optional  : Bool
  overdue   : Bool
  mandatory : Bool
  hotFlag   : Bool
  pass      : Option Bin
deriving DecidableEq, Repr

/-- `priority::compute`'s cascade. -/
def rowOf (r : RuleIn) : PrioRow :=
  if r.wall then .wall
  else if r.optional then .optional
  else if r.overdue then .overdue
  else if r.mandatory then .mandatory
  else if r.hotFlag then .hotFlag
  else match r.pass with
    | some b => .pressure b
    | none   => .rank

/-- A row's `p`. -/
inductive PVal where
  | offScale
  | fixed (n : Nat)
  | kPlus (b : Bin)
deriving DecidableEq, Repr

def PVal.eval (k : Nat) : PVal → Option Nat
  | .offScale => none
  | .fixed n  => some n
  | .kPlus b  => some (prio k b)

/-- **§7.2's table**: each row's `p`, and whether §7.4's hysteresis may hold it. -/
def rowTable : PrioRow → PVal × Bool
  | .wall        => (.offScale, false)
  | .optional    => (.fixed 5, false)
  | .overdue     => (.fixed 0, true)
  | .mandatory   => (.fixed 0, true)
  | .hotFlag     => (.fixed 0, true)
  | .pressure b  => (.kPlus b, true)
  | .rank        => (.kPlus (.plus 2), true)

/-- §7.2's raw `p`, before hysteresis; `none` is off the scale. -/
def rawPrio (k : Nat) (r : RuleIn) : Option Nat := (rowTable (rowOf r)).1.eval k

/-- §7.2 then §7.4: the `p` a candidate is ranked by. -/
def finalPrio (enabled : Bool) (yesterday : Option (Fin 8)) (k : Nat) (r : RuleIn) :
    Option Nat :=
  (rawPrio k r).map (fun raw =>
    if (rowTable (rowOf r)).2 then applyHysteresis enabled yesterday raw else raw)

/-! ### `p` is on the scale, whichever row answered (stage 6 P4)

`prio_is_clamped` says §7.2's `k + bin` row is clamped to `0..7`; it says nothing about the
five *fixed* rows or about §7.4's damping, and `DayPlan.priorities` carries a `Fin 8`, so the
whole cascade has to be on the scale or a row would be silently dropped at the boundary of a
type.  These two close it. -/

/-- **Every `p` §7.2's table produces is `0..7`** — the fixed rows (`5`, and `0` three times)
as much as the clamped `k + bin`. -/
theorem rawPrio_is_on_the_scale (k : Nat) (r : RuleIn) {n : Nat} (h : rawPrio k r = some n) :
    n ≤ 7 := by
  unfold rawPrio at h
  cases hr : rowOf r <;> rw [hr] at h <;>
    simp only [rowTable, PVal.eval, Option.some.injEq] at h
  case wall => exact absurd h (by simp)
  case optional => omega
  case overdue => omega
  case mandatory => omega
  case hotFlag => omega
  case pressure b => exact h ▸ prio_is_clamped k b
  case rank => exact h ▸ prio_is_clamped k _

/-- **And §7.4's damping cannot take it off the scale**: yesterday's stored `p` is a `Fin 8`
and `hysteresis` never exceeds the larger of the two. -/
theorem applyHysteresis_is_on_the_scale (enabled : Bool) (y : Option (Fin 8)) (raw : Nat)
    (h : raw ≤ 7) : applyHysteresis enabled y raw ≤ 7 := by
  cases enabled with
  | false => cases y <;> exact h
  | true =>
    cases y with
    | none => exact h
    | some yy =>
      have hy := yy.isLt
      have := hysteresis_le_max yy.val raw
      show hysteresis yy.val raw ≤ 7
      omega

/-- **The `p` a candidate is ranked by is `0..7`.** -/
theorem finalPrio_is_on_the_scale (enabled : Bool) (y : Option (Fin 8)) (k : Nat) (r : RuleIn)
    {n : Nat} (h : finalPrio enabled y k r = some n) : n ≤ 7 := by
  unfold finalPrio at h
  cases hr : rawPrio k r with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some raw =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hraw : raw ≤ 7 := rawPrio_is_on_the_scale k r hr
    split at h
    · exact h ▸ applyHysteresis_is_on_the_scale enabled y raw hraw
    · omega

/-! ### The bridges: each row, stated over the inputs -/

theorem rawPrio_of_a_wall (k : Nat) (r : RuleIn) (hw : r.wall = true) : rawPrio k r = none := by
  simp [rawPrio, rowOf, hw, rowTable, PVal.eval]

theorem rawPrio_of_an_optional (k : Nat) (r : RuleIn) (hw : r.wall = false)
    (ho : r.optional = true) : rawPrio k r = some 5 := by
  simp [rawPrio, rowOf, hw, ho, rowTable, PVal.eval]

theorem rawPrio_of_overdue (k : Nat) (r : RuleIn) (hw : r.wall = false)
    (ho : r.optional = false) (hd : r.overdue = true) : rawPrio k r = some 0 := by
  simp [rawPrio, rowOf, hw, ho, hd, rowTable, PVal.eval]

theorem rawPrio_of_a_mandatory_instance (k : Nat) (r : RuleIn) (hw : r.wall = false)
    (ho : r.optional = false) (hd : r.overdue = false) (hm : r.mandatory = true) :
    rawPrio k r = some 0 := by
  simp [rawPrio, rowOf, hw, ho, hd, hm, rowTable, PVal.eval]

theorem rawPrio_of_the_hot_flag (k : Nat) (r : RuleIn) (hw : r.wall = false)
    (ho : r.optional = false) (hd : r.overdue = false) (hm : r.mandatory = false)
    (hh : r.hotFlag = true) : rawPrio k r = some 0 := by
  simp [rawPrio, rowOf, hw, ho, hd, hm, hh, rowTable, PVal.eval]

theorem rawPrio_of_a_pass (k : Nat) (r : RuleIn) (b : Bin) (hw : r.wall = false)
    (ho : r.optional = false) (hd : r.overdue = false) (hm : r.mandatory = false)
    (hh : r.hotFlag = false) (hp : r.pass = some b) : rawPrio k r = some (prio k b) := by
  simp [rawPrio, rowOf, hw, ho, hd, hm, hh, hp, rowTable, PVal.eval]

theorem rawPrio_of_pure_rank (k : Nat) (r : RuleIn) (hw : r.wall = false)
    (ho : r.optional = false) (hd : r.overdue = false) (hm : r.mandatory = false)
    (hh : r.hotFlag = false) (hp : r.pass = none) : rawPrio k r = some (min (k + 2) 7) := by
  simp [rawPrio, rowOf, hw, ho, hd, hm, hh, hp, rowTable, PVal.eval, prio]

/-- Every row lands in `0..=7`. -/
theorem rawPrio_is_clamped (k : Nat) (r : RuleIn) {n : Nat} (h : rawPrio k r = some n) :
    n ≤ 7 := by
  unfold rawPrio at h
  cases hr : rowOf r with
  | wall => rw [hr] at h; cases h
  | optional => rw [hr] at h; cases h; decide
  | overdue => rw [hr] at h; cases h; decide
  | mandatory => rw [hr] at h; cases h; decide
  | hotFlag => rw [hr] at h; cases h; decide
  | pressure b => rw [hr] at h; cases h; exact prio_is_clamped k b
  | rank => rw [hr] at h; cases h; exact prio_is_clamped k _

/-- The cascade's first line is the only way to the wall row. -/
theorem rowOf_eq_wall_iff (r : RuleIn) : rowOf r = .wall ↔ r.wall = true := by
  obtain ⟨w, o, d, m, h, p⟩ := r
  cases w <;> cases o <;> cases d <;> cases m <;> cases h <;> cases p <;> simp [rowOf]

/-- Off the scale is walls and nothing else. -/
theorem rawPrio_isNone_iff (k : Nat) (r : RuleIn) : rawPrio k r = none ↔ r.wall = true := by
  constructor
  · intro h
    refine (rowOf_eq_wall_iff r).mp ?_
    unfold rawPrio at h
    cases hr : rowOf r with
    | wall => rfl
    | _ => rw [hr] at h; cases h
  · exact rawPrio_of_a_wall k r

/-! ### After hysteresis -/

theorem finalPrio_of_a_wall (en : Bool) (y : Option (Fin 8)) (k : Nat) (r : RuleIn)
    (hw : r.wall = true) : finalPrio en y k r = none := by
  simp [finalPrio, rawPrio_of_a_wall k r hw]

/-- `optional.md` is pinned at `5` whatever yesterday said (deviation 5). -/
theorem finalPrio_of_an_optional (en : Bool) (y : Option (Fin 8)) (k : Nat) (r : RuleIn)
    (hw : r.wall = false) (ho : r.optional = true) : finalPrio en y k r = some 5 := by
  have hrow : rowOf r = .optional := by simp [rowOf, hw, ho]
  simp [finalPrio, rawPrio, hrow, rowTable, PVal.eval]

/-- **Every other row is damped.** -/
theorem finalPrio_damps (en : Bool) (y : Option (Fin 8)) (k : Nat) (r : RuleIn)
    (hw : r.wall = false) (ho : r.optional = false) :
    finalPrio en y k r = (rawPrio k r).map (applyHysteresis en y) := by
  have hdamp : (rowTable (rowOf r)).2 = true := by
    unfold rowOf
    simp only [hw, ho, Bool.false_eq_true, if_false]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl
  simp only [finalPrio, hdamp, if_true]

/-- **A `p = 0` row is never delayed**, by any yesterday. -/
theorem finalPrio_never_delays_zero (en : Bool) (y : Option (Fin 8)) (k : Nat) (r : RuleIn)
    (h : rawPrio k r = some 0) : finalPrio en y k r = some 0 := by
  unfold finalPrio
  rw [h]
  simp only [Option.map_some, applyHysteresis_zero, ite_self]

/-- **The final `p` is still in `0..=7`**: yesterday's stored `p` is itself bounded. -/
theorem finalPrio_is_clamped (en : Bool) (y : Option (Fin 8)) (k : Nat) (r : RuleIn) {n : Nat}
    (h : finalPrio en y k r = some n) : n ≤ 7 := by
  unfold finalPrio at h
  cases hraw : rawPrio k r with
  | none => rw [hraw] at h; cases h
  | some raw =>
    rw [hraw] at h
    have hr7 := rawPrio_is_clamped k r hraw
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    split
    · rcases applyHysteresis_cases en y raw with he | ⟨y', _, he⟩
      · rw [he]; exact hr7
      · rw [he]
        have := hysteresis_le_max y'.val raw
        have := y'.isLt
        omega
    · exact hr7

/-- **§7.4 through the table: on a damped row, one step per day.** -/
theorem finalPrio_improves_by_at_most_one_step (k : Nat) (r : RuleIn) (y : Fin 8) {n : Nat}
    (hw : r.wall = false) (ho : r.optional = false)
    (h : finalPrio true (some y) k r = some n) (hn : 0 < n) : y.val ≤ n + 1 := by
  rw [finalPrio_damps true (some y) k r hw ho] at h
  cases hraw : rawPrio k r with
  | none => rw [hraw] at h; cases h
  | some raw =>
    rw [hraw] at h
    simp only [Option.map_some, Option.some.injEq, applyHysteresis_enabled] at h
    subst h
    exact hysteresis_improves_by_at_most_one_bin y.val raw hn

end Tm
