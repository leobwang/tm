/-!
# The exact-arithmetic layer

§7 and §8 of the spec are written in decimals — `safety = 1.3`, `bins =
[0.5, 0.25, 0.1]`, `budget_ratio = 0.75`, `u = need / capacity`, `capacity 0 →
u = ∞`.  The Rust reads all of that into `f64`.  This module decides every one
of those questions in `Nat`, with no `Float` and no fixed-point scale.

The observation the whole layer rests on:

> **Every ratio in tm appears inside a comparison, and comparisons
> cross-multiply.**

`u = need/avail` is never formed.  `u ≥ 1` is `need ≥ avail`; `u ≥ 1/2` is
`2·need ≥ avail`; and in general `u ≥ p/q` is `q·need ≥ p·avail`.  A scale
constant folds into the same product rather than being applied first: with
`need = rem × 13/10`, the test against `p/q` is `13·rem·q ≥ 10·avail·p`.  Three
integer multiplications and one `≤`, exactly.

Three things follow, and each is a theorem below rather than a remark.

1. **`∞` stops being a special case.**  A ratio is a *pair*, and `avail = 0` is
   the pair `⟨need, 0⟩`.  Cross-multiplication already gives `p·0 ≤ q·need`,
   which is true — so `u = ∞ ≥ p/q` for every edge, with no `is_finite()`
   guard to forget.  §3.5's "replaces `f64::INFINITY` and its five
   `is_finite()` guards" is `utilGe_capacity_zero`.
2. **The order is the *rational* order**, not merely some order on pairs:
   `Q.le` is reflexive, transitive, antisymmetric-up-to-value and total, and —
   the part that makes it faithful — a *congruence* for `n/d ≈ (k·n)/(k·d)`
   (`Q.le_congr_left`, `Q.le_congr_right`, `Q.le_scale_left`).  A comparison
   cannot see how a ratio was written, only what it denotes.  That congruence
   is what licenses folding a scale constant in.  And it is anchored outside
   its own definition: on ratios that are whole numbers it *is* the `Nat`
   order (`le_agrees_with_exact_division`).
3. **The bin ladder is antitone for a reason, not by inspection.**  It is a
   *count* of the edges `u` fails to reach; each edge's test is antitone in `u`
   by transitivity, so the count is (`rungs_antitone`).  That argument does not
   care whether the edges are sorted, which matters, because §7.1's edges are
   `1/2, 1/4, 1/10` — three halvings and then *not* the fourth.  A generating
   structure is wrong here and the disagreement is exhibited
   (`log2_ladder_disagrees_at_eleven_percent`), so the edges are data, sorting
   is a hypothesis only where it is genuinely needed (`ladder_eq_rungs`), and
   antitonicity — the one property the list actually supports — is proved
   without it.  With the shipped edges the ladder is then §7.1's `bin(u)`
   *exactly*: `defaultBins_are_the_intervals` is the five half-open intervals
   themselves, not a table of sample points, and the half-openness is derived
   from "reaching an edge implies reaching every smaller one".

## The rounding sites

A quotient that must become whole minutes has to say which way it rounds, at
its site, never inherited.  The vocabulary is `floorQ` / `ceilQ` / `halfUpQ`,
each monotone (`*_mono`) and each within one minute of the exact value
(`*_withinOne`).  Every site §7 and §8 contain:

| # | site | rule | here |
|---|---|---|---|
| R1 | §7.1/§7.3 `need = remaining × safety`, for the EDF reservation | **ceiling** — a margin rounded down stops being a margin | `needMin` |
| R2 | §8.1 `budget = floor(window_hours × 60 / block_min × budget_ratio)` | **floor**, one division, constants folded | `budgetBlocks`; on the exact pairs, `Look.budgetOf` (stage 5 D10 step L2) |
| R3 | §8.1 `window_min = round(window_hours × 60)` | **half-up**, on the exact pair `window_hours = num/den` (fork `(window_hours × 60.0).round()`). *Reopened at stage 5 D10 step L2 (design D10-10): the kernel computes the window, so the site exists; this row said "eliminated" while the window entered the kernel as minutes.* Parity P27 | `Look.windowMinOf` |
| R4 | §8.5 `planned = round(est × duration multiplier)` | **half-up** | `plannedMin` |
| R5 | §8.5 slot energy after the posterior correction | **half-up, then clamp to `0..5`** — and the clamp is load-bearing (`posterior_can_go_negative`) | `energyAfter` |
| R6 | §8.2 step 3's short last block, "≥ 30m or dropped" (§16 `min_last_block_min`) | a **comparison**, not a rounding — named so that nobody adds one | — |
| R7 | §8.4's future-day capacity, mixing the two locations by `p_lounge` | **open**: a mixture of two integer capacities by a rational weight. Nothing rounds here yet; the pair is carried exact | — |
| R11 | §8.5's hours since wake, `hsw = round(seconds / 36) / 100` (fork `log::hours_since_wake`), which `energy::bucket` floors and the prior curve's range keys compare | **half away from zero**, on whole seconds (`Cal.secondsBetween`, chrono's `num_seconds`); exact against the fork's `f64` for every input, because no quotient lies within an ulp of a tie and no hundredth within an ulp of a range key with `den ≤ 10^6`. *Added at stage 5 D10 step L4 (design D10-11). R8 and R9 are the D9 track's rows, added by their steps* | `Look.hsw100` (`hsw100_mono`, `hsw100_withinOne`) |
| R10 | §8.5's sleep-debt shift, `model.sleep_shift(cfg).round()`, subtracted from the base level before the `0..5` clamp | **half away from zero** on a **signed** decimal — §8.5 fits `sleep_debt_shift` as a shrunken mean, so the sign is real and `f64::round` is not half-up below zero. *Added at stage 6 step L9 (design §13.5), with day 0 as its caller* | `roundAway` (`roundAway_mono`, `roundAway_withinOne`) |

Two families that look like rounding and are not.  §7.1's utilization, §7.3's
`avail` and `reserve`, §7.4's hysteresis, §7.5's batching threshold, §8.5's
`slept < under_hours` and §16's `min_last_block_min` are all *comparisons*, and
comparisons cross-multiply — nothing rounds on the decision path.  And
`progress` / `plan_honesty` / `as_blocks` are display: the kernel emits a
numerator and a denominator as integers and the host divides.

`rounding_the_need_changes_the_bin` is the theorem that keeps R1 honest: the
rounded need and the exact one give *different bins*, so the ordering path uses
`utilScaledGe` and never `needMin`.

## Why not `Rat`

Lean's `Rat` normalises by `gcd` on every operation — work the kernel never
needs, since nothing here is ever *displayed* as a reduced fraction, only
compared and floored, and normalisation would put a gcd inside every `decide`
on a bin ladder.  A pair of `Nat`s also lets `⟨n, 0⟩` denote `∞`, which `Rat`
cannot represent and which §7.1 requires.  So `Q` is defined here and `Rat` is
deliberately unused.
-/
namespace Tm.Arith

/-! ## A rational as a pair -/

/-- A ratio, **unnormalised**: `num / den`.

`den = 0` is not an error and not a rational: `⟨n, 0⟩` with `n > 0` is the `∞`
that §7.1 asks for when capacity is zero, and `⟨0, 0⟩` is the one point where
`num/den` denotes nothing at all.  `Q.ok` picks out the honest rationals and
`Q.defined` excludes only `⟨0, 0⟩`; every theorem below carries whichever of the
two it actually needs, and no more. -/
structure Q where
  num : Nat
  den : Nat
deriving DecidableEq, Repr, Inhabited

/-- `q` denotes a rational number (`den > 0`).  Decidable and `Bool`-valued:
the kernel's second tier. -/
def Q.ok (q : Q) : Bool := decide (0 < q.den)

/-- `q` denotes *something* — a rational, or `∞`.  Only `⟨0, 0⟩` fails, and that
is exactly the point at which a float implementation produces `NaN`. -/
def Q.defined (q : Q) : Bool := decide (0 < q.den ∨ 0 < q.num)

theorem Q.ok_defined {q : Q} (h : q.ok = true) : q.defined = true := by
  simp only [Q.ok, decide_eq_true_eq] at h
  simp only [Q.defined, decide_eq_true_eq]
  exact Or.inl h

/-- The rationals: a ratio with a positive denominator.  A `Subtype`, so a
rounding site cannot be handed a zero denominator by accident. -/
abbrev Pos := { q : Q // q.ok = true }

theorem denPos (p : Pos) : 0 < p.val.den := by
  have h := p.property
  simpa [Q.ok] using h

/-- The smart constructor.  A `Pos` is never built by hand. -/
def mkPos (n d : Nat) (h : 0 < d) : Pos := ⟨⟨n, d⟩, by simp [Q.ok, h]⟩

@[simp] theorem mkPos_num (n d : Nat) (h : 0 < d) : (mkPos n d h).val.num = n := rfl
@[simp] theorem mkPos_den (n d : Nat) (h : 0 < d) : (mkPos n d h).val.den = d := rfl

/-- The decoding constructor — what a `FromJson` for a configured rational must
call.  A zero denominator is rejected, not repaired. -/
def ofPair? (n d : Nat) : Option Pos :=
  if h : 0 < d then some (mkPos n d h) else none

theorem ofPair?_zero (n : Nat) : ofPair? n 0 = none := rfl

theorem ofPair?_some {n d : Nat} (h : 0 < d) : ofPair? n d = some (mkPos n d h) := by
  simp [ofPair?, h]

/-- A whole number as a ratio. -/
def ofNat (n : Nat) : Q := ⟨n, 1⟩

/-- A whole number as a rational. -/
def posOfNat (n : Nat) : Pos := mkPos n 1 (by omega)

def Q.mul (a b : Q) : Q := ⟨a.num * b.num, a.den * b.den⟩

/-- Division on pairs is exact and total: it swaps a denominator up.  Dividing
by zero produces `⟨_, 0⟩`, which is `∞` — the spec's own convention, arrived at
through the representation rather than through a branch. -/
def Q.div (a b : Q) : Q := ⟨a.num * b.den, a.den * b.num⟩

/-! ## The order, and why cross-multiplication deserves the name

`Q.le` is *defined* by cross-multiplication.  What has to be earned is that it
is the order on the rationals those pairs denote: the four order laws, plus the
congruence that says a comparison sees the value and not the spelling. -/

/-- `a ≤ b`, by cross-multiplication.  No quotient is formed. -/
def Q.le (a b : Q) : Bool := decide (a.num * b.den ≤ b.num * a.den)

/-- `a < b`, by cross-multiplication. -/
def Q.lt (a b : Q) : Bool := decide (a.num * b.den < b.num * a.den)

/-- `a` and `b` denote the same rational.  `1/2 ≈ 5/10`; nothing normalises. -/
def Q.equiv (a b : Q) : Bool := decide (a.num * b.den = b.num * a.den)

/-- Introduce a comparison from its cross-multiplied form. -/
theorem Q.le_of {a b : Q} (h : a.num * b.den ≤ b.num * a.den) : Q.le a b = true :=
  decide_eq_true h

/-- Eliminate a comparison into its cross-multiplied form. -/
theorem Q.le_elim {a b : Q} (h : Q.le a b = true) : a.num * b.den ≤ b.num * a.den :=
  of_decide_eq_true h

private theorem cancelR {a b c : Nat} (hc : 0 < c) (h : a * c ≤ b * c) : a ≤ b :=
  Nat.le_of_mul_le_mul_left (by rw [Nat.mul_comm c a, Nat.mul_comm c b]; exact h) hc

theorem Q.lt_iff_not_le (a b : Q) : Q.lt a b = ! Q.le b a := by
  simp only [Q.lt, Q.le]
  by_cases h : a.num * b.den < b.num * a.den
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.le_of_not_lt h]

theorem Q.le_refl (a : Q) : Q.le a a = true := by simp [Q.le]

theorem Q.lt_irrefl (a : Q) : Q.lt a a = false := by simp [Q.lt]

/-- Totality holds for *every* pair, `⟨0,0⟩` included: it is `Nat.le_total` and
nothing more. -/
theorem Q.le_total (a b : Q) : Q.le a b = true ∨ Q.le b a = true := by
  simp only [Q.le, decide_eq_true_eq]
  exact Nat.le_total _ _

/-- Antisymmetry lands on `equiv`, not on equality — `1/2` and `5/10` are two
spellings and the order cannot tell them apart, which is the point. -/
theorem Q.le_antisymm {a b : Q} (h₁ : Q.le a b = true) (h₂ : Q.le b a = true) :
    Q.equiv a b = true := by
  simp only [Q.le, decide_eq_true_eq] at h₁ h₂
  simp only [Q.equiv, decide_eq_true_eq]
  omega

/-- Transitivity needs the *middle* ratio to denote something.  It genuinely
fails at `⟨0,0⟩`, which is above and below everything at once — the pair-shaped
image of `NaN`, whose every comparison is false — and that is what `Q.defined`
is for. -/
theorem Q.le_trans {a b c : Q} (hb : b.defined = true)
    (hab : Q.le a b = true) (hbc : Q.le b c = true) : Q.le a c = true := by
  simp only [Q.le, decide_eq_true_eq] at hab hbc ⊢
  simp only [Q.defined, decide_eq_true_eq] at hb
  rcases Nat.eq_zero_or_pos b.den with hbd | hbd
  · -- `b = ⟨n, 0⟩` with `n > 0`, i.e. `b` is `∞`; then `c` is `∞` too.
    have hbn : 0 < b.num := by omega
    rw [hbd, Nat.mul_zero] at hbc
    have hcd : c.den = 0 := by
      rcases Nat.eq_zero_or_pos c.den with h | h
      · exact h
      · exact absurd hbc (by have := Nat.mul_pos hbn h; omega)
    rw [hcd, Nat.mul_zero]
    exact Nat.zero_le _
  · -- `b` is a rational: multiply out and cancel it.
    have key : a.num * c.den * b.den ≤ c.num * a.den * b.den :=
      calc a.num * c.den * b.den
          = a.num * b.den * c.den := by rw [Nat.mul_right_comm]
        _ ≤ b.num * a.den * c.den := Nat.mul_le_mul_right _ hab
        _ = b.num * c.den * a.den := by rw [Nat.mul_right_comm]
        _ ≤ c.num * b.den * a.den := Nat.mul_le_mul_right _ hbc
        _ = c.num * a.den * b.den := by rw [Nat.mul_right_comm]
    exact cancelR hbd key

/-- **The congruence, on the left.**  Two spellings of one rational compare the
same way against everything.  This is what makes "cross-multiply" a statement
about rationals rather than about pairs. -/
theorem Q.le_congr_left {a a' b : Q} (ha : a.ok = true) (ha' : a'.ok = true)
    (h : Q.equiv a a' = true) : Q.le a b = Q.le a' b := by
  simp only [Q.ok, decide_eq_true_eq] at ha ha'
  simp only [Q.equiv, decide_eq_true_eq] at h
  simp only [Q.le, decide_eq_decide]
  constructor
  · intro hab
    refine cancelR ha ?_
    calc a'.num * b.den * a.den
        = a'.num * a.den * b.den := by rw [Nat.mul_right_comm]
      _ = a.num * a'.den * b.den := by rw [h]
      _ = a.num * b.den * a'.den := by rw [Nat.mul_right_comm]
      _ ≤ b.num * a.den * a'.den := Nat.mul_le_mul_right _ hab
      _ = b.num * a'.den * a.den := by rw [Nat.mul_right_comm]
  · intro hab
    refine cancelR ha' ?_
    calc a.num * b.den * a'.den
        = a.num * a'.den * b.den := by rw [Nat.mul_right_comm]
      _ = a'.num * a.den * b.den := by rw [← h]
      _ = a'.num * b.den * a.den := by rw [Nat.mul_right_comm]
      _ ≤ b.num * a'.den * a.den := Nat.mul_le_mul_right _ hab
      _ = b.num * a.den * a'.den := by rw [Nat.mul_right_comm]

/-- The congruence, on the right. -/
theorem Q.le_congr_right {a b b' : Q} (hb : b.ok = true) (hb' : b'.ok = true)
    (h : Q.equiv b b' = true) : Q.le a b = Q.le a b' := by
  simp only [Q.ok, decide_eq_true_eq] at hb hb'
  simp only [Q.equiv, decide_eq_true_eq] at h
  simp only [Q.le, decide_eq_decide]
  constructor
  · intro hab
    refine cancelR hb ?_
    calc a.num * b'.den * b.den
        = a.num * b.den * b'.den := by rw [Nat.mul_right_comm]
      _ ≤ b.num * a.den * b'.den := Nat.mul_le_mul_right _ hab
      _ = b.num * b'.den * a.den := by rw [Nat.mul_right_comm]
      _ = b'.num * b.den * a.den := by rw [h]
      _ = b'.num * a.den * b.den := by rw [Nat.mul_right_comm]
  · intro hab
    refine cancelR hb' ?_
    calc a.num * b.den * b'.den
        = a.num * b'.den * b.den := by rw [Nat.mul_right_comm]
      _ ≤ b'.num * a.den * b.den := Nat.mul_le_mul_right _ hab
      _ = b'.num * b.den * a.den := by rw [Nat.mul_right_comm]
      _ = b.num * b'.den * a.den := by rw [← h]
      _ = b.num * a.den * b'.den := by rw [Nat.mul_right_comm]

/-- Multiplying a ratio through by a positive constant does not change what it
denotes. -/
theorem Q.equiv_scale (k : Nat) (a : Q) : Q.equiv ⟨k * a.num, k * a.den⟩ a = true := by
  simp only [Q.equiv, decide_eq_true_eq]
  rw [Nat.mul_comm k a.num, Nat.mul_assoc]

/-- **This is the theorem that lets a scale constant fold in.**  `13·rem/10`
compared against `p/q` may be rewritten with the `13` and the `10` pushed into
the two sides of `u` without changing a single answer. -/
theorem Q.le_scale_left {a b : Q} {k : Nat} (hk : 0 < k) (ha : a.ok = true) :
    Q.le ⟨k * a.num, k * a.den⟩ b = Q.le a b := by
  refine Q.le_congr_left ?_ ha (Q.equiv_scale k a)
  simp only [Q.ok, decide_eq_true_eq] at ha ⊢
  exact Nat.mul_pos hk ha

/-- **The order is anchored outside itself.**  On two ratios that happen to be
whole numbers, cross-multiplication gives back the comparison of those whole
numbers — so `Q.le` is not merely *some* order on pairs that happens to satisfy
the laws. -/
theorem le_agrees_with_exact_division {a b : Pos} {ka kb : Nat}
    (ha : a.val.num = ka * a.val.den) (hb : b.val.num = kb * b.val.den) :
    Q.le a.val b.val = decide (ka ≤ kb) := by
  have hda := denPos a
  have hdb := denPos b
  have hd : 0 < a.val.den * b.val.den := Nat.mul_pos hda hdb
  have eL : a.val.num * b.val.den = ka * (a.val.den * b.val.den) := by
    rw [ha, Nat.mul_assoc]
  have eR : b.val.num * a.val.den = kb * (a.val.den * b.val.den) := by
    rw [hb, Nat.mul_assoc, Nat.mul_comm b.val.den a.val.den]
  simp only [Q.le, eL, eR]
  rw [decide_eq_decide]
  refine ⟨fun h => ?_, fun h => Nat.mul_le_mul_right _ h⟩
  exact Nat.le_of_mul_le_mul_left
    (by rw [Nat.mul_comm (a.val.den * b.val.den) ka,
            Nat.mul_comm (a.val.den * b.val.den) kb]; exact h) hd

/-! ## Utilization: §7.1's `u`, never formed

`u = need / avail` is the pair `⟨need, avail⟩`, and `avail = 0` is `∞` by the
representation.  `utilGe` is the comparison the kernel actually runs;
`utilGe_eq_le` is the proof that it is the order on that pair. -/

/-- §7.1's `u = need / capacity`, as a pair.  Never divided. -/
def util (need avail : Nat) : Q := ⟨need, avail⟩

/-- **The general form.**  `u ≥ e`, where `e = p/q`, is `q·need ≥ p·avail`.
Three multiplications and one comparison; no quotient, no `Float`, no guard. -/
def utilGe (need avail : Nat) (e : Q) : Bool :=
  decide (e.num * avail ≤ e.den * need)

/-- **Faithfulness.**  The cross-multiplied test *is* the rational comparison it
replaces — unconditionally, `avail = 0` included. -/
theorem utilGe_eq_le (need avail : Nat) (e : Q) :
    utilGe need avail e = Q.le e (util need avail) := by
  simp only [utilGe, Q.le, util, Nat.mul_comm]

/-- §7.1's `capacity 0 → u = ∞`, derived rather than branched on: every edge is
reached.  This replaces `f64::INFINITY` and the `is_finite()` guards around
it. -/
theorem utilGe_capacity_zero (need : Nat) (e : Q) : utilGe need 0 e = true := by
  simp [utilGe]

/-- `u` denotes something.  False only at `need = avail = 0`. -/
def utilDefined (need avail : Nat) : Bool := (util need avail).defined

theorem utilDefined_iff (need avail : Nat) :
    utilDefined need avail = true ↔ (0 < avail ∨ 0 < need) :=
  ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

/-- **The one point where the spec's sentence and a float part company.**
`need = 0` with `avail = 0` is `0/0`: the pair denotes nothing, the spec's words
("capacity 0 → `u = ∞`") make it `∞`, and an `f64` makes it `NaN`, whose every
comparison is false — so the float falls off the ladder into the *lowest* bin
while this kernel calls it HOT.  Recorded, not hidden: a caller that can produce
`need = 0` must decide which it wants, and `utilDefined` is the guard to
test. -/
theorem util_zero_over_zero_is_undefined : utilDefined 0 0 = false := by decide

theorem util_zero_over_zero_is_hot : utilGe 0 0 (ofNat 1) = true := by decide

/-- **Scale constants fold in.**  §7.1's `need = remaining × safety`, with
`safety = s.num/s.den`: the test against `p/q` becomes
`s.num·rem·q ≥ s.den·avail·p`.  The scale multiplies the numerator and the
denominator of `u`; it is not applied to `need` first, so nothing is rounded
before the comparison. -/
def utilScaledGe (s : Pos) (rem avail : Nat) (e : Q) : Bool :=
  utilGe (s.val.num * rem) (s.val.den * avail) e

theorem utilScaledGe_cross (s : Pos) (rem avail : Nat) (e : Q) :
    utilScaledGe s rem avail e
      = decide (e.num * s.val.den * avail ≤ e.den * s.val.num * rem) := by
  simp only [utilScaledGe, utilGe, Nat.mul_assoc]

/-- **Faithfulness for the scaled form.**  It agrees with comparing the edge
against the rational `(rem × s) / avail`, formed for real. -/
theorem utilScaledGe_eq_le (s : Pos) (rem avail : Nat) (e : Q) :
    utilScaledGe s rem avail e = Q.le e (Q.div (Q.mul (ofNat rem) s.val) (ofNat avail)) := by
  simp only [utilScaledGe, utilGe, Q.le, Q.div, Q.mul, ofNat, Nat.one_mul, Nat.mul_one]
  rw [Nat.mul_comm rem s.val.num, Nat.mul_comm e.den (s.val.num * rem)]

/-! ### §7.3's two verdicts

`u ≥ 1` is `need ≥ avail`, and IMPOSSIBLE is its strict half.  The gap between
them is one equation, which is worth saying out loud: an item is HOT but not
impossible exactly when its need equals its capacity to the minute. -/

def isHot (need avail : Nat) : Bool := utilGe need avail (ofNat 1)

def isImpossible (need avail : Nat) : Bool := decide (avail < need)

theorem isHot_iff (need avail : Nat) : isHot need avail = decide (avail ≤ need) := by
  simp [isHot, utilGe, ofNat]

theorem impossible_imp_hot {need avail : Nat} (h : isImpossible need avail = true) :
    isHot need avail = true := by
  simp only [isImpossible, decide_eq_true_eq] at h
  simp only [isHot_iff, decide_eq_true_eq]
  omega

theorem hot_and_possible_iff_exact (need avail : Nat) :
    (isHot need avail = true ∧ isImpossible need avail = false) ↔ need = avail := by
  simp only [isHot_iff, isImpossible, decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt]
  omega

/-! ## The bin ladder (§7.1)

`bin(u)`: `u ≥ 1 → HOT`; `0.5 ≤ u < 1 → +0`; `0.25 ≤ u < 0.5 → +1`;
`0.1 ≤ u < 0.25 → +2`; `u < 0.1 → +3`.  The edges are `config.priority_bins`, so
they are a list, not a generator: three of them are halvings and the fourth is
`1/10` rather than `1/8`, and `log2_ladder_disagrees_at_eleven_percent`
exhibits a `u` at which the generator and the table give different answers.

Two formulations, and they agree wherever the edges are sorted:

* `ladderIx` scans from the top and stops at the first edge reached — §7.1 as
  written;
* `rungs` **counts** the edges not reached — antitone in `u` for a reason (each
  edge's test is antitone, and a count of antitone tests is antitone), and
  antitone without needing the edges sorted.
-/

/-- The implicit top edge: `u ≥ 1` is HOT, and is off the configurable ladder. -/
def hotEdge : Q := ofNat 1

/-- §16 `[priority] bins = [0.5, 0.25, 0.1]`, as data. -/
def defaultBins : List Q := [⟨1, 2⟩, ⟨1, 4⟩, ⟨1, 10⟩]

/-- The generating structure a first-principles reading suggests: keep
halving. -/
def log2Bins : List Q := [⟨1, 2⟩, ⟨1, 4⟩, ⟨1, 8⟩]

/-- Every edge must denote a rational; `∞` is not an edge. -/
def binsWf (bins : List Q) : Bool := bins.all (fun e => e.ok)

/-- The ladder counts down: each edge is no larger than the one before it. -/
def descending : List Q → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => Q.le b a && descending (b :: t)

/-- **The ladder, as a count.**  How many edges of `1 :: bins` does `u` fail to
reach?  `0` means `u ≥ 1`, which is HOT. -/
def rungs (bins : List Q) (need avail : Nat) : Nat :=
  (hotEdge :: bins).countP (fun e => ! utilGe need avail e)

/-- §7.2's bin.  HOT is off the scale (`p = 0`); otherwise `p = k + n`. -/
inductive Bin where
  | hot
  | plus (n : Nat)
deriving DecidableEq, Repr, Inhabited

/-- Urgency as one number, `0` most urgent, so that "never a larger bin" is a
statement about `Nat`. -/
def Bin.ix : Bin → Nat
  | .hot => 0
  | .plus n => n + 1

def binOf (bins : List Q) (need avail : Nat) : Bin :=
  match rungs bins need avail with
  | 0 => .hot
  | n + 1 => .plus n

theorem binOf_ix (bins : List Q) (need avail : Nat) :
    (binOf bins need avail).ix = rungs bins need avail := by
  unfold binOf
  cases rungs bins need avail with
  | zero => rfl
  | succ n => rfl

theorem binOf_eq_hot_iff (bins : List Q) (need avail : Nat) :
    binOf bins need avail = .hot ↔ rungs bins need avail = 0 := by
  unfold binOf
  cases h : rungs bins need avail with
  | zero => simp
  | succ n => simp

theorem binOf_eq_plus_iff (bins : List Q) (need avail n : Nat) :
    binOf bins need avail = .plus n ↔ rungs bins need avail = n + 1 := by
  unfold binOf
  cases h : rungs bins need avail with
  | zero => simp
  | succ m => simp

theorem rungs_le (bins : List Q) (need avail : Nat) :
    rungs bins need avail ≤ bins.length + 1 := by
  have h := List.countP_le_length (p := fun e => ! utilGe need avail e) (l := hotEdge :: bins)
  simpa [rungs] using h

/-- With the default edges the ladder never leaves `0..3`, so §7.2's
`clamp p to 0..=7` never fires on the bin's account: `k ≤ 4` and `bin ≤ 3`. -/
theorem default_bin_le_three (need avail : Nat) :
    ∀ n, binOf defaultBins need avail = .plus n → n ≤ 3 := by
  intro n h
  have hlen := rungs_le defaultBins need avail
  have hix : (binOf defaultBins need avail).ix = rungs defaultBins need avail :=
    binOf_ix _ _ _
  rw [h] at hix
  simp only [Bin.ix, defaultBins, List.length_cons, List.length_nil] at hix hlen
  omega

/-- Zero capacity reaches every edge, so it is HOT.  No `is_finite()` guard, no
branch. -/
theorem rungs_capacity_zero (bins : List Q) (need : Nat) : rungs bins need 0 = 0 := by
  simp only [rungs]
  refine List.countP_eq_zero.mpr ?_
  intro a _
  simp [utilGe]

theorem binOf_capacity_zero (bins : List Q) (need : Nat) : binOf bins need 0 = .hot := by
  simp only [binOf, rungs_capacity_zero]

/-- One edge's test is antitone in `u`.  This is transitivity, `e ≤ u₁ ≤ u₂`,
and it needs `u₁` to denote something. -/
theorem utilGe_mono {n₁ a₁ n₂ a₂ : Nat} (hd : utilDefined n₁ a₁ = true)
    (h : Q.le (util n₁ a₁) (util n₂ a₂) = true) (e : Q) :
    utilGe n₁ a₁ e = true → utilGe n₂ a₂ e = true := by
  intro he
  rw [utilGe_eq_le] at he ⊢
  exact Q.le_trans hd he h

/-- **The ladder is antitone.**  A larger `u` never gets a larger bin — for any
edge list at all, sorted or not, because a count of antitone tests is
antitone. -/
theorem rungs_antitone (bins : List Q) {n₁ a₁ n₂ a₂ : Nat}
    (hd : utilDefined n₁ a₁ = true)
    (h : Q.le (util n₁ a₁) (util n₂ a₂) = true) :
    rungs bins n₂ a₂ ≤ rungs bins n₁ a₁ := by
  simp only [rungs]
  refine List.countP_mono_left ?_
  intro e _ hfail
  simp only [Bool.not_eq_true'] at hfail ⊢
  rcases Bool.eq_false_or_eq_true (utilGe n₁ a₁ e) with h1 | h1
  · rw [utilGe_mono hd h e h1] at hfail
    exact Bool.noConfusion hfail
  · exact h1

theorem binOf_antitone (bins : List Q) {n₁ a₁ n₂ a₂ : Nat}
    (hd : utilDefined n₁ a₁ = true)
    (h : Q.le (util n₁ a₁) (util n₂ a₂) = true) :
    (binOf bins n₂ a₂).ix ≤ (binOf bins n₁ a₁).ix := by
  rw [binOf_ix, binOf_ix]
  exact rungs_antitone bins hd h

/-- More need at the same capacity never improves the bin.  Unconditional: the
`⟨0,0⟩` hole is filled by `rungs_capacity_zero`. -/
theorem rungs_mono_need (bins : List Q) {n₁ n₂ avail : Nat} (h : n₁ ≤ n₂) :
    rungs bins n₂ avail ≤ rungs bins n₁ avail := by
  rcases Nat.eq_zero_or_pos avail with ha | ha
  · subst ha; simp only [rungs_capacity_zero]; exact Nat.le_refl _
  · refine rungs_antitone bins ((utilDefined_iff _ _).mpr (Or.inl ha)) ?_
    exact Q.le_of (Nat.mul_le_mul_right _ h)

/-- More capacity for the same need never worsens the bin. -/
theorem rungs_anti_avail (bins : List Q) {need a₁ a₂ : Nat} (hne : 0 < need) (h : a₁ ≤ a₂) :
    rungs bins need a₁ ≤ rungs bins need a₂ := by
  refine rungs_antitone bins ((utilDefined_iff _ _).mpr (Or.inr hne)) ?_
  exact Q.le_of (Nat.mul_le_mul_left _ h)

/-! ### §7.1 as written, and the two formulations agreeing -/

/-- The first edge `u` reaches, scanning from the top. -/
def firstReach (need avail : Nat) : List Q → Nat
  | [] => 0
  | e :: es => if utilGe need avail e then 0 else 1 + firstReach need avail es

/-- §7.1's ladder in its written form. -/
def ladderIx (bins : List Q) (need avail : Nat) : Nat :=
  firstReach need avail (hotEdge :: bins)

/-- Once one edge is reached, every edge below it is: the tail contributes
nothing to the count.  This is where sortedness is needed, and the only place
it is. -/
theorem countP_tail_zero (need avail : Nat) :
    ∀ (bins : List Q) (e : Q), e.ok = true → utilGe need avail e = true →
      descending (e :: bins) = true → binsWf bins = true →
      bins.countP (fun e' => ! utilGe need avail e') = 0 := by
  intro bins
  induction bins with
  | nil => intro _ _ _ _ _; rfl
  | cons b t ih =>
    intro e he hue hd hwf
    simp only [descending, Bool.and_eq_true] at hd
    obtain ⟨hbe, hdt⟩ := hd
    have hbwf : b.ok = true := (List.all_eq_true.mp hwf) b (by simp)
    have htwf : binsWf t = true := by
      simp only [binsWf, List.all_eq_true] at hwf ⊢
      intro x hx; exact hwf x (by simp [hx])
    -- `b ≤ e ≤ u`, so `u` reaches `b` too.
    have hub : utilGe need avail b = true := by
      rw [utilGe_eq_le] at hue ⊢
      exact Q.le_trans (Q.ok_defined he) hbe hue
    rw [List.countP_cons, ih b hbwf hub hdt htwf]
    simp [hub]

/-- **The two ladders are one ladder.**  On a well-formed descending edge list,
"the first edge reached" and "the count of edges missed" are the same number —
so §7.1 as written and the antitone formulation are the same function. -/
theorem ladder_eq_rungs (bins : List Q) (need avail : Nat)
    (hwf : binsWf bins = true) (hd : descending (hotEdge :: bins) = true) :
    ladderIx bins need avail = rungs bins need avail := by
  have hgen : ∀ (l : List Q), binsWf l = true → descending l = true →
      firstReach need avail l = l.countP (fun e => ! utilGe need avail e) := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons a t ih =>
      intro hwf' hd'
      have hawf : a.ok = true := (List.all_eq_true.mp hwf') a (by simp)
      have htwf : binsWf t = true := by
        simp only [binsWf, List.all_eq_true] at hwf' ⊢
        intro x hx; exact hwf' x (by simp [hx])
      have hdt : descending t = true := by
        cases t with
        | nil => rfl
        | cons b t' =>
          simp only [descending, Bool.and_eq_true] at hd'
          exact hd'.2
      rw [firstReach, List.countP_cons]
      by_cases hua : utilGe need avail a = true
      · rw [if_pos hua, countP_tail_zero need avail t a hawf hua hd' htwf]
        simp [hua]
      · simp only [Bool.not_eq_true] at hua
        rw [if_neg (by simp [hua]), ih htwf hdt, hua]
        simp [Nat.add_comm]
  have hwf' : binsWf (hotEdge :: bins) = true := by
    simp only [binsWf, List.all_eq_true] at hwf ⊢
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · rfl
    · exact hwf x hx'
  exact hgen (hotEdge :: bins) hwf' hd

theorem default_ladder_eq_rungs (need avail : Nat) :
    ladderIx defaultBins need avail = rungs defaultBins need avail :=
  ladder_eq_rungs _ _ _ (by decide) (by decide)

/-! ### The table is the table

The edges are a carve-out — the one place the architecture says a generating
structure is *wrong* — so they are encoded as data.  What has to be shown is
that the data reproduce §7.1, and that comes in two strengths: ten witnesses at
the interval boundaries, and then the five intervals themselves. -/

theorem defaultBins_match_the_spec :
    binOf defaultBins 100 100 = .hot ∧
    binOf defaultBins 101 100 = .hot ∧
    binOf defaultBins 99 100 = .plus 0 ∧
    binOf defaultBins 50 100 = .plus 0 ∧
    binOf defaultBins 49 100 = .plus 1 ∧
    binOf defaultBins 25 100 = .plus 1 ∧
    binOf defaultBins 24 100 = .plus 2 ∧
    binOf defaultBins 10 100 = .plus 2 ∧
    binOf defaultBins 9 100 = .plus 3 ∧
    binOf defaultBins 0 100 = .plus 3 := by decide

/-- Reaching a larger edge implies reaching a smaller one. -/
theorem utilGe_edge_mono {need avail : Nat} {e f : Q} (hf : f.ok = true)
    (hef : Q.le e f = true) (h : utilGe need avail f = true) :
    utilGe need avail e = true := by
  rw [utilGe_eq_le] at h ⊢
  exact Q.le_trans (Q.ok_defined hf) hef h

/-- **§7.1's `bin(u)`, exactly.**  Not ten witnesses but the five intervals
themselves, each in the cross-multiplied form the kernel actually evaluates:
`u ≥ 1 → HOT`, `1/2 ≤ u < 1 → +0`, `1/4 ≤ u < 1/2 → +1`, `1/10 ≤ u < 1/4 → +2`,
`u < 1/10 → +3`.  The half-open intervals are not assumed — they come out of the
ladder, because reaching an edge implies reaching every smaller one. -/
theorem defaultBins_are_the_intervals (need avail : Nat) :
    (binOf defaultBins need avail = .hot ↔ utilGe need avail ⟨1, 1⟩ = true) ∧
    (binOf defaultBins need avail = .plus 0 ↔
        (utilGe need avail ⟨1, 1⟩ = false ∧ utilGe need avail ⟨1, 2⟩ = true)) ∧
    (binOf defaultBins need avail = .plus 1 ↔
        (utilGe need avail ⟨1, 2⟩ = false ∧ utilGe need avail ⟨1, 4⟩ = true)) ∧
    (binOf defaultBins need avail = .plus 2 ↔
        (utilGe need avail ⟨1, 4⟩ = false ∧ utilGe need avail ⟨1, 10⟩ = true)) ∧
    (binOf defaultBins need avail = .plus 3 ↔ utilGe need avail ⟨1, 10⟩ = false) := by
  have m10 : utilGe need avail ⟨1, 1⟩ = true → utilGe need avail ⟨1, 2⟩ = true :=
    utilGe_edge_mono (by decide) (by decide)
  have m21 : utilGe need avail ⟨1, 2⟩ = true → utilGe need avail ⟨1, 4⟩ = true :=
    utilGe_edge_mono (by decide) (by decide)
  have m32 : utilGe need avail ⟨1, 4⟩ = true → utilGe need avail ⟨1, 10⟩ = true :=
    utilGe_edge_mono (by decide) (by decide)
  simp only [binOf_eq_hot_iff, binOf_eq_plus_iff, rungs, defaultBins, hotEdge, ofNat,
    List.countP_cons, List.countP_nil]
  rcases Bool.eq_false_or_eq_true (utilGe need avail ⟨1, 1⟩) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (utilGe need avail ⟨1, 2⟩) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (utilGe need avail ⟨1, 4⟩) with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true (utilGe need avail ⟨1, 10⟩) with h3 | h3 <;>
    simp_all

/-- **Why the edges are data.**  The halving generator and §7.1's table give
different bins at `u = 0.11`: the table's last edge is `1/10`, the generator's
is `1/8`.  Deriving the ladder as `1/2^i` would be a silent behaviour change at
every `u` in `[0.1, 0.125)`. -/
theorem log2_ladder_disagrees_at_eleven_percent :
    binOf log2Bins 11 100 ≠ binOf defaultBins 11 100 := by decide

/-! ## Rounding

Three rules, named, each with the two facts a site needs of it: it is monotone,
and it is within one minute of the exact value.  `Pos` in the argument means a
zero denominator cannot reach them. -/

/-- `⌊num/den⌋`. -/
def floorQ (p : Pos) : Nat := p.val.num / p.val.den

/-- `⌈num/den⌉`. -/
def ceilQ (p : Pos) : Nat := (p.val.num + p.val.den - 1) / p.val.den

/-- Round half **up**: a tie goes to the larger whole minute. -/
def halfUpQ (p : Pos) : Nat := (2 * p.val.num + p.val.den) / (2 * p.val.den)

/-- `r` is within one minute of the exact value of `p`, in both directions. -/
def WithinOne (r : Nat) (p : Pos) : Prop :=
  r * p.val.den < p.val.num + p.val.den ∧ p.val.num < r * p.val.den + p.val.den

/-- The floor adjunction, `n ≤ ⌊p⌋ ↔ n ≤ p`, stated in `Q.le` because that is
what "agrees with the exact value" has to mean here. -/
theorem floorQ_spec (p : Pos) (n : Nat) :
    n ≤ floorQ p ↔ Q.le (ofNat n) p.val = true := by
  rw [floorQ, Nat.le_div_iff_mul_le (denPos p)]
  simp [Q.le, ofNat]

theorem floorQ_le_self (p : Pos) : Q.le (ofNat (floorQ p)) p.val = true :=
  (floorQ_spec p (floorQ p)).mp (Nat.le_refl _)

theorem self_lt_floorQ_succ (p : Pos) : Q.lt p.val (ofNat (floorQ p + 1)) = true := by
  simp only [Q.lt, ofNat, decide_eq_true_eq, Nat.mul_one]
  exact (Nat.div_lt_iff_lt_mul (denPos p)).mp (Nat.lt_succ_self _)

theorem floorQ_withinOne (p : Pos) : WithinOne (floorQ p) p := by
  have hd := denPos p
  have h1 : floorQ p * p.val.den ≤ p.val.num := Nat.div_mul_le_self _ _
  have h2 : p.val.num < (floorQ p + 1) * p.val.den :=
    (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self _)
  rw [Nat.add_mul, Nat.one_mul] at h2
  exact ⟨by omega, by omega⟩

theorem floorQ_mono {a b : Pos} (h : Q.le a.val b.val = true) : floorQ a ≤ floorQ b := by
  rw [floorQ_spec]
  simp only [Q.le, ofNat, decide_eq_true_eq, Nat.mul_one] at h ⊢
  refine cancelR (denPos a) ?_
  calc floorQ a * b.val.den * a.val.den
      = floorQ a * a.val.den * b.val.den := by rw [Nat.mul_right_comm]
    _ ≤ a.val.num * b.val.den := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
    _ ≤ b.val.num * a.val.den := h

theorem ceilQ_ge (p : Pos) : p.val.num ≤ ceilQ p * p.val.den := by
  have hd := denPos p
  have hlt : p.val.num + p.val.den - 1 < (ceilQ p + 1) * p.val.den :=
    (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self _)
  rw [Nat.add_mul, Nat.one_mul] at hlt
  omega

theorem ceilQ_lt (p : Pos) : ceilQ p * p.val.den < p.val.num + p.val.den := by
  have hd := denPos p
  have hle : ceilQ p * p.val.den ≤ p.val.num + p.val.den - 1 :=
    Nat.div_mul_le_self _ _
  omega

/-- The ceiling adjunction: `⌈p⌉ ≤ n ↔ p ≤ n`. -/
theorem ceilQ_spec (p : Pos) (n : Nat) :
    ceilQ p ≤ n ↔ Q.le p.val (ofNat n) = true := by
  simp only [Q.le, ofNat, decide_eq_true_eq, Nat.mul_one]
  have hd := denPos p
  constructor
  · intro h
    have h1 := Nat.mul_le_mul_right p.val.den h
    have h2 := ceilQ_ge p
    omega
  · intro h
    have hlt : p.val.num + p.val.den - 1 < (n + 1) * p.val.den := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    have h3 := (Nat.div_lt_iff_lt_mul hd).mpr hlt
    simp only [ceilQ]
    omega

theorem self_le_ceilQ (p : Pos) : Q.le p.val (ofNat (ceilQ p)) = true :=
  (ceilQ_spec p (ceilQ p)).mp (Nat.le_refl _)

theorem ceilQ_withinOne (p : Pos) : WithinOne (ceilQ p) p :=
  ⟨ceilQ_lt p, by have := ceilQ_ge p; have := denPos p; omega⟩

theorem ceilQ_mono {a b : Pos} (h : Q.le a.val b.val = true) : ceilQ a ≤ ceilQ b := by
  rw [ceilQ_spec]
  simp only [Q.le, ofNat, decide_eq_true_eq, Nat.mul_one] at h ⊢
  refine cancelR (denPos b) ?_
  calc a.val.num * b.val.den
      ≤ b.val.num * a.val.den := h
    _ ≤ ceilQ b * b.val.den * a.val.den := Nat.mul_le_mul_right _ (ceilQ_ge b)
    _ = ceilQ b * a.val.den * b.val.den := by rw [Nat.mul_right_comm]

theorem floorQ_le_ceilQ (p : Pos) : floorQ p ≤ ceilQ p := by
  refine cancelR (denPos p) ?_
  have h1 : floorQ p * p.val.den ≤ p.val.num := Nat.div_mul_le_self _ _
  have h2 := ceilQ_ge p
  omega

/-- Half-up is a floor, of a ratio shifted by a half. -/
theorem halfUpQ_eq_floor (p : Pos) :
    halfUpQ p = floorQ (mkPos (2 * p.val.num + p.val.den) (2 * p.val.den)
      (by have := denPos p; omega)) := rfl

/-- Half-up, characterised the same way: `n ≤ round(p) ↔ n - 1/2 ≤ p`. -/
theorem halfUpQ_spec (p : Pos) (n : Nat) :
    n ≤ halfUpQ p ↔ 2 * (n * p.val.den) ≤ 2 * p.val.num + p.val.den := by
  have hd : 0 < 2 * p.val.den := by have := denPos p; omega
  rw [halfUpQ, Nat.le_div_iff_mul_le hd]
  have e : n * (2 * p.val.den) = 2 * (n * p.val.den) := by
    rw [Nat.mul_left_comm]
  rw [e]

theorem halfUpQ_withinOne (p : Pos) : WithinOne (halfUpQ p) p := by
  have hd := denPos p
  have hle : 2 * (halfUpQ p * p.val.den) ≤ 2 * p.val.num + p.val.den :=
    (halfUpQ_spec p (halfUpQ p)).mp (Nat.le_refl _)
  have hgt : ¬ (2 * ((halfUpQ p + 1) * p.val.den) ≤ 2 * p.val.num + p.val.den) := by
    intro hc
    have := (halfUpQ_spec p (halfUpQ p + 1)).mpr hc
    omega
  rw [Nat.add_mul, Nat.one_mul] at hgt
  exact ⟨by omega, by omega⟩

theorem halfUpQ_mono {a b : Pos} (h : Q.le a.val b.val = true) : halfUpQ a ≤ halfUpQ b := by
  have h' := Q.le_elim h
  rw [halfUpQ_eq_floor, halfUpQ_eq_floor]
  refine floorQ_mono (Q.le_of ?_)
  show (2 * a.val.num + a.val.den) * (2 * b.val.den)
      ≤ (2 * b.val.num + b.val.den) * (2 * a.val.den)
  have eL : (2 * a.val.num + a.val.den) * (2 * b.val.den)
      = 2 * (2 * (a.val.num * b.val.den) + a.val.den * b.val.den) := by
    rw [Nat.mul_left_comm, Nat.add_mul, Nat.mul_assoc]
  have eR : (2 * b.val.num + b.val.den) * (2 * a.val.den)
      = 2 * (2 * (b.val.num * a.val.den) + b.val.den * a.val.den) := by
    rw [Nat.mul_left_comm, Nat.add_mul, Nat.mul_assoc]
  rw [eL, eR]
  refine Nat.mul_le_mul_left 2 ?_
  have ecomm : a.val.den * b.val.den = b.val.den * a.val.den := Nat.mul_comm _ _
  omega

theorem floorQ_le_halfUpQ (p : Pos) : floorQ p ≤ halfUpQ p := by
  refine (halfUpQ_spec p (floorQ p)).mpr ?_
  have h1 : floorQ p * p.val.den ≤ p.val.num := Nat.div_mul_le_self _ _
  omega

theorem halfUpQ_le_ceilQ (p : Pos) : halfUpQ p ≤ ceilQ p := by
  have hd := denPos p
  rcases Nat.lt_or_ge (ceilQ p) (halfUpQ p) with hc | hc
  · exfalso
    have h2 : 2 * ((ceilQ p + 1) * p.val.den) ≤ 2 * p.val.num + p.val.den :=
      (halfUpQ_spec p (ceilQ p + 1)).mp hc
    rw [Nat.add_mul, Nat.one_mul] at h2
    have h3 := ceilQ_ge p
    omega
  · exact hc

/-- The three rules agree wherever the division is exact, so a site's choice of
rule only ever moves the answer where there is genuinely a fraction to place. -/
theorem rounding_agrees_when_exact (p : Pos) (k : Nat) (h : p.val.num = k * p.val.den) :
    floorQ p = k ∧ ceilQ p = k ∧ halfUpQ p = k := by
  have hd := denPos p
  have hfl : floorQ p = k := by rw [floorQ, h, Nat.mul_div_cancel _ hd]
  have hce : ceilQ p = k := by
    refine Nat.le_antisymm ((ceilQ_spec p k).mpr (Q.le_of ?_)) ?_
    · show p.val.num * 1 ≤ k * p.val.den
      rw [h, Nat.mul_one]
      exact Nat.le_refl _
    · rw [← hfl]; exact floorQ_le_ceilQ p
  refine ⟨hfl, hce, Nat.le_antisymm ?_ ?_⟩
  · rw [← hce]; exact halfUpQ_le_ceilQ p
  · rw [← hfl]; exact floorQ_le_halfUpQ p

/-! ## The sites

Each site names its rule once, here, and the planner reads the name. -/

/-- Multiply a rational by a whole number, exactly. -/
def scale (s : Pos) (n : Nat) : Pos := mkPos (s.val.num * n) s.val.den (denPos s)

@[simp] theorem scale_num (s : Pos) (n : Nat) : (scale s n).val.num = s.val.num * n := rfl
@[simp] theorem scale_den (s : Pos) (n : Nat) : (scale s n).val.den = s.val.den := rfl

/-- §16 `[priority] safety = 1.3`. -/
def safety : Pos := mkPos 13 10 (by omega)

/-- §16 `[day] budget_ratio = 0.75`. -/
def budgetRatio : Pos := mkPos 3 4 (by omega)

/-- §16 `[week] plan_ratio = 0.8`. -/
def planRatio : Pos := mkPos 4 5 (by omega)

/-- **R1** — §7.3's reservation needs whole minutes, and it **ceilings**: a
margin rounded down stops being a margin.  The Rust rounds, at
`priority.rs:349` and again at `planner.rs:323`. -/
def needMin (s : Pos) (rem : Nat) : Nat := ceilQ (scale s rem)

/-- The reservation covers the exact need.  This is the property `round()`
loses, and the reason the rule is a ceiling. -/
theorem needMin_covers (s : Pos) (rem : Nat) :
    Q.le (scale s rem).val (ofNat (needMin s rem)) = true :=
  self_le_ceilQ _

/-- A safety factor of at least one leaves at least the remaining minutes. -/
theorem needMin_ge_remaining {s : Pos} (h : s.val.den ≤ s.val.num) (rem : Nat) :
    rem ≤ needMin s rem := by
  unfold needMin
  refine Nat.le_trans ((floorQ_spec (scale s rem) rem).mpr (Q.le_of ?_))
    (floorQ_le_ceilQ (scale s rem))
  show rem * s.val.den ≤ s.val.num * rem * 1
  rw [Nat.mul_one, Nat.mul_comm rem s.val.den]
  exact Nat.mul_le_mul_right rem h

/-- The default `safety = 1.3` satisfies that hypothesis, so the statement above
is about the configuration the spec ships. -/
theorem needMin_safety_ge_remaining (rem : Nat) : rem ≤ needMin safety rem :=
  needMin_ge_remaining (by decide) rem

theorem needMin_safety_examples :
    needMin safety 10 = 13 ∧ needMin safety 1 = 2 ∧ needMin safety 60 = 78 := by decide

/-- **The rounding at `priority.rs:349` is not on the ordering path.**  The bin
computed from the *rounded* need differs from the bin computed from the exact
one, so the comparison path uses `utilScaledGe` and `needMin` appears only where
whole minutes are actually reserved. -/
theorem rounding_the_need_changes_the_bin :
    utilScaledGe safety 1 2 hotEdge ≠ utilGe (needMin safety 1) 2 hotEdge := by decide

/-- **R2** — §8.1's budget: `floor(window_min / block_min × ratio)`, folded into
one division so that the constants never leave the integers.  `block_min = 0` is
not representable at the call. -/
def budgetBlocks (windowMin blockMin : Nat) (h : 0 < blockMin) (r : Pos) : Nat :=
  floorQ (mkPos (windowMin * r.val.num) (blockMin * r.val.den) (Nat.mul_pos h (denPos r)))

/-- §8.1's own worked example: 8h of window at 60m blocks with
`budget_ratio = 0.75` is 6 blocks. -/
theorem budget_eight_hours : budgetBlocks 480 60 (by omega) budgetRatio = 6 := by decide

/-- §8.1: "a late start gets a later end and the same budget formula, so the day
is proportional, never cancelled" — a longer window never gets a smaller
budget. -/
theorem budget_mono_window {w₁ w₂ b : Nat} (hb : 0 < b) (r : Pos) (h : w₁ ≤ w₂) :
    budgetBlocks w₁ b hb r ≤ budgetBlocks w₂ b hb r := by
  unfold budgetBlocks
  refine floorQ_mono (Q.le_of ?_)
  show w₁ * r.val.num * (b * r.val.den) ≤ w₂ * r.val.num * (b * r.val.den)
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)

/-- §16 `[week] plan_ratio` — "warn if planned > 0.8 × budget", cross
multiplied.  A comparison, so nothing rounds. -/
def overRatio (r : Pos) (planned budget : Nat) : Bool :=
  decide (r.val.num * budget < r.val.den * planned)

theorem overRatio_eq_lt (r : Pos) (planned budget : Nat) :
    overRatio r planned budget = Q.lt (Q.mul r.val (ofNat budget)) (ofNat planned) := by
  simp only [overRatio, Q.lt, Q.mul, ofNat, Nat.mul_one]
  rw [Nat.mul_comm planned r.val.den]

theorem overRatio_example :
    overRatio planRatio 5 6 = true ∧ overRatio planRatio 4 6 = false := by decide

/-- **R4** — §8.5's `est × duration multiplier`, rounded **half-up** to whole
minutes.  §3.5 measured this as the only site at which the exact kernel and the
`f64` Rust disagree: 0.09% of cases, by exactly one minute. -/
def plannedMin (mult : Pos) (est : Nat) : Nat := halfUpQ (scale mult est)

theorem plannedMin_mono {mult : Pos} {e₁ e₂ : Nat} (h : e₁ ≤ e₂) :
    plannedMin mult e₁ ≤ plannedMin mult e₂ := by
  unfold plannedMin
  refine halfUpQ_mono (Q.le_of ?_)
  show mult.val.num * e₁ * mult.val.den ≤ mult.val.num * e₂ * mult.val.den
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)

theorem plannedMin_withinOne (mult : Pos) (est : Nat) :
    WithinOne (plannedMin mult est) (scale mult est) := halfUpQ_withinOne _

/-- §8.5's own example: `2b × 1.6` at 60m blocks is 192 minutes. -/
theorem plannedMin_example : plannedMin (mkPos 8 5 (by omega)) 120 = 192 := by decide

/-! ### R5 — the §8.5 posterior

`w(Δt)` is `1` up to `posterior_full_hours` and falls linearly to `0` at
`posterior_zero_hours`.  Both clamps are `Nat` truncation, so the ramp is one
expression with no branches. -/

/-- The posterior weight `w(Δt)`, exactly.  `fullMin` and `zeroMin` are §16's
`posterior_full_hours` and `posterior_zero_hours`, in minutes. -/
def ramp (fullMin zeroMin : Nat) (h : fullMin < zeroMin) (dt : Nat) : Pos :=
  mkPos (min (zeroMin - fullMin) (zeroMin - dt)) (zeroMin - fullMin) (by omega)

theorem ramp_le_one (fullMin zeroMin : Nat) (h : fullMin < zeroMin) (dt : Nat) :
    Q.le (ramp fullMin zeroMin h dt).val (ofNat 1) = true := by
  simp only [ramp, Q.le, ofNat, mkPos_num, mkPos_den, decide_eq_true_eq,
    Nat.mul_one, Nat.one_mul]
  exact Nat.min_le_left _ _

/-- Full weight up to `fullMin`. -/
theorem ramp_full (fullMin zeroMin : Nat) (h : fullMin < zeroMin) {dt : Nat} (hdt : dt ≤ fullMin) :
    Q.equiv (ramp fullMin zeroMin h dt).val (ofNat 1) = true := by
  simp only [ramp, Q.equiv, ofNat, mkPos_num, mkPos_den, decide_eq_true_eq,
    Nat.mul_one, Nat.one_mul]
  omega

/-- No weight at or beyond `zeroMin`. -/
theorem ramp_zero (fullMin zeroMin : Nat) (h : fullMin < zeroMin) {dt : Nat} (hdt : zeroMin ≤ dt) :
    (ramp fullMin zeroMin h dt).val.num = 0 := by
  simp only [ramp, mkPos_num]
  omega

/-- **`ramp_antitone`** — a staler report weighs less.  §3.5 names this one. -/
theorem ramp_antitone (fullMin zeroMin : Nat) (h : fullMin < zeroMin) {d₁ d₂ : Nat} (hd : d₁ ≤ d₂) :
    Q.le (ramp fullMin zeroMin h d₂).val (ramp fullMin zeroMin h d₁).val = true := by
  refine Q.le_of ?_
  show min (zeroMin - fullMin) (zeroMin - d₂) * (zeroMin - fullMin)
      ≤ min (zeroMin - fullMin) (zeroMin - d₁) * (zeroMin - fullMin)
  exact Nat.mul_le_mul_right _ (by omega)

/-- §16's defaults: full weight for 3h, nothing after 6h. -/
def defaultRamp (dt : Nat) : Pos := ramp 180 360 (by omega) dt

theorem defaultRamp_examples :
    (defaultRamp 0).val = ⟨180, 180⟩ ∧
    (defaultRamp 180).val = ⟨180, 180⟩ ∧
    (defaultRamp 270).val = ⟨90, 180⟩ ∧
    (defaultRamp 360).val = ⟨0, 180⟩ ∧
    (defaultRamp 999).val = ⟨0, 180⟩ := by decide

/-- The corrected slot energy `pred(t') + δ·w`, as a signed numerator over
`w.den`.  `δ = rep − pred(t)` is a report's residual and is genuinely signed; it
is measured against `pred(t)` and applied to `pred(t')`, so the result is *not* a
convex combination of two energies and can leave `0..5` in both directions. -/
def posteriorNum (predAt : Nat) (delta : Int) (w : Pos) : Int :=
  (predAt : Int) * (w.val.den : Int) + delta * (w.val.num : Int)

/-- The clamp is load-bearing: a full-weight residual of `−5` against a later
prediction of `2` puts the corrected value below zero. -/
theorem posterior_can_go_negative : posteriorNum 2 (-5) (defaultRamp 0) < 0 := by decide

/-- **R5** — half-up, then clamp to the `0..5` energy scale.  The result is a
`Fin 6` by construction, so §8.5's scale is structural rather than asserted. -/
def energyAfter (predAt : Nat) (delta : Int) (w : Pos) : Fin 6 :=
  if h : 0 < posteriorNum predAt delta w then
    ⟨min 5 (halfUpQ (mkPos (posteriorNum predAt delta w).toNat w.val.den (denPos w))), by omega⟩
  else
    ⟨0, by omega⟩

theorem energyAfter_nonpos {predAt : Nat} {delta : Int} {w : Pos}
    (h : posteriorNum predAt delta w ≤ 0) : (energyAfter predAt delta w).val = 0 := by
  simp only [energyAfter, dif_neg (Int.not_lt.mpr h)]

/-- No report, no correction: the posterior is the prediction, clamped. -/
theorem energyAfter_no_report (predAt : Nat) (w : Pos) :
    (energyAfter predAt 0 w).val = min 5 predAt := by
  have hd := denPos w
  have hcast : (predAt : Int) * (w.val.den : Int) = ((predAt * w.val.den : Nat) : Int) :=
    (Int.natCast_mul _ _).symm
  have hnum : posteriorNum predAt 0 w = ((predAt * w.val.den : Nat) : Int) := by
    simp only [posteriorNum, Int.zero_mul, Int.add_zero, hcast]
  by_cases hp : predAt = 0
  · subst hp
    have : posteriorNum 0 0 w = 0 := by rw [hnum]; simp
    simp only [energyAfter, dif_neg (by omega : ¬ (0 < posteriorNum 0 0 w))]
    omega
  · have hk : 0 < predAt * w.val.den := Nat.mul_pos (Nat.pos_of_ne_zero hp) hd
    have hpos : 0 < posteriorNum predAt 0 w := by rw [hnum]; omega
    have htn : (posteriorNum predAt 0 w).toNat = predAt * w.val.den := by
      rw [hnum, Int.toNat_natCast]
    simp only [energyAfter, dif_pos hpos]
    have hex := rounding_agrees_when_exact
      (mkPos (posteriorNum predAt 0 w).toNat w.val.den (denPos w)) predAt
      (by simp only [mkPos_num, mkPos_den, htn])
    rw [hex.2.2]

theorem energyAfter_examples :
    (energyAfter 4 0 (defaultRamp 0)).val = 4 ∧
    (energyAfter 4 (-2) (defaultRamp 0)).val = 2 ∧
    (energyAfter 4 (-2) (defaultRamp 270)).val = 3 ∧
    (energyAfter 2 (-5) (defaultRamp 0)).val = 0 ∧
    (energyAfter 5 3 (defaultRamp 0)).val = 5 := by decide

/-! ### R10 — the §8.5 sleep-debt shift (stage 6 step L9)

Fork `energy::predict`: when the night was short, the base level loses
`model.sleep_shift(cfg).round()` levels **before** the `0..5` clamp.  The shift is a
configured decimal (`config.toml`'s `[energy.sleep_debt] shift`) or a fitted one
(`.tm/model.json`'s `sleep_debt_shift`, which `Model::sleep_shift` prefers), and §8.5
writes the fitted one as a shrunken *mean*, so it is genuinely **signed**.
`f64::round` is half **away from zero**: that is `halfUpQ` on the magnitude with the
sign put back, and it is *not* half-up on a negative value (`-1.5` rounds to `-2`,
not to `-1`).

`under_slept` — `slept_min as f64 / 60.0 < under_hours` — is a **comparison**, not a
rounding, and it cross-multiplies (`slept · den < 60 · num`): the table's note above
already says why a comparison has no row. -/

/-- A signed decimal, as a sign and a non-negative pair.  The host reads the sign off
the literal and sends it beside the magnitude, so nothing is rounded and nothing is
lost (D17). -/
structure Signed where
  neg : Bool
  mag : Pos

/-- The signed value's numerator, over `den`. -/
def Signed.num (s : Signed) : Int := if s.neg then -(s.mag.val.num : Int) else (s.mag.val.num : Int)

/-- The signed value's denominator, positive by construction. -/
def Signed.den (s : Signed) : Nat := s.mag.val.den

theorem Signed.den_pos (s : Signed) : 0 < s.den := denPos s.mag

/-- **R10** — `f64::round` on a signed decimal: half away from zero. -/
def roundAway (s : Signed) : Int := if s.neg then -(halfUpQ s.mag : Int) else (halfUpQ s.mag : Int)

/-- A pair with a zero numerator rounds to zero, whatever its sign. -/
theorem halfUpQ_of_zero_num {p : Pos} (h : p.val.num = 0) : halfUpQ p = 0 := by
  have hd := denPos p
  simp only [halfUpQ, h, Nat.mul_zero, Nat.zero_add]
  exact Nat.div_eq_of_lt (by omega)

/-- The sign-carrying half of R10's two laws, over the naturals it is built from. -/
theorem roundAway_withinOne_aux (neg : Bool) (h m d : Nat) (hlt : h * d < m + d)
    (hgt : m < h * d + d) :
    (if neg then -(h : Int) else (h : Int)) * (d : Int)
        < (if neg then -(m : Int) else (m : Int)) + (d : Int) ∧
      (if neg then -(m : Int) else (m : Int))
        < (if neg then -(h : Int) else (h : Int)) * (d : Int) + (d : Int) := by
  have hmul : ((h : Int)) * ((d : Int)) = ((h * d : Nat) : Int) := (Int.natCast_mul _ _).symm
  cases neg
  · simp only [Bool.false_eq_true, if_false, hmul]
    omega
  · simp only [if_true, Int.neg_mul, hmul]
    omega

/-- **R10 is within one level of the exact shift**, in both directions: the magnitude's
`WithinOne`, which the sign carries to the other end. -/
theorem roundAway_withinOne (s : Signed) :
    roundAway s * (s.den : Int) < s.num + (s.den : Int) ∧
      s.num < roundAway s * (s.den : Int) + (s.den : Int) := by
  obtain ⟨hlt, hgt⟩ := halfUpQ_withinOne s.mag
  exact roundAway_withinOne_aux s.neg (halfUpQ s.mag) s.mag.val.num s.mag.val.den hlt hgt

/-- The monotone half of R10's two laws, over the naturals it is built from. -/
theorem roundAway_mono_aux (na nb : Bool) (ma da mb db ha hb : Nat)
    (hda : 0 < da) (hdb : 0 < db)
    (hup : ma * db ≤ mb * da → ha ≤ hb) (hdown : mb * da ≤ ma * db → hb ≤ ha)
    (hza : ma = 0 → ha = 0) (hzb : mb = 0 → hb = 0)
    (h : (if na then -(ma : Int) else (ma : Int)) * (db : Int)
        ≤ (if nb then -(mb : Int) else (mb : Int)) * (da : Int)) :
    (if na then -(ha : Int) else (ha : Int)) ≤ (if nb then -(hb : Int) else (hb : Int)) := by
  have hA : ((ma : Int)) * ((db : Int)) = ((ma * db : Nat) : Int) := (Int.natCast_mul _ _).symm
  have hB : ((mb : Int)) * ((da : Int)) = ((mb * da : Nat) : Int) := (Int.natCast_mul _ _).symm
  cases na <;> cases nb <;>
    simp only [Bool.false_eq_true, if_false, if_true, Int.neg_mul, hA, hB] at h ⊢
  · have := hup (by omega); omega
  · -- `a ≥ 0 ≥ b` forces both magnitudes, and so both roundings, to zero
    have h1 : ma * db = 0 := by omega
    have h2 : mb * da = 0 := by omega
    have hma : ma = 0 := by rcases Nat.mul_eq_zero.mp h1 with h' | h' <;> omega
    have hmb : mb = 0 := by rcases Nat.mul_eq_zero.mp h2 with h' | h' <;> omega
    rw [hza hma, hzb hmb]
    omega
  · omega
  · have := hdown (by omega); omega

/-- **R10 is monotone**: a larger shift never subtracts less — within each sign and
across the two. -/
theorem roundAway_mono {a b : Signed} (h : a.num * (b.den : Int) ≤ b.num * (a.den : Int)) :
    roundAway a ≤ roundAway b := by
  simp only [Signed.num, Signed.den] at h
  simp only [roundAway]
  refine roundAway_mono_aux a.neg b.neg a.mag.val.num a.mag.val.den b.mag.val.num b.mag.val.den
    (halfUpQ a.mag) (halfUpQ b.mag) (denPos a.mag) (denPos b.mag)
    (fun hc => halfUpQ_mono (Q.le_of hc)) (fun hc => halfUpQ_mono (Q.le_of hc))
    (fun hc => halfUpQ_of_zero_num hc) (fun hc => halfUpQ_of_zero_num hc) h

/-- §16's default: a whole level, subtracted. -/
def defaultShift : Signed := ⟨false, mkPos 1 1 (by omega)⟩

/-- Half away from zero, both ways, and the default. -/
theorem roundAway_examples :
    roundAway defaultShift = 1 ∧
    roundAway ⟨false, mkPos 15 10 (by omega)⟩ = 2 ∧
    roundAway ⟨true, mkPos 15 10 (by omega)⟩ = -2 ∧
    roundAway ⟨false, mkPos 14 10 (by omega)⟩ = 1 ∧
    roundAway ⟨true, mkPos 14 10 (by omega)⟩ = -1 ∧
    roundAway ⟨true, mkPos 0 1 (by omega)⟩ = 0 := by decide

end Tm.Arith
