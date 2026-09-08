/-!
# The horizon order, derived rather than enumerated

tm has eight horizon *files* (month, week, day, backlog, routines, optional,
calendar, and the day's `# Pinned` section).  The Rust models this as an enum
with hand-written transitions; §6.3 then states three separate close rules and
`horizon.rs` implements three different targets.

Here a **grain** is a partition of the timeline, the bounded grains form a
3-chain `day ⊂ week ⊂ month`, and every horizon fact is derived from one
generator: `coarsen`, the *saturating* successor of that chain.

* `demote` is one step along the chain.
* §6.3's three close rows are one operation at three grains; the third row
  ("`close month` files into the next month") is the **fixed point**, `rfl`.
* Backlog is the *absence* of a bound, not a coarser grain — which is why the
  successor saturates instead of running off the end.
-/
namespace Tm

/-- The bounded grains, indexed by position in the containment chain.
`Fin 3`, so `horizon: 99` is not a value that exists. -/
abbrev Grain := Fin 3

def day   : Grain := 0
def week  : Grain := 1
def month : Grain := 2

/-- **The generator.**  One step up the chain, saturating at the coarsest. -/
def coarsen (g : Grain) : Grain := ⟨min (g.val + 1) 2, by omega⟩

theorem coarsen_day   : coarsen day   = week  := rfl
theorem coarsen_week  : coarsen week  = month := rfl
/-- §6.3 row 3 is not a special case: it is the fixed point of rows 1-2. -/
theorem coarsen_month : coarsen month = month := rfl

theorem coarsen_saturates_only_at_month : ∀ g : Grain, coarsen g = g ↔ g = month := by
  decide

theorem coarsen_is_up (g : Grain) : g.val ≤ (coarsen g).val := by
  simp [coarsen]; omega

/-- `demote` is *defined* as one step along the chain.  There is no table of
legal (from, to) pairs to get wrong. -/
def demoteGrain (g : Grain) : Grain := coarsen g

theorem demote_is_one_step (g : Grain) : g ≠ month → (demoteGrain g).val = g.val + 1 := by
  revert g; decide

/-- A day number since an epoch.  Real calendar arithmetic is stage 5; what
matters here is that each grain has an index function. -/
abbrev Day := Nat

/-- Toy grain indexing, so the close rule can be *evaluated*.  The real kernel
uses ISO week and civil month arithmetic; the shape is this. -/
def index (g : Grain) (d : Day) : Nat :=
  match g with
  | ⟨0, _⟩ => d
  | ⟨1, _⟩ => d / 7
  | _      => d / 30

/-- One horizon file: a grain and one block of it. -/
structure Region where
  grain : Grain
  ix    : Nat
deriving DecidableEq, Repr, Inhabited

def regionOf (g : Grain) (d : Day) : Region := ⟨g, index g d⟩

/-- A region is *closed* at `now` once `now` has moved past it. -/
def Closed (r : Region) (now : Day) : Prop := index r.grain now > r.ix

instance (r : Region) (now : Day) : Decidable (Closed r now) := by
  unfold Closed; infer_instance

/-- **The single close rule.**  Closing grain `g` at `now` files leftovers into
the block of the next coarser grain that contains `now`. -/
def closeTo (g : Grain) (now : Day) : Region := regionOf (coarsen g) now

/-- The property that picks this rule out of the three the Rust uses, and the
reason it is worth the behaviour change: it can never file work into a file
that is already closed.  (This is also what makes `close` idempotence provable
at stage 4: the fold's own output is never back in scope.) -/
theorem closeTo_target_is_open (g : Grain) (now : Day) : ¬ Closed (closeTo g now) now := by
  simp [Closed, closeTo, regionOf]

/-- The rule `close_day` actually uses (`IsoWeek::from_date(date)`,
horizon.rs:1323): the coarser block containing the *closed region*. -/
def targetContaining (g : Grain) (closedDay : Day) : Region := regionOf (coarsen g) closedDay

/-- It disagrees with the derived rule, and the disagreement is a Sunday close
run on Monday: day 6 is in week 0, day 7 in week 1.  **A behaviour change that
needs the user's assent** — recorded, not decided. -/
theorem impl_day_rule_disagrees : targetContaining day 6 ≠ closeTo day 7 := by decide

/-- And the rule the Rust uses can target an already-closed week. -/
theorem containing_can_target_a_closed_region : Closed (targetContaining day 6) 7 := by decide

/-! ## The order a close generates

A demotion writes two lines: the tombstone stays in the region that was
**closed**, and the live copy goes to `closeTo`, which `closeTo_target_is_open`
says is never itself closed.  So the two regions of a demotion are never
interchangeable — one of them is behind the other in this order — and that is
the fact the loader inverts when both lines read `[-]`.

`Option Region` is a *horizon*: `none` is backlog, the **absence** of a bound.
Nothing closes backlog, so no tombstone can sit in it; it is therefore after
every bounded region and before none of them. -/

/-- Strictly before, on bounded regions: a finer grain is demoted into a coarser
one (day → week → month), and a month is closed into a later month — §6.3's
three rows, which are one rule (`closeTo`) at three grains. -/
def Region.precedes (a b : Region) : Bool :=
  decide (a.grain.val < b.grain.val) ||
    (decide (a.grain.val = b.grain.val) && decide (a.ix < b.ix))

/-- The same order on horizons, with backlog last. -/
def horizonPrecedes : Option Region → Option Region → Bool
  | some a, some b => Region.precedes a b
  | some _, none   => true
  | none,   _      => false

theorem horizonPrecedes_iff (a b : Region) :
    horizonPrecedes (some a) (some b) = true ↔
      (a.grain.val < b.grain.val ∨ (a.grain.val = b.grain.val ∧ a.ix < b.ix)) := by
  simp [horizonPrecedes, Region.precedes]

theorem horizonPrecedes_irrefl (r : Option Region) : horizonPrecedes r r = false := by
  cases r with
  | none => rfl
  | some a => simp [horizonPrecedes, Region.precedes]

/-- **Antisymmetry is what makes the loader determinate.**  At most one of the
two orientations of a pair of horizons is a demotion, so "which line is the
tombstone" is decided by the files and never by the order they were listed. -/
theorem horizonPrecedes_asymm {a b : Option Region} (h : horizonPrecedes a b = true) :
    horizonPrecedes b a = false := by
  rcases a with _ | a
  · simp [horizonPrecedes] at h
  · rcases b with _ | b
    · rfl
    · rw [horizonPrecedes_iff] at h
      have hn : ¬ (horizonPrecedes (some b) (some a) = true) := by
        rw [horizonPrecedes_iff]; omega
      simpa using hn

/-- **Where the order comes from: the close rule itself.**  Close grain `g` at
`now` and the tombstone's region — the one that was closed — comes strictly
before the region the leftovers were filed into.  For a bounded grain below
month the grain alone settles it; for month it is `Closed`, the hypothesis, that
does.  So every demotion `tm close` writes is orientable, and the loader does not
have to guess. -/
theorem demotion_target_follows_the_closed_region (r : Region) (now : Day) (h : Closed r now) :
    horizonPrecedes (some r) (some (closeTo r.grain now)) = true := by
  have hlt := r.grain.isLt
  simp only [Closed] at h
  rw [horizonPrecedes_iff]
  by_cases hg : r.grain.val = 2
  · have hfix : coarsen r.grain = r.grain := Fin.ext (by simp [coarsen, hg])
    simp only [closeTo, regionOf, hfix]
    exact Or.inr ⟨trivial, h⟩
  · left
    simp only [closeTo, regionOf, coarsen]
    omega

end Tm
