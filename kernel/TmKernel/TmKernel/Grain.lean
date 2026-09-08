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

/-- A horizon reference as the user writes it: `tm move ^id week`, or
`backlog`, which is the *absence* of a bound. -/
inductive HorizonRef
  | bounded (g : Grain)
  | backlog
deriving DecidableEq, Repr

/-- The file a horizon reference names at `now`. -/
def HorizonRef.regionAt : HorizonRef → Day → Option Region
  | .bounded g, now => some (regionOf g now)
  | .backlog,   _   => none

end Tm
