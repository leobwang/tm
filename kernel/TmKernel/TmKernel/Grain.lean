import TmKernel.Cal
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

**What changed here.**  `index` used to be `d`, `d/7`, `d/30` — a toy, and the
module said so.  It is now the real calendar (`Cal.lean`): day, ISO week
ordinal, civil month ordinal, over proleptic Gregorian dates with leap years.
Every derivation below is unchanged, because none of them ever depended on
*which* partition each grain names — only on there being one per grain.  That
is the point of deriving them.

Two things the real calendar does change, and both are recorded rather than
hidden:

1. the two disagreement theorems about `horizon.rs`'s close rule **still hold**,
   and they are no longer accidents of the toy index: days 6 and 7 of the
   kernel's epoch are a Sunday and the Monday after it
   (`epoch_day_6_is_a_sunday`), which is exactly the case the finding names.
   They are also restated on a date a reader can check
   (`impl_day_rule_disagrees_2026`), and *generalised*: the two rules disagree
   **exactly** when the coarser period rolled over between the closed day and
   `now` (`impl_rule_disagrees_iff`), so this is a fact about closing late, not
   about one witness;
2. `week` does not refine `month` — an ISO week can straddle two civil months —
   so the top step of the chain is coarsening, not containment
   (`week_does_not_refine_month`).  The tie-break that resolves it is named in
   `Cal.lean`'s header and re-exported here as `monthOfWeek`.
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

/-- **Which block of grain `g` contains day `d`.**  Real arithmetic, from
`Cal.lean`: the day itself, the ISO week ordinal (`d / 7`, because the kernel's
day 0 is a Monday), and the civil month ordinal `12 * (year - 1) + month - 1`.

Each is a *monotone* function of the day (`index_mono`), which is the only
property the horizon order below uses. -/
def index (g : Grain) (d : Day) : Nat :=
  match g with
  | ⟨0, _⟩ => d
  | ⟨1, _⟩ => Cal.weekOrdinal d
  | _      => Cal.monthOrdinal d

theorem index_day   (d : Day) : index day d   = d                 := rfl
theorem index_week  (d : Day) : index week d  = Cal.weekOrdinal d := rfl
theorem index_month (d : Day) : index month d = Cal.monthOrdinal d := rfl

/-- Time only moves periods forward, at every grain. -/
theorem index_mono (g : Grain) {a b : Nat} (h : a ≤ b) : index g a ≤ index g b := by
  match g with
  | ⟨0, _⟩ => exact h
  | ⟨1, _⟩ => exact Cal.weekOrdinal_mono h
  | ⟨2, _⟩ => exact Cal.monthOrdinal_mono h

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

/-- The region a day is in is never closed at that day. -/
theorem regionOf_is_open (g : Grain) (now : Day) : ¬ Closed (regionOf g now) now := by
  simp [Closed, regionOf]

/-- **Once closed, always closed.**  This is what makes catch-up at stage 4 a
fold rather than a fixed point: a region the clock has passed cannot re-open,
so `autoClose`'s work only ever shrinks. -/
theorem closed_is_stable_in_time (r : Region) {a b : Nat} (h : a ≤ b) (hc : Closed r a) :
    Closed r b := by
  have := index_mono r.grain h
  simp only [Closed] at *
  omega

/-- **The single close rule.**  Closing grain `g` at `now` files leftovers into
the block of the next coarser grain that contains `now`. -/
def closeTo (g : Grain) (now : Day) : Region := regionOf (coarsen g) now

/-- The property that picks this rule out of the three the Rust uses, and the
reason it is worth the behaviour change: it can never file work into a file
that is already closed.  (This is also what makes `close` idempotence provable
at stage 4: the fold's own output is never back in scope.) -/
theorem closeTo_target_is_open (g : Grain) (now : Day) : ¬ Closed (closeTo g now) now :=
  regionOf_is_open (coarsen g) now

/-- The rule `close_day` actually uses (`IsoWeek::from_date(date)`,
horizon.rs:1323): the coarser block containing the *closed region*. -/
def targetContaining (g : Grain) (closedDay : Day) : Region := regionOf (coarsen g) closedDay

/-- **The three close rows, constant-folded** (D40).  `Check.lean` used to carry
`#eval (closeTo day 250, closeTo week 250, closeTo month 250)` beside its audit
lines, printing this triple for a reader; a print is not a check, and `#eval` is
the command a new axiom walked past every gate through (W-31 repair, README gap
2255), so the values it printed are asserted here instead.  Day 250 of the
epoch closes into week 35, and both coarser grains close into month 8 — which is
`coarsen_month` again, the fixed point, at a value rather than in general. -/
theorem the_three_close_rows_at_day_250 :
    (closeTo day 250, closeTo week 250, closeTo month 250)
      = (⟨week, 35⟩, ⟨month, 8⟩, ⟨month, 8⟩) := by decide

/-! ### The disagreement, re-checked over the real calendar

The toy index made `closeTo` and `targetContaining` differ at days 6 and 7
because `6 / 7 = 0` and `7 / 7 = 1`.  Over the real calendar the same two days
are Sunday 0001-01-07 and Monday 0001-01-08 — the *same* week boundary, for the
right reason now — so the two shipped findings survive verbatim.  But a single
witness was always the weak form.  The general statements are `iff`s. -/

theorem epoch_day_6_is_a_sunday : Cal.weekdayOf 6 = .sunday := by decide
theorem epoch_day_7_is_a_monday : Cal.weekdayOf 7 = .monday := by decide

/-- **The general form.**  The rule at horizon.rs:1323 and the derived rule
disagree exactly when the coarser period rolled over between the day that was
closed and the day the close is run — that is, exactly when the close is late. -/
theorem impl_rule_disagrees_iff (g : Grain) (closedDay now : Nat) :
    targetContaining g closedDay ≠ closeTo g now ↔
      index (coarsen g) closedDay ≠ index (coarsen g) now := by
  unfold targetContaining closeTo regionOf
  constructor
  · intro h hix; exact h (by rw [hix])
  · intro h hr; exact h (by injection hr)

/-- **And the general form of the second finding.**  The Rust's target is an
already-closed region exactly when the coarser period rolled over — so every
late `close day` files work into a week that is shut. -/
theorem containing_targets_a_closed_region_iff (g : Grain) (closedDay now : Nat) :
    Closed (targetContaining g closedDay) now ↔
      index (coarsen g) closedDay < index (coarsen g) now := by
  simp [Closed, targetContaining, regionOf]

/-- It disagrees with the derived rule, and the disagreement is a Sunday close
run on Monday: day 6 is in week 0, day 7 in week 1.  **A behaviour change that
needs the user's assent** — recorded, not decided. -/
theorem impl_day_rule_disagrees : targetContaining day 6 ≠ closeTo day 7 := by decide

/-- And the rule the Rust uses can target an already-closed week. -/
theorem containing_can_target_a_closed_region : Closed (targetContaining day 6) 7 := by decide

/-- The same two findings on a date a user would recognise: Sunday 2026-09-06
closed on Monday 2026-09-07, the first day of `week/2026-W37.md`. -/
theorem impl_day_rule_disagrees_2026 :
    targetContaining day (Cal.toDay ⟨2026, 9, 6⟩) ≠ closeTo day (Cal.toDay ⟨2026, 9, 7⟩) := by
  decide

theorem containing_can_target_a_closed_region_2026 :
    Closed (targetContaining day (Cal.toDay ⟨2026, 9, 6⟩)) (Cal.toDay ⟨2026, 9, 7⟩) := by
  decide

/-! ### Where the chain is containment, and where it is not

A grain refines the next one when "same block here" implies "same block there".
Below, `day` refines `week` — but only degenerately, because a day-block is a
single day, so *every* grain refines `week` from `day`.  It is stated to make
the contrast exact, not because it carries information.

`week` does **not** refine `month`, and that is the fact with content: the
`day ⊂ week ⊂ month` chain is containment at its first step and coarsening only
at its second.  Naming the month of a week is therefore a choice, made in
`Cal.lean`'s header and re-exported below. -/

/-- `g` refines `h`: any two days in one block of `g` are in one block of `h`. -/
def refines (g h : Grain) : Prop := ∀ a b : Nat, index g a = index g b → index h a = index h b

/-- Degenerate, and labelled as such: a day-block holds one day. -/
theorem day_refines_week : refines day week := by
  intro a b h
  rw [index_day, index_day] at h
  rw [h]

/-- **The fact with content.**  An ISO week can straddle two civil months —
2026-W36 runs Aug 31 to Sep 6 — so `week` does not refine `month`. -/
theorem week_does_not_refine_month : ¬ refines week month := by
  intro h
  have := h (Cal.toDay ⟨2026, 8, 31⟩) (Cal.toDay ⟨2026, 9, 6⟩) (by decide)
  revert this
  decide

/-- **The named tie-break**, at region level: the month region a week region
belongs to, taken from `Cal.monthOfIsoWeek` — the month containing the week's
Thursday.  Its stability is structural: `now` is not in the type. -/
def monthOfWeek (w : Nat) : Region := ⟨month, Cal.monthOfIsoWeek w⟩

/-- The month it names is one the week actually meets — by construction, since
the Thursday is in both. -/
theorem monthOfWeek_is_met (w : Nat) :
    ∃ d : Nat, index week d = w ∧ regionOf month d = monthOfWeek w :=
  ⟨Cal.thursdayOf w, Cal.thursdayOf_in_week w, rfl⟩

theorem monthOfWeek_mono {a b : Nat} (h : a ≤ b) : (monthOfWeek a).ix ≤ (monthOfWeek b).ix :=
  Cal.monthOfIsoWeek_mono h

/-- **The tie-break is not the close rule, and must not be confused with it.**
`closeTo week now` files into the month containing `now`, which is right because
a close happens at a time; `monthOfWeek w` names the month a week *belongs* to,
which must not depend on when you asked.  They are different functions and they
differ: close 2026-W36 on its own Monday (August 31st) and the leftovers go to
August, while the week itself is filed under September. -/
theorem closeTo_week_is_not_monthOfWeek :
    ∃ now : Nat, closeTo week now ≠ monthOfWeek (index week now) := by
  refine ⟨Cal.toDay ⟨2026, 8, 31⟩, ?_⟩
  decide

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
