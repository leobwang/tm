import TmKernel.Plan
/-!
# Tree — §6.4's `remaining` and §5.4's series head

Fork-point `tm-core/src/tree.rs` is the home of both: `Tree::remaining` (with
`remaining_inner`) and `Tree::series_head`.  Both are functions of the plan and
nothing else — no log, no configuration beyond the block length, no clock — so
neither waits on AGENTS §10.5 q4 (which side replays the log) or q5 (how
`p_lounge` enters the lookahead).

## `remaining`, read off the fork point

`Tree::remaining_inner`, in order: an id the tree does not hold is `None`; a
`Done` or `Dropped` item (`State::is_closed`) is `Some(0)`; an item with its own
estimate (`Item::own_remaining` = `est` → `est_original` → `dur`) is that many
minutes; otherwise the children's remainings are summed, a child with no
estimate anywhere below it contributing nothing, and the answer is `None` when no
child contributed.  `seen` guards a parent cycle, which `planWf`'s
`parentsAcyclic` refuses before any plan exists (D6).

The kernel's `remainingAux` is that recursion with **structural fuel**
(`effectiveCiAux`'s pattern, AGENTS §5.10), so small witnesses reduce under
`decide`; `remainingOpt` runs it at `fuel p`, and `remainingOpt_step` /
`remainingOpt_is_the_unique_fixed_point` say the fuel is never the answer on a
well-formed plan: `remainingOpt` *is* the rollup, the one function the step
fixes.

**Deliberate differences from the fork point** (kernel/README.md, "Stage 5
step 1"): no `u32` saturation (a `Nat`); the children are enumerated in the
store's `dom` order, not `(file, line)` order, which a sum cannot see; there is
no `MIN_REMAINING_MIN` floor here because `Tree::remaining` has none — the floor
is `horizon::remaining_est`'s, the close's reading, and arrives with the close's
rewire (README gap 73, owed).

**`Goals.lean`'s three §6.4 rows are refuted as written** (`Boundary.lean`, on a loaded
plan): they quantify over settled items and have no `dur:` row, and the fork point
answers `0` for the first and reads `dur:` before the children.  The laws beside them
carry the two hypotheses (`remaining_is_the_est_key_when_set_and_unsettled`,
`remaining_falls_back_to_the_leading_estimate_when_unsettled`,
`remaining_falls_back_to_dur_when_unsettled`,
`remaining_sums_the_children_when_unsettled_with_no_dur`).

**Nothing here reads the log.**  `remaining` is a function of the plan; `done_minutes`
and `progress` are the owner's D9 tranche (the kernel replays the log) and will take
the replayed per-item minutes as a plain argument.

## The series head

`Tree::series_head(name)`: the first member of the section, in line order, whose
state is not `Done`/`Dropped`.  `seriesHead p k name` is that per document: the
unsettled member of document `k` sitting in a `## series:<name>` section
(`seriesOf`) with the least rank.  The fork point concatenates same-named
sections across files in file order; the kernel names the document (README,
"Stage 5 step 1", difference (s1)).
-/

namespace Tm

open Field (Dur)

/-! ## §6.4's `remaining` -/

/-- **A line's own remaining estimate** — fork-point `Item::own_remaining`:
`est:`, else the leading estimate as written (§3.1's `est_original`), else
`dur:`.  One function over the three views; `remainingAux` reads nothing else of
the line. -/
def ownRemaining (l : RawItem) : Option Dur :=
  match Field.viewEstKey l with
  | some d => some d
  | none   =>
    match Field.estLeadOf l with
    | some d => some d
    | none   => Field.viewDur l

/-- The goal statements read the leading estimate through `viewFields`; it is the
same view. -/
theorem viewFields_estLead (l : RawItem) :
    (Field.viewFields l).estLead = Field.estLeadOf l := rfl

theorem ownRemaining_of_estKey {l : RawItem} {d : Dur} (h : Field.viewEstKey l = some d) :
    ownRemaining l = some d := by
  simp [ownRemaining, h]

theorem ownRemaining_of_lead {l : RawItem} {d : Dur} (hno : Field.viewEstKey l = none)
    (h : Field.estLeadOf l = some d) : ownRemaining l = some d := by
  simp [ownRemaining, hno, h]

theorem ownRemaining_of_dur {l : RawItem} {d : Dur} (hno : Field.viewEstKey l = none)
    (hnolead : Field.estLeadOf l = none) (h : Field.viewDur l = some d) :
    ownRemaining l = some d := by
  simp [ownRemaining, hno, hnolead, h]

theorem ownRemaining_none {l : RawItem} (hno : Field.viewEstKey l = none)
    (hnolead : Field.estLeadOf l = none) (hnodur : Field.viewDur l = none) :
    ownRemaining l = none := by
  simp [ownRemaining, hno, hnolead, hnodur]

/-- §6.1's hierarchy one level down: the ids whose `@parent` is `i`, in `dom`
order (fork-point `Tree::children`). -/
def childrenOf (p : PlanCore) (i : Id) : List Id :=
  p.store.dom.filter (fun j => parentStep p j == some i)

theorem parentStep_of_mem_childrenOf {p : PlanCore} {i j : Id} (h : j ∈ childrenOf p i) :
    parentStep p j = some i := by
  simp only [childrenOf, List.mem_filter, beq_iff_eq] at h
  exact h.2

/-- `remaining_inner`'s accumulator: `None` until a child contributes. -/
def optAdd : Option Nat → Option Nat → Option Nat
  | none,   b      => b
  | some a, none   => some a
  | some a, some b => some (a + b)

theorem optAdd_getD (a b : Option Nat) : (optAdd a b).getD 0 = a.getD 0 + b.getD 0 := by
  cases a <;> cases b <;> simp [optAdd]

/-- One level of `remaining_inner`, with the children's answers supplied. -/
def remainingStep (bm : Nat) (p : PlanCore) (rec : Id → Option Nat) (i : Id) : Option Nat :=
  match p.store.get i with
  | none   => none
  | some e =>
    match e.val.status with
    | .settled _ => some 0
    | _ =>
      match ownRemaining e.val.line with
      | some d => some (Dur.minutes bm d)
      | none   => ((childrenOf p i).map rec).foldl optAdd none

/-- The recursion, with structural fuel so that it reduces. -/
def remainingAux (bm : Nat) (p : PlanCore) : Nat → Id → Option Nat
  | 0,     _ => none
  | n + 1, i => remainingStep bm p (remainingAux bm p n) i

/-- **§6.4's `remaining(item)`, as fork-point `Tree::remaining` answers it**:
`none` when neither the item nor anything below it has an estimate. -/
def remainingOpt (bm : Nat) (p : PlanCore) (i : Id) : Option Nat :=
  remainingAux bm p (fuel p) i

/-- **§6.4's `remaining(item)` in minutes**, `0` where `remainingOpt` has nothing. -/
def remainingMin (bm : Nat) (p : WfPlan) (i : Id) : Nat :=
  (remainingOpt bm p.val i).getD 0

/-! ### One step -/

theorem remainingStep_congr (bm : Nat) (p : PlanCore) {r₁ r₂ : Id → Option Nat} (i : Id)
    (h : ∀ j ∈ childrenOf p i, r₁ j = r₂ j) :
    remainingStep bm p r₁ i = remainingStep bm p r₂ i := by
  unfold remainingStep
  rw [List.map_congr_left h]

theorem remainingStep_missing (bm : Nat) (p : PlanCore) (rec : Id → Option Nat) (i : Id)
    (hget : p.store.get i = none) : remainingStep bm p rec i = none := by
  simp [remainingStep, hget]

theorem remainingStep_settled (bm : Nat) (p : PlanCore) (rec : Id → Option Nat) (i : Id)
    (e : Entity) (o : Outcome) (hget : p.store.get i = some e) (hs : e.val.status = .settled o) :
    remainingStep bm p rec i = some 0 := by
  simp [remainingStep, hget, hs]

theorem remainingStep_own (bm : Nat) (p : PlanCore) (rec : Id → Option Nat) (i : Id)
    (e : Entity) (d : Dur) (hget : p.store.get i = some e)
    (hopen : ∀ o : Outcome, e.val.status ≠ .settled o)
    (hown : ownRemaining e.val.line = some d) :
    remainingStep bm p rec i = some (Dur.minutes bm d) := by
  cases hs : e.val.status with
  | settled o => exact absurd hs (hopen o)
  | live h => simp [remainingStep, hget, hs, hown]
  | demoted => simp [remainingStep, hget, hs, hown]

theorem remainingStep_children (bm : Nat) (p : PlanCore) (rec : Id → Option Nat) (i : Id)
    (e : Entity) (hget : p.store.get i = some e)
    (hopen : ∀ o : Outcome, e.val.status ≠ .settled o)
    (hown : ownRemaining e.val.line = none) :
    remainingStep bm p rec i = ((childrenOf p i).map rec).foldl optAdd none := by
  cases hs : e.val.status with
  | settled o => exact absurd hs (hopen o)
  | live h => simp [remainingStep, hget, hs, hown]
  | demoted => simp [remainingStep, hget, hs, hown]

/-! ### The fuel is never the answer -/

/-- Walking `n + 1` links is walking `n` and then one more. -/
theorem anc_succ_bind (p : PlanCore) (n : Nat) (k : Id) :
    anc p (n + 1) k = (anc p n k).bind (parentStep p) := by
  rw [anc_add p n 1 k]
  cases anc p n k with
  | none => rfl
  | some x =>
    simp only [Option.bind_some]
    cases hs : parentStep p x with
    | none => exact anc_succ_none p 0 x hs
    | some y => rw [anc_succ_some p 0 x y hs]; rfl

/-- **On an acyclic plan no chain is `fuel p` links long** — from any id at all,
not only from the ids of the store. -/
theorem anc_fuel_none (p : PlanCore) (h : parentsAcyclic p = true) (k : Id) :
    anc p (fuel p) k = none := by
  by_cases hk : k ∈ p.store.dom
  · unfold parentsAcyclic at h
    have := List.all_eq_true.mp h k hk
    simpa using this
  · have hg : p.store.get k = none := by
      cases hg : p.store.get k with
      | none => rfl
      | some e => exact absurd ((p.store.domSpec k).mpr (by simp [hg])) hk
    have h1 : anc p 1 k = none := anc_succ_none p 0 k (by simp [parentStep, hg])
    have := anc_none_add p 1 k h1 p.store.dom.length
    simpa [fuel, Nat.add_comm] using this

theorem WfPlan.acyclic (p : WfPlan) : parentsAcyclic p.val = true :=
  (itemsWf_parts p.items).2.2.1

/-- A child of `i` has no descendant `n` links down when `i` has none `n + 1`
links down. -/
theorem anc_ne_of_child {p : PlanCore} {n : Nat} {i j : Id} (hj : j ∈ childrenOf p i)
    (h : ∀ k, anc p (n + 1) k ≠ some i) : ∀ k, anc p n k ≠ some j := by
  intro k hk
  apply h k
  rw [anc_succ_bind, hk]
  simpa using parentStep_of_mem_childrenOf hj

/-- **More fuel changes nothing** once nothing lies `n` links below `i`. -/
theorem remainingAux_stable (bm : Nat) (p : PlanCore) :
    ∀ n i m, (∀ k, anc p n k ≠ some i) → remainingAux bm p (n + m) i = remainingAux bm p n i := by
  intro n
  induction n with
  | zero => intro i m h; exact absurd (anc_zero p i) (h i)
  | succ n ih =>
    intro i m h
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [remainingAux]
    exact remainingStep_congr bm p i (fun j hj => ih j m (anc_ne_of_child hj h))

/-- **The fuel is always enough**: on a well-formed plan any larger fuel gives the
same answer. -/
theorem remainingAux_fuel_is_enough (bm : Nat) (p : WfPlan) (i : Id) (m : Nat) :
    remainingAux bm p.val (fuel p.val + m) i = remainingOpt bm p.val i :=
  remainingAux_stable bm p.val (fuel p.val) i m
    (fun k hk => by rw [anc_fuel_none p.val p.acyclic k] at hk; cases hk)

/-- **`remainingOpt` is the rollup**: one step of `remaining_inner` over its own
answers on the children, with no fuel in the statement. -/
theorem remainingOpt_step (bm : Nat) (p : WfPlan) (i : Id) :
    remainingOpt bm p.val i = remainingStep bm p.val (remainingOpt bm p.val) i := by
  show remainingAux bm p.val (p.val.store.dom.length + 1) i = _
  simp only [remainingAux]
  apply remainingStep_congr
  intro j hj
  have hlen : ∀ k, anc p.val p.val.store.dom.length k ≠ some j :=
    anc_ne_of_child hj (fun k hk => by
      rw [show p.val.store.dom.length + 1 = fuel p.val from rfl,
        anc_fuel_none p.val p.acyclic k] at hk
      cases hk)
  exact (remainingAux_stable bm p.val _ j 1 hlen).symm

/-- **And the only one**: every function the step fixes is `remainingOpt` — so the
rollup is determined by §6.4's sentence, not by how the recursion was bounded. -/
theorem remainingOpt_is_the_unique_fixed_point (bm : Nat) (p : WfPlan)
    (f : Id → Option Nat) (hf : ∀ i, f i = remainingStep bm p.val f i) (i : Id) :
    f i = remainingOpt bm p.val i := by
  have key : ∀ n i, (∀ k, anc p.val n k ≠ some i) → f i = remainingAux bm p.val n i := by
    intro n
    induction n with
    | zero => intro i h; exact absurd (anc_zero p.val i) (h i)
    | succ n ih =>
      intro i h
      rw [hf i]
      simp only [remainingAux]
      exact remainingStep_congr bm p.val i (fun j hj => ih j (anc_ne_of_child hj h))
  exact key (fuel p.val) i (fun k hk => by rw [anc_fuel_none p.val p.acyclic k] at hk; cases hk)

/-! ### §6.4's rows, in minutes -/

theorem foldl_optAdd_getD (f : Id → Option Nat) : ∀ (l : List Id) (acc : Option Nat),
    ((l.map f).foldl optAdd acc).getD 0 = l.foldl (fun a j => a + (f j).getD 0) (acc.getD 0)
  | [],     _   => rfl
  | j :: l, acc => by
    simp only [List.map_cons, List.foldl_cons]
    rw [foldl_optAdd_getD f l, optAdd_getD]

/-- A `Done` or `Dropped` item has nothing remaining, whatever its line says —
fork-point `remaining_inner`'s first rule. -/
theorem remaining_of_a_settled_item_is_zero (bm : Nat) (p : WfPlan) (i : Id) (e : Entity)
    (o : Outcome) (hget : p.val.store.get i = some e) (hs : e.val.status = .settled o) :
    remainingMin bm p i = 0 := by
  unfold remainingMin
  rw [remainingOpt_step, remainingStep_settled bm p.val _ i e o hget hs]
  rfl

/-- An id the plan does not hold has nothing remaining. -/
theorem remaining_of_a_missing_id_is_zero (bm : Nat) (p : WfPlan) (i : Id)
    (hget : p.val.store.get i = none) : remainingMin bm p i = 0 := by
  unfold remainingMin
  rw [remainingOpt_step, remainingStep_missing bm p.val _ i hget]
  rfl

/-- **§6.4 row 1, on an unsettled item.**  An explicit `est:` wins over the
leading estimate — C1 does not re-enter through the rollup. -/
theorem remaining_is_the_est_key_when_set_and_unsettled (bm : Nat) (p : WfPlan) (i : Id)
    (e : Entity) (d : Dur) (hget : p.val.store.get i = some e)
    (hopen : ∀ o : Outcome, e.val.status ≠ .settled o)
    (hd : Field.viewEstKey e.val.line = some d) :
    remainingMin bm p i = Dur.minutes bm d := by
  unfold remainingMin
  rw [remainingOpt_step, remainingStep_own bm p.val _ i e d hget hopen (ownRemaining_of_estKey hd)]
  rfl

/-- **§6.4 row 2, on an unsettled item.**  With no `est:`, the leading estimate as
written. -/
theorem remaining_falls_back_to_the_leading_estimate_when_unsettled (bm : Nat) (p : WfPlan)
    (i : Id) (e : Entity) (d : Dur) (hget : p.val.store.get i = some e)
    (hopen : ∀ o : Outcome, e.val.status ≠ .settled o)
    (hno : Field.viewEstKey e.val.line = Option.none)
    (hlead : (Field.viewFields e.val.line).estLead = some d) :
    remainingMin bm p i = Dur.minutes bm d := by
  unfold remainingMin
  rw [remainingOpt_step,
    remainingStep_own bm p.val _ i e d hget hopen (ownRemaining_of_lead hno hlead)]
  rfl

/-- **The fork point's row between 2 and 3**, which §6.4 does not write: with
neither estimate, `dur:` (fork-point `Item::own_remaining`). -/
theorem remaining_falls_back_to_dur_when_unsettled (bm : Nat) (p : WfPlan) (i : Id)
    (e : Entity) (d : Dur) (hget : p.val.store.get i = some e)
    (hopen : ∀ o : Outcome, e.val.status ≠ .settled o)
    (hno : Field.viewEstKey e.val.line = Option.none)
    (hnolead : (Field.viewFields e.val.line).estLead = Option.none)
    (hdur : Field.viewDur e.val.line = some d) :
    remainingMin bm p i = Dur.minutes bm d := by
  unfold remainingMin
  rw [remainingOpt_step,
    remainingStep_own bm p.val _ i e d hget hopen (ownRemaining_of_dur hno hnolead hdur)]
  rfl

/-- **§6.4 row 3, on an unsettled item with no `dur:`.**  The sum over children,
at any depth — each child's own `remainingMin`. -/
theorem remaining_sums_the_children_when_unsettled_with_no_dur (bm : Nat) (p : WfPlan)
    (i : Id) (e : Entity) (hget : p.val.store.get i = some e)
    (hopen : ∀ o : Outcome, e.val.status ≠ .settled o)
    (hno : Field.viewEstKey e.val.line = Option.none)
    (hnolead : (Field.viewFields e.val.line).estLead = Option.none)
    (hnodur : Field.viewDur e.val.line = Option.none) :
    remainingMin bm p i
      = (p.val.store.dom.filter (fun j => parentStep p.val j == some i)).foldl
          (fun a j => a + remainingMin bm p j) 0 := by
  unfold remainingMin
  rw [remainingOpt_step,
    remainingStep_children bm p.val _ i e hget hopen (ownRemaining_none hno hnolead hnodur)]
  exact foldl_optAdd_getD _ _ none

/-! ## §5.4's series head -/

/-- The unsettled members of `## series:<nm>` in document `k`, each with its rank. -/
def seriesOpen (p : PlanCore) (k : DocIx) (nm : List Char) : List (Id × Nat) :=
  p.store.dom.filterMap (fun i =>
    match p.store.get i with
    | none   => none
    | some e =>
      match e.val.status with
      | .settled _ => none
      | _ =>
        if decide (e.val.live.doc = k) && seriesOf p e.val.live == some nm then
          some (i, e.val.live.rank)
        else none)

/-- The entry of least rank (the earliest listed among equals). -/
def firstByRank : List (Id × Nat) → Option (Id × Nat)
  | []      => none
  | q :: qs =>
    match firstByRank qs with
    | none   => some q
    | some r => if r.2 < q.2 then some r else some q

theorem firstByRank_mem : ∀ {l : List (Id × Nat)} {r : Id × Nat}, firstByRank l = some r → r ∈ l
  | [], _, h => by simp [firstByRank] at h
  | q :: qs, r, h => by
    simp only [firstByRank] at h
    split at h
    · cases h; simp
    · rename_i r' hr'
      split at h
      · cases h; exact List.mem_cons_of_mem _ (firstByRank_mem hr')
      · cases h; simp

theorem firstByRank_isSome_cons (a : Id × Nat) (as : List (Id × Nat)) :
    (firstByRank (a :: as)).isSome = true := by
  simp only [firstByRank]
  split
  · rfl
  · split <;> rfl

theorem firstByRank_le : ∀ {l : List (Id × Nat)} {r : Id × Nat}, firstByRank l = some r →
    ∀ q ∈ l, r.2 ≤ q.2
  | [], _, h => by simp [firstByRank] at h
  | q :: qs, r, h => by
    simp only [firstByRank] at h
    intro x hx
    split at h
    · rename_i hn
      cases h
      cases List.mem_cons.mp hx with
      | inl hq => rw [hq]; exact Nat.le_refl _
      | inr hq => cases qs with
        | nil => cases hq
        | cons a as =>
          have := firstByRank_isSome_cons a as
          rw [hn] at this; cases this
    · rename_i r' hr'
      have hle := firstByRank_le hr'
      split at h
      · rename_i hlt
        cases h
        cases List.mem_cons.mp hx with
        | inl hq => rw [hq]; exact Nat.le_of_lt hlt
        | inr hq => exact hle x hq
      · rename_i hnlt
        cases h
        cases List.mem_cons.mp hx with
        | inl hq => rw [hq]; exact Nat.le_refl _
        | inr hq => exact Nat.le_trans (Nat.le_of_not_lt hnlt) (hle x hq)

theorem firstByRank_eq_none {l : List (Id × Nat)} : firstByRank l = none ↔ l = [] := by
  cases l with
  | nil => simp [firstByRank]
  | cons q qs =>
    simp only [firstByRank, reduceCtorEq, iff_false]
    split
    · simp
    · split <;> simp

/-- **§5.4's head**: the unsettled member of `## series:<name>` in document `k`
with the least rank — fork-point `Tree::series_head`, per document. -/
def seriesHead (p : WfPlan) (k : DocIx) (name : List Char) : Option Id :=
  (firstByRank (seriesOpen p.val k name)).map Prod.fst

theorem mem_seriesOpen {p : PlanCore} {k : DocIx} {nm : List Char} {i : Id} {r : Nat} :
    (i, r) ∈ seriesOpen p k nm ↔
      ∃ e, p.store.get i = some e ∧ (∀ o : Outcome, e.val.status ≠ .settled o) ∧
        e.val.live.doc = k ∧ seriesOf p e.val.live = some nm ∧ r = e.val.live.rank := by
  unfold seriesOpen
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨j, _, hj⟩
    split at hj
    · cases hj
    · rename_i e hge
      split at hj
      · cases hj
      · rename_i hns
        split at hj
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hj
          obtain ⟨rfl, rfl⟩ := hj
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
          exact ⟨e, hge, fun o h => hns o h, hc.1, hc.2, rfl⟩
        · cases hj
  · rintro ⟨e, hge, hun, hdoc, hser, rfl⟩
    refine ⟨i, (p.store.domSpec i).mpr (by simp [hge]), ?_⟩
    simp only [hge]
    cases hs : e.val.status with
    | settled o => exact absurd hs (hun o)
    | live h => simp [hdoc, hser]
    | demoted => simp [hdoc, hser]

/-- What the head is: an unsettled member of the series in that document. -/
theorem seriesHead_spec {p : WfPlan} {k : DocIx} {nm : List Char} {i : Id}
    (h : seriesHead p k nm = some i) :
    ∃ e, p.val.store.get i = some e ∧ (∀ o : Outcome, e.val.status ≠ .settled o) ∧
      e.val.live.doc = k ∧ seriesOf p.val e.val.live = some nm ∧
      ∀ j f, p.val.store.get j = some f → (∀ o : Outcome, f.val.status ≠ .settled o) →
        f.val.live.doc = k → seriesOf p.val f.val.live = some nm →
        e.val.live.rank ≤ f.val.live.rank := by
  unfold seriesHead at h
  cases hq : firstByRank (seriesOpen p.val k nm) with
  | none => rw [hq] at h; cases h
  | some q =>
    rw [hq] at h
    simp only [Option.map_some, Option.some.injEq] at h
    obtain ⟨qi, qr⟩ := q
    simp only at h
    subst h
    obtain ⟨e, hge, hun, hdoc, hser, hr⟩ := mem_seriesOpen.mp (firstByRank_mem hq)
    refine ⟨e, hge, hun, hdoc, hser, fun j f hgf hunf hdocf hserf => ?_⟩
    have := firstByRank_le hq (j, f.val.live.rank) (mem_seriesOpen.mpr ⟨f, hgf, hunf, hdocf, hserf, rfl⟩)
    simpa [hr] using this

/-- **§5.4: the head is not settled** — completing it hands the role to the next
line. -/
theorem the_series_head_is_not_settled (p : WfPlan) (k : DocIx) (nm : List Char)
    (i : Id) (e : Entity) (h : seriesHead p k nm = some i)
    (hget : p.val.store.get i = some e) (o : Outcome) :
    e.val.status ≠ .settled o := by
  obtain ⟨e', hge', hun, -⟩ := seriesHead_spec h
  rw [hget] at hge'
  cases hge'
  exact hun o

/-- **§5.4: the head is the first unsettled member** — no unsettled member of the
same series in the same document ranks ahead of it. -/
theorem the_series_head_ranks_first (p : WfPlan) (k : DocIx) (nm : List Char)
    (i j : Id) (e f : Entity) (h : seriesHead p k nm = some i)
    (hi : p.val.store.get i = some e) (hj : p.val.store.get j = some f)
    (_hsi : seriesOf p.val e.val.live = some nm) (hsj : seriesOf p.val f.val.live = some nm)
    (hk : f.val.live.doc = k) (hun : ∀ o : Outcome, f.val.status ≠ .settled o) :
    e.val.live.rank ≤ f.val.live.rank := by
  obtain ⟨e', hge', -, -, -, hfirst⟩ := seriesHead_spec h
  rw [hi] at hge'
  cases hge'
  exact hfirst j f hj hun hk hsj

/-- **The other direction (AGENTS §5.8): a series with an unsettled member has a
head.**  The check does not over-bite. -/
theorem seriesHead_isSome_of_an_unsettled_member (p : WfPlan) (k : DocIx) (nm : List Char)
    (j : Id) (f : Entity) (hj : p.val.store.get j = some f)
    (hun : ∀ o : Outcome, f.val.status ≠ .settled o) (hk : f.val.live.doc = k)
    (hsj : seriesOf p.val f.val.live = some nm) :
    (seriesHead p k nm).isSome = true := by
  unfold seriesHead
  cases hq : firstByRank (seriesOpen p.val k nm) with
  | some q => rfl
  | none =>
    have hmem := mem_seriesOpen.mpr ⟨f, hj, hun, hk, hsj, rfl⟩
    rw [firstByRank_eq_none.mp hq] at hmem
    cases hmem

/-- **And a series whose members are all settled has none** — the head is not a
default. -/
theorem seriesHead_none_when_every_member_is_settled (p : WfPlan) (k : DocIx) (nm : List Char)
    (hall : ∀ j f, p.val.store.get j = some f → f.val.live.doc = k →
      seriesOf p.val f.val.live = some nm → ∃ o : Outcome, f.val.status = .settled o) :
    seriesHead p k nm = none := by
  unfold seriesHead
  cases hq : firstByRank (seriesOpen p.val k nm) with
  | none => rfl
  | some q =>
    obtain ⟨qi, qr⟩ := q
    obtain ⟨f, hgf, hun, hdoc, hser, -⟩ := mem_seriesOpen.mp (firstByRank_mem hq)
    obtain ⟨o, ho⟩ := hall qi f hgf hdoc hser
    exact absurd ho (hun o)

end Tm
