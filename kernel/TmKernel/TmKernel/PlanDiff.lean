import TmKernel.Planner
/-!
# `diff` and §9.1's overtime what-if — fork `planner::diff` and `planner::overtime_drops`

Stage 6, run W-34, track D.  README gaps **2680** onward are this module's.

## What this is, and why a module of its own

R3 deletes `tm-core/src/planner.rs` with its last caller, and two of those callers are the TUI's
§9.1 overtime prompt: `App::extend_drops` (`tm/src/tui/app.rs`) computes *"x extend +1 block →
drops: …"* as `planner::diff(&base, &alt).removed` — or, for an item that is not the running
one, through `planner::overtime_drops`, which is the same two plans and the same `diff`.  The
kernel had neither (W-31's R3 table, README gap 2228).

* `diff` is **fork `planner::diff`** (`planner.rs:2414`), read by function name: every item a
  plan holds keyed by the start of its **first** segment — Rest and Break rows skipped — and the
  three lists and the drift the fork derives from two such maps.  It is a function of two
  `DayPlan`s and nothing in `Planner` needs it: it is a *consumer* of the day, as `Emit` is, so
  it sits downstream of `Planner` rather than inside it.
* `overtimeDiff` is **stated over `dayPlan` and `diff`** and is not a second planner: the base
  day, the day of the what-if request, and the ids the second no longer holds.  The what-if is
  the one `App::extend_drops` actually runs — the running block's `active.est_min` grows *and* an
  `extra_min` override rides beside it (`PlanOverrides::extending`) — and the override is
  `Planner.PlanOverrides`, the value `PlanWire.readOptOverrides` already decodes, **reused**.

Two further reasons for a module of its own, both about the run it was written in: track H holds
the section of `Planner.lean` right after `dayPlan`, so a section appended there would have been
a merge conflict with nothing gained; and nothing here moves a line of `Planner.lean`, whose
check-9 pins are line-addressed (README gap 2136).

## What it does NOT do, by name

**`dayPlan` reads `PlanOverrides.drop` in one place (`PlanReq.activeRun`) and `estMin`/`extraMin`
in NONE.**  W-34 measured it (`grep -rn 'extraMin'` over the library, this file aside: the
structure, `isEmpty` and one decoder law, nothing else) — the what-if input crosses and reaches no
row.  Fork `PlanOverrides::apply` recomputes the extended candidate's `remaining_min`,
`planned_min` and `need_min`, so its step 5 gives the running group more commitment; this
kernel's step 5 reads `plannedMin` off the wire fact, so `overtimeDiff` sees the extension only
through the reservation §8.2 choice 5b sizes from `state.active.estMin`.  Recomputing
`planned_min` in the kernel is §8.5's `est × multiplier` (`Arith.plannedMin`, R4) applied to a
candidate the host sent, which is exactly where D34's line ("no candidate fact derived in the
kernel") is drawn, and the fork's with-ranking what-if keeps the base `p` for an item given more
minutes (README gap 114) — so it is an owner question and not this step's to take.  README gap
**2680** carries it; `tm/tests/planner_invariants.rs` measures what it costs on generated days.
-/

namespace Tm
namespace Planner

/-! ## `diff` -/

/-- **Fork `planner::PlanDiff`** (`planner.rs:2388`) — what changed between two plans of one
day.  Starts are absolute seconds, like every other instant here. -/
structure PlanDiff where
  /-- `(item, old start, new start)` for everything that moved. -/
  moved    : List (Id × Nat × Nat)
  /-- Items the new plan has and the old one did not. -/
  added    : List Id
  /-- Items the old plan had and the new one does not — §9's dropped tail. -/
  removed  : List Id
  /-- Σ minutes the moved items moved — the `plan` event's `drift_min` (§10.1). -/
  driftMin : Nat
deriving DecidableEq, Repr

/-! Fork `PlanDiff::is_empty` is **not** ported: no caller in `tm/src` reads it (the TUI reads
`.removed`), and a definition only theorems call is one check 12 is right to call dead (D51).
`diff_self` states "a plan diffed with itself is empty" over the four fields instead. -/

/-- **The rows `diff` reads** — fork `starts`' `if matches!(seg.kind, SegKind::Rest |
SegKind::Break) { continue; }`: every row but the day's Rest and its Breaks. -/
def diffRow (s : WfSeg) : Bool :=
  !(decide (s.val.kind = SegKind.rest) || decide (s.val.kind = SegKind.brk))

/-- **Every kind is read but Rest and Break**, run over ten of the eleven (a Batch holds its
members, and is read like a Block). -/
theorem diffRow_reads_every_kind_but_rest_and_break :
    ([SegKind.block, .brk, .routine, .wall, .rest, .optional, .windDown, .sleep, .lost, .ghost].map
      (fun k => diffRow (segOf ⟨0, 0, k, none, none, none, SegFlags.none, none, none, none⟩)))
      = [true, false, true, true, false, true, true, true, true, true] := by
  decide

/-- **An item's first start** — fork `starts`' value: the least `start` over the rows `diff`
reads that hold it (`seg.items()`: the row's item, or a batch's members). -/
def firstStart (d : DayPlan) (i : Id) : Option Nat :=
  ((d.segments.filter (fun s => diffRow s && decide (i ∈ segItems s))).map
    (fun s => s.val.start)).min?

/-- **The items a plan holds, once each, in serde's `String` order** — fork `starts`' keys, a
`BTreeMap<Id, _>` iterated in its own order.  `Seal.canon` over `Seal.idLt` is stage 5's one
canonical list in that order (`Log.charsLt`, "serde's `String` order"). -/
def diffIds (d : DayPlan) : List Id :=
  Seal.canon Seal.idLt ((d.segments.filter diffRow).flatMap segItems)

/-- **Fork `planner::diff`** (`planner.rs:2414`): for every item of the old plan, in key order,
*moved* when the new plan starts it elsewhere and *removed* when the new plan does not hold it;
*added* for every item of the new plan the old one did not hold; and the drift, Σ of the moves'
absolute minutes — `(new − old).num_minutes().unsigned_abs()`, which on whole seconds is
`Look.spanMinutes` of the pair taken in order. -/
def diff (old new : DayPlan) : PlanDiff :=
  let moved := (diffIds old).filterMap (fun i =>
    match firstStart old i, firstStart new i with
    | some s, some t => if s = t then none else some (i, s, t)
    | _, _ => none)
  { moved := moved
    added := (diffIds new).filter (fun i => !decide (i ∈ diffIds old))
    removed := (diffIds old).filter (fun i => !decide (i ∈ diffIds new))
    driftMin := (moved.map (fun m => Look.spanMinutes (min m.2.1 m.2.2) (max m.2.1 m.2.2))).sum }

/-! ### What `diff` is -/

/-- **An item is keyed exactly when a row `diff` reads holds it.** -/
theorem mem_diffIds (d : DayPlan) (i : Id) :
    i ∈ diffIds d ↔ ∃ s ∈ d.segments, diffRow s = true ∧ i ∈ segItems s := by
  unfold diffIds
  rw [Seal.mem_canon Seal.idLt_strictTotal, List.mem_flatMap]
  constructor
  · rintro ⟨s, hs, hi⟩
    obtain ⟨hs, hd⟩ := List.mem_filter.1 hs
    exact ⟨s, hs, hd, hi⟩
  · rintro ⟨s, hs, hd, hi⟩
    exact ⟨s, List.mem_filter.2 ⟨hs, hd⟩, hi⟩

/-- **The keys ascend strictly** — a `BTreeMap`'s, each once. -/
theorem diffIds_sorted (d : DayPlan) :
    (diffIds d).Pairwise (fun a b => Seal.idLt a b = true) :=
  Seal.sorted_canon Seal.idLt_strictTotal _

/-- **An item has a first start exactly when it is keyed.** -/
theorem firstStart_eq_none_iff (d : DayPlan) (i : Id) :
    firstStart d i = none ↔ i ∉ diffIds d := by
  unfold firstStart
  rw [List.min?_eq_none_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff, mem_diffIds]
  constructor
  · rintro h ⟨s, hs, hd, hi⟩
    exact absurd (h s hs) (by simp [hd, hi])
  · intro h s hs
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    exact fun hd hi => h ⟨s, hs, hd, hi⟩

/-- **The first start is the start of the first row that holds the item** — it is some row's
start, and no row `diff` reads holds the item earlier.  Fork `starts`' `min`, which on the
sorted day is the first segment's (`planner.rs:2410`: *"compared by the start of their first
segment"*). -/
theorem firstStart_spec (d : DayPlan) (i : Id) (t : Nat) (h : firstStart d i = some t) :
    (∃ s ∈ d.segments, diffRow s = true ∧ i ∈ segItems s ∧ s.val.start = t) ∧
      ∀ s ∈ d.segments, diffRow s = true → i ∈ segItems s → t ≤ s.val.start := by
  unfold firstStart at h
  rw [List.min?_eq_some_iff] at h
  obtain ⟨hm, hle⟩ := h
  refine ⟨?_, fun s hs hd hi => hle _ (List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, by simp [hd, hi]⟩, rfl⟩)⟩
  obtain ⟨s, hs, hst⟩ := List.mem_map.1 hm
  obtain ⟨hs, hdi⟩ := List.mem_filter.1 hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdi
  exact ⟨s, hs, hdi.1, hdi.2, hst⟩

/-- **Removed: held by the old plan and not by the new** — both directions. -/
theorem mem_diff_removed (a b : DayPlan) (i : Id) :
    i ∈ (diff a b).removed ↔ i ∈ diffIds a ∧ i ∉ diffIds b := by
  simp [diff, List.mem_filter]

/-- **Added: held by the new plan and not by the old** — both directions. -/
theorem mem_diff_added (a b : DayPlan) (i : Id) :
    i ∈ (diff a b).added ↔ i ∈ diffIds b ∧ i ∉ diffIds a := by
  simp [diff, List.mem_filter]

/-- **Moved: held by both, first started at two different instants** — both directions, and the
two instants are the two first starts. -/
theorem mem_diff_moved (a b : DayPlan) (i : Id) (s t : Nat) :
    (i, s, t) ∈ (diff a b).moved ↔ firstStart a i = some s ∧ firstStart b i = some t ∧ s ≠ t := by
  show (i, s, t) ∈ (diffIds a).filterMap _ ↔ _
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨j, -, hj⟩
    revert hj
    cases ha : firstStart a j <;> cases hb : firstStart b j <;> simp only [reduceCtorEq, imp_self,
      false_implies]
    rename_i s' t'
    by_cases hst : s' = t'
    · simp [hst]
    · simp only [hst, if_false, Option.some.injEq, Prod.mk.injEq]
      rintro ⟨rfl, rfl, rfl⟩
      exact ⟨ha, hb, hst⟩
  · rintro ⟨ha, hb, hst⟩
    refine ⟨i, ?_, ?_⟩
    · exact Classical.byContradiction (fun hn => by
        rw [← firstStart_eq_none_iff] at hn
        rw [hn] at ha
        cases ha)
    · simp [ha, hb, hst]

/-- **An item that keeps its opening slot is not moved**, whatever else it gains — the fork's
own sentence, *"an item that keeps its opening slot but gains another one does not count as
moved"*. -/
theorem an_item_that_keeps_its_first_start_is_not_moved (a b : DayPlan) (i : Id)
    (h : firstStart a i = firstStart b i) (s t : Nat) : (i, s, t) ∉ (diff a b).moved := by
  rw [mem_diff_moved]
  rintro ⟨ha, hb, hst⟩
  rw [h, hb] at ha
  exact hst (Option.some.inj ha).symm

/-- **What is removed and what is added are disjoint** — one is in the old plan only, the
other in the new plan only. -/
theorem diff_removed_and_added_are_disjoint (a b : DayPlan) (i : Id)
    (h : i ∈ (diff a b).removed) : i ∉ (diff a b).added := by
  rw [mem_diff_removed] at h
  rw [mem_diff_added]
  exact fun h' => h.2 h'.1

/-- **A moved item is neither removed nor added** — it is in both plans. -/
theorem a_moved_item_is_neither_removed_nor_added (a b : DayPlan) (i : Id) (s t : Nat)
    (h : (i, s, t) ∈ (diff a b).moved) : i ∉ (diff a b).removed ∧ i ∉ (diff a b).added := by
  obtain ⟨ha, hb, -⟩ := (mem_diff_moved a b i s t).1 h
  have hia : i ∈ diffIds a := Classical.byContradiction (fun hn => by
    rw [← firstStart_eq_none_iff] at hn; rw [hn] at ha; cases ha)
  have hib : i ∈ diffIds b := Classical.byContradiction (fun hn => by
    rw [← firstStart_eq_none_iff] at hn; rw [hn] at hb; cases hb)
  rw [mem_diff_removed, mem_diff_added]
  exact ⟨fun h' => h'.2 hib, fun h' => h'.2 hia⟩

/-- **The removed and added ids ascend strictly**, each once — the fork's `BTreeMap` order, and
not *"the order the first plan had them"*, which `overtime_drops`' own doc comment says and its
code does not do (README gap 2681). -/
theorem diff_removed_sorted (a b : DayPlan) :
    (diff a b).removed.Pairwise (fun x y => Seal.idLt x y = true) :=
  List.Pairwise.sublist List.filter_sublist (diffIds_sorted a)

theorem diff_added_sorted (a b : DayPlan) :
    (diff a b).added.Pairwise (fun x y => Seal.idLt x y = true) :=
  List.Pairwise.sublist List.filter_sublist (diffIds_sorted b)

/-- **The drift is the moves' minutes**, Σ over `moved` of the minutes between its two starts. -/
theorem diff_driftMin_is_the_moved_minutes (a b : DayPlan) :
    (diff a b).driftMin =
      ((diff a b).moved.map (fun m => Look.spanMinutes (min m.2.1 m.2.2) (max m.2.1 m.2.2))).sum :=
  rfl

/-- **A plan diffed with itself is empty**, drift included — the law every caller that asks
"did the replan move anything" rests on. -/
theorem diff_self (d : DayPlan) : diff d d = ⟨[], [], [], 0⟩ := by
  have hm : (diffIds d).filterMap (fun i =>
      match firstStart d i, firstStart d i with
      | some s, some t => if s = t then none else some (i, s, t)
      | _, _ => none) = [] := by
    refine List.filterMap_eq_nil_iff.2 (fun i _ => ?_)
    cases firstStart d i <;> simp
  have hr : (diffIds d).filter (fun i => !decide (i ∈ diffIds d)) = [] :=
    List.filter_eq_nil_iff.2 (fun i hi => by simp [hi])
  simp only [diff, hm, hr, List.map_nil, List.sum_nil]

/-! ## §9.1's overtime what-if -/

/-- **The what-if request `App::extend_drops` runs**: `m` more minutes on `i` — the running
block's `active.est_min` grows when `i` is the running item (`runtime.active.est_min =
est_min.saturating_add(minutes)`, because `planner::active_run` sizes the reservation from it and
never reads `extra_min`), and one `extra_min` override rides beside it (`PlanOverrides::new()
.extending(id, minutes)`, which REPLACES the request's overrides, as `with_overrides` does).  The
override is `Planner.PlanOverrides`, the value `PlanWire.readOptOverrides` decodes — reused, not
re-typed.  Nothing else of the request moves. -/
def PlanReq.extending (r : PlanReq) (i : Id) (m : Nat) : PlanReq :=
  { r with
    state := { r.state with
      active := r.state.active.map (fun a => if a.id = i then { a with estMin := a.estMin + m } else a) }
    overrides := some ⟨Capped.nil, ⟨[(i, m)], by show 1 ≤ maxCands; decide⟩, Capped.nil⟩ }

/-- **Fork `planner::overtime_drops`** (`planner.rs:708`) and `App::extend_drops`' own branch
for the running block (`app.rs:1220-1240`), whole: the day as it stands against the day with
`blocks` more blocks on `i` (fork `blocks.saturating_mul(block_min)` minutes), as `diff` answers
it.  Since W-36 (D58, README gap 2873) the extended day carries the HOST's grown facts `g` when
the host sends them (`PlanReq.growing`: fork `PlanOverrides::apply`'s `remaining_min` and
`planned_min`), so step 5 gives the extended group the fork's commitment; with none it is the
estimate's what-if, parity P44's.  No second definition holds `.removed` alone: it would be a
projection the wire does not call, and check 12 would be right to call it dead (D51). -/
def overtimeDiff (r : PlanReq) (i : Id) (blocks : Nat) (g : Option WfGrown) : PlanDiff :=
  diff (dayPlan r) (dayPlan ((r.extending i (blocks * r.blockMin)).growing i g))

/-! ### What the what-if is -/

/-- **The extension moves the running estimate and the overrides, and nothing else.** -/
theorem the_extension_moves_only_the_running_estimate_and_the_overrides (r : PlanReq) (i : Id)
    (m : Nat) :
    (r.extending i m).plan = r.plan ∧ (r.extending i m).run = r.run ∧
      (r.extending i m).look = r.look ∧ (r.extending i m).cands = r.cands ∧
      (r.extending i m).prio = r.prio ∧ (r.extending i m).routines = r.routines ∧
      (r.extending i m).state.brk = r.state.brk ∧
      (r.extending i m).state.interrupt = r.state.interrupt ∧
      (r.extending i m).state.lastHash = r.state.lastHash ∧
      (r.extending i m).state.yesterday = r.state.yesterday ∧
      (r.extending i m).state.activeId = r.state.activeId := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold PlanReq.extending RuntimeIn.activeId
  cases r.state.active with
  | none => rfl
  | some a => by_cases h : a.id = i <;> simp [h]

/-- **The running block's estimate grows by the extension** when it is the extended item. -/
theorem the_extension_grows_the_running_estimate (r : PlanReq) (i : Id) (m : Nat)
    (a : ActiveBlock) (h : r.state.active = some a) (hi : a.id = i) :
    (r.extending i m).state.active = some { a with estMin := a.estMin + m } := by
  simp [PlanReq.extending, h, hi]

/-- **And another item's running block is left alone** — fork `overtime_drops` for an item that
is not the running one moves only the override. -/
theorem the_extension_leaves_another_items_block (r : PlanReq) (i : Id) (m : Nat)
    (a : ActiveBlock) (h : r.state.active = some a) (hi : a.id ≠ i) :
    (r.extending i m).state.active = some a := by
  simp [PlanReq.extending, h, hi]

/-- **The override is one `extra_min` record and nothing else.** -/
theorem the_extension_is_one_extra_override (r : PlanReq) (i : Id) (m : Nat) :
    (r.extending i m).overrides.map (fun o => (o.estMin.val, o.extraMin.val, o.drop.val))
      = some ([], [(i, m)], []) := rfl

/-- **An overtime drop is an item of the day as it stands that the extended day does not
hold** — both directions (fork `overtime_drops`' *"what the second plan no longer has room
for"*). -/
theorem mem_overtime_drops (r : PlanReq) (i : Id) (blocks : Nat) (g : Option WfGrown) (x : Id) :
    x ∈ (overtimeDiff r i blocks g).removed ↔ x ∈ diffIds (dayPlan r) ∧
      x ∉ diffIds (dayPlan ((r.extending i (blocks * r.blockMin)).growing i g)) :=
  mem_diff_removed _ _ x

/-- **The drops ascend in `Id` order, each once** — the fork's code, and not its doc comment's
*"in the order the first plan had them"* (README gap 2681). -/
theorem overtime_drops_ascend_in_id_order (r : PlanReq) (i : Id) (blocks : Nat) (g : Option WfGrown) :
    (overtimeDiff r i blocks g).removed.Pairwise (fun x y => Seal.idLt x y = true) :=
  diff_removed_sorted _ _

/-- **An extension that leaves the day as it was changes nothing and drops nothing.** -/
theorem overtimeDiff_of_an_unchanged_day (r : PlanReq) (i : Id) (blocks : Nat) (g : Option WfGrown)
    (h : dayPlan ((r.extending i (blocks * r.blockMin)).growing i g) = dayPlan r) :
    overtimeDiff r i blocks g = ⟨[], [], [], 0⟩ := by
  unfold overtimeDiff
  rw [h, diff_self]

/-- **The what-if stays inside the decoder's domain when the grown estimate fits the host's width** (W-34 repair,
README gap 2737; restated at W-41 for D81's gap 3902).  `PlanReq.extending` sets `estMin` directly rather than through
`mkActive?`, so it can build a request `mkActive?` would refuse; this names the subdomain where it does not: a request
that agreed still agrees after an extension that keeps the running estimate within `Look.maxPlanMinutes` (the fork's
`u32`, reused).  Until W-41 the bound was the day's and E1 read the clause; since D78 E1 reads the lead and no lift
needs the clause, so this is now a statement about the decoder's domain alone.  It implies its W-34 form, the day's. -/
theorem the_extension_agrees_when_the_estimate_fits_the_width (r : PlanReq) (i : Id) (m : Nat)
    (hok : r.activeAgrees = true)
    (hm : ∀ a, r.state.active = some a → a.id = i → a.estMin + m ≤ Look.maxPlanMinutes) :
    (r.extending i m).activeAgrees = true := by
  unfold PlanReq.activeAgrees at hok ⊢
  unfold PlanReq.extending
  cases ha : r.state.active with
  | none => rfl
  | some a =>
    rw [ha] at hok
    by_cases hi : a.id = i
    · simp only [Option.map, hi, if_true]
      have := hm a ha hi
      unfold ActiveBlock.wf at hok ⊢
      simp only [decide_eq_true_eq] at hok ⊢
      exact this
    · simp only [Option.map, hi, if_false]
      exact hok

/-- **And it leaves the domain exactly when the grown estimate passes the width** — the other direction (AGENTS §5.8):
the what-if day of such an extension is still planned (D28), but `mkActive?` would not have built its block.  Its W-34
form, the_extension_disagrees_past_a_day, is REFUTED since D81's gap 3902 (`PlannerWit`'s W-41 block extends a running
block past the day and the request agrees). -/
theorem the_extension_disagrees_past_the_width (r : PlanReq) (i : Id) (m : Nat) (a : ActiveBlock)
    (ha : r.state.active = some a) (hi : a.id = i) (hm : Look.maxPlanMinutes < a.estMin + m) :
    (r.extending i m).activeAgrees = false := by
  unfold PlanReq.activeAgrees PlanReq.extending
  simp only [ha, Option.map, hi, if_true]
  unfold ActiveBlock.wf
  simp only [decide_eq_false_iff_not]
  omega


/-! ### The what-if's request pays D80 when the request does (W-41 repair, README gap 4147)

`PlanWire.planReqOf` refuses by name the two requests D80 names (`eveningPastTheCalendar`, `ciDisagrees`), and the
wind-down law is proved over the requests it accepts.  §9.1's what-if is planned off a request NO decoder reads —
`(r.extending i m).growing i g` — so "the requests the decoder accepts" covered the day and not its what-if until these
two: the extension and the growth each keep both clauses, so a what-if of an accepted request is a request the
decoder's two clauses accept, and every law stated over them reaches the what-if's day. -/

/-- **The evening is read off the lookahead and the run**, which neither the extension nor the growth touches. -/
theorem PlanReq.the_whatif_keeps_the_evening (r : PlanReq) (i : Id) (m : Nat) (g : Option WfGrown) :
    ((r.extending i m).growing i g).eveningInsideTheCalendar = r.eveningInsideTheCalendar := by
  cases g <;> rfl

/-- **Growing keeps every candidate's id and `ci`**, so D80 (b)'s clause holds after it when it held before. -/
theorem PlanReq.growing_keeps_the_ci_agreement (r : PlanReq) (i : Id) (g : Option WfGrown)
    (h : r.ciDisagreement = none) : (r.growing i g).ciDisagreement = none := by
  cases g with
  | none => exact h
  | some g =>
    rw [PlanReq.ciDisagreement_eq_none_iff] at h ⊢
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have hv := h q hq
    split
    · exact hv
    · exact hv

/-- **The what-if's request pays D80's two clauses when the request does.** -/
theorem PlanReq.the_whatif_request_pays_d80 (r : PlanReq) (i : Id) (m : Nat) (g : Option WfGrown)
    (hev : r.eveningInsideTheCalendar = true) (hci : r.ciDisagreement = none) :
    ((r.extending i m).growing i g).eveningInsideTheCalendar = true ∧
      ((r.extending i m).growing i g).ciDisagreement = none :=
  ⟨(r.the_whatif_keeps_the_evening i m g).trans hev,
    (r.extending i m).growing_keeps_the_ci_agreement i g hci⟩

end Planner
end Tm
