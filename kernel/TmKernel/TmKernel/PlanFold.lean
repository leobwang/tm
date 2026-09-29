import TmKernel.Planner
/-!
# What §8.2 steps 5 and 6 do to a day that assigns nothing (stage 6, W-37 track K)

The campaign's D66 reads `PlanCheck.impossibleKept`'s eligibility as §8.2 step 5's own filter
evaluated against the day's slots **before step 5 assigns anything**, and D59 asked that the five
`_on_an_unassigned_day` lifts carry no `hnoimp`.  Both need two facts about the planner that
nothing in the tree stated until this module.  Neither mentions the checker, so they live here, below
`PlanCheck` in the import graph: `PlanCheck.lean`'s check-9 pin sites are line numbers (README gap
2136), and a planner-level proof has no business moving them.

1. **README gap 903 is a theorem** (`finalAssign_is_assignFold`).  §8.2 step 6's displacement
   (`Planner.PlanReq.displaceInto`) has been argued unreachable in prose since W-20: *"step 2
   places a mandatory instance wherever a stretch as wide as it is free, and a slot wide enough
   inside its window is exactly such a stretch."*  That sentence is now proved, from facts that
   were already theorems — the cut never touches what step 2 blocked
   (`Planner.PlanReq.a_slot_touches_nothing_blocked`), the victim is a slot of the day inside the
   window and long enough (`Planner.PlanReq.victimSlot_spec`) — and two that were not: step 2's
   blocked list only grows while it records each refusal (`placeStep_keeps_the_record`), and
   `Planner.earliestFree` finds any free run as wide as it asks for
   (`earliestFree_isSome_of_a_free_run`, the completeness half of
   `Planner.earliestFree_from_a_stretch`).  So the assignment step 6 hands `emit_segments` IS the
   one step 5 ended with, on every request.
2. **A day step 5 filled nothing is a day on which no group fit any slot before the walk began,
   unless the budget was already spent** (`nothing_fits_before_where_the_fold_fills_nothing`):
   the walk visits every slot from the state it started in, and a slot a group fits under the
   budget is a slot it fills (`assignStep_fills_a_free_slot_a_group_fits`).

`the_reservation_row_is_a_work_row_of_the_day` reads §8.2 choice 5b's row off the day, which is
the row `PlanCheck.budgetLeft` counts against the budget before anything else.

Theorems only: nothing here is compiled into the export, so check 12 has nothing to reach and
check 9 nothing to fold.
-/

namespace Tm
namespace PlanFold

open Planner

/-! ## A free run is found -/

/-- Two members of a list ordered pairwise by `R` are equal, or ordered one way or the other. -/
theorem pairwise_mem_or {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a = b ∨ R a b ∨ R b a
  | [], _, _, _, ha, _ => absurd ha (by simp)
  | x :: xs, h, a, b, ha, hb => by
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.1 h
    rcases List.mem_cons.1 ha with hax | hax <;> rcases List.mem_cons.1 hb with hbx | hbx
    · exact Or.inl (hax.trans hbx.symm)
    · subst hax; exact Or.inr (Or.inl (hx b hbx))
    · subst hbx; exact Or.inr (Or.inr (hx a hax))
    · exact pairwise_mem_or hxs hax hbx

/-- **Two free units a second apart lie in ONE free stretch** — `Look.freeIntervals_spec`'s order
clause: two different stretches have a covered unit between them. -/
theorem freeIntervals_next_unit {lo hi : Nat} {ws : List (Nat × Nat)} {iv : Nat × Nat} {u : Nat}
    (hiv : iv ∈ Look.freeIntervals lo hi ws) (h1 : iv.1 ≤ u) (h2 : u < iv.2)
    (hu : lo ≤ u + 1 ∧ u + 1 < hi ∧ Look.covered ws (u + 1) = false) : u + 1 < iv.2 := by
  obtain ⟨-, hpw, hunits⟩ := Look.freeIntervals_spec lo hi ws
  obtain ⟨iv', hiv', h1', h2'⟩ := (hunits (u + 1)).2 hu
  rcases pairwise_mem_or hpw hiv hiv' with he | hlt | hlt
  · rw [he]; exact h2'
  · have : iv.2 < iv'.1 := hlt
    omega
  · have : iv'.2 < iv.1 := hlt
    omega

/-- **A run of free units is inside one free stretch**, by induction along the run. -/
theorem freeIntervals_holds_a_free_run {lo hi : Nat} {ws : List (Nat × Nat)} {t n : Nat}
    (hn : 0 < n)
    (hfree : ∀ u, t ≤ u → u < t + n → lo ≤ u ∧ u < hi ∧ Look.covered ws u = false) :
    ∃ iv ∈ Look.freeIntervals lo hi ws, iv.1 ≤ t ∧ t + n ≤ iv.2 := by
  obtain ⟨-, -, hunits⟩ := Look.freeIntervals_spec lo hi ws
  obtain ⟨iv, hiv, h1, h2⟩ := (hunits t).2 (hfree t (Nat.le_refl t) (by omega))
  have key : ∀ k, k < n → t + k < iv.2 := by
    intro k
    induction k with
    | zero => intro _; simpa using h2
    | succ k ih =>
      intro hk
      have := freeIntervals_next_unit hiv (by omega) (ih (by omega))
        (hfree (t + k + 1) (by omega) (by omega))
      omega
  exact ⟨iv, hiv, h1, by have := key (n - 1) (by omega); omega⟩

/-- **`Planner.earliestFree` finds any free run as wide as it asks for** — the completeness half
of `Planner.earliestFree_from_a_stretch`, which says only that what it finds is free.  A request
of zero width still needs one free unit, hence `max d 1`. -/
theorem earliestFree_isSome_of_a_free_run {lo hi d : Nat} {ws : List (Nat × Nat)} {t : Nat}
    (hfree : ∀ u, t ≤ u → u < t + max d 1 → lo ≤ u ∧ u < hi ∧ Look.covered ws u = false) :
    (earliestFree lo hi d ws).isSome = true := by
  obtain ⟨iv, hiv, h1, h2⟩ := freeIntervals_holds_a_free_run (by omega) hfree
  unfold earliestFree
  rw [Option.isSome_map, List.find?_isSome]
  exact ⟨iv, hiv, by simp only [decide_eq_true_eq]; omega⟩

/-! ## Step 2 records every refusal -/

/-- **One placement keeps step 2's record**: every mandatory instance step 2 deferred found no
position in its window free of the evening and of what was blocked when its turn came, and what
is blocked only grows. -/
theorem placeStep_keeps_the_record (r : PlanReq) (acc : List Placed × List (Nat × Nat))
    (q0 : Placed)
    (h : ∀ q ∈ acc.1, q.placedAt = none → q.inst.mandatory = true →
      ∃ ws : List (Nat × Nat), (∀ w ∈ ws, w ∈ acc.2) ∧
        earliestFree (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) (r.night :: ws)
          = none) :
    (∀ w ∈ acc.2, w ∈ (placeStep r acc q0).2) ∧
    ∀ q ∈ (placeStep r acc q0).1, q.placedAt = none → q.inst.mandatory = true →
      ∃ ws : List (Nat × Nat), (∀ w ∈ ws, w ∈ (placeStep r acc q0).2) ∧
        earliestFree (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) (r.night :: ws)
          = none := by
  have shape : ∃ (p : Placed) (ws' : List (Nat × Nat)),
      placeStep r acc q0 = (p :: acc.1, ws') ∧ (∀ w ∈ acc.2, w ∈ ws') ∧
      p.span = q0.span ∧ p.inst = q0.inst ∧
      (p.placedAt = none → p.inst.mandatory = true →
        earliestFree (max q0.span.1 r.now.sec) q0.span.2 (60 * q0.inst.durMin)
          (r.night :: acc.2) = none) := by
    unfold placeStep
    dsimp only
    split
    · split
      · exact ⟨_, _, rfl, fun w hw => List.mem_cons_of_mem _ hw, rfl, rfl,
          fun hp => absurd hp (by simp)⟩
      · rename_i ht
        split
        · exact ⟨_, _, rfl, fun w hw => List.mem_cons_of_mem _ hw, rfl, rfl,
            fun hp => absurd hp (by simp)⟩
        · exact ⟨_, _, rfl, fun w hw => hw, rfl, rfl, fun _ _ => ht⟩
    · rename_i hm
      split
      · split
        · exact ⟨_, _, rfl, fun w hw => List.mem_cons_of_mem _ hw, rfl, rfl,
            fun hp => absurd hp (by simp)⟩
        · exact ⟨_, _, rfl, fun w hw => hw, rfl, rfl, fun _ hmt => absurd hmt hm⟩
      · exact ⟨_, _, rfl, fun w hw => hw, rfl, rfl, fun _ hmt => absurd hmt hm⟩
  obtain ⟨p, ws', he, hgrow, hspan, hinst, hrec⟩ := shape
  rw [he]
  refine ⟨hgrow, fun q hq hqn hqm => ?_⟩
  rcases List.mem_cons.1 hq with hqp | hq
  · subst hqp
    rw [hspan, hinst]
    exact ⟨acc.2, hgrow, hrec hqn hqm⟩
  · obtain ⟨ws, hws, hef⟩ := h q hq hqn hqm
    exact ⟨ws, fun w hw => hgrow w (hws w hw), hef⟩

theorem foldl_placeStep_keeps_the_record (r : PlanReq) :
    ∀ (l : List Placed) (acc : List Placed × List (Nat × Nat)),
      (∀ q ∈ acc.1, q.placedAt = none → q.inst.mandatory = true →
        ∃ ws : List (Nat × Nat), (∀ w ∈ ws, w ∈ acc.2) ∧
          earliestFree (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) (r.night :: ws)
            = none) →
      ∀ q ∈ (l.foldl (placeStep r) acc).1, q.placedAt = none → q.inst.mandatory = true →
        ∃ ws : List (Nat × Nat), (∀ w ∈ ws, w ∈ (l.foldl (placeStep r) acc).2) ∧
          earliestFree (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) (r.night :: ws)
            = none
  | [], _, h => h
  | q0 :: l, acc, h => by
    simp only [List.foldl_cons]
    exact foldl_placeStep_keeps_the_record r l _ (placeStep_keeps_the_record r acc q0 h).2

/-- **Every mandatory instance step 2 deferred found no free position**, against a list of what
was blocked that the cut also flows around (`Planner.PlanReq.slotBlocked` is the evening and the
whole of step 2's blocked list). -/
theorem a_deferred_mandatory_instance_found_no_position (r : PlanReq) (q : Placed)
    (hq : q ∈ r.placedRoutines) (hn : q.placedAt = none) (hm : q.inst.mandatory = true) :
    ∃ ws : List (Nat × Nat), (∀ w ∈ ws, w ∈ r.placementFold.2) ∧
      earliestFree (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) (r.night :: ws)
        = none := by
  unfold PlanReq.placedRoutines at hq
  unfold PlanReq.placementFold at hq ⊢
  exact foldl_placeStep_keeps_the_record r _ ([], r.blockedBeforeRoutines)
    (fun _ h => absurd h (by simp)) q (List.mem_reverse.1 hq) hn hm

/-! ## README gap 903: step 6 never displaces -/

/-- **Step 6 hands the assignment back unchanged** for every instance whose deferral step 2
recorded: the displacement needs a victim slot inside the window and long enough, and that slot
is a free run step 2's own search would have found. -/
theorem deferOne_keeps_the_assignment (r : PlanReq) (budget : Nat) (qs : List Placed)
    (a : Assign) (q : Placed)
    (hrec : q.placedAt = none → q.inst.mandatory = true →
      ∃ ws : List (Nat × Nat), (∀ w ∈ ws, w ∈ r.placementFold.2) ∧
        earliestFree (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) (r.night :: ws)
          = none) :
    (r.deferOne budget qs a q).2 = a := by
  unfold PlanReq.deferOne
  by_cases hp : q.placedAt.isSome = true
  · rw [if_pos hp]
  have hnone : q.placedAt = none := by
    cases hq : q.placedAt with
    | none => rfl
    | some _ => rw [hq] at hp; exact absurd rfl hp
  rw [if_neg hp]
  by_cases hs : q.span.2 ≤ max q.span.1 r.now.sec
  · rw [if_pos hs]
  rw [if_neg hs]
  cases ht1 : r.lowestFree (r.occupiedNow qs a ++ r.keptBreaksToday ++ [r.night])
      (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) with
  | some t => rfl
  | none =>
    dsimp only
    by_cases hm : q.inst.mandatory = false
    · rw [if_pos hm]
    rw [if_neg hm]
    cases ht2 : r.lowestFree (r.occupiedNow qs a ++ r.keptBreaksToday)
        (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) with
    | some t => rfl
    | none =>
      cases hv : r.victimSlot a (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) with
      | none => rfl
      | some vi =>
        exfalso
        have hmt : q.inst.mandatory = true := by
          cases h : q.inst.mandatory with
          | false => exact absurd h hm
          | true => rfl
        obtain ⟨ws, hws, hef⟩ := hrec hnone hmt
        obtain ⟨e, s, hslot, -, h1, h2, h3⟩ := PlanReq.victimSlot_spec hv
        have hsl : s ∈ r.todaySlots := r.energised_slot_is_a_slot (List.mem_of_getElem? hslot)
        have hwin := r.a_slot_is_inside_the_window s hsl
        have hcov : ∀ u, s.start ≤ u → u < s.stop → Look.covered (r.night :: ws) u = false := by
          intro u hu1 hu2
          cases hc : Look.covered (r.night :: ws) u with
          | false => rfl
          | true =>
            obtain ⟨w, hw, hw1, hw2⟩ := Look.covered_eq_true.1 hc
            have hwb : w ∈ r.slotBlocked ++ r.restsToday := by
              refine List.mem_append_left _ ?_
              unfold PlanReq.slotBlocked
              rcases List.mem_cons.1 hw with hwn | hw'
              · rw [hwn]; exact List.mem_cons_self ..
              · exact List.mem_cons_of_mem _ (hws w hw')
            exact absurd ⟨hw1, hw2⟩ (r.a_slot_touches_nothing_blocked s hsl hwb hu1 hu2)
        have hsome : (earliestFree (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin)
            (r.night :: ws)).isSome = true :=
          earliestFree_isSome_of_a_free_run (t := s.start)
            (fun u hu1 hu2 => ⟨by omega, by omega, hcov u hu1 (by omega)⟩)
        rw [hef] at hsome
        exact absurd hsome (by simp)

/-- **And so does the whole walk**, over any suffix of the instances step 2 placed. -/
theorem deferWalk_keeps_the_assignment (r : PlanReq) (budget : Nat) :
    ∀ (post pre : List Placed) (a : Assign), (∀ q ∈ post, q ∈ r.placedRoutines) →
      (r.deferWalk budget pre a post).2 = a
  | [], _, _, _ => rfl
  | q :: post, pre, a, h => by
    unfold PlanReq.deferWalk
    dsimp only
    rw [deferWalk_keeps_the_assignment r budget post _ _
      (fun z hz => h z (List.mem_cons_of_mem _ hz))]
    exact deferOne_keeps_the_assignment r budget _ a q
      (fun hn hm => a_deferred_mandatory_instance_found_no_position r q
        (h q (List.mem_cons_self ..)) hn hm)

/-- **README gap 903, closed: the assignment step 6 hands `emit_segments` IS step 5's.** -/
theorem finalAssign_is_assignFold (r : PlanReq) : r.finalAssign = r.assignFold := by
  unfold PlanReq.finalAssign PlanReq.deferFold
  exact deferWalk_keeps_the_assignment r _ r.placedRoutines [] r.assignFold (fun _ h => h)

/-! ## A walk that fills nothing -/

/-- **A slot a group fits, under the budget, is a slot the step fills.** -/
theorem assignStep_fills_a_free_slot_a_group_fits (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat)
    (hfree : (a.slotOf[x.2]?).join = none) (hbud : a.used < budget) (g : Group)
    (hg : g ∈ a.groups) (hfit : r.groupFitsSlot slots a.slotOf breaks x.2 x.1.1 x.1.2 g = true)
    (hx : x.2 < a.slotOf.length) :
    ∃ gi, (r.assignStep slots breaks budget a x).slotOf[x.2]? = some (some gi) := by
  have hfind : (a.groups.findIdx? (r.groupFitsSlot slots a.slotOf breaks x.2 x.1.1 x.1.2)).isSome
      = true := by
    rw [List.findIdx?_isSome, List.any_eq_true]
    exact ⟨g, hg, hfit⟩
  obtain ⟨gi, hgi⟩ := Option.isSome_iff_exists.1 hfind
  obtain ⟨hlt, -, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hgi
  unfold PlanReq.assignStep
  rw [if_neg (by rw [hfree]; simp; omega), hgi]
  dsimp only
  rw [List.getElem?_eq_getElem hlt]
  exact ⟨gi, List.getElem?_set_self hx⟩

/-- **A fold that ends having filled no slot changed nothing on the way**: every step it took
returned the state it was handed. -/
theorem foldl_assignStep_idle (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign), (∀ x ∈ l, x.2 < a.slotOf.length) →
      (∀ (i gi : Nat), (l.foldl (r.assignStep slots breaks budget) a).slotOf[i]? ≠ some (some gi)) →
      l.foldl (r.assignStep slots breaks budget) a = a ∧
        ∀ x ∈ l, r.assignStep slots breaks budget a x = a
  | [], _, _, _ => ⟨rfl, fun _ hx => absurd hx (by simp)⟩
  | x :: xs, a, hlen, hnone => by
    simp only [List.foldl_cons] at hnone ⊢
    have hlen' : ∀ y ∈ xs, y.2 < (r.assignStep slots breaks budget a x).slotOf.length := by
      intro y hy
      rw [(PlanReq.assignStep_lengths r slots breaks budget a x).1]
      exact hlen y (List.mem_cons_of_mem _ hy)
    obtain ⟨hfold, hsteps⟩ := foldl_assignStep_idle r slots breaks budget xs _ hlen' hnone
    have hxa : r.assignStep slots breaks budget a x = a := by
      rcases PlanReq.assignStep_cases r slots breaks budget a x with heq | ⟨gi, g, -, -, -, heq⟩
      · exact heq
      · exfalso
        have hx := hnone x.2 gi
        rw [hfold, heq] at hx
        exact hx (List.getElem?_set_self (hlen x (List.mem_cons_self ..)))
    refine ⟨by rw [hfold, hxa], fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with hyx | hy
    · rw [hyx]; exact hxa
    · have := hsteps y hy
      rwa [hxa] at this

/-- **§8.2 step 5 filling nothing means no group fit any slot before the walk began** — unless the
budget was spent before it began (the running block's one block, `PlanReq.activeSeed`, against
`Planner.remainingBudget`). -/
theorem nothing_fits_before_where_the_fold_fills_nothing (r : PlanReq)
    (hnone : ∀ (i gi : Nat), r.assignFold.slotOf[i]? ≠ some (some gi))
    (hbud : r.activeSeed < remainingBudget r) :
    ∀ x ∈ r.energisedSlots.zipIdx, ∀ g ∈ r.startGroups,
      r.groupFitsSlot r.todaySlots r.assignStart.slotOf r.todayBreaks x.2 x.1.1 x.1.2 g
        = false := by
  have hlen : ∀ x ∈ r.energisedSlots.zipIdx, x.2 < r.assignStart.slotOf.length := by
    intro x hx
    have hget := List.mem_zipIdx_iff_getElem?.1 hx
    have hl : r.assignStart.slotOf.length = r.energisedSlots.length := by
      unfold PlanReq.assignStart
      rw [List.length_replicate, r.energisedSlots_length]
    rw [hl]
    exact lt_of_getElem?_some hget
  obtain ⟨-, hsteps⟩ := foldl_assignStep_idle r _ _ _ _ r.assignStart hlen hnone
  intro x hx g hg
  cases hfit : r.groupFitsSlot r.todaySlots r.assignStart.slotOf r.todayBreaks x.2 x.1.1 x.1.2 g
    with
  | false => rfl
  | true =>
    exfalso
    have hfree : (r.assignStart.slotOf[x.2]?).join = none := by
      unfold PlanReq.assignStart
      simp only [List.getElem?_replicate]
      split <;> rfl
    obtain ⟨gi, hgi⟩ := assignStep_fills_a_free_slot_a_group_fits r r.todaySlots r.todayBreaks
      (remainingBudget r) r.assignStart x hfree hbud g hg hfit (hlen x hx)
    rw [hsteps x hx] at hgi
    have hj : (r.assignStart.slotOf[x.2]?).join = some gi := by rw [hgi]; rfl
    rw [hfree] at hj
    exact absurd hj (by simp)

/-- **A day with no assigned row is a day the fold filled nothing** — through
`finalAssign_is_assignFold`, since `Planner.PlanReq.assignedRows` reads step 6's answer. -/
theorem the_fold_fills_nothing_on_an_unassigned_day (r : PlanReq)
    (hnoassign : r.assignedRows = []) : ∀ (i gi : Nat), r.assignFold.slotOf[i]? ≠ some (some gi) := by
  intro i gi h
  obtain ⟨-, hcl⟩ := PlanReq.assignFold_ok r
  obtain ⟨e, s, g, he, hg, -, -, -⟩ := hcl i gi h
  have hmem : ((e, s), some gi) ∈ r.energisedSlots.zip r.finalAssign.slotOf := by
    rw [finalAssign_is_assignFold]
    exact List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨he, h⟩)
  have hrow : assignedSeg e s g ∈ r.assignedRows := by
    unfold PlanReq.assignedRows
    refine List.mem_filterMap.2 ⟨((e, s), some gi), hmem, ?_⟩
    simp only [finalAssign_is_assignFold, hg]
  rw [hnoassign] at hrow
  exact absurd hrow (by simp)

/-- **The whole of it, as the checker reads it**: on a day with no assigned row, a group fits no
slot before the walk began whenever the budget was not spent before it began. -/
theorem nothing_fits_before_on_an_unassigned_day (r : PlanReq)
    (hnoassign : r.assignedRows = []) (hbud : r.activeSeed < remainingBudget r) :
    ∀ x ∈ r.energisedSlots.zipIdx, ∀ g ∈ r.startGroups,
      r.groupFitsSlot r.todaySlots r.assignStart.slotOf r.todayBreaks x.2 x.1.1 x.1.2 g
        = false :=
  nothing_fits_before_where_the_fold_fills_nothing r
    (the_fold_fills_nothing_on_an_unassigned_day r hnoassign) hbud

/-! ## The reservation, as a row the budget pays for -/

/-- **§8.2 choice 5b's reservation is a work row of the day starting at `now` — `now` on the
rows' own clock, `Planner.clampSec`, the one `Planner.segOf` draws every row on — and it names the
running item.**  The row `PlanCheck.budgetLeft` counts against the budget, whatever else the day
holds, and with no bound on `now`: the reservation starts where the planner's clock says `now` is. -/
theorem the_reservation_row_is_a_work_row_of_the_day (r : PlanReq) (q : ActiveRes)
    (hq : r.activeRun = some q) :
    ∃ s ∈ (dayPlan r).segments, s.val.kind.isWork = true ∧ s.val.start = clampSec r.now.sec ∧
      s.val.item = r.state.activeId := by
  obtain ⟨t, ht⟩ : ∃ t, t ∈ reservationSegs r := by
    unfold reservationSegs PlanReq.activeRow
    rw [hq]
    exact ⟨_, List.mem_singleton_self _⟩
  refine ⟨segOf t, ?_, ?_, ?_, ?_⟩
  · rw [dayPlan_segments]
    exact mem_dayRows_of_mem (by simp [ht])
  · rw [segOf_kind, reservationSegs_are_blocks r t ht]; rfl
  · show clampSec t.start = clampSec r.now.sec
    rw [(r.activeRow_is_an_energyless_block t ht).2.2.2.2]
  · rw [segOf_item]; exact (r.activeRow_is_an_energyless_block t ht).2.2.2.1

end PlanFold
end Tm
