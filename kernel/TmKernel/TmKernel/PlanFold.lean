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

3. **Since W-38 (D67): an item step 5 admitted and did not place was passed for the budget or
   found every slot it fits taken** — the section at the end, which proves each reason the day names
   true of the day (`a_budget_spent_name_is_true_of_the_day`, `a_taken_name_holds_every_slot_it_fits`).

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


/-! ## W-38 (D67, P58): what step 5 does to an item it admitted and did not place

The owner's D67 (README gap 3160) keeps §8.2 step 5 GREEDY and asks the day to SAY why an owed
impossible item has no row; `Planner.PlanReq.dayUnplaced` writes the reason and
`PlanCheck.impossibleKept` checks it is TRUE of the day.  This section proves the reasons are the
walk's, from the walk:

* **the walk reads nothing it has already written.**  A step writes the slot vector at its own
  index (`assignStep_slotOf_ne`) and a group's entry only when it picks that group
  (`assignStep_groups_of_not_picked`); the walk visits the day's slots once each, in order
  (`zipIdx_split`); and the filter reads the cursor only from the slot it is at
  (`groupFitsSlot_of_drop`).  So a group given nothing so far fits a slot at the walk's own state
  exactly when it fit it before the walk, and a free slot a group fits under the budget is a slot
  the step fills — which leaves ONE reason for a slot the group fits to end the walk EMPTY: the
  budget (`the_walk_passes_a_slot_a_group_fits_before_it_only_for_the_budget`);
* **the walk's budget is the day's rows.**  `used` is the running block's one block plus one per
  slot filled (`assignFold_used_counts`), step 5 draws one row per filled slot
  (`assignedRows_length`), and each of those rows and §8.2 choice 5b's reservation is a work row
  of the day from `now` (`the_day_holds_every_block_the_walk_spent`) — README gap 2020's count, for
  the budget the WALK spends;
* so `budgetSpent` is true of the day (`a_budget_spent_name_is_true_of_the_day`), and a name that
  is not `budgetSpent` holds every slot the item fits with another item's work row
  (`a_taken_name_holds_every_slot_it_fits`).  `a_filled_slot_assigns_its_groups_members` is what
  ties a slot the item's group was given to the item: the walk moves nothing but `spent`, and a
  group has at most `maxBatch` members, so its row names all of them (README gap 1900's missing
  half, for the fold's own groups).

Theorems only, as above. -/

/-- A step writes the slot vector at its own index and nowhere else. -/
theorem assignStep_slotOf_ne (r : PlanReq) (slots : List Look.Slot) (breaks : List (Nat × Nat))
    (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat) (j : Nat) (hj : j ≠ x.2) :
    (r.assignStep slots breaks budget a x).slotOf[j]? = a.slotOf[j]? := by
  rcases PlanReq.assignStep_cases r slots breaks budget a x with heq | ⟨gi, g, -, -, -, heq⟩
  · rw [heq]
  · rw [heq]; exact List.getElem?_set_ne (Ne.symm hj)

/-- A step moves a group's entry only when it gives that group the slot it visits. -/
theorem assignStep_groups_of_not_picked (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat)
    (hx : x.2 < a.slotOf.length) (gi : Nat)
    (hn : (r.assignStep slots breaks budget a x).slotOf[x.2]? ≠ some (some gi)) :
    (r.assignStep slots breaks budget a x).groups[gi]? = a.groups[gi]? := by
  rcases PlanReq.assignStep_cases r slots breaks budget a x with heq | ⟨gj, g, -, -, -, heq⟩
  · rw [heq]
  · rw [heq] at hn ⊢
    simp only at hn ⊢
    by_cases hgj : gj = gi
    · subst hgj; rw [List.getElem?_set_self hx] at hn; exact absurd rfl hn
    · exact List.getElem?_set_ne hgj

/-- A step never gives back a block of the budget. -/
theorem assignStep_used_le (r : PlanReq) (slots : List Look.Slot) (breaks : List (Nat × Nat))
    (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat) :
    a.used ≤ (r.assignStep slots breaks budget a x).used := by
  rcases PlanReq.assignStep_cases r slots breaks budget a x with heq | ⟨gi, g, -, -, -, heq⟩ <;>
    rw [heq]
  · exact Nat.le_refl _
  · exact Nat.le_succ _

theorem foldl_assignStep_slotOf_ne (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign) (j : Nat), (∀ y ∈ l, y.2 ≠ j) →
      (l.foldl (r.assignStep slots breaks budget) a).slotOf[j]? = a.slotOf[j]?
  | [], _, _, _ => rfl
  | y :: ys, a, j, h => by
    simp only [List.foldl_cons]
    rw [foldl_assignStep_slotOf_ne r slots breaks budget ys _ j
      (fun z hz => h z (List.mem_cons_of_mem _ hz))]
    exact assignStep_slotOf_ne r slots breaks budget a y j
      (fun hc => h y List.mem_cons_self hc.symm)

theorem foldl_assignStep_used_le (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign),
      a.used ≤ (l.foldl (r.assignStep slots breaks budget) a).used
  | [], _ => Nat.le_refl _
  | y :: ys, a => by
    simp only [List.foldl_cons]
    exact Nat.le_trans (assignStep_used_le r slots breaks budget a y)
      (foldl_assignStep_used_le r slots breaks budget ys _)

theorem foldl_assignStep_lengths (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign),
      (l.foldl (r.assignStep slots breaks budget) a).slotOf.length = a.slotOf.length ∧
        (l.foldl (r.assignStep slots breaks budget) a).groups.length = a.groups.length
  | [], _ => ⟨rfl, rfl⟩
  | y :: ys, a => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_assignStep_lengths r slots breaks budget ys
      (r.assignStep slots breaks budget a y)
    obtain ⟨h3, h4⟩ := PlanReq.assignStep_lengths r slots breaks budget a y
    exact ⟨h1.trans h3, h2.trans h4⟩

/-- **A group the walk never gives a slot keeps its entry**: over a stretch of slots with
distinct indices, an entry moves only at a pick, and a pick survives the rest of the stretch. -/
theorem foldl_assignStep_groups_of_never_picked (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign) (gi : Nat),
      (l.map (·.2)).Nodup → (∀ y ∈ l, y.2 < a.slotOf.length) →
      (∀ y ∈ l, (l.foldl (r.assignStep slots breaks budget) a).slotOf[y.2]? ≠ some (some gi)) →
      (l.foldl (r.assignStep slots breaks budget) a).groups[gi]? = a.groups[gi]?
  | [], _, _, _, _, _ => rfl
  | y :: ys, a, gi, hnd, hlen, hn => by
    simp only [List.foldl_cons] at hn ⊢
    simp only [List.map_cons] at hnd
    obtain ⟨hy, hnd'⟩ := List.nodup_cons.1 hnd
    have hlen' : ∀ z ∈ ys, z.2 < (r.assignStep slots breaks budget a y).slotOf.length := by
      intro z hz
      rw [(PlanReq.assignStep_lengths r slots breaks budget a y).1]
      exact hlen z (List.mem_cons_of_mem _ hz)
    rw [foldl_assignStep_groups_of_never_picked r slots breaks budget ys _ gi hnd' hlen'
      (fun z hz => hn z (List.mem_cons_of_mem _ hz))]
    apply assignStep_groups_of_not_picked r slots breaks budget a y (hlen y List.mem_cons_self) gi
    intro hc
    apply hn y List.mem_cons_self
    rw [foldl_assignStep_slotOf_ne r slots breaks budget ys _ y.2
      (fun z hz hzy => hy (hzy ▸ List.mem_map.2 ⟨z, hz, rfl⟩))]
    exact hc


/-- The index of the `k`-th slot the walk visits is `k`. -/
theorem zipIdx_index (l : List (Fin 6 × Look.Slot)) (k : Nat) (y : (Fin 6 × Look.Slot) × Nat)
    (h : l.zipIdx[k]? = some y) : y.2 = k := by
  rw [List.getElem?_zipIdx] at h
  cases hl : l[k]? with
  | none => rw [hl] at h; exact absurd h (by simp)
  | some a => rw [hl] at h; simp only [Option.map_some, Option.some.injEq] at h; rw [← h]; simp

/-- **The walk splits at a slot it visits**: what comes before holds the lower indices, what comes
after the higher ones. -/
theorem zipIdx_split (l : List (Fin 6 × Look.Slot)) (x : (Fin 6 × Look.Slot) × Nat)
    (hx : x ∈ l.zipIdx) :
    l.zipIdx = l.zipIdx.take x.2 ++ x :: l.zipIdx.drop (x.2 + 1) ∧
      (∀ y ∈ l.zipIdx.take x.2, y.2 < x.2) ∧ (∀ y ∈ l.zipIdx.drop (x.2 + 1), x.2 < y.2) ∧
      (l.zipIdx.map (·.2)).Nodup := by
  have hget : l[x.2]? = some x.1 := List.mem_zipIdx_iff_getElem?.1 hx
  have hk : x.2 < l.zipIdx.length := by
    rw [List.length_zipIdx]; exact Planner.lt_of_getElem?_some hget
  have hlk : l.zipIdx[x.2] = x := by
    have h1 : l.zipIdx[x.2]? = some x := by
      rw [List.getElem?_zipIdx, hget]; simp
    rw [List.getElem?_eq_getElem hk] at h1
    exact Option.some.inj h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := (List.take_append_drop x.2 l.zipIdx).symm
    rw [List.drop_eq_getElem_cons hk, hlk] at h
    exact h
  · intro y hy
    obtain ⟨j, hj, hyj⟩ := List.mem_take_iff_getElem.1 hy
    have hj' : j < l.zipIdx.length := Nat.lt_of_lt_of_le hj (Nat.min_le_right _ _)
    have := zipIdx_index l j y (by rw [List.getElem?_eq_getElem hj', hyj])
    omega
  · intro y hy
    obtain ⟨j, hj, hyj⟩ := List.mem_drop_iff_getElem.1 hy
    have hj' : x.2 + 1 + j < l.zipIdx.length := by omega
    have := zipIdx_index l (x.2 + 1 + j) y (by rw [List.getElem?_eq_getElem hj', hyj])
    omega
  · have : l.zipIdx.map (·.2) = List.range' 0 l.length := List.zipIdx_map_snd 0 l
    rw [this]; exact List.nodup_range' 1


theorem drop_zip {α β : Type} : ∀ (n : Nat) (l₁ : List α) (l₂ : List β),
    (l₁.zip l₂).drop n = (l₁.drop n).zip (l₂.drop n)
  | 0, _, _ => rfl
  | _ + 1, [], _ => by simp
  | _ + 1, _ :: _, [] => by simp
  | n + 1, _ :: l₁, _ :: l₂ => by simp [drop_zip n l₁ l₂]

/-- **The filter reads the cursor only from the slot it is at**: `contiguousFits` walks the slots
from `i` on, so two cursors that agree from `i` on give every group the same answer at `i`. -/
theorem groupFitsSlot_of_drop (r : PlanReq) (slots : List Look.Slot) (s1 s2 : List (Option Nat))
    (breaks : List (Nat × Nat)) (i : Nat) (e : Fin 6) (s : Look.Slot) (g : Group)
    (h : s1.drop i = s2.drop i) :
    r.groupFitsSlot slots s1 breaks i e s g = r.groupFitsSlot slots s2 breaks i e s g := by
  unfold PlanReq.groupFitsSlot contiguousFits
  rw [drop_zip, drop_zip, h]

/-- **A slot a group fits before the walk, that step 5 leaves EMPTY and never gives that group,
was passed because the budget was spent** — the walk visits every slot once, in order, from the
state it started in: a group given nothing so far has its first entry, the slots from the cursor
on are still free, so the group fits there as it did before the walk, and a free slot a group
fits under the budget is a slot the step fills (`assignStep_fills_a_free_slot_a_group_fits`). -/
theorem the_walk_passes_a_slot_a_group_fits_before_it_only_for_the_budget (r : PlanReq)
    (x : (Fin 6 × Look.Slot) × Nat) (hx : x ∈ r.energisedSlots.zipIdx)
    (gi : Nat) (g : Group) (hg : r.startGroups[gi]? = some g)
    (hfit : r.groupFitsSlot r.todaySlots r.assignStart.slotOf r.todayBreaks x.2 x.1.1 x.1.2 g = true)
    (hempty : (r.assignFold.slotOf[x.2]?).join = none)
    (hnever : ∀ y ∈ r.energisedSlots.zipIdx, r.assignFold.slotOf[y.2]? ≠ some (some gi)) :
    remainingBudget r ≤ r.assignFold.used := by
  obtain ⟨hsplit, hpre, hpost, hnd⟩ := zipIdx_split r.energisedSlots x hx
  generalize hP : r.energisedSlots.zipIdx.take x.2 = pre at hsplit hpre
  generalize hQ : r.energisedSlots.zipIdx.drop (x.2 + 1) = post at hsplit hpost
  have hfold : r.assignFold = post.foldl (r.assignStep r.todaySlots r.todayBreaks (remainingBudget r))
      (r.assignStep r.todaySlots r.todayBreaks (remainingBudget r)
        (pre.foldl (r.assignStep r.todaySlots r.todayBreaks (remainingBudget r)) r.assignStart) x) := by
    unfold PlanReq.assignFold
    rw [hsplit, List.foldl_append, List.foldl_cons]
  generalize ha_def : pre.foldl (r.assignStep r.todaySlots r.todayBreaks (remainingBudget r))
    r.assignStart = a at hfold
  have hk : x.2 < r.energisedSlots.length :=
    Planner.lt_of_getElem?_some (List.mem_zipIdx_iff_getElem?.1 hx)
  have hlen_start : r.assignStart.slotOf.length = r.energisedSlots.length := by
    unfold PlanReq.assignStart; rw [List.length_replicate, r.energisedSlots_length]
  have ha_len : a.slotOf.length = r.energisedSlots.length := by
    rw [← ha_def]; exact (foldl_assignStep_lengths r _ _ _ pre _).1.trans hlen_start
  have hpre_mem : ∀ y ∈ pre, y ∈ r.energisedSlots.zipIdx := fun y hy => by
    rw [hsplit]; exact List.mem_append_left _ hy
  have hfin : ∀ j, j ≤ x.2 → r.assignFold.slotOf[j]? =
      (r.assignStep r.todaySlots r.todayBreaks (remainingBudget r) a x).slotOf[j]? := by
    intro j hj
    rw [hfold]
    exact foldl_assignStep_slotOf_ne r _ _ _ post _ j (fun y hy hyj => by
      have := hpost y hy; omega)
  have hstart_get : ∀ j, j < r.energisedSlots.length → r.assignStart.slotOf[j]? = some none := by
    intro j hj
    unfold PlanReq.assignStart
    rw [List.getElem?_replicate, if_pos (by rw [r.energisedSlots_length] at hj; exact hj)]
  have ha_from : ∀ j, x.2 ≤ j → a.slotOf[j]? = r.assignStart.slotOf[j]? := by
    intro j hj
    rw [← ha_def]
    exact foldl_assignStep_slotOf_ne r _ _ _ pre _ j (fun y hy hyj => by
      have := hpre y hy; omega)
  have ha_drop : a.slotOf.drop x.2 = r.assignStart.slotOf.drop x.2 := by
    apply List.ext_getElem?
    intro m
    rw [List.getElem?_drop, List.getElem?_drop, ha_from _ (Nat.le_add_right _ _)]
  have ha_free : (a.slotOf[x.2]?).join = none := by
    rw [ha_from _ (Nat.le_refl _), hstart_get _ hk]; rfl
  have hnd_pre : (pre.map (·.2)).Nodup := by
    rw [hsplit] at hnd
    exact hnd.sublist ((List.sublist_append_left pre (x :: post)).map _)
  have hlen_pre : ∀ y ∈ pre, y.2 < r.assignStart.slotOf.length := by
    intro y hy
    rw [hlen_start]
    exact Planner.lt_of_getElem?_some (List.mem_zipIdx_iff_getElem?.1 (hpre_mem y hy))
  have hnever_pre : ∀ y ∈ pre, (pre.foldl (r.assignStep r.todaySlots r.todayBreaks (remainingBudget r))
      r.assignStart).slotOf[y.2]? ≠ some (some gi) := by
    intro y hy
    have h1 := hnever y (hpre_mem y hy)
    rw [hfin y.2 (Nat.le_of_lt (hpre y hy)),
      assignStep_slotOf_ne r _ _ _ _ x y.2 (Nat.ne_of_lt (hpre y hy)), ← ha_def] at h1
    exact h1
  have ha_group : a.groups[gi]? = some g := by
    rw [← ha_def, foldl_assignStep_groups_of_never_picked r r.todaySlots r.todayBreaks
      (remainingBudget r) pre r.assignStart gi hnd_pre hlen_pre hnever_pre]
    unfold PlanReq.assignStart
    exact hg
  by_cases hlt : a.used < remainingBudget r
  · exfalso
    have hfit' : r.groupFitsSlot r.todaySlots a.slotOf r.todayBreaks x.2 x.1.1 x.1.2 g = true := by
      rw [groupFitsSlot_of_drop r _ _ _ _ _ _ _ _ ha_drop]; exact hfit
    obtain ⟨gj, hgj⟩ := assignStep_fills_a_free_slot_a_group_fits r r.todaySlots r.todayBreaks
      (remainingBudget r) a x ha_free hlt g (List.mem_of_getElem? ha_group) hfit'
      (by rw [ha_len]; exact hk)
    have hf := hfin x.2 (Nat.le_refl _)
    rw [hgj] at hf
    rw [hf] at hempty
    exact absurd hempty (by simp)
  · have h1 := assignStep_used_le r r.todaySlots r.todayBreaks (remainingBudget r) a x
    have h2 := foldl_assignStep_used_le r r.todaySlots r.todayBreaks (remainingBudget r) post
      (r.assignStep r.todaySlots r.todayBreaks (remainingBudget r) a x)
    rw [hfold]
    omega

/-- **The walk's budget counter is the running block's block plus the slots it filled** — a step
either changes nothing or fills one EMPTY slot and spends one block. -/
theorem assignStep_counts (r : PlanReq) (slots : List Look.Slot) (breaks : List (Nat × Nat))
    (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat) (hx : x.2 < a.slotOf.length)
    (c : Nat) (h : a.used = c + a.slotOf.countP Option.isSome) :
    (r.assignStep slots breaks budget a x).used =
      c + (r.assignStep slots breaks budget a x).slotOf.countP Option.isSome := by
  unfold PlanReq.assignStep
  split
  · exact h
  · rename_i hguard
    split
    · exact h
    · split
      · exact h
      · simp only
        have hfree : a.slotOf[x.2] = none := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true] at hguard
          have h1 := hguard.1
          rw [List.getElem?_eq_getElem hx] at h1
          cases hs : a.slotOf[x.2] with
          | none => rfl
          | some v => rw [hs] at h1; exact absurd h1 (by simp)
        rw [List.countP_set hx, hfree]
        simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
        omega

theorem foldl_assignStep_counts (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) (c : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign), (∀ y ∈ l, y.2 < a.slotOf.length) →
      a.used = c + a.slotOf.countP Option.isSome →
      (l.foldl (r.assignStep slots breaks budget) a).used =
        c + (l.foldl (r.assignStep slots breaks budget) a).slotOf.countP Option.isSome
  | [], _, _, h => h
  | y :: ys, a, hl, h => by
    simp only [List.foldl_cons]
    refine foldl_assignStep_counts r slots breaks budget c ys _ (fun z hz => ?_)
      (assignStep_counts r slots breaks budget a y (hl y List.mem_cons_self) c h)
    rw [(PlanReq.assignStep_lengths r slots breaks budget a y).1]
    exact hl z (List.mem_cons_of_mem _ hz)

/-- **The budget the walk has spent is the running block's block and one per filled slot.** -/
theorem assignFold_used_counts (r : PlanReq) :
    r.assignFold.used = r.activeSeed + r.assignFold.slotOf.countP Option.isSome := by
  unfold PlanReq.assignFold
  refine foldl_assignStep_counts r _ _ _ _ _ _ (fun y hy => ?_) ?_
  · unfold PlanReq.assignStart
    rw [List.length_replicate, ← r.energisedSlots_length]
    exact Planner.lt_of_getElem?_some (List.mem_zipIdx_iff_getElem?.1 hy)
  · unfold PlanReq.assignStart
    simp [List.countP_replicate]

theorem countP_snd_zip {α β : Type} (p : β → Bool) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
      (l₁.zip l₂).countP (fun q => p q.2) = l₂.countP p
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | _ :: as, b :: bs, h => by
    simp only [List.zip_cons_cons, List.countP_cons]
    rw [countP_snd_zip p as bs (by simpa using h)]

/-- **One row of §8.2 step 5 per filled slot.** -/
theorem assignedRows_length (r : PlanReq) :
    r.assignedRows.length = r.assignFold.slotOf.countP Option.isSome := by
  obtain ⟨hlen, hok⟩ := PlanReq.assignFold_ok r
  unfold PlanReq.assignedRows
  rw [finalAssign_is_assignFold, List.length_filterMap_eq_countP]
  rw [← countP_snd_zip Option.isSome r.energisedSlots r.assignFold.slotOf hlen.symm]
  apply List.countP_congr
  intro q hq
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hq
  rw [List.getElem?_zip_eq_some] at hi
  obtain ⟨h1, h2⟩ := hi
  cases hq2 : q.2 with
  | none => simp
  | some gi =>
    rw [hq2] at h2
    obtain ⟨e, s, g, -, hg, -⟩ := hok i gi h2
    simp [hg]

/-- `clampSec` keeps the order. -/
theorem clampSec_mono {a b : Nat} (h : a ≤ b) : clampSec a ≤ clampSec b := by
  unfold clampSec; omega

/-- **The day holds a row for every block the walk spent** — §8.2 choice 5b's reservation and one
row per slot step 5 filled, each a work row from `now` on the rows' clock. -/
theorem the_day_holds_every_block_the_walk_spent (r : PlanReq) :
    r.assignFold.used ≤ ((dayPlan r).segments.filter
      (fun s => s.val.kind.isWork && decide (clampSec r.now.sec ≤ s.val.start))).length := by
  rw [← List.countP_eq_length_filter, dayPlan_segments]
  unfold dayRows sortRows
  rw [(Replay.insSort_perm rowLe _).countP_eq, List.countP_map]
  simp only [List.countP_append]
  have hres : (reservationSegs r).countP ((fun s : WfSeg => s.val.kind.isWork &&
      decide (clampSec r.now.sec ≤ s.val.start)) ∘ segOf) = r.activeSeed := by
    have hall : ∀ t ∈ reservationSegs r, ((fun s : WfSeg => s.val.kind.isWork &&
        decide (clampSec r.now.sec ≤ s.val.start)) ∘ segOf) t = true := by
      intro t ht
      obtain ⟨hk, -, -, -, hst⟩ := r.activeRow_is_an_energyless_block t ht
      simp only [Function.comp, segOf_kind, hk, SegKind.isWork, Bool.true_and, decide_eq_true_eq]
      show clampSec r.now.sec ≤ clampSec t.start
      rw [hst]; exact Nat.le_refl _
    rw [List.countP_eq_length.2 hall]
    unfold reservationSegs PlanReq.activeRow PlanReq.activeSeed
    cases r.activeRun <;> rfl
  have hasg : r.assignedRows.countP ((fun s : WfSeg => s.val.kind.isWork &&
      decide (clampSec r.now.sec ≤ s.val.start)) ∘ segOf) = r.assignedRows.length := by
    refine List.countP_eq_length.2 (fun t ht => ?_)
    simp only [Function.comp, segOf_kind, r.assignedRows_are_work t ht, Bool.true_and,
      decide_eq_true_eq]
    exact clampSec_mono (r.an_assigned_row_starts_at_or_after_now t ht)
  rw [hres, hasg, assignedRows_length, assignFold_used_counts]
  omega

theorem foldl_assignStep_keeps_the_members (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign) (n : Nat) (g' : Group),
      (l.foldl (r.assignStep slots breaks budget) a).groups[n]? = some g' →
        ∃ g, a.groups[n]? = some g ∧ g.members = g'.members
  | [], _, _, g', h => ⟨g', h, rfl⟩
  | y :: ys, a, n, g', h => by
    simp only [List.foldl_cons] at h
    obtain ⟨g1, hg1, hm1⟩ := foldl_assignStep_keeps_the_members r slots breaks budget ys _ n g' h
    obtain ⟨g0, hg0, -, hm0, -⟩ := PlanReq.assignStep_keeps_the_group r slots breaks budget a y n g1 hg1
    exact ⟨g0, hg0, hm0.trans hm1⟩

/-- **A slot step 5 filled with a group puts every member of that group into the day's assigned
set** — the row is `assignedSeg` of the group, whose members are the ones `build_groups` gave it
(the walk moves nothing but `spent`), at most `maxBatch` of them, so the batch row names them all
(README gap 1900's missing half, for the fold's own groups). -/
theorem a_filled_slot_assigns_its_groups_members (r : PlanReq) (j gi : Nat)
    (h : r.assignFold.slotOf[j]? = some (some gi)) (g : Group) (hg : r.startGroups[gi]? = some g) :
    ∀ i ∈ g.ids, i ∈ dayAssigned r := by
  intro i hi
  obtain ⟨-, hok⟩ := PlanReq.assignFold_ok r
  obtain ⟨e, s, g', hes, hg', -⟩ := hok j gi h
  obtain ⟨g0, hg0, hm⟩ := foldl_assignStep_keeps_the_members r _ _ _ _ _ gi g' hg'
  have hg0g : g0 = g := by
    unfold PlanReq.assignStart at hg0
    rw [hg] at hg0
    exact (Option.some.inj hg0).symm
  subst hg0g
  have hids : g'.ids = g0.ids := by unfold Group.ids; rw [hm]
  obtain ⟨gb, hgb, -, hmb, -⟩ := PlanReq.a_started_group_is_a_built_group (List.mem_of_getElem? hg)
  have hbound : g'.ids.length ≤ maxBatch := by
    rw [hids]
    unfold Group.ids
    rw [List.length_map, hmb]
    exact (PlanReq.a_group_is_a_bounded_batch hgb).2
  have hrow : assignedSeg e s g' ∈ r.assignedRows := by
    unfold PlanReq.assignedRows
    refine List.mem_filterMap.2 ⟨((e, s), some gi), ?_, ?_⟩
    · rw [finalAssign_is_assignFold]
      exact List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hes, h⟩)
    · simp only [finalAssign_is_assignFold, hg']
  have hday : segOf (assignedSeg e s g') ∈ dayRows r :=
    mem_dayRows_of_mem (by simp [hrow])
  unfold dayAssigned
  refine List.mem_flatMap.2 ⟨segOf (assignedSeg e s g'), List.mem_filter.2 ⟨hday, ?_⟩, ?_⟩
  · rw [segOf_kind]; exact assignedSeg_is_work e s g'
  · show i ∈ (segOf (assignedSeg e s g')).val.items
    rw [segOf_items, assignedSeg_items_when_the_group_fits_the_batch_bound e s g' hbound, hids]
    exact hi

/-- **A `budgetSpent` name is true of the day**: the item's group fits a slot before the walk,
step 5 left that slot EMPTY and gave the group nothing (its members would be in the day), so the
walk passed the slot for the budget — and every block the walk spent is a work row of the day from
`now` (`the_day_holds_every_block_the_walk_spent`). -/
theorem a_budget_spent_name_is_true_of_the_day (r : PlanReq) (i : Id)
    (h : (i, NoPlace.budgetSpent) ∈ r.dayUnplaced (dayAssigned r)) :
    remainingBudget r ≤ ((dayPlan r).segments.filter
      (fun s => s.val.kind.isWork && decide (clampSec r.now.sec ≤ s.val.start))).length := by
  obtain ⟨-, hna, hw⟩ := (r.mem_dayUnplaced (dayAssigned r) i NoPlace.budgetSpent).1 h
  have hany : ((r.energisedSlots.zipIdx.filter (fitsBefore r i)).any
      (fun x => (r.finalAssign.slotOf[x.2]?).join.isNone)) = true := by
    cases he : (r.energisedSlots.zipIdx.filter (fitsBefore r i)).isEmpty
    · rw [he] at hw; simp only [Bool.false_eq_true, ↓reduceIte] at hw
      cases ha : (r.energisedSlots.zipIdx.filter (fitsBefore r i)).any
          (fun x => (r.finalAssign.slotOf[x.2]?).join.isNone)
      · rw [ha] at hw; simp only [Bool.false_eq_true, ↓reduceIte] at hw; split at hw <;> cases hw
      · rfl
    · rw [he] at hw; simp at hw
  obtain ⟨x, hx, hnone⟩ := List.any_eq_true.1 hany
  obtain ⟨hxz, hfb⟩ := List.mem_filter.1 hx
  unfold fitsBefore at hfb
  obtain ⟨g, hgs, hgf⟩ := List.any_eq_true.1 hfb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hgf
  obtain ⟨gi, hgi⟩ := List.mem_iff_getElem?.1 hgs
  have hna' : i ∉ dayAssigned r := by simpa using hna
  refine Nat.le_trans ?_ (the_day_holds_every_block_the_walk_spent r)
  refine the_walk_passes_a_slot_a_group_fits_before_it_only_for_the_budget r x hxz gi g hgi hgf.2
    (by rw [← finalAssign_is_assignFold]; simpa using hnone) (fun y _ hy => ?_)
  exact hna' (a_filled_slot_assigns_its_groups_members r y.2 gi hy g hgi i hgf.1)

/-- **A `noRunLeft`/`noSlotLeft` name is true of the day**: every slot the item's group fits
before the walk is one step 5 filled, with a group the item is not in. -/
theorem a_taken_name_holds_every_slot_it_fits (r : PlanReq) (i : Id) (w : NoPlace)
    (h : (i, w) ∈ r.dayUnplaced (dayAssigned r)) (hw : w ≠ NoPlace.budgetSpent) :
    ∀ x ∈ r.energisedSlots.zipIdx, fitsBefore r i x = true →
      ∃ s ∈ (dayPlan r).segments, s.val.kind.isWork = true ∧ s.val.start = clampSec x.1.2.start ∧
        i ∉ s.val.items := by
  obtain ⟨-, hna, hwdef⟩ := (r.mem_dayUnplaced (dayAssigned r) i w).1 h
  have hany : ((r.energisedSlots.zipIdx.filter (fitsBefore r i)).any
      (fun x => (r.finalAssign.slotOf[x.2]?).join.isNone)) = false := by
    cases ha : (r.energisedSlots.zipIdx.filter (fitsBefore r i)).any
        (fun x => (r.finalAssign.slotOf[x.2]?).join.isNone)
    · rfl
    · have hne : (r.energisedSlots.zipIdx.filter (fitsBefore r i)).isEmpty = false := by
        cases he : (r.energisedSlots.zipIdx.filter (fitsBefore r i)).isEmpty
        · rfl
        · rw [List.isEmpty_iff] at he; rw [he] at ha; simp at ha
      rw [hne, ha] at hwdef; exact absurd hwdef (by simpa using hw)
  have hna' : i ∉ dayAssigned r := by simpa using hna
  intro x hx hfit
  have hsome : (r.finalAssign.slotOf[x.2]?).join.isNone = false :=
    Bool.eq_false_iff.2 ((List.any_eq_false.1 hany) x (List.mem_filter.2 ⟨hx, hfit⟩))
  obtain ⟨-, hok⟩ := PlanReq.assignFold_ok r
  rw [finalAssign_is_assignFold] at hsome
  cases hj : r.assignFold.slotOf[x.2]? with
  | none => rw [hj] at hsome; exact absurd hsome (by simp)
  | some o =>
    cases o with
    | none => rw [hj] at hsome; exact absurd hsome (by simp)
    | some gi =>
      obtain ⟨e, s, g', hes, hg', -⟩ := hok x.2 gi hj
      have hxs : x.1 = (e, s) := by
        have := List.mem_zipIdx_iff_getElem?.1 hx
        rw [hes] at this
        exact (Option.some.inj this).symm
      have hrow : assignedSeg e s g' ∈ r.assignedRows := by
        unfold PlanReq.assignedRows
        refine List.mem_filterMap.2 ⟨((e, s), some gi), ?_, ?_⟩
        · rw [finalAssign_is_assignFold]
          exact List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hes, hj⟩)
        · simp only [finalAssign_is_assignFold, hg']
      have hday : segOf (assignedSeg e s g') ∈ dayRows r := mem_dayRows_of_mem (by simp [hrow])
      refine ⟨segOf (assignedSeg e s g'), by rw [dayPlan_segments]; exact hday, ?_, ?_, ?_⟩
      · rw [segOf_kind]; exact assignedSeg_is_work e s g'
      · rw [hxs]; rfl
      · intro hi
        apply hna'
        unfold dayAssigned
        exact List.mem_flatMap.2 ⟨_, List.mem_filter.2 ⟨hday, by rw [segOf_kind]; exact assignedSeg_is_work e s g'⟩, hi⟩

end PlanFold
end Tm
