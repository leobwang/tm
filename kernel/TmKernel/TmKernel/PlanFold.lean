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



/-! ## W-39 (track K): the ORDER step 5 serves in, the groups it serves, and what the budget-free
laws of §8.3 say about both

Three facts the walk has always had and nothing stated, each a deliverable on its own, and four of
§8.3's laws restated on them after their statements as stage 6 wrote them were refuted
(`PlannerWit`, W-39 block):

* **README gap 3526 — the walk serves its groups in order, at every slot.**  A group that fits a
  slot before the walk and was given nothing before that slot finds it filled by itself or by a
  group ahead of it (`a_slot_a_group_fits_before_the_walk_went_to_a_group_served_no_later`) — the
  step picks the FIRST group that fits (`assignStep_fills_with_the_first_that_fits`) and the walk
  reads nothing it has not yet written (the W-38 section above).  So P58's "every run it fits went
  to work ranked before it" is a theorem (`a_taken_name_went_to_groups_served_before_the_items`) —
  in the order step 5 serves its GROUPS, which is §7.4's key over each group's least member
  (`startGroups_sorted`) and is NOT `Planner.PlanReq.dayServed`'s candidate order (README gap 3540).
* **README gap 3354 — the groups partition the entries they were built from**: a ranked entry sits
  in one start group at most (`a_ranked_entry_is_in_one_start_group_at_most`), because §7.5's
  batching partitions step 4's order and the split partitions each batch; an ITEM sits in one only
  when the request sends each id once (`PlanCheck.an_item_is_in_one_start_group_at_most`).
* **E2 — every batch is a run of consecutive equal-`ci` entries of step 4's order**
  (`batchLoop_is_a_run_of_its_ci`): the gather's `break` is what the infix says.

The restated laws: `plan_is_monotone_in_rank` and `plan_puts_hot_before_the_queue` here,
`PlanCheck.plan_never_batches_past_an_equal_ci_candidate` and
`PlanCheck.plan_places_no_demanding_block_after_wind_down` beside the checker.  Theorems only, as
above: nothing here is compiled into the export. -/

/-- **A step that fills a free slot fills it with the FIRST group that fits** — `List.findIdx?`'s
own clause (`Planner.pickedGroup_is_the_first_that_fits`), read off the slot the step wrote:
every group ahead of the one the slot went to fails §8.2 step 5's filter at the state the step
was handed. -/
theorem assignStep_fills_with_the_first_that_fits (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat)
    (hfree : (a.slotOf[x.2]?).join = none) (gj : Nat)
    (hfill : (r.assignStep slots breaks budget a x).slotOf[x.2]? = some (some gj)) :
    ∀ k, k < gj → ∀ g, a.groups[k]? = some g →
      r.groupFitsSlot slots a.slotOf breaks x.2 x.1.1 x.1.2 g = false := by
  have hkeep : a.slotOf[x.2]? ≠ some (some gj) := by
    intro h; rw [h] at hfree; exact absurd hfree (by simp)
  unfold PlanReq.assignStep at hfill
  split at hfill
  · exact absurd hfill hkeep
  · split at hfill
    · exact absurd hfill hkeep
    · rename_i gi hp
      split at hfill
      · exact absurd hfill hkeep
      · rename_i g hg
        simp only at hfill
        have hlt : x.2 < a.slotOf.length := by
          have := lt_of_getElem?_some hfill
          rwa [List.length_set] at this
        rw [List.getElem?_set_self hlt] at hfill
        have hgj : gi = gj := by simpa using hfill
        subst hgj
        obtain ⟨-, hbefore⟩ := pickedGroup_is_the_first_that_fits _ a.groups gi hp
        exact hbefore

/-- **§8.2 step 5's groups are walked in §7.4's key order** — `Planner.PlanReq.buildGroups_sorted`
through `Planner.spendActive`, which moves one group's `spent` and never a key. -/
theorem spendActive_sorted (id : Id) (mins : Nat) :
    ∀ l : List Group, l.Pairwise (fun a b => groupLe a b = true) →
      (spendActive id mins l).Pairwise (fun a b => groupLe a b = true)
  | [], _ => by simp [spendActive]
  | g :: rest, h => by
    obtain ⟨hg, hrest⟩ := List.pairwise_cons.1 h
    unfold spendActive
    by_cases hb : (g.members.any (fun x => x.cand.id == id)) = true
    · rw [if_pos hb]
      refine List.pairwise_cons.2 ⟨fun b hb' => ?_, hrest⟩
      exact hg b hb'
    · rw [if_neg hb]
      refine List.pairwise_cons.2 ⟨fun b hb' => ?_, spendActive_sorted id mins rest hrest⟩
      obtain ⟨b₀, hb₀, hkey, -⟩ := spendActive_keys id mins rest b hb'
      have := hg b₀ hb₀
      unfold groupLe at this ⊢
      rw [hkey]
      exact this

theorem startGroups_sorted (r : PlanReq) :
    r.startGroups.Pairwise (fun a b => groupLe a b = true) := by
  unfold PlanReq.startGroups
  cases r.activeRun with
  | none => exact r.buildGroups_sorted
  | some q => exact spendActive_sorted _ _ _ r.buildGroups_sorted

/-- **A group served earlier is no later in §7.4's key** — the walk's index order and the key it
was sorted by, one fact. -/
theorem a_group_served_earlier_is_no_later_in_the_key (r : PlanReq) {gj gi : Nat} {h g : Group}
    (hh : r.startGroups[gj]? = some h) (hg : r.startGroups[gi]? = some g) (hlt : gj < gi) :
    groupLe h g = true := by
  have hi : gi < r.startGroups.length := lt_of_getElem?_some hg
  have hj : gj < r.startGroups.length := lt_of_getElem?_some hh
  have := List.pairwise_iff_getElem.mp (startGroups_sorted r) gj gi hj hi hlt
  rw [List.getElem?_eq_getElem hj] at hh
  rw [List.getElem?_eq_getElem hi] at hg
  rw [← Option.some.inj hh, ← Option.some.inj hg]
  exact this

/-- **README gap 3526: a slot a group fits before the walk went to a group served no later** —
unless the group was given a slot before it.  The walk visits the slots once each, in order, from
the state it started in; a group given nothing so far still has its start entry, and the slots
from the cursor on are still free, so it fits the slot at the walk's own state exactly as it did
before the walk (`groupFitsSlot_of_drop`); and the step gives the slot to the FIRST group that fits
(`assignStep_fills_with_the_first_that_fits`).  So the group the slot went to is this one or one
ahead of it in the order §8.2 step 5 serves the groups in. -/
theorem a_slot_a_group_fits_before_the_walk_went_to_a_group_served_no_later (r : PlanReq)
    (x : (Fin 6 × Look.Slot) × Nat) (hx : x ∈ r.energisedSlots.zipIdx)
    (gi : Nat) (g : Group) (hg : r.startGroups[gi]? = some g)
    (hfit : r.groupFitsSlot r.todaySlots r.assignStart.slotOf r.todayBreaks x.2 x.1.1 x.1.2 g = true)
    (hbefore : ∀ y ∈ r.energisedSlots.zipIdx, y.2 < x.2 → r.assignFold.slotOf[y.2]? ≠ some (some gi))
    (gj : Nat) (hfill : r.assignFold.slotOf[x.2]? = some (some gj)) : gj ≤ gi := by
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
    have h1 := hbefore y (hpre_mem y hy) (hpre y hy)
    rw [hfin y.2 (Nat.le_of_lt (hpre y hy)),
      assignStep_slotOf_ne r _ _ _ _ x y.2 (Nat.ne_of_lt (hpre y hy)), ← ha_def] at h1
    exact h1
  have ha_group : a.groups[gi]? = some g := by
    rw [← ha_def, foldl_assignStep_groups_of_never_picked r r.todaySlots r.todayBreaks
      (remainingBudget r) pre r.assignStart gi hnd_pre hlen_pre hnever_pre]
    unfold PlanReq.assignStart
    exact hg
  have hfit' : r.groupFitsSlot r.todaySlots a.slotOf r.todayBreaks x.2 x.1.1 x.1.2 g = true := by
    rw [groupFitsSlot_of_drop r _ _ _ _ _ _ _ _ ha_drop]; exact hfit
  have hstep : (r.assignStep r.todaySlots r.todayBreaks (remainingBudget r) a x).slotOf[x.2]?
      = some (some gj) := by
    rw [← hfin x.2 (Nat.le_refl _)]; exact hfill
  rcases Nat.lt_or_ge gi gj with hlt | hge
  · have := assignStep_fills_with_the_first_that_fits r r.todaySlots r.todayBreaks (remainingBudget r)
      a x ha_free gj hstep gi hlt g ha_group
    rw [hfit'] at this
    exact absurd this (by simp)
  · exact hge

/-- **And strictly ahead of it, when the group was never given a slot at all** — the form P58's
`noRunLeft` and `noSlotLeft` read: the slot is filled, and not by this group. -/
theorem a_slot_a_group_fits_before_the_walk_went_to_a_group_served_before_it (r : PlanReq)
    (x : (Fin 6 × Look.Slot) × Nat) (hx : x ∈ r.energisedSlots.zipIdx)
    (gi : Nat) (g : Group) (hg : r.startGroups[gi]? = some g)
    (hfit : r.groupFitsSlot r.todaySlots r.assignStart.slotOf r.todayBreaks x.2 x.1.1 x.1.2 g = true)
    (hnever : ∀ y ∈ r.energisedSlots.zipIdx, r.assignFold.slotOf[y.2]? ≠ some (some gi))
    (gj : Nat) (hfill : r.assignFold.slotOf[x.2]? = some (some gj)) :
    gj < gi ∧ ∃ h, r.startGroups[gj]? = some h ∧ groupLe h g = true := by
  have hle := a_slot_a_group_fits_before_the_walk_went_to_a_group_served_no_later r x hx gi g hg
    hfit (fun y hy _ => hnever y hy) gj hfill
  have hne : gj ≠ gi := by
    intro he; subst he; exact hnever x hx hfill
  have hlt : gj < gi := by omega
  refine ⟨hlt, ?_⟩
  obtain ⟨-, hok⟩ := PlanReq.assignFold_ok r
  obtain ⟨-, -, h', -, hh', -⟩ := hok x.2 gj hfill
  have hlen : r.assignFold.groups.length = r.startGroups.length := by
    unfold PlanReq.assignFold
    rw [(foldl_assignStep_lengths r _ _ _ _ _).2]; rfl
  have hgjlt : gj < r.startGroups.length := by
    rw [← hlen]; exact lt_of_getElem?_some hh'
  refine ⟨r.startGroups[gj], List.getElem?_eq_getElem hgjlt, ?_⟩
  exact a_group_served_earlier_is_no_later_in_the_key r (List.getElem?_eq_getElem hgjlt) hg hlt

/-- **P58's "ranked before it", as a theorem** (README gap 3526).  An item the day names
`noRunLeft` or `noSlotLeft` (D67) sits in a group that fits some slot before the walk, and EVERY
such slot went to a group §8.2 step 5 serves strictly ahead of every group holding the item that
fits it — ahead in the walk's order, and no later in §7.4's key (with D60's component) that order
was sorted by.  **The order is the GROUPS' and not `Planner.PlanReq.dayServed`'s**: §7.5 batches
and splits before step 5 walks, and a group is keyed by its least member, so the candidate order
and the served order can disagree (README gap 3540). -/
theorem a_taken_name_went_to_groups_served_before_the_items (r : PlanReq) (i : Id) (w : NoPlace)
    (h : (i, w) ∈ r.dayUnplaced (dayAssigned r)) (hw : w ≠ NoPlace.budgetSpent) :
    ∀ x ∈ r.energisedSlots.zipIdx, ∀ (gi : Nat) (g : Group), r.startGroups[gi]? = some g →
      i ∈ g.ids →
      r.groupFitsSlot r.todaySlots r.assignStart.slotOf r.todayBreaks x.2 x.1.1 x.1.2 g = true →
      ∃ (gj : Nat) (h : Group), r.assignFold.slotOf[x.2]? = some (some gj) ∧
        r.startGroups[gj]? = some h ∧ gj < gi ∧ groupLe h g = true := by
  obtain ⟨-, hna, hwdef⟩ := (r.mem_dayUnplaced (dayAssigned r) i w).1 h
  have hna' : i ∉ dayAssigned r := by simpa using hna
  intro x hx gi g hg hig hfit
  have hfb : fitsBefore r i x = true := by
    unfold fitsBefore
    exact List.any_eq_true.2 ⟨g, List.mem_of_getElem? hg, by simp [hig, hfit]⟩
  have hxs : x ∈ r.energisedSlots.zipIdx.filter (fitsBefore r i) := List.mem_filter.2 ⟨hx, hfb⟩
  have hne : (r.energisedSlots.zipIdx.filter (fitsBefore r i)).isEmpty = false := by
    cases he : (r.energisedSlots.zipIdx.filter (fitsBefore r i)).isEmpty
    · rfl
    · rw [List.isEmpty_iff] at he; rw [he] at hxs; simp at hxs
  have hany : ((r.energisedSlots.zipIdx.filter (fitsBefore r i)).any
      (fun x => (r.finalAssign.slotOf[x.2]?).join.isNone)) = false := by
    cases ha : (r.energisedSlots.zipIdx.filter (fitsBefore r i)).any
        (fun x => (r.finalAssign.slotOf[x.2]?).join.isNone)
    · rfl
    · rw [hne, ha] at hwdef; exact absurd hwdef (by simpa using hw)
  have hsome : (r.finalAssign.slotOf[x.2]?).join.isNone = false :=
    Bool.eq_false_iff.2 ((List.any_eq_false.1 hany) x hxs)
  rw [finalAssign_is_assignFold] at hsome
  have hnever : ∀ y ∈ r.energisedSlots.zipIdx, r.assignFold.slotOf[y.2]? ≠ some (some gi) :=
    fun y _ hy => hna' (a_filled_slot_assigns_its_groups_members r y.2 gi hy g hg i hig)
  cases hj : r.assignFold.slotOf[x.2]? with
  | none => rw [hj] at hsome; exact absurd hsome (by simp)
  | some o =>
    cases o with
    | none => rw [hj] at hsome; exact absurd hsome (by simp)
    | some gj =>
      obtain ⟨hlt, hh, hhs, hkey⟩ :=
        a_slot_a_group_fits_before_the_walk_went_to_a_group_served_before_it r x hx gi g hg hfit
          hnever gj hj
      exact ⟨gj, hh, rfl, hhs, hlt, hkey⟩

/-- `natsLe` is reflexive — `natsLe_total` at one list. -/
theorem natsLe_refl (a : List Nat) : natsLe a a = true := by
  have := natsLe_total a a
  simpa using this

/-- **A key strictly ahead is served strictly earlier**: the walk's groups are sorted by
`Planner.groupLe` (`startGroups_sorted`), so a group whose key is not at or before another's
cannot sit at or ahead of it. -/
theorem served_earlier_of_the_key (r : PlanReq) {gi gj : Nat} {g h : Group}
    (hg : r.startGroups[gi]? = some g) (hh : r.startGroups[gj]? = some h)
    (hkey : groupLe h g = false) : gi < gj := by
  rcases Nat.lt_trichotomy gi gj with hlt | heq | hgt
  · exact hlt
  · subst heq
    rw [hg] at hh
    have hgh : g = h := Option.some.inj hh
    subst hgh
    unfold groupLe groupKeyLe at hkey
    rw [natsLe_refl] at hkey
    exact absurd hkey (by simp)
  · rw [a_group_served_earlier_is_no_later_in_the_key r hh hg hgt] at hkey
    exact absurd hkey (by simp)

/-- **A group served earlier that fits a slot a later group took was given a slot before it** —
`a_slot_a_group_fits_before_the_walk_went_to_a_group_served_no_later`, read the other way round:
had it been given nothing before the slot, the slot would have gone to it or to a group ahead of
it. -/
theorem an_earlier_group_that_fits_a_taken_slot_was_placed_before_it (r : PlanReq)
    (x : (Fin 6 × Look.Slot) × Nat) (hx : x ∈ r.energisedSlots.zipIdx)
    (gi gj : Nat) (g : Group) (hg : r.startGroups[gi]? = some g) (hlt : gi < gj)
    (htook : r.assignFold.slotOf[x.2]? = some (some gj))
    (hfit : r.groupFitsSlot r.todaySlots r.assignStart.slotOf r.todayBreaks x.2 x.1.1 x.1.2 g = true) :
    ∃ y ∈ r.energisedSlots.zipIdx, y.2 < x.2 ∧ r.assignFold.slotOf[y.2]? = some (some gi) := by
  refine Classical.byContradiction fun hno => ?_
  have hle := a_slot_a_group_fits_before_the_walk_went_to_a_group_served_no_later r x hx gi g hg
    hfit (fun y hy hyx heq => hno ⟨y, hy, hyx, heq⟩) gj htook
  omega

/-- **A slot step 5 filled draws a work row of the day at the slot's start, holding every member
of the group it went to** — the row `Planner.assignedSeg` builds from the slot and the group, whose
members are the ones `build_groups` gave it and at most `maxBatch` of them. -/
theorem a_filled_slot_draws_a_work_row_of_its_groups_members (r : PlanReq)
    (y : (Fin 6 × Look.Slot) × Nat) (hy : y ∈ r.energisedSlots.zipIdx) (gi : Nat)
    (h : r.assignFold.slotOf[y.2]? = some (some gi)) (g : Group) (hg : r.startGroups[gi]? = some g) :
    ∃ s ∈ (dayPlan r).segments, s.val.kind.isWork = true ∧ s.val.start = clampSec y.1.2.start ∧
      ∀ i ∈ g.ids, i ∈ s.val.items := by
  obtain ⟨-, hok⟩ := PlanReq.assignFold_ok r
  obtain ⟨e, s, g', hes, hg', -⟩ := hok y.2 gi h
  have hye : y.1 = (e, s) := by
    have := List.mem_zipIdx_iff_getElem?.1 hy
    rw [hes] at this
    exact (Option.some.inj this).symm
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
  have hday : Planner.segOf (assignedSeg e s g') ∈ dayRows r := mem_dayRows_of_mem (by simp [hrow])
  refine ⟨Planner.segOf (assignedSeg e s g'), by rw [dayPlan_segments]; exact hday, ?_, ?_, ?_⟩
  · rw [segOf_kind]; exact assignedSeg_is_work e s g'
  · rw [hye]; rfl
  · intro i hi
    show i ∈ (Planner.segOf (assignedSeg e s g')).val.items
    rw [segOf_items, assignedSeg_items_when_the_group_fits_the_batch_bound e s g' hbound, hids]
    exact hi

/-- **Step 3 cuts the slots in time order**, so the walk's earlier index is the earlier start. -/
theorem an_earlier_slot_starts_earlier (r : PlanReq) {y x : (Fin 6 × Look.Slot) × Nat}
    (hy : y ∈ r.energisedSlots.zipIdx) (hx : x ∈ r.energisedSlots.zipIdx) (hlt : y.2 < x.2) :
    y.1.2.start < x.1.2.start := by
  have hyg := List.mem_zipIdx_iff_getElem?.1 hy
  have hxg := List.mem_zipIdx_iff_getElem?.1 hx
  unfold PlanReq.energisedSlots Look.energizeToday at hyg hxg
  rw [List.getElem?_map] at hyg hxg
  have hxl : x.2 < r.todaySlots.length := by
    cases hc : r.todaySlots[x.2]? with
    | none => rw [hc] at hxg; exact absurd hxg (by simp)
    | some _ => exact lt_of_getElem?_some hc
  have hyl : y.2 < r.todaySlots.length := by omega
  rw [List.getElem?_eq_getElem hxl] at hxg
  rw [List.getElem?_eq_getElem hyl] at hyg
  simp only [Option.map_some, Option.some.injEq] at hxg hyg
  have hsorted : r.todaySlots.Pairwise (fun a b => a.stop ≤ b.start) := by
    unfold PlanReq.todaySlots PlanReq.todayCut
    exact Look.cutSlots_slots_are_in_order _ _ _ _ _ _
  have hord := List.pairwise_iff_getElem.mp hsorted y.2 x.2 hyl hxl hlt
  have hne := r.a_slot_is_not_empty r.todaySlots[y.2] (List.getElem_mem hyl)
  rw [← hxg, ← hyg]
  simp only
  omega

/-- **§8.3's monotone rank, restated in the order §8.2 step 5 SERVES its groups** (W-39, README
gaps 3526 and 3542).  A group whose §7.4 key (with D60's component, `Planner.groupLe`) is strictly
ahead of another's is never left out while the other takes a slot the first fits on the empty
cursor — D66's filter before the walk, at THAT slot.

This is `Goals.plan_is_monotone_in_rank` restated, and the goal left `Goals.lean` for it with its
refutations beside it: line order (`PlannerWit.plan_is_monotone_in_rank_as_stage_6_wrote_it_is_refuted`,
`PlannerWit.plan_is_monotone_in_rank_is_refuted_at_a_paying_day`), eligibility somewhere before the
walk (`PlannerWit.monotone_rank_over_step_fives_filter_before_the_walk_is_refuted`), and — the
reason the order is the GROUPS' and not the candidates' — §7.5's split
(`PlannerWit.monotone_rank_in_the_candidate_order_at_the_taken_slot_is_refuted`). -/
theorem plan_is_monotone_in_rank (r : PlanReq) (i : Id) (gi gj : Nat) (g h : Group)
    (hg : r.startGroups[gi]? = some g) (hh : r.startGroups[gj]? = some h) (hi : i ∈ g.ids)
    (hkey : groupLe h g = false)
    (x : (Fin 6 × Look.Slot) × Nat) (hx : x ∈ r.energisedSlots.zipIdx)
    (htook : r.assignFold.slotOf[x.2]? = some (some gj))
    (hfit : r.groupFitsSlot r.todaySlots r.assignStart.slotOf r.todayBreaks x.2 x.1.1 x.1.2 g = true) :
    i ∈ assignedOf (dayPlan r) := by
  obtain ⟨y, -, -, hy⟩ := an_earlier_group_that_fits_a_taken_slot_was_placed_before_it r x hx gi gj g
    hg (served_earlier_of_the_key r hg hh hkey) htook hfit
  exact a_filled_slot_assigns_its_groups_members r y.2 gi hy g hg i hi

/-- **§8.3's "HOT before queue", restated in the order §8.2 step 5 serves its groups** (W-39, README
gap 3543).  §7.4's key reads `p` first, so a group whose key is HOT (`p = 0`, which a group has as
soon as one member has, `Planner.PlanReq.a_group_key_is_its_minimum`) is served ahead of every
queue group (`p > 0`); at a slot a queue group took and the HOT group fits before the walk, the HOT
group already holds a work row of the day that starts no later.

`Goals.plan_puts_hot_before_the_queue` left `Goals.lean` for this with its three refutations
beside it (`PlannerWit.plan_puts_hot_before_the_queue_as_stage_6_wrote_it_is_refuted`,
`PlannerWit.hotBeforeQueue_is_false_on_a_quiet_day`,
`PlannerWit.plan_puts_hot_before_the_queue_is_refuted_at_a_day_that_assigns_and_pays`). -/
theorem plan_puts_hot_before_the_queue (r : PlanReq) (i : Id) (gi gj : Nat) (g h : Group)
    (hg : r.startGroups[gi]? = some g) (hh : r.startGroups[gj]? = some h) (hi : i ∈ g.ids)
    (hhot : g.key.p = 0) (hqueue : 0 < h.key.p)
    (x : (Fin 6 × Look.Slot) × Nat) (hx : x ∈ r.energisedSlots.zipIdx)
    (htook : r.assignFold.slotOf[x.2]? = some (some gj))
    (hfit : r.groupFitsSlot r.todaySlots r.assignStart.slotOf r.todayBreaks x.2 x.1.1 x.1.2 g = true) :
    ∃ si ∈ (dayPlan r).segments, ∃ sj ∈ (dayPlan r).segments,
      si.val.kind.isWork = true ∧ sj.val.kind.isWork = true ∧ i ∈ si.val.items ∧
      (∀ j ∈ h.ids, j ∈ sj.val.items) ∧ sj.val.start = clampSec x.1.2.start ∧
      si.val.start ≤ sj.val.start := by
  have hkey : groupLe h g = false := by
    cases hc : groupLe h g with
    | false => rfl
    | true =>
      have := (natsLe_cons_le hc).1
      rw [hhot] at this
      omega
  obtain ⟨y, hy, hyx, hyg⟩ := an_earlier_group_that_fits_a_taken_slot_was_placed_before_it r x hx
    gi gj g hg (served_earlier_of_the_key r hg hh hkey) htook hfit
  obtain ⟨si, hsi, hwi, hsti, hmemi⟩ :=
    a_filled_slot_draws_a_work_row_of_its_groups_members r y hy gi hyg g hg
  obtain ⟨sj, hsj, hwj, hstj, hmemj⟩ :=
    a_filled_slot_draws_a_work_row_of_its_groups_members r x hx gj htook h hh
  refine ⟨si, hsi, sj, hsj, hwi, hwj, hmemi i hi, hmemj, hstj, ?_⟩
  rw [hsti, hstj]
  exact clampSec_mono (Nat.le_of_lt (an_earlier_slot_starts_earlier r hy hx hyx))


/-! ## W-39 (gap 3354): §8.2 step 5's groups partition the entries they were built from -/

/-- Two members of a list whose images are pairwise distinct are equal when their images are. -/
theorem eq_of_mem_of_nodup_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (he : f a = f b) : a = b := by
  have hp : l.Pairwise (fun a b => f a ≠ f b) := List.pairwise_map.1 h
  rcases pairwise_mem_or hp ha hb with hab | hab | hab
  · exact hab
  · exact absurd he hab
  · exact absurd he.symm hab

/-- A list whose images are pairwise distinct is itself duplicate-free. -/
theorem nodup_of_nodup_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) :
    l.Nodup :=
  List.nodup_iff_pairwise_ne.2 (List.Pairwise.of_map f (fun _ _ hne he => hne (he ▸ rfl)) h)

/-- **Two positions of a list whose `flatMap` is duplicate-free share no element of their
images** — the two halves of the list either side of the later position are disjoint. -/
theorem flatMap_nodup_at_two_positions {α β : Type} (f : α → List β) (l : List α)
    (h : (l.flatMap f).Nodup) {a b : Nat} (ha : a < l.length) (hb : b < l.length)
    (hab : a < b) {x : β} (hxa : x ∈ f l[a]) (hxb : x ∈ f l[b]) : False := by
  rw [← List.take_append_drop b l, List.flatMap_append] at h
  obtain ⟨-, -, hd⟩ := List.nodup_append.1 h
  have hA : x ∈ (l.take b).flatMap f :=
    List.mem_flatMap.2 ⟨l[a], List.mem_take_iff_getElem.2 ⟨a, by omega, rfl⟩, hxa⟩
  have hB : x ∈ (l.drop b).flatMap f :=
    List.mem_flatMap.2 ⟨l[b], List.mem_drop_iff_getElem.2 ⟨0, by omega, by simp⟩, hxb⟩
  exact hd x hA x hB rfl

/-- `flatMap` of pointwise sublists is a sublist. -/
theorem flatMap_sublist {α β : Type} (f g : α → List β) (hfg : ∀ a, (g a).Sublist (f a)) :
    ∀ l : List α, (l.flatMap g).Sublist (l.flatMap f)
  | [] => by simp
  | x :: xs => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (hfg x).append (flatMap_sublist f g hfg xs)

/-- **Step 4's order holds each request position once** — an entry's `ix` is the position its
answer arrived at (`Planner.PlanReq.keyOf`), and the filter only drops positions. -/
theorem rankedCands_ix_nodup (r : PlanReq) : (r.rankedCands.map (·.key.ix)).Nodup := by
  unfold PlanReq.rankedCands
  have hperm := (Replay.insSort_perm rankedLe
    ((r.candAnswers.zipIdx.filter (fun x => entersTheOrder x.1)).map
      (fun x => (⟨r.keyOf x.2 x.1, x.1⟩ : Ranked)))).map (·.key.ix)
  unfold sortRanked
  refine (hperm.nodup_iff).2 ?_
  rw [List.map_map]
  have hmap : ((r.candAnswers.zipIdx.filter (fun x => entersTheOrder x.1)).map
      ((fun y : Ranked => y.key.ix) ∘ (fun x => (⟨r.keyOf x.2 x.1, x.1⟩ : Ranked))))
      = (r.candAnswers.zipIdx.filter (fun x => entersTheOrder x.1)).map Prod.snd := by
    apply List.map_congr_left
    intro x _
    rfl
  rw [hmap]
  refine List.Nodup.sublist (List.filter_sublist.map _) ?_
  rw [List.zipIdx_map_snd]
  exact List.nodup_range' 1

theorem rankedCands_nodup (r : PlanReq) : r.rankedCands.Nodup :=
  nodup_of_nodup_map _ (rankedCands_ix_nodup r)

/-- A split bucket list's groups carry its buckets' members: `groupOf` refuses only an empty
bucket, which carries none. -/
theorem filterMap_groupOf_members :
    ∀ L : List (SplitKey × List Ranked),
      (L.filterMap (fun e => groupOf e.1 e.2)).flatMap (·.members) = L.flatMap (·.2)
  | [] => rfl
  | e :: L => by
    rw [List.filterMap_cons, List.flatMap_cons]
    cases hg : groupOf e.1 e.2 with
    | none =>
      have he : e.2 = [] := by
        cases hl : e.2 with
        | nil => rfl
        | cons z zs => rw [hl] at hg; simp [groupOf] at hg
      simp only
      rw [filterMap_groupOf_members L, he, List.nil_append]
    | some g =>
      simp only [List.flatMap_cons]
      rw [(groupOf_members hg).1, filterMap_groupOf_members L]

/-- **The raw groups' members are the batches' plain members, rearranged.** -/
theorem rawGroups_members_perm (r : PlanReq) :
    (r.rawGroups.flatMap (·.members)).Perm (r.dayBatches.flatMap batchMembers) := by
  unfold PlanReq.rawGroups
  rw [List.flatMap_assoc]
  induction r.dayBatches with
  | nil => simp
  | cons b bs ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    refine List.Perm.append ?_ ih
    rw [filterMap_groupOf_members]
    have := splitGroups_flatten (r.activeRun.map (·.id)) (batchMembers b)
    rwa [← List.flatMap_def] at this

/-- **No ranked entry is a member of two of step 5's raw groups, nor twice of one.** -/
theorem rawGroups_members_nodup (r : PlanReq) : (r.rawGroups.flatMap (·.members)).Nodup := by
  refine (rawGroups_members_perm r).nodup_iff.2 ?_
  refine List.Nodup.sublist (flatMap_sublist (fun b => b) batchMembers
    (fun b => List.filter_sublist) r.dayBatches) ?_
  have h := (batches_flatten_perm r.prio.batchMaxMin r.blockMin r.rankedCands).nodup_iff.2
    (rankedCands_nodup r)
  unfold PlanReq.dayBatches
  rwa [List.flatMap_def, List.map_id']

/-- `spendActive` keeps every group's members where they were. -/
theorem spendActive_members (id : Id) (mins : Nat) :
    ∀ l : List Group, (spendActive id mins l).map (·.members) = l.map (·.members)
  | [] => rfl
  | g :: rest => by
    unfold spendActive
    by_cases hb : (g.members.any (fun x => x.cand.id == id)) = true
    · rw [if_pos hb]; rfl
    · rw [if_neg hb, List.map_cons, List.map_cons, spendActive_members id mins rest]

theorem startGroups_members_nodup (r : PlanReq) : (r.startGroups.flatMap (·.members)).Nodup := by
  have hs : r.startGroups.flatMap (·.members) = r.buildGroups.flatMap (·.members) := by
    unfold PlanReq.startGroups
    cases r.activeRun with
    | none => rfl
    | some q => rw [List.flatMap_def, List.flatMap_def, spendActive_members]
  rw [hs]
  refine ((Replay.insSort_perm groupLe r.rawGroups).flatMap_right (·.members)).nodup_iff.2 ?_
  exact rawGroups_members_nodup r

/-- **README gap 3354, per entry: a ranked entry sits in one start group at most** — the batching
is a partition of §7.4's order (`Planner.batches_flatten_perm`), the split a partition of each
batch (`Planner.splitGroups_flatten`), and each group is one bucket (`Planner.groupOf_members`);
an entry is a request position, and no two entries share one. -/
theorem a_ranked_entry_is_in_one_start_group_at_most (r : PlanReq) {a b : Nat} {ga gb : Group}
    (ha : r.startGroups[a]? = some ga) (hb : r.startGroups[b]? = some gb) {x : Ranked}
    (hxa : x ∈ ga.members) (hxb : x ∈ gb.members) : a = b := by
  have hal : a < r.startGroups.length := lt_of_getElem?_some ha
  have hbl : b < r.startGroups.length := lt_of_getElem?_some hb
  have ea : r.startGroups[a] = ga := Option.some.inj ((List.getElem?_eq_getElem hal).symm.trans ha)
  have eb : r.startGroups[b] = gb := Option.some.inj ((List.getElem?_eq_getElem hbl).symm.trans hb)
  have hnd := startGroups_members_nodup r
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exact (flatMap_nodup_at_two_positions (·.members) _ hnd hal hbl hab
      (by rw [ea]; exact hxa) (by rw [eb]; exact hxb)).elim
  · exact hab
  · exact (flatMap_nodup_at_two_positions (·.members) _ hnd hbl hal hab
      (by rw [eb]; exact hxb) (by rw [ea]; exact hxa)).elim

/-! ## W-39 (E2): every batch of §7.5 is a run of consecutive equal-`ci` entries of the order -/

/-- **What the gather keeps of another `ci` is everything of it** — the gather takes only its own
`ci`, and passes every other entry over into what it keeps (the fork's `continue`). -/
theorem gatherBatch_snd_filter_other (ms bm : Nat) (ci c : Fin 6) (hc : c ≠ ci) :
    ∀ (l : List Ranked) (room tot : Nat),
      (gatherBatch ms bm ci room tot l).2.filter (fun y => decide (y.cand.ci = c)) =
        l.filter (fun y => decide (y.cand.ci = c))
  | [], _, _ => by simp [gatherBatch]
  | x :: xs, room, tot => by
    unfold gatherBatch
    by_cases hci : x.cand.ci = ci
    · rw [if_pos hci]
      have hxc : ¬ x.cand.ci = c := fun h => hc (h ▸ hci)
      by_cases hstop : (room == 0 || !x.gatherable ms ||
          decide (bm < tot + x.facts.plannedMin)) = true
      · rw [if_pos hstop]
      · rw [if_neg hstop]
        simp only [List.filter_cons, hxc, decide_false, Bool.false_eq_true, if_false]
        exact gatherBatch_snd_filter_other ms bm ci c hc xs (room - 1) (tot + x.facts.plannedMin)
    · rw [if_neg hci]
      simp only [List.filter_cons]
      rw [gatherBatch_snd_filter_other ms bm ci c hc xs room tot]

/-- **What the gather keeps of its own `ci` is what follows the gathered prefix** — the gather's
`break` keeps the rest of the walk whole. -/
theorem gatherBatch_snd_filter_own (ms bm : Nat) (ci : Fin 6) :
    ∀ (l : List Ranked) (room tot : Nat),
      (gatherBatch ms bm ci room tot l).2.filter (fun y => decide (y.cand.ci = ci)) =
        (l.filter (fun y => decide (y.cand.ci = ci))).drop (gatherBatch ms bm ci room tot l).1.length
  | [], _, _ => by simp [gatherBatch]
  | x :: xs, room, tot => by
    unfold gatherBatch
    by_cases hci : x.cand.ci = ci
    · rw [if_pos hci]
      by_cases hstop : (room == 0 || !x.gatherable ms ||
          decide (bm < tot + x.facts.plannedMin)) = true
      · rw [if_pos hstop]; simp
      · rw [if_neg hstop]
        simp only [List.filter_cons, hci, decide_true, if_true, List.length_cons, List.drop_succ_cons]
        exact gatherBatch_snd_filter_own ms bm ci xs (room - 1) (tot + x.facts.plannedMin)
    · rw [if_neg hci]
      simp only [List.filter_cons, hci, decide_false, Bool.false_eq_true, if_false]
      exact gatherBatch_snd_filter_own ms bm ci xs room tot

/-- **E2, for the batching's own loop**: every batch is an infix of the equal-`ci` entries of what
the loop walked — the gather's members are a prefix of the equal-`ci` entries after the leader
(`Planner.gatherBatch_fst_is_a_prefix_of_its_ci`, the `break`), and what a later batch walks is the
rest with nothing of its `ci` taken out of order. -/
theorem batchLoop_is_a_run_of_its_ci (ms bm : Nat) :
    ∀ (fuel : Nat) (l : List Ranked), ∀ B ∈ batchLoop ms bm fuel l,
      ∃ c : Fin 6, B <:+: l.filter (fun y => decide (y.cand.ci = c))
  | 0, _, _, h => by simp [batchLoop] at h
  | _ + 1, [], _, h => by simp [batchLoop] at h
  | fuel + 1, x :: xs, B, h => by
    unfold batchLoop at h
    generalize hp : (if x.gatherable ms = true then
        gatherBatch ms bm x.cand.ci (maxBatch - 1) x.facts.plannedMin xs else ([], xs)) = p at h
    have hfst : p.1 <+: xs.filter (fun y => decide (y.cand.ci = x.cand.ci)) := by
      rw [← hp]
      split
      · exact gatherBatch_fst_is_a_prefix_of_its_ci ms bm x.cand.ci xs _ _
      · exact List.nil_prefix
    have hsnd : ∀ c : Fin 6, p.2.filter (fun y => decide (y.cand.ci = c)) <:+
        (x :: xs).filter (fun y => decide (y.cand.ci = c)) := by
      intro c
      by_cases hc : c = x.cand.ci
      · subst hc
        have heq : p.2.filter (fun y => decide (y.cand.ci = x.cand.ci)) =
            (xs.filter (fun y => decide (y.cand.ci = x.cand.ci))).drop p.1.length := by
          rw [← hp]
          split
          · exact gatherBatch_snd_filter_own ms bm x.cand.ci xs _ _
          · simp
        rw [heq, List.filter_cons, if_pos (by simp)]
        exact (List.drop_suffix _ _).trans (List.suffix_cons _ _)
      · have heq : p.2.filter (fun y => decide (y.cand.ci = c)) =
            xs.filter (fun y => decide (y.cand.ci = c)) := by
          rw [← hp]
          split
          · exact gatherBatch_snd_filter_other ms bm x.cand.ci c hc xs _ _
          · rfl
        have hx : ¬ x.cand.ci = c := fun h => hc h.symm
        rw [heq, List.filter_cons, if_neg (by simpa using hx)]
        exact List.suffix_refl _
    rcases List.mem_cons.1 h with rfl | h
    · refine ⟨x.cand.ci, ?_⟩
      rw [List.filter_cons, if_pos (by simp)]
      exact ((List.prefix_cons_inj x).2 hfst).isInfix
    · obtain ⟨c, hc⟩ := batchLoop_is_a_run_of_its_ci ms bm fuel p.2 B h
      exact ⟨c, hc.trans (hsnd c).isInfix⟩

/-- **E2 at this request: every one of §7.5's batches is a run of consecutive equal-`ci` entries
of step 4's order** (W-39, README gap 3547) — it never reaches past an equal-`ci` entry between two
of its members, and its members stand in the order's own order. -/
theorem a_batch_is_a_run_of_equal_ci_entries_of_the_order (r : PlanReq) (B : List Ranked)
    (hB : B ∈ r.dayBatches) :
    ∃ c : Fin 6, B <:+: r.rankedCands.filter (fun y => decide (y.cand.ci = c)) :=
  batchLoop_is_a_run_of_its_ci _ _ _ _ B hB


/-! ## W-39 (L24): the budget only stops the walk early -/

/-- **A step with its budget spent changes nothing** — the fork's `continue` on `used >= budget`. -/
theorem assignStep_of_spent (r : PlanReq) (slots : List Look.Slot) (breaks : List (Nat × Nat))
    (b : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat) (h : b ≤ a.used) :
    r.assignStep slots breaks b a x = a := by
  unfold PlanReq.assignStep
  rw [if_pos (by simp [h])]

/-- **Below the smaller budget, the two budgets take the same step** — the guard is the only
place a step reads its budget. -/
theorem assignStep_below (r : PlanReq) (slots : List Look.Slot) (breaks : List (Nat × Nat))
    {b' b : Nat} (hb : b' ≤ b) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat) (h : a.used < b') :
    r.assignStep slots breaks b' a x = r.assignStep slots breaks b a x := by
  unfold PlanReq.assignStep
  have h1 : decide (b' ≤ a.used) = false := decide_eq_false (Nat.not_le.2 h)
  have h2 : decide (b ≤ a.used) = false := decide_eq_false (Nat.not_le.2 (Nat.lt_of_lt_of_le h hb))
  rw [h1, h2]

theorem foldl_assignStep_of_spent (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (b : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign), b ≤ a.used →
      l.foldl (r.assignStep slots breaks b) a = a
  | [], _, _ => rfl
  | x :: l, a, h => by
    simp only [List.foldl_cons]
    rw [assignStep_of_spent r slots breaks b a x h]
    exact foldl_assignStep_of_spent r slots breaks b l a h

/-- **The smaller budget's walk is the larger budget's walk stopped after its first `k` slots** —
L24's heart: the budget reaches the walk only through the guard, so the two walks agree step for
step until the smaller budget is spent, and from there the smaller one stands still. -/
theorem foldl_assignStep_truncates (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) {b' b : Nat} (hb : b' ≤ b) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign), ∃ k,
      l.foldl (r.assignStep slots breaks b') a = (l.take k).foldl (r.assignStep slots breaks b) a
  | [], _ => ⟨0, rfl⟩
  | x :: l, a => by
    by_cases h : a.used < b'
    · obtain ⟨k, hk⟩ := foldl_assignStep_truncates r slots breaks hb l
        (r.assignStep slots breaks b a x)
      refine ⟨k + 1, ?_⟩
      simp only [List.foldl_cons, List.take_succ_cons]
      rw [assignStep_below r slots breaks hb a x h]
      exact hk
    · refine ⟨0, ?_⟩
      simp only [List.take_zero, List.foldl_nil]
      exact foldl_assignStep_of_spent r slots breaks b' (x :: l) a (Nat.not_lt.1 h)

/-- **A step moves a group's `spent` and nothing else**: every group of the state it returns is a
group of the state it was handed with another `spent`. -/
theorem assignStep_group_is_the_group_with_its_spent (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat)
    (n : Nat) (g' : Group) (h : (r.assignStep slots breaks budget a x).groups[n]? = some g') :
    ∃ g, a.groups[n]? = some g ∧ g' = { g with spent := g'.spent } := by
  rcases PlanReq.assignStep_cases r slots breaks budget a x with heq | ⟨gi, g, hg, -, -, heq⟩
  · rw [heq] at h; exact ⟨g', h, rfl⟩
  · rw [heq] at h
    simp only at h
    by_cases hn : n = gi
    · subst hn
      rw [List.getElem?_set_self (lt_of_getElem?_some hg)] at h
      simp only [Option.some.injEq] at h
      exact ⟨g, hg, by rw [← h]⟩
    · rw [List.getElem?_set_ne (by omega)] at h
      exact ⟨g', h, rfl⟩

theorem foldl_assignStep_group_is_the_group_with_its_spent (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign) (n : Nat) (g' : Group),
      (l.foldl (r.assignStep slots breaks budget) a).groups[n]? = some g' →
      ∃ g, a.groups[n]? = some g ∧ g' = { g with spent := g'.spent }
  | [], _, _, g', h => ⟨g', h, rfl⟩
  | x :: l, a, n, g', h => by
    simp only [List.foldl_cons] at h
    obtain ⟨g1, h1, e1⟩ := foldl_assignStep_group_is_the_group_with_its_spent r slots breaks budget
      l _ n g' h
    obtain ⟨g0, h0, e0⟩ := assignStep_group_is_the_group_with_its_spent r slots breaks budget a x n
      g1 h1
    refine ⟨g0, h0, ?_⟩
    rw [e1, e0]

/-- **A row of step 5 does not read how much its group has spent.** -/
theorem assignedSeg_ignores_spent (e : Fin 6) (s : Look.Slot) (g : Group) (m : Nat) :
    assignedSeg e s { g with spent := m } = assignedSeg e s g := rfl

/-- **What a filter-map keeps of two lists that agree on a head and whose tail maps to nothing is
a prefix** — the list form of "the smaller budget's rows are the larger's first rows". -/
theorem filterMap_prefix_of_agreeing_head {α β : Type} (f' f : α → Option β) :
    ∀ (L' L : List α) (k : Nat), L'.length = L.length →
      (∀ j (a' a : α), j < k → L'[j]? = some a' → L[j]? = some a → f' a' = f a) →
      (∀ j (a' : α), k ≤ j → L'[j]? = some a' → f' a' = none) →
      L'.filterMap f' <+: L.filterMap f
  | [], [], _, _, _, _ => List.prefix_refl _
  | [], _ :: _, _, h, _, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | a' :: L', a :: L, 0, _, _, hnone => by
    have : (a' :: L').filterMap f' = [] := by
      refine List.filterMap_eq_nil_iff.2 (fun x hx => ?_)
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
      exact hnone j x (Nat.zero_le _) hj
    rw [this]; exact List.nil_prefix
  | a' :: L', a :: L, k + 1, hlen, hagree, hnone => by
    have h0 : f' a' = f a := hagree 0 a' a (Nat.succ_pos _) rfl rfl
    have ih := filterMap_prefix_of_agreeing_head f' f L' L k (by simpa using hlen)
      (fun j x' x hj h' h => hagree (j + 1) x' x (by omega) h' h)
      (fun j x' hj h' => hnone (j + 1) x' (by omega) h')
    rw [List.filterMap_cons, List.filterMap_cons, h0]
    cases f a with
    | none => exact ih
    | some b => exact (List.prefix_cons_inj b).2 ih

/-- **A stable insertion sort of two blocks, the second wholly after the first, is the two blocks
sorted** — `Replay.insSort` inserts each element at the first place it is not after, so nothing of
the second block moves ahead of the first. -/
theorem insBy_append_after {α : Type} (le : α → α → Bool) (x : α) :
    ∀ (S T : List α), (∀ t ∈ T, le x t = true) →
      Replay.insBy le x (S ++ T) = Replay.insBy le x S ++ T
  | [], [], _ => rfl
  | [], t :: T, h => by simp [Replay.insBy, h t (List.mem_cons_self ..)]
  | s :: S, T, h => by
    simp only [List.cons_append, Replay.insBy]
    split
    · rfl
    · simp only [List.cons_append, insBy_append_after le x S T h]

theorem insSort_append_after {α : Type} (le : α → α → Bool) :
    ∀ (L M : List α), (∀ l ∈ L, ∀ m ∈ M, le l m = true) →
      Replay.insSort le (L ++ M) = Replay.insSort le L ++ Replay.insSort le M
  | [], M, _ => rfl
  | x :: L, M, h => by
    simp only [List.cons_append, Replay.insSort]
    rw [insSort_append_after le L M (fun l hl m hm => h l (List.mem_cons_of_mem _ hl) m hm)]
    exact insBy_append_after le x _ _ (fun t ht =>
      h x (List.mem_cons_self ..) t ((Replay.insSort_perm le M).mem_iff.1 ht))

/-- **The slots are the energised entries' second halves.** -/
theorem todaySlots_of_energisedSlots (r : PlanReq) : r.energisedSlots.map Prod.snd = r.todaySlots := by
  unfold PlanReq.energisedSlots Look.energizeToday
  rw [List.map_map]
  exact List.map_id _

/-- **The running block's seed is the reservation's row count.** -/
theorem activeSeed_is_the_reservation (r : PlanReq) : r.activeSeed = (reservationSegs r).length := by
  unfold PlanReq.activeSeed reservationSegs PlanReq.activeRow
  cases r.activeRun <;> rfl

/-- **A later slot of the cut starts after an earlier one.** -/
theorem energised_start_lt (r : PlanReq) {i j : Nat} (hij : i < j) {e e' : Fin 6} {s s' : Look.Slot}
    (hi : r.energisedSlots[i]? = some (e, s)) (hj : r.energisedSlots[j]? = some (e', s')) :
    s.start < s'.start :=
  an_earlier_slot_starts_earlier r (x := ((e', s'), j)) (y := ((e, s), i))
    (List.mem_zipIdx_iff_getElem?.2 hi) (List.mem_zipIdx_iff_getElem?.2 hj) hij

/-- A row of the day's work set, as `segOf` draws it, is ordered before another whose raw start
is later. -/
theorem rowLe_of_start_lt (l m : Seg) (h : l.start < m.start) :
    rowLe (Planner.segOf l) (Planner.segOf m) = true := by
  show (decide (Planner.clampSec l.start < Planner.clampSec m.start) ||
      (decide (Planner.clampSec l.start = Planner.clampSec m.start) &&
        decide (max (Planner.clampSec l.start) (Planner.clampSec l.stop) ≤
          max (Planner.clampSec m.start) (Planner.clampSec m.stop)))) = true
  unfold Planner.clampSec
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- **Rows no member of which is work contribute nothing to the day's work set.** -/
theorem filter_work_of_no_work (L : List Seg) (h : ∀ t ∈ L, t.kind.isWork = false) :
    (L.map Planner.segOf).filter (fun s => s.val.kind.isWork) = [] := by
  refine List.filter_eq_nil_iff.2 (fun s hs => ?_)
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
  rw [Planner.segOf_kind]
  simp [h t ht]

/-- **The work rows of step 1 are its replayed rows**: interruptions are Lost, a running break is
a Break and a wall row is a Wall, whichever order `stepOneOrder` walks them in. -/
theorem stepOneOrder_work (r : PlanReq) :
    ((stepOneOrder r).map Planner.segOf).filter (fun s => s.val.kind.isWork) =
      ((replayedRows r).map Planner.segOf).filter (fun s => s.val.kind.isWork) := by
  have hi : ∀ t ∈ interruptRows r, t.kind.isWork = false := fun t ht => by
    rw [(interruptRows_are_open_lost_time r t ht).1]; rfl
  have hb : ∀ t ∈ breakRows r, t.kind.isWork = false := fun t ht => by
    rw [(breakRows_are_running_breaks r t ht).1]; rfl
  have hw : ∀ (L : List Look.WallIx), ∀ t ∈ L.flatMap (fun x => wallRows (r.isTravelDay x.id) x),
      t.kind.isWork = false := fun L t ht => by
    obtain ⟨x, -, hx⟩ := List.mem_flatMap.1 ht
    rw [(wallRows_are_walls_of_the_item _ x t hx).1]; rfl
  unfold stepOneOrder
  split
  · unfold stepOneSegs
    simp only [List.map_append, List.filter_append]
    rw [filter_work_of_no_work _ hi, filter_work_of_no_work _ hb, filter_work_of_no_work _ (hw _)]
    simp
  · simp only [List.map_append, List.filter_append]
    rw [filter_work_of_no_work _ hi, filter_work_of_no_work _ hb, filter_work_of_no_work _ (hw _),
      filter_work_of_no_work _ (hw _)]
    simp

/-- **The day's work rows are the replayed ones that are work, the reservation and step 5's, in the
day's order** — every other row the day draws is a wall, a routine, the evening, a break, an
optional or Rest. -/
theorem work_rows_of_the_day (r : PlanReq) :
    (dayRows r).filter (fun s => s.val.kind.isWork) =
      sortRows (((replayedRows r).map Planner.segOf).filter (fun s => s.val.kind.isWork) ++
        (reservationSegs r).map Planner.segOf ++ r.assignedRows.map Planner.segOf) := by
  unfold dayRows
  rw [sortRows_filter]
  congr 1
  simp only [List.map_append, List.filter_append]
  rw [stepOneOrder_work,
    filter_work_of_no_work (dayRoutineSegs r) (fun t ht => by
      rcases routineRows_kinds r _ t ht with h | h | h <;> rw [h] <;> rfl),
    filter_work_of_no_work r.keptBreakRows (fun t ht => r.keptBreakRows_are_not_work t ht),
    filter_work_of_no_work r.optionalRows (fun t ht => r.optionalRows_are_not_work t ht),
    filter_work_of_no_work r.restRows (fun t ht => r.restRows_are_not_work t ht)]
  have hres : ((reservationSegs r).map Planner.segOf).filter (fun s => s.val.kind.isWork) =
      (reservationSegs r).map Planner.segOf :=
    List.filter_eq_self.2 (fun s hs => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
      rw [Planner.segOf_kind, reservationSegs_are_blocks r t ht]; rfl)
  have hasg : (r.assignedRows.map Planner.segOf).filter (fun s => s.val.kind.isWork) =
      r.assignedRows.map Planner.segOf :=
    List.filter_eq_self.2 (fun s hs => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
      rw [Planner.segOf_kind]; exact r.assignedRows_are_work t ht)
  rw [hres, hasg]
  simp

/-- **Step 5's rows, read off step 5's own assignment.** -/
theorem assignedRows_of_assignFold (r : PlanReq) :
    r.assignedRows = (r.energisedSlots.zip r.assignFold.slotOf).filterMap (fun p =>
      match p.2 with
      | Option.none => Option.none
      | some gi =>
        match r.assignFold.groups[gi]? with
        | Option.none => Option.none
        | some g => some (assignedSeg p.1.1 p.1.2 g)) := by
  unfold PlanReq.assignedRows
  rw [finalAssign_is_assignFold]
  rfl

/-- **Two group lists that agree on every group but its `spent` draw the same rows.** -/
theorem rows_ignore_spent (E : List (Fin 6 × Look.Slot)) (S : List (Option Nat)) (GA GB : List Group)
    (hlen : GA.length = GB.length)
    (hg : ∀ (n : Nat) (gA gB : Group), GA[n]? = some gA → GB[n]? = some gB →
      ∃ g0 : Group, gA = { g0 with spent := gA.spent } ∧ gB = { g0 with spent := gB.spent }) :
    (E.zip S).filterMap (fun p =>
      match p.2 with
      | Option.none => Option.none
      | some gi =>
        match GA[gi]? with
        | Option.none => Option.none
        | some g => some (assignedSeg p.1.1 p.1.2 g)) =
    (E.zip S).filterMap (fun p =>
      match p.2 with
      | Option.none => Option.none
      | some gi =>
        match GB[gi]? with
        | Option.none => Option.none
        | some g => some (assignedSeg p.1.1 p.1.2 g)) := by
  congr 1
  funext p
  cases p.2 with
  | none => rfl
  | some gi =>
    simp only
    cases ha : GA[gi]? with
    | none =>
      cases hb : GB[gi]? with
      | none => rfl
      | some gB =>
        have h1 := lt_of_getElem?_some hb
        have h2 := List.getElem?_eq_none_iff.1 ha
        omega
    | some gA =>
      cases hb : GB[gi]? with
      | none =>
        have h1 := lt_of_getElem?_some ha
        have h2 := List.getElem?_eq_none_iff.1 hb
        omega
      | some gB =>
        obtain ⟨g0, e1, e2⟩ := hg gi gA gB ha hb
        simp only
        rw [e1, e2]
        rfl

/-- **§8.2 step 5's filter reads five fields of a group**: its `ci`, its `loc:`, whether it is
`splittable`, what it commits to and what it has spent. -/
theorem groupFitsSlot_congr (r : PlanReq) (slots : List Look.Slot) (slotOf : List (Option Nat))
    (breaks : List (Nat × Nat)) (i : Nat) (e : Fin 6) (s : Look.Slot) (g g' : Group)
    (hci : g.ci = g'.ci) (hloc : g.loc = g'.loc) (hsp : g.splittable = g'.splittable)
    (hc : g.commitMin = g'.commitMin) (hs : g.spent = g'.spent) :
    r.groupFitsSlot slots slotOf breaks i e s g = r.groupFitsSlot slots slotOf breaks i e s g' := by
  unfold PlanReq.groupFitsSlot Group.live Group.leftMin
  rw [hci, hloc, hsp, hc, hs]

/-- **A row of step 5 reads five things of its group**: the members' ids and priorities, its
`ci`, its multiplier and its commitment. -/
theorem assignedSeg_congr (e : Fin 6) (s : Look.Slot) (g g' : Group) (hids : g.ids = g'.ids)
    (hp : g.members.map (fun m => m.key.p) = g'.members.map (fun m => m.key.p))
    (hci : g.ci = g'.ci) (hm : g.mult = g'.mult) (hc : g.commitMin = g'.commitMin) :
    assignedSeg e s g = assignedSeg e s g' := by
  have hhot : g.members.any (fun m => m.key.p == 0) = g'.members.any (fun m => m.key.p == 0) := by
    have h1 : g.members.any (fun m => m.key.p == 0) =
        (g.members.map (fun m => m.key.p)).any (fun n => n == 0) := by rw [List.any_map]; rfl
    have h2 : g'.members.any (fun m => m.key.p == 0) =
        (g'.members.map (fun m => m.key.p)).any (fun n => n == 0) := by rw [List.any_map]; rfl
    rw [h1, h2, hp]
  unfold assignedSeg
  rw [hids, hci, hm, hc, hhot]

/-- `List.findIdx?` is decided by the predicate's values alone. -/
theorem findIdx?_of_values {α : Type} (P : α → Bool) :
    ∀ (l l' : List α), l.map P = l'.map P → l.findIdx? P = l'.findIdx? P
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: l, x' :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [List.findIdx?_cons, List.findIdx?_cons, h.1, findIdx?_of_values P l l' h.2]

/-- **Two walks whose states agree on the slot vector, the budget spent and every group as step 5
reads it take the same step** (the view: ids, the members' priorities, `ci`, `loc:`, `splittable`,
multiplier, commitment and `spent`). -/
theorem assignStep_on_views (r : PlanReq) (slots : List Look.Slot) (breaks : List (Nat × Nat))
    (budget : Nat) (a a' : Assign) (x : (Fin 6 × Look.Slot) × Nat)
    (hs : a'.slotOf = a.slotOf) (hu : a'.used = a.used)
    (hg : a'.groups.map (fun g => (g.ids, g.members.map (fun m => m.key.p), g.ci, g.loc, g.splittable,
      g.mult, g.commitMin, g.spent)) =
      a.groups.map (fun g => (g.ids, g.members.map (fun m => m.key.p), g.ci, g.loc, g.splittable,
        g.mult, g.commitMin, g.spent))) :
    (r.assignStep slots breaks budget a' x).slotOf = (r.assignStep slots breaks budget a x).slotOf ∧
    (r.assignStep slots breaks budget a' x).used = (r.assignStep slots breaks budget a x).used ∧
    (r.assignStep slots breaks budget a' x).groups.map (fun g => (g.ids,
        g.members.map (fun m => m.key.p), g.ci, g.loc, g.splittable, g.mult, g.commitMin, g.spent)) =
      (r.assignStep slots breaks budget a x).groups.map (fun g => (g.ids,
        g.members.map (fun m => m.key.p), g.ci, g.loc, g.splittable, g.mult, g.commitMin, g.spent)) := by
  have hlen : a'.groups.length = a.groups.length := by
    have := congrArg List.length hg; simpa using this
  have hfit : a'.groups.map (r.groupFitsSlot slots a'.slotOf breaks x.2 x.1.1 x.1.2) =
      a.groups.map (r.groupFitsSlot slots a.slotOf breaks x.2 x.1.1 x.1.2) := by
    rw [hs]
    apply List.ext_getElem?
    intro n
    rw [List.getElem?_map, List.getElem?_map]
    cases h1 : a'.groups[n]? with
    | none =>
      cases h2 : a.groups[n]? with
      | none => rfl
      | some g => have := lt_of_getElem?_some h2; have := List.getElem?_eq_none_iff.1 h1; omega
    | some g' =>
      cases h2 : a.groups[n]? with
      | none => have := lt_of_getElem?_some h1; have := List.getElem?_eq_none_iff.1 h2; omega
      | some g =>
        have hv := congrArg (·[n]?) hg
        simp only [List.getElem?_map, h1, h2, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at hv
        obtain ⟨-, -, hci, hloc, hsp, -, hc, hsp2⟩ := hv
        simp only [Option.map_some]
        rw [groupFitsSlot_congr r slots a.slotOf breaks x.2 x.1.1 x.1.2 g' g hci hloc hsp hc hsp2]
  have hfind : a'.groups.findIdx? (r.groupFitsSlot slots a'.slotOf breaks x.2 x.1.1 x.1.2) =
      a.groups.findIdx? (r.groupFitsSlot slots a.slotOf breaks x.2 x.1.1 x.1.2) := by
    rw [hs] at hfit ⊢
    exact findIdx?_of_values _ _ _ hfit
  have hguard : ((a'.slotOf[x.2]?).join.isSome || decide (budget ≤ a'.used)) =
      ((a.slotOf[x.2]?).join.isSome || decide (budget ≤ a.used)) := by rw [hs, hu]
  unfold PlanReq.assignStep
  rw [hguard, hfind]
  by_cases hG : ((a.slotOf[x.2]?).join.isSome || decide (budget ≤ a.used)) = true
  · rw [if_pos hG, if_pos hG]; exact ⟨hs, hu, hg⟩
  · rw [if_neg hG, if_neg hG]
    cases hf : a.groups.findIdx? (r.groupFitsSlot slots a.slotOf breaks x.2 x.1.1 x.1.2) with
    | none => exact ⟨hs, hu, hg⟩
    | some gi =>
      dsimp only
      cases h1 : a'.groups[gi]? with
      | none =>
        cases h2 : a.groups[gi]? with
        | none => exact ⟨hs, hu, hg⟩
        | some g => have := lt_of_getElem?_some h2; have := List.getElem?_eq_none_iff.1 h1; omega
      | some g' =>
        cases h2 : a.groups[gi]? with
        | none => have := lt_of_getElem?_some h1; have := List.getElem?_eq_none_iff.1 h2; omega
        | some g =>
          dsimp only
          have hv := congrArg (·[gi]?) hg
          simp only [List.getElem?_map, h1, h2, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at hv
          obtain ⟨hid, hp, hci, hloc, hsp, hm, hc, hsp2⟩ := hv
          refine ⟨by rw [hs], by rw [hu], ?_⟩
          rw [List.map_set, List.map_set, hg]
          congr 1
          simp only [Prod.mk.injEq]
          exact ⟨hid, hp, hci, hloc, hsp, hm, hc, by rw [hsp2]⟩

theorem foldl_assignStep_on_views (r : PlanReq) (slots : List Look.Slot) (breaks : List (Nat × Nat))
    (budget : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a a' : Assign),
      a'.slotOf = a.slotOf → a'.used = a.used →
      a'.groups.map (fun g => (g.ids, g.members.map (fun m => m.key.p), g.ci, g.loc, g.splittable,
        g.mult, g.commitMin, g.spent)) =
        a.groups.map (fun g => (g.ids, g.members.map (fun m => m.key.p), g.ci, g.loc, g.splittable,
          g.mult, g.commitMin, g.spent)) →
      (l.foldl (r.assignStep slots breaks budget) a').slotOf =
          (l.foldl (r.assignStep slots breaks budget) a).slotOf ∧
        (l.foldl (r.assignStep slots breaks budget) a').groups.map (fun g => (g.ids,
            g.members.map (fun m => m.key.p), g.ci, g.loc, g.splittable, g.mult, g.commitMin,
            g.spent)) =
          (l.foldl (r.assignStep slots breaks budget) a).groups.map (fun g => (g.ids,
            g.members.map (fun m => m.key.p), g.ci, g.loc, g.splittable, g.mult, g.commitMin,
            g.spent))
  | [], _, _, hs, _, hg => ⟨hs, hg⟩
  | x :: l, a, a', hs, hu, hg => by
    simp only [List.foldl_cons]
    obtain ⟨hs', hu', hg'⟩ := assignStep_on_views r slots breaks budget a a' x hs hu hg
    exact foldl_assignStep_on_views r slots breaks budget l _ _ hs' hu' hg'

/-- **Two group lists that agree as step 5 reads them draw the same rows.** -/
theorem rows_of_views (E : List (Fin 6 × Look.Slot)) (S : List (Option Nat)) (GA GB : List Group)
    (hv : GA.map (fun g => (g.ids, g.members.map (fun m => m.key.p), g.ci, g.loc, g.splittable,
        g.mult, g.commitMin, g.spent)) =
      GB.map (fun g => (g.ids, g.members.map (fun m => m.key.p), g.ci, g.loc, g.splittable,
        g.mult, g.commitMin, g.spent))) :
    (E.zip S).filterMap (fun p =>
      match p.2 with
      | Option.none => Option.none
      | some gi =>
        match GA[gi]? with
        | Option.none => Option.none
        | some g => some (assignedSeg p.1.1 p.1.2 g)) =
    (E.zip S).filterMap (fun p =>
      match p.2 with
      | Option.none => Option.none
      | some gi =>
        match GB[gi]? with
        | Option.none => Option.none
        | some g => some (assignedSeg p.1.1 p.1.2 g)) := by
  have hlen : GA.length = GB.length := by have := congrArg List.length hv; simpa using this
  congr 1
  funext p
  cases p.2 with
  | none => rfl
  | some gi =>
    simp only
    cases ha : GA[gi]? with
    | none =>
      cases hb : GB[gi]? with
      | none => rfl
      | some gB => have := lt_of_getElem?_some hb; have := List.getElem?_eq_none_iff.1 ha; omega
    | some gA =>
      cases hb : GB[gi]? with
      | none => have := lt_of_getElem?_some ha; have := List.getElem?_eq_none_iff.1 hb; omega
      | some gB =>
        have h := congrArg (·[gi]?) hv
        simp only [List.getElem?_map, ha, hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hid, hp, hci, -, -, hm, hc, -⟩ := h
        simp only
        rw [assignedSeg_congr p.1.1 p.1.2 gA gB hid hp hci hm hc]

/-- **The view step 5 reads of a group list, from its three parts** — each part is a list whose
equality `decide` can settle, which the eight-part view is not (instance search gives up on a list
of eight-fold products). -/
theorem views_of_three_parts :
    ∀ (l' l : List Group),
      l'.map (fun g => (g.ids, g.members.map (fun m => m.key.p))) =
        l.map (fun g => (g.ids, g.members.map (fun m => m.key.p))) →
      l'.map (fun g => (g.ci, g.loc, g.splittable)) = l.map (fun g => (g.ci, g.loc, g.splittable)) →
      l'.map (fun g => (g.mult, g.commitMin, g.spent)) = l.map (fun g => (g.mult, g.commitMin, g.spent)) →
      l'.map (fun g => (g.ids, g.members.map (fun m => m.key.p), g.ci, g.loc, g.splittable, g.mult,
        g.commitMin, g.spent)) =
        l.map (fun g => (g.ids, g.members.map (fun m => m.key.p), g.ci, g.loc, g.splittable, g.mult,
          g.commitMin, g.spent))
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | g' :: l', g :: l, h1, h2, h3 => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h1 h2 h3 ⊢
    exact ⟨⟨h1.1.1, h1.1.2, h2.1.1, h2.1.2.1, h2.1.2.2, h3.1.1, h3.1.2.1, h3.1.2.2⟩,
      views_of_three_parts l' l h1.2 h2.2 h3.2⟩

/-- A zipped entry's second half is an element of the second list. -/
theorem snd_mem_of_mem_zip {α β : Type} {l₁ : List α} {l₂ : List β} {p : α × β} (h : p ∈ l₁.zip l₂) :
    p.2 ∈ l₂ := (List.of_mem_zip (a := p.1) (b := p.2) h).2

/-- **L24 — §8.3's tail-drop — restated, and proved** (W-39, README gap 3549; D5, D29).  Two
requests that plan the SAME day — the same replayed past, the same reservation, the same energised
cut and breaks, the same groups, the same location and wind-down — and differ in how much of the
budget is left: the smaller budget's assigned items are a PREFIX of the larger's, in the day's own
row order.

The budget reaches the day only through §8.2 step 5's guard (`assignStep_below`), so the smaller
budget's walk is the larger's stopped after its first `k` slots (`foldl_assignStep_truncates`); its
rows are the larger walk's rows at those slots (`rows_ignore_spent`); and every row the larger walk
adds starts after every work row the smaller one keeps — after the replayed past (it ends at `now`),
after §8.2 choice 5b's reservation (step 3 cuts no slot on it) and after the slots before it (step
3 cuts them in time order) — so the day's stable sort leaves the kept rows first.

**The Active item needs no erasure in this order**, and D29's form is the corollary below
(`plan_tail_drop_with_the_active_item_erased`): the reservation sits at `now`, before every row the
budget can take away.  D29 was written about KEY order, where it is right that the result is not a
prefix; the Lean goal was always stated in `assignedOf`'s row order.

The goal as stage 6 wrote it left `run` and every other field but five free, and is refuted
(`PlannerWit.plan_tail_drop_as_stage_6_wrote_it_is_refuted_by_the_run_it_does_not_pin`, W-15, with
`PlannerWit.erasing_the_active_item_does_not_repair_a_law_whose_run_is_free`); this statement pins
the day by the views its rows are built from. -/
theorem plan_tail_drop (r r' : PlanReq)
    (hrep : replayedRows r' = replayedRows r) (hres : reservationSegs r' = reservationSegs r)
    (hes : r'.energisedSlots = r.energisedSlots) (hbr : r'.todayBreaks = r.todayBreaks)
    (hsg₁ : r'.startGroups.map (fun g => (g.ids, g.members.map (fun m => m.key.p))) =
      r.startGroups.map (fun g => (g.ids, g.members.map (fun m => m.key.p))))
    (hsg₂ : r'.startGroups.map (fun g => (g.ci, g.loc, g.splittable)) =
      r.startGroups.map (fun g => (g.ci, g.loc, g.splittable)))
    (hsg₃ : r'.startGroups.map (fun g => (g.mult, g.commitMin, g.spent)) =
      r.startGroups.map (fun g => (g.mult, g.commitMin, g.spent)))
    (hloc : r'.curLoc = r.curLoc) (hwd : r'.windDownSec = r.windDownSec)
    (hless : remainingBudget r' ≤ remainingBudget r) :
    ∃ n : Nat, assignedOf (dayPlan r') = (assignedOf (dayPlan r)).take n := by
  -- r' walks r's walk with the smaller budget, over groups step 5 cannot tell apart
  have hsl : r'.todaySlots = r.todaySlots := by
    rw [← todaySlots_of_energisedSlots, hes, todaySlots_of_energisedSlots]
  have hseed : r'.activeSeed = r.activeSeed := by
    rw [activeSeed_is_the_reservation, hres, activeSeed_is_the_reservation]
  have hgfs : r'.groupFitsSlot = r.groupFitsSlot := by
    funext slots slotOf breaks i e s g
    unfold PlanReq.groupFitsSlot; rw [hloc, hwd]
  have hstep : r'.assignStep = r.assignStep := by
    funext slots breaks budget a x
    unfold PlanReq.assignStep; rw [hgfs]
  have hA0 := foldl_assignStep_on_views r r.todaySlots r.todayBreaks (remainingBudget r')
    r.energisedSlots.zipIdx r.assignStart r'.assignStart
    (by unfold PlanReq.assignStart; rw [hsl]) (by unfold PlanReq.assignStart; exact hseed)
    (by unfold PlanReq.assignStart; exact views_of_three_parts _ _ hsg₁ hsg₂ hsg₃)
  have hfold' : r'.assignFold = r.energisedSlots.zipIdx.foldl
      (r.assignStep r.todaySlots r.todayBreaks (remainingBudget r')) r'.assignStart := by
    unfold PlanReq.assignFold
    rw [hstep, hsl, hbr, hes]
  rw [← hfold'] at hA0
  obtain ⟨k, hk⟩ := foldl_assignStep_truncates r r.todaySlots r.todayBreaks hless
    r.energisedSlots.zipIdx r.assignStart
  rw [hk] at hA0
  generalize hAdef : (r.energisedSlots.zipIdx.take k).foldl
    (r.assignStep r.todaySlots r.todayBreaks (remainingBudget r)) r.assignStart = A at hA0
  obtain ⟨hAs, hAg⟩ := hA0
  have hB : r.assignFold = (r.energisedSlots.zipIdx.drop k).foldl
      (r.assignStep r.todaySlots r.todayBreaks (remainingBudget r)) A := by
    rw [← hAdef]; unfold PlanReq.assignFold; rw [← List.foldl_append, List.take_append_drop]
  -- where each half of the walk writes
  have hZk : ∀ y ∈ r.energisedSlots.zipIdx.take k, y.2 < k := by
    intro y hy
    obtain ⟨j, hj, hyj⟩ := List.mem_take_iff_getElem.1 hy
    have hj' : j < r.energisedSlots.zipIdx.length := Nat.lt_of_lt_of_le hj (Nat.min_le_right _ _)
    have := zipIdx_index r.energisedSlots j y (by rw [List.getElem?_eq_getElem hj', hyj])
    have : j < k := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
    omega
  have hZd : ∀ y ∈ r.energisedSlots.zipIdx.drop k, k ≤ y.2 := by
    intro y hy
    obtain ⟨j, hj, hyj⟩ := List.mem_drop_iff_getElem.1 hy
    have := zipIdx_index r.energisedSlots (k + j) y
      (by rw [List.getElem?_eq_getElem (by omega : k + j < r.energisedSlots.zipIdx.length), hyj])
    omega
  have hlt : ∀ j, j < k → r.assignFold.slotOf[j]? = A.slotOf[j]? := by
    intro j hj
    rw [hB]
    exact foldl_assignStep_slotOf_ne r _ _ _ _ _ j (fun y hy hyj => by have := hZd y hy; omega)
  have hge : ∀ j, k ≤ j → A.slotOf[j]? = r.assignStart.slotOf[j]? := by
    intro j hj
    rw [← hAdef]
    exact foldl_assignStep_slotOf_ne r _ _ _ _ _ j (fun y hy hyj => by have := hZk y hy; omega)
  -- the two walks' groups differ only in `spent`
  have hgroups : ∀ (n : Nat) (gA gB : Group), A.groups[n]? = some gA →
      r.assignFold.groups[n]? = some gB →
      ∃ g0 : Group, gA = { g0 with spent := gA.spent } ∧ gB = { g0 with spent := gB.spent } := by
    intro n gA gB ha hb
    rw [← hAdef] at ha
    obtain ⟨g0, h0, e0⟩ := foldl_assignStep_group_is_the_group_with_its_spent r _ _ _ _ _ n gA ha
    unfold PlanReq.assignFold at hb
    obtain ⟨g1, h1, e1⟩ := foldl_assignStep_group_is_the_group_with_its_spent r _ _ _ _ _ n gB hb
    rw [h0] at h1
    cases h1
    exact ⟨g0, e0, e1⟩
  have hglen : A.groups.length = r.assignFold.groups.length := by
    rw [← hAdef]
    unfold PlanReq.assignFold
    rw [(foldl_assignStep_lengths r _ _ _ _ _).2, (foldl_assignStep_lengths r _ _ _ _ _).2]
  -- step 5's rows: r's first `k` slots are r''s, and r' has nothing after them
  have htake : A.slotOf.take k = r.assignFold.slotOf.take k := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take, List.getElem?_take]
    split
    · rename_i hj; exact (hlt j hj).symm
    · rfl
  have hrows' : r'.assignedRows = ((r.energisedSlots.zip r.assignFold.slotOf).take k).filterMap
      (fun p => match p.2 with
        | Option.none => Option.none
        | some gi => match r.assignFold.groups[gi]? with
          | Option.none => Option.none
          | some g => some (assignedSeg p.1.1 p.1.2 g)) := by
    rw [assignedRows_of_assignFold, hes, hAs, rows_of_views _ _ _ _ hAg,
      rows_ignore_spent _ _ _ _ hglen hgroups,
      ← List.take_append_drop k (r.energisedSlots.zip A.slotOf), List.filterMap_append]
    have hnil : ((r.energisedSlots.zip A.slotOf).drop k).filterMap (fun p =>
        match p.2 with
        | Option.none => Option.none
        | some gi => match r.assignFold.groups[gi]? with
          | Option.none => Option.none
          | some g => some (assignedSeg p.1.1 p.1.2 g)) = [] := by
      refine List.filterMap_eq_nil_iff.2 (fun p hp => ?_)
      rw [drop_zip] at hp
      have hp2 := snd_mem_of_mem_zip hp
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hp2
      rw [List.getElem?_drop, hge (k + i) (Nat.le_add_right _ _)] at hi
      unfold PlanReq.assignStart at hi
      rw [List.getElem?_replicate] at hi
      split at hi
      · simp only [Option.some.injEq] at hi
        rw [← hi]
      · exact absurd hi (by simp)
    rw [hnil, List.append_nil, List.zip_eq_zipWith, List.zip_eq_zipWith, List.take_zipWith,
      List.take_zipWith, htake]
  have hrows : r.assignedRows = ((r.energisedSlots.zip r.assignFold.slotOf).take k).filterMap
      (fun p => match p.2 with
        | Option.none => Option.none
        | some gi => match r.assignFold.groups[gi]? with
          | Option.none => Option.none
          | some g => some (assignedSeg p.1.1 p.1.2 g)) ++
      ((r.energisedSlots.zip r.assignFold.slotOf).drop k).filterMap
      (fun p => match p.2 with
        | Option.none => Option.none
        | some gi => match r.assignFold.groups[gi]? with
          | Option.none => Option.none
          | some g => some (assignedSeg p.1.1 p.1.2 g)) := by
    rw [assignedRows_of_assignFold, ← List.filterMap_append, List.take_append_drop]
  -- a row of the drop half starts at a slot at index `k` or later, and one of the take half before
  have hdrop_start : ∀ m ∈ ((r.energisedSlots.zip r.assignFold.slotOf).drop k).filterMap
      (fun p => match p.2 with
        | Option.none => Option.none
        | some gi => match r.assignFold.groups[gi]? with
          | Option.none => Option.none
          | some g => some (assignedSeg p.1.1 p.1.2 g)),
      ∃ (j : Nat) (e : Fin 6) (s : Look.Slot), k ≤ j ∧ r.energisedSlots[j]? = some (e, s) ∧
        m.start = s.start ∧ m ∈ r.assignedRows := by
    intro m hm
    obtain ⟨p, hp, hpm⟩ := List.mem_filterMap.1 hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hp
    rw [List.getElem?_drop] at hi
    obtain ⟨h1, -⟩ := List.getElem?_zip_eq_some.1 hi
    have hmr : m ∈ r.assignedRows := by rw [hrows]; exact List.mem_append_right _ hm
    cases hp2 : p.2 with
    | none => rw [hp2] at hpm; exact absurd hpm (by simp)
    | some gi =>
      rw [hp2] at hpm
      simp only at hpm
      cases hg : r.assignFold.groups[gi]? with
      | none => rw [hg] at hpm; exact absurd hpm (by simp)
      | some g =>
        rw [hg] at hpm
        simp only [Option.some.injEq] at hpm
        exact ⟨k + i, p.1.1, p.1.2, Nat.le_add_right _ _, h1, by rw [← hpm]; rfl, hmr⟩
  have htake_start : ∀ l ∈ ((r.energisedSlots.zip r.assignFold.slotOf).take k).filterMap
      (fun p => match p.2 with
        | Option.none => Option.none
        | some gi => match r.assignFold.groups[gi]? with
          | Option.none => Option.none
          | some g => some (assignedSeg p.1.1 p.1.2 g)),
      ∃ (i : Nat) (e : Fin 6) (s : Look.Slot), i < k ∧ r.energisedSlots[i]? = some (e, s) ∧
        l.start = s.start := by
    intro l hl
    obtain ⟨p, hp, hpl⟩ := List.mem_filterMap.1 hl
    obtain ⟨i, hi, hpi⟩ := List.mem_take_iff_getElem.1 hp
    have hik : i < k := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have hil : i < (r.energisedSlots.zip r.assignFold.slotOf).length :=
      Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
    have hget : (r.energisedSlots.zip r.assignFold.slotOf)[i]? = some p := by
      rw [List.getElem?_eq_getElem hil, hpi]
    obtain ⟨h1, -⟩ := List.getElem?_zip_eq_some.1 hget
    cases hp2 : p.2 with
    | none => rw [hp2] at hpl; exact absurd hpl (by simp)
    | some gi =>
      rw [hp2] at hpl
      simp only at hpl
      cases hg : r.assignFold.groups[gi]? with
      | none => rw [hg] at hpl; exact absurd hpl (by simp)
      | some g =>
        rw [hg] at hpl
        simp only [Option.some.injEq] at hpl
        exact ⟨i, p.1.1, p.1.2, hik, h1, by rw [← hpl]; rfl⟩
  -- every row the larger budget adds follows every work row the smaller one keeps
  have hord : ∀ l ∈ ((replayedRows r).map Planner.segOf).filter (fun s => s.val.kind.isWork) ++
        (reservationSegs r).map Planner.segOf ++
        (((r.energisedSlots.zip r.assignFold.slotOf).take k).filterMap
          (fun p => match p.2 with
            | Option.none => Option.none
            | some gi => match r.assignFold.groups[gi]? with
              | Option.none => Option.none
              | some g => some (assignedSeg p.1.1 p.1.2 g))).map Planner.segOf,
      ∀ m ∈ (((r.energisedSlots.zip r.assignFold.slotOf).drop k).filterMap
          (fun p => match p.2 with
            | Option.none => Option.none
            | some gi => match r.assignFold.groups[gi]? with
              | Option.none => Option.none
              | some g => some (assignedSeg p.1.1 p.1.2 g))).map Planner.segOf,
      rowLe l m = true := by
    intro l hl m hm
    obtain ⟨mt, hmt, rfl⟩ := List.mem_map.1 hm
    obtain ⟨j, e, s, hkj, hjs, hms, hmr⟩ := hdrop_start mt hmt
    have hnow := r.an_assigned_row_starts_at_or_after_now mt hmr
    rcases List.mem_append.1 hl with hl | hl
    · rcases List.mem_append.1 hl with hl | hl
      · obtain ⟨lt, hlt, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hl).1
        obtain ⟨-, h2, h3⟩ := replayedRows_end_at_now r lt hlt
        exact rowLe_of_start_lt lt mt (by omega)
      · obtain ⟨lt, hlt, rfl⟩ := List.mem_map.1 hl
        obtain ⟨q, hq, hst, -, -, -, -, -⟩ := r.mem_activeRow lt hlt
        obtain ⟨-, -, -, -, hs0, hlt0, -⟩ := r.activeRun_spec q hq
        have hsl' : s ∈ r.todaySlots := r.energised_slot_is_a_slot (List.mem_of_getElem? hjs)
        have hne := r.a_slot_is_not_empty s hsl'
        have hfree := r.no_slot_touches_the_running_block q hq s hsl' (t := s.start)
          (Nat.le_refl _) hne
        apply rowLe_of_start_lt
        rw [hst, hms]
        omega
    · obtain ⟨lt, hlt, rfl⟩ := List.mem_map.1 hl
      obtain ⟨i, e', s', hik, his, hls⟩ := htake_start lt hlt
      exact rowLe_of_start_lt lt mt
        (by rw [hls, hms]; exact energised_start_lt r (by omega) his hjs)
  -- the day's work rows: the kept ones sorted, then the added ones
  have hwork := work_rows_of_the_day r
  have hwork' := work_rows_of_the_day r'
  rw [hrep, hres, hrows'] at hwork'
  rw [hrows, List.map_append, ← List.append_assoc] at hwork
  unfold sortRows at hwork hwork'
  rw [insSort_append_after rowLe _ _ hord] at hwork
  refine ⟨((Replay.insSort rowLe (((replayedRows r).map Planner.segOf).filter
      (fun s => s.val.kind.isWork) ++ (reservationSegs r).map Planner.segOf ++
      (((r.energisedSlots.zip r.assignFold.slotOf).take k).filterMap
        (fun p => match p.2 with
          | Option.none => Option.none
          | some gi => match r.assignFold.groups[gi]? with
            | Option.none => Option.none
            | some g => some (assignedSeg p.1.1 p.1.2 g))).map Planner.segOf)).flatMap
      segItems).length, ?_⟩
  show ((dayPlan r').segments.filter (fun s => s.val.kind.isWork)).flatMap segItems =
    (((dayPlan r).segments.filter (fun s => s.val.kind.isWork)).flatMap segItems).take _
  rw [dayPlan_segments, dayPlan_segments, hwork', hwork, List.flatMap_append, List.take_left]

/-- **D29's form, as the corollary it is**: erasing the Active item from both sides keeps a prefix a
prefix. -/
theorem take_erase_is_a_prefix_of_erase {α : Type} [BEq α] [LawfulBEq α] (a : α) :
    ∀ (L : List α) (n : Nat), ∃ m, (L.take n).erase a = (L.erase a).take m
  | [], n => ⟨0, by simp⟩
  | x :: L, 0 => ⟨0, by simp⟩
  | x :: L, n + 1 => by
    simp only [List.take_succ_cons, List.erase_cons]
    by_cases hx : (x == a) = true
    · rw [if_pos hx, if_pos hx]; exact ⟨n, rfl⟩
    · rw [if_neg hx, if_neg hx]
      obtain ⟨m, hm⟩ := take_erase_is_a_prefix_of_erase a L n
      exact ⟨m + 1, by rw [hm, List.take_succ_cons]⟩

/-- **D29's statement of L24, proved** — `plan_tail_drop` with the Active item erased from both
sides, which the owner's D29 wrote; it follows from the unerased form. -/
theorem plan_tail_drop_with_the_active_item_erased (r r' : PlanReq)
    (hrep : replayedRows r' = replayedRows r) (hres : reservationSegs r' = reservationSegs r)
    (hes : r'.energisedSlots = r.energisedSlots) (hbr : r'.todayBreaks = r.todayBreaks)
    (hsg₁ : r'.startGroups.map (fun g => (g.ids, g.members.map (fun m => m.key.p))) =
      r.startGroups.map (fun g => (g.ids, g.members.map (fun m => m.key.p))))
    (hsg₂ : r'.startGroups.map (fun g => (g.ci, g.loc, g.splittable)) =
      r.startGroups.map (fun g => (g.ci, g.loc, g.splittable)))
    (hsg₃ : r'.startGroups.map (fun g => (g.mult, g.commitMin, g.spent)) =
      r.startGroups.map (fun g => (g.mult, g.commitMin, g.spent)))
    (hloc : r'.curLoc = r.curLoc) (hwd : r'.windDownSec = r.windDownSec)
    (hless : remainingBudget r' ≤ remainingBudget r) (a : Id) :
    ∃ n : Nat, (assignedOf (dayPlan r')).erase a = ((assignedOf (dayPlan r)).erase a).take n := by
  obtain ⟨n, hn⟩ := plan_tail_drop r r' hrep hres hes hbr hsg₁ hsg₂ hsg₃ hloc hwd hless
  rw [hn]
  exact take_erase_is_a_prefix_of_erase a _ n


/-! ## W-39 (L25): a replan leaves what ended before `now` where it was -/

/-! The invariant a longer clip keeps over a shorter one, cut by cut: every piece ending before the
shorter clip's end is a piece of the longer, and every piece ending AT it has a piece of the longer
that starts where it does and ends no earlier (written out at each use rather than named: this
module declares theorems only). -/

theorem a_longer_clip_keeps_its_pieces_through_a_cut (b : Nat) (s : Nat × Nat) (ps ps' : List (Nat × Nat))
    (h : ((∀ q ∈ ps, q.1 < q.2 ∧ q.2 ≤ b) ∧ (∀ q ∈ ps, q.2 < b → q ∈ ps') ∧
      (∀ q ∈ ps, q.2 = b → ∃ q' ∈ ps', q'.1 = q.1 ∧ b ≤ q'.2))) :
    ((∀ q ∈ ps.flatMap (cutOne s), q.1 < q.2 ∧ q.2 ≤ b) ∧ (∀ q ∈ ps.flatMap (cutOne s), q.2 < b → q ∈ ps'.flatMap (cutOne s)) ∧
      (∀ q ∈ ps.flatMap (cutOne s), q.2 = b → ∃ q' ∈ ps'.flatMap (cutOne s), q'.1 = q.1 ∧ b ≤ q'.2)) := by
  obtain ⟨hwin, hlt, heq⟩ := h
  refine ⟨fun q hq => ?_, fun q hq hqb => ?_, fun q hq hqb => ?_⟩
  · obtain ⟨p, hp, hqp⟩ := List.mem_flatMap.1 hq
    have h1 := cutOne_sub hqp
    have h2 := cutOne_nonempty (hwin p hp).1 hqp
    have := (hwin p hp).2
    exact ⟨h2, by omega⟩
  · obtain ⟨p, hp, hqp⟩ := List.mem_flatMap.1 hq
    have hsub := cutOne_sub hqp
    by_cases hpb : p.2 < b
    · exact List.mem_flatMap.2 ⟨p, hlt p hp hpb, hqp⟩
    · have hpb' : p.2 = b := by have := (hwin p hp).2; omega
      obtain ⟨p', hp', h1, h2⟩ := heq p hp hpb'
      refine List.mem_flatMap.2 ⟨p', hp', ?_⟩
      -- q is the part of p before s; it is the part of p' before s too
      unfold cutOne at hqp ⊢
      by_cases hs : s.2 ≤ s.1
      · rw [if_pos hs] at hqp ⊢
        simp only [List.mem_singleton] at hqp
        subst hqp
        omega
      · rw [if_neg hs] at hqp ⊢
        simp only [List.mem_append] at hqp ⊢
        rcases hqp with hq1 | hq2
        · left
          split at hq1
          · simp only [List.mem_singleton] at hq1
            subst hq1
            rw [if_pos (by simp only at hqb; omega)]
            simp only [List.mem_singleton, Prod.mk.injEq]
            simp only at hqb
            omega
          · simp at hq1
        · exfalso
          split at hq2
          · simp only [List.mem_singleton] at hq2
            subst hq2
            simp only at hqb
            omega
          · simp at hq2
  · obtain ⟨p, hp, hqp⟩ := List.mem_flatMap.1 hq
    have hsub := cutOne_sub hqp
    have hpb' : p.2 = b := by have := (hwin p hp).2; omega
    have hpn := (hwin p hp).1
    obtain ⟨p', hp', h1, h2⟩ := heq p hp hpb'
    unfold cutOne at hqp
    by_cases hs : s.2 ≤ s.1
    · rw [if_pos hs] at hqp
      simp only [List.mem_singleton] at hqp
      subst hqp
      exact ⟨p', List.mem_flatMap.2 ⟨p', hp', by unfold cutOne; rw [if_pos hs]; simp⟩, h1, h2⟩
    · rw [if_neg hs] at hqp
      simp only [List.mem_append] at hqp
      rcases hqp with hq1 | hq2
      · split at hq1
        · simp only [List.mem_singleton] at hq1
          subst hq1
          simp only at hqb
          -- `min p.2 s.1 = b`, so `s.1 ≥ b`: the part of p' before s starts at p.1 and ends at b or later
          refine ⟨(p'.1, min p'.2 s.1), List.mem_flatMap.2 ⟨p', hp', ?_⟩, by simp only; omega,
            by simp only; omega⟩
          unfold cutOne
          rw [if_neg hs]
          simp only [List.mem_append]
          left
          rw [if_pos (by omega)]
          simp
        · simp at hq1
      · split at hq2
        · simp only [List.mem_singleton] at hq2
          subst hq2
          simp only at hqb
          refine ⟨(max p'.1 s.2, p'.2), List.mem_flatMap.2 ⟨p', hp', ?_⟩, by simp only; omega,
            by simp only; omega⟩
          unfold cutOne
          rw [if_neg hs]
          simp only [List.mem_append]
          right
          rw [if_pos (by omega)]
          simp
        · simp at hq2

theorem a_longer_clip_keeps_its_pieces_through_the_cuts (b : Nat) :
    ∀ (ss : List (Nat × Nat)) (ps ps' : List (Nat × Nat)), ((∀ q ∈ ps, q.1 < q.2 ∧ q.2 ≤ b) ∧ (∀ q ∈ ps, q.2 < b → q ∈ ps') ∧
      (∀ q ∈ ps, q.2 = b → ∃ q' ∈ ps', q'.1 = q.1 ∧ b ≤ q'.2)) →
      ((∀ q ∈ cutAll ss ps, q.1 < q.2 ∧ q.2 ≤ b) ∧ (∀ q ∈ cutAll ss ps, q.2 < b → q ∈ cutAll ss ps') ∧
      (∀ q ∈ cutAll ss ps, q.2 = b → ∃ q' ∈ cutAll ss ps', q'.1 = q.1 ∧ b ≤ q'.2))
  | [], _, _, h => h
  | s :: ss, ps, ps', h => a_longer_clip_keeps_its_pieces_through_the_cuts b ss _ _
      (a_longer_clip_keeps_its_pieces_through_a_cut b s ps ps' h)

/-- **A piece of a clip that ends before the clip does is a piece of any longer clip from the same
start** — the walls cut both the same way below the shorter end. -/
theorem clipCut_keeps_an_early_piece {a b b' : Nat} {ss : List (Nat × Nat)} {q : Nat × Nat}
    (hbb : b ≤ b') (hq : q ∈ clipCut a b ss) (hqb : q.2 < b) : q ∈ clipCut a b' ss := by
  unfold clipCut at hq ⊢
  by_cases hab : b ≤ a
  · rw [if_pos hab] at hq; simp at hq
  · rw [if_neg hab] at hq
    rw [if_neg (by omega)]
    have h0 : ((∀ q ∈ [(a, b)], q.1 < q.2 ∧ q.2 ≤ b) ∧ (∀ q ∈ [(a, b)], q.2 < b → q ∈ [(a, b')]) ∧
      (∀ q ∈ [(a, b)], q.2 = b → ∃ q' ∈ [(a, b')], q'.1 = q.1 ∧ b ≤ q'.2)) := by
      refine ⟨fun q hq => ?_, fun q hq hqb => ?_, fun q hq hqb => ?_⟩
      · simp only [List.mem_singleton] at hq; subst hq; simp only; omega
      · simp only [List.mem_singleton] at hq; subst hq; simp only at hqb; omega
      · simp only [List.mem_singleton] at hq; subst hq
        exact ⟨(a, b'), List.mem_singleton_self _, rfl, by simp only; omega⟩
    exact (a_longer_clip_keeps_its_pieces_through_the_cuts b ss _ _ h0).2.1 q hq hqb

/-- **A replayed row that ended before `now` is replayed the same by a later replan of the same log
and day** — its clip to `[day_start, now]` is cut by the same walls, and a longer clip keeps every
piece that ended before the shorter one did (`clipCut_keeps_an_early_piece`). -/
theorem a_past_row_ended_before_now_is_a_past_row_later (r r' : PlanReq)
    (htr : r'.todayRecord = r.todayRecord) (hday : r'.dayStart = r.dayStart)
    (hwalls : wallsToday r' = wallsToday r) (hlater : r.now.sec ≤ r'.now.sec)
    (t : Seg) (ht : t ∈ pastRows r) (hend : t.stop < r.now.sec) : t ∈ pastRows r' := by
  obtain ⟨d, hd, g, hg, q, hq, rfl⟩ := mem_pastRows.1 ht
  refine mem_pastRows.2 ⟨d, by rw [htr, hd], g, hg, q, ?_, rfl⟩
  have hws : wallSpans r' = wallSpans r := by unfold wallSpans; rw [hwalls]
  have hq2 : q.2 < r.now.sec := hend
  unfold pastSpans at hq ⊢
  rw [hday, hws]
  by_cases hgs : g.stop.1.sec ≤ r.now.sec
  · rw [Nat.min_eq_left hgs] at hq
    rw [Nat.min_eq_left (by omega : g.stop.1.sec ≤ r'.now.sec)]
    exact hq
  · rw [Nat.min_eq_right (by omega : r.now.sec ≤ g.stop.1.sec)] at hq
    exact clipCut_keeps_an_early_piece
      (by omega : r.now.sec ≤ min g.stop.1.sec r'.now.sec) hq hq2

/-- **Every slot of the cut starts at or after `now`** — the cut runs from `max(now, window start)`,
and when the window has closed before `now` it cuts nothing. -/
theorem a_slot_starts_at_or_after_now (r : PlanReq) (s : Look.Slot) (h : s ∈ r.todaySlots) :
    r.now.sec ≤ s.start := by
  obtain ⟨h1, h2, h3⟩ := r.a_slot_is_inside_the_window s h
  unfold PlanReq.cutFrom at h1
  omega

/-- **A row of the day that the log did not replay and the calendar did not wall starts at or after
`now`**: a routine step 2 or 6 placed, the evening, §8.2 choice 5b's reservation, a row of step 5,
a kept break, an optional or a Rest row. -/
theorem a_planned_row_starts_at_or_after_now (r : PlanReq) (t : Seg)
    (ht : t ∈ dayRoutineSegs r ++ reservationSegs r ++ r.assignedRows ++ r.keptBreakRows ++
      r.optionalRows ++ r.restRows) : r.now.sec ≤ t.start := by
  simp only [List.mem_append] at ht
  rcases ht with (((((ht | ht) | ht) | ht) | ht) | ht)
  · unfold dayRoutineSegs routineRows at ht
    rcases List.mem_append.1 ht with ht | ht
    · obtain ⟨q, hq, htq⟩ := List.mem_flatMap.1 ht
      obtain ⟨a, b, hab, hst, -, -, -⟩ := a_routine_row_is_where_the_placement_put_it r q t htq
      have := (a_deferred_routine_is_inside_its_window r q hq a b hab).1
      omega
    · unfold PlanReq.eveningRows at ht
      rcases List.mem_append.1 ht with ht | ht
      · split at ht
        · rename_i hc
          simp only [List.mem_singleton] at ht
          subst ht
          show r.now.sec ≤ r.windDownSec
          omega
        · simp at ht
      · split at ht
        · rename_i hc
          simp only [List.mem_singleton] at ht
          subst ht
          show r.now.sec ≤ min (max r.bedSec r.now.sec) r.dayEnd
          omega
        · simp at ht
  · exact Nat.le_of_eq (r.activeRow_is_an_energyless_block t ht).2.2.2.2.symm
  · exact r.an_assigned_row_starts_at_or_after_now t ht
  · obtain ⟨b, hb, hst, -⟩ := r.mem_keptBreakRows t ht
    rw [hst]; exact (r.a_kept_break_is_after_now b hb).1
  · unfold PlanReq.optionalRows at ht
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 ht
    have := (an_optional_is_placed_in_the_free_day_before_the_wind_down r o ho).1
    show r.now.sec ≤ o.start
    omega
  · obtain ⟨e, sl, hsl, h1, -⟩ := a_rest_row_is_a_piece_of_an_unfilled_slot r t ht
    have := a_slot_starts_at_or_after_now r sl (r.energised_slot_is_a_slot hsl)
    omega

/-- **L25 — §8.3's stability — restated, and proved** (W-39, README gap 3550; D5).  A replan of the
same log's day, at the same walls and the same plan, later: every row of the earlier day that
ENDED BEFORE `now` and is not open is a row of the later day.

**Why strictly before `now`, and why not open.**  Every row the planner places starts at or after
`now` (`a_planned_row_starts_at_or_after_now`), so what ends before `now` is the log's and the
calendar's; of those, the rows that end AT `now` are the ones that grow — the running interruption,
the log's open block, a running break, and a replayed segment the clip cut at `now` — and the log's
open block can stop before `now`, at what paused it, while its `so far` note grows: it is marked
`open`.  A closed replayed row is clipped by the same walls to the same end
(`a_past_row_ended_before_now_is_a_past_row_later`), and a wall row is the calendar's.

The goal as stage 6 wrote it pinned `plan`, `window`, `blockMin` and the budget and left the run free,
and is refuted (`PlannerWit.plan_is_stable_across_a_replan_as_stage_6_wrote_it_is_refuted_by_the_run_it_does_not_pin`,
W-25), as is design §6.3 row 3's own restatement
(`PlannerWit.the_designs_restatement_of_the_stability_law_is_refuted_too`); this statement pins the
day by the views the past half is built from, and `hcal` is the R10 bound on the rows' clock. -/
theorem plan_is_stable_across_a_replan (r r' : PlanReq)
    (htr : r'.todayRecord = r.todayRecord) (hday : r'.dayStart = r.dayStart)
    (hwalls : wallsToday r' = wallsToday r) (htravel : ∀ i, r'.isTravelDay i = r.isTravelDay i)
    (hlater : r.now.sec ≤ r'.now.sec) (hcal : r.now.sec < LogStamp.yearEnd)
    (s : WfSeg) (hs : s ∈ (dayPlan r).segments) (hend : s.val.stop < r.now.sec)
    (hopen : s.val.flags.isOpen = false) : s ∈ (dayPlan r').segments := by
  obtain ⟨t, ht, rfl⟩ := mem_dayRows (dayPlan_segments r ▸ hs)
  have hstop : (Planner.segOf t).val.stop = max (clampSec t.start) (clampSec t.stop) := rfl
  have hlate : ∀ u : Nat, r.now.sec ≤ u → r.now.sec ≤ max (clampSec u) (clampSec t.stop) := by
    intro u hu; unfold clampSec; omega
  rw [dayPlan_segments]
  have hmem : t ∈ stepOneSegs r ∨
      t ∈ dayRoutineSegs r ++ reservationSegs r ++ r.assignedRows ++ r.keptBreakRows ++
        r.optionalRows ++ r.restRows := by
    simp only [List.mem_append] at ht ⊢
    rcases ht with ((((((ht | ht) | ht) | ht) | ht) | ht) | ht)
    · exact Or.inl ht
    all_goals simp_all
  rcases hmem with ht | ht
  · unfold stepOneSegs at ht
    simp only [List.mem_append] at ht
    rcases ht with ((ht | ht) | ht) | ht
    · rcases mem_replayedRows.1 ht with hp | ho
      · have htend : t.stop < r.now.sec := by
          have := (pastRows_end_at_now r t hp).2.2
          rw [hstop] at hend
          unfold clampSec at hend
          omega
        have hp' := a_past_row_ended_before_now_is_a_past_row_later r r' htr hday hwalls hlater t hp
          htend
        exact mem_dayRows_of_mem (by simp [stepOneSegs, replayedRows, hp'])
      · exfalso
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfl, -⟩ := mem_openBlockRows ho
        have : (Planner.segOf t).val.flags = t.flags := rfl
        rw [this, hfl] at hopen
        exact absurd hopen (by simp)
    · exfalso
      have := (interruptRows_are_open_lost_time r t ht).2.2
      rw [hstop] at hend
      unfold clampSec at hend
      omega
    · exfalso
      have := (breakRows_are_running_breaks r t ht).2.1
      rw [hstop] at hend
      unfold clampSec at hend
      omega
    · have hw' : t ∈ (wallsToday r').flatMap (fun x => wallRows (r'.isTravelDay x.id) x) := by
        rw [hwalls]
        obtain ⟨x, hx, htx⟩ := List.mem_flatMap.1 ht
        exact List.mem_flatMap.2 ⟨x, hx, by rw [htravel]; exact htx⟩
      exact mem_dayRows_of_mem (by simp [stepOneSegs, hw'])
  · exfalso
    have := a_planned_row_starts_at_or_after_now r t ht
    rw [hstop] at hend
    have := hlate t.start this
    omega

end PlanFold
end Tm
