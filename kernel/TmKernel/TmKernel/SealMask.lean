import TmKernel.SealMaskAux
/-!
# SealMask — the mask splits at the cut under G1 (stage 5, D9, W2)

The survivors of a whole log are the checkpoint's folded survivors followed by the survivors of the tail with its settled
undos set aside (`survivors_append_of_g1`), whenever G1 accepts the tail: a settled undo cancels a folded line or
nothing, every other undo of the remainder cancels a line of the remainder, and an undo appended since that dangles in
the tail has a tag no folded survivor carries.  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (maskStep «matches» survivors danglingOf dangleStep)
open Log (Entry)

/-- The survivor stack of a list, most recent first. -/
def stackOf (xs : List Entry) : List Entry := xs.foldl maskStep []

theorem stackOf_append (xs ys : List Entry) : stackOf (xs ++ ys) = ys.foldl maskStep (stackOf xs) := by
  unfold stackOf; rw [List.foldl_append]

theorem settledStep_fst (es : List Entry) : ∀ (xs : List Entry) (acc : List Entry × List Nat),
    (xs.foldl (settledStep es) acc).1 = xs.foldl maskStep acc.1
  | [], _ => rfl
  | x :: xs, acc => by
    rw [List.foldl_cons, List.foldl_cons, settledStep_fst es xs]
    congr 1
    unfold settledStep maskStep
    cases x.ev <;> rfl

/-! ### The stack's shape: the new lines on top, the folded below -/

def Split (A : List Entry) (st : List Entry) : Prop :=
  ∃ U V, st = U ++ V ∧ (∀ u ∈ U, A.contains u = false) ∧ (∀ v ∈ V, A.contains v = true)

theorem Split.push {A st : List Entry} (h : Split A st) (e : Entry) (he : A.contains e = false) : Split A (e :: st) := by
  obtain ⟨U, V, rfl, hU, hV⟩ := h
  exact ⟨e :: U, V, rfl, fun u hu => by rcases List.mem_cons.1 hu with rfl | hu; exact he; exact hU u hu, hV⟩

theorem Split.eraseP {A st : List Entry} (h : Split A st) (p : Entry → Bool) : Split A (st.eraseP p) := by
  obtain ⟨U, V, rfl, hU, hV⟩ := h
  rw [List.eraseP_append]
  split
  · exact ⟨U.eraseP p, V, rfl, fun u hu => hU u (List.mem_of_mem_eraseP hu), hV⟩
  · exact ⟨U, V.eraseP p, rfl, hU, fun v hv => hV v (List.mem_of_mem_eraseP hv)⟩

theorem Split.foldl {A : List Entry} : ∀ (X st : List Entry), Split A st → (∀ x ∈ X, A.contains x = false) →
    Split A (X.foldl maskStep st)
  | [], _, h, _ => h
  | e :: X, st, h, hX => by
    rw [List.foldl_cons]
    apply Split.foldl X _ _ (fun x hx => hX x (List.mem_cons_of_mem _ hx))
    unfold maskStep
    cases e.ev with
    | undo of_ id => exact h.eraseP _
    | _ => exact h.push e (hX e List.mem_cons_self)

theorem Split.eq {A st : List Entry} (h : Split A st) :
    st = st.filter (fun x => !A.contains x) ++ st.filter (fun x => A.contains x) := by
  obtain ⟨U, V, rfl, hU, hV⟩ := h
  have h1 : U.filter (fun x => !A.contains x) = U := List.filter_eq_self.2 (fun u hu => by rw [hU u hu]; rfl)
  have h2 : V.filter (fun x => !A.contains x) = [] := List.filter_eq_nil_iff.2 (fun v hv => by rw [hV v hv]; simp)
  have h3 : U.filter (fun x => A.contains x) = [] := List.filter_eq_nil_iff.2 (fun u hu => by rw [hU u hu]; simp)
  have h4 : V.filter (fun x => A.contains x) = V := List.filter_eq_self.2 (fun v hv => hV v hv)
  rw [List.filter_append, List.filter_append, h1, h2, h3, h4]; simp

/-! ### Part 1: over the remainder the checkpoint knew -/

theorem eraseP_eq_self_of_find?_none {α : Type} (p : α → Bool) (l : List α) (h : l.find? p = none) : l.eraseP p = l :=
  List.eraseP_of_forall_not (fun a ha hp => by
    rw [List.find?_eq_none] at h; exact h a ha (by simpa using hp))

/-- **The remainder's part of the whole stack is the stack of the remainder without its settled undos.** -/
theorem part1 (A : List Entry) : ∀ (X : List Entry) (acc : List Entry × List Nat) (T : List Entry),
    (∀ x ∈ X, A.contains x = false) →
    (∀ x ∈ X, ∀ n ∈ acc.2, x.line ≠ n) → X.Pairwise (fun x y => x.line ≠ y.line) →
    acc.1.filter (fun x => !A.contains x) = T →
    (X.foldl (settledStep A) acc).1.filter (fun x => !A.contains x)
      = (unsettled (X.foldl (settledStep A) acc).2 X).foldl maskStep T
  | [], _, _, _, _, _, h => h
  | e :: X, acc, T, hXA, hln, hp, hT => by
    have hpe : ∀ x ∈ X, e.line ≠ x.line := fun x hx => List.rel_of_pairwise_cons hp hx
    -- the final settled lines agree with the first step's on `e`
    have hfin : ∀ (Y : List Entry) (acc' : List Entry × List Nat), (∀ y ∈ Y, y.line ≠ e.line) →
        ((Y.foldl (settledStep A) acc').2.contains e.line = acc'.2.contains e.line) := by
      intro Y
      induction Y with
      | nil => intro _ _; rfl
      | cons y Y ih =>
        intro acc' hy
        rw [List.foldl_cons, ih _ (fun y' hy' => hy y' (List.mem_cons_of_mem _ hy'))]
        unfold settledStep
        cases y.ev with
        | undo of_ id =>
          simp only
          split
          · have hne : y.line ≠ e.line := hy y List.mem_cons_self
            simp [List.contains_cons, Ne.symm hne]
          · rfl
        | _ => rfl
    have hunsE : unsettled ((X.foldl (settledStep A) (settledStep A acc e)).2) [e]
        = unsettled (settledStep A acc e).2 [e] := by
      unfold unsettled
      simp only [List.filter_cons, List.filter_nil]
      rw [hfin X _ (fun y hy => Ne.symm (hpe y hy))]
    rw [List.foldl_cons]
    have hsplit : unsettled ((X.foldl (settledStep A) (settledStep A acc e)).2) (e :: X)
        = unsettled ((X.foldl (settledStep A) (settledStep A acc e)).2) [e]
          ++ unsettled ((X.foldl (settledStep A) (settledStep A acc e)).2) X := by
      unfold unsettled; rw [← List.filter_append]; rfl
    rw [hsplit, hunsE, List.foldl_append]
    apply part1 A X (settledStep A acc e) _ (fun x hx => hXA x (List.mem_cons_of_mem _ hx)) _ hp.of_cons
    · -- the first step, on both sides
      cases hev : e.ev with
      | undo of_ id =>
        have hs1 : settledStep A acc e = (acc.1.eraseP («matches» of_ id),
            if (acc.1.find? («matches» of_ id)).all (fun t => A.contains t) then e.line :: acc.2 else acc.2) := by
          unfold settledStep; rw [hev]
        rw [hs1]
        by_cases hs : (acc.1.find? («matches» of_ id)).all (fun t => A.contains t) = true
        · rw [if_pos hs]
          have hu : unsettled (e.line :: acc.2) [e] = [] := by
            simp [unsettled, Log.Event.isUndo, hev]
          simp only
          rw [hu, List.foldl_nil]
          cases hf : acc.1.find? («matches» of_ id) with
          | none => rw [eraseP_eq_self_of_find?_none _ _ hf, hT]
          | some x =>
            rw [hf] at hs
            rw [eraseP_filter_of_first_not _ _ acc.1 x hf (by simpa using hs), hT]
        · rw [if_neg hs]
          have hnm : e.line ∉ acc.2 := fun hm => hln e List.mem_cons_self e.line hm rfl
          have hu : unsettled acc.2 [e] = [e] := by
            simp [unsettled, Log.Event.isUndo, hev, hnm]
          simp only
          rw [hu]
          have hm : maskStep T e = T.eraseP («matches» of_ id) := by unfold maskStep; rw [hev]
          rw [List.foldl_cons, List.foldl_nil, hm]
          cases hf : acc.1.find? («matches» of_ id) with
          | none => rw [hf] at hs; simp at hs
          | some x =>
            rw [hf] at hs
            rw [eraseP_filter_of_first _ _ acc.1 (fun y hy => by rw [hf] at hy; cases hy; simpa using hs), hT]
      | _ =>
        have hs1 : settledStep A acc e = (e :: acc.1, acc.2) := by unfold settledStep; rw [hev]
        have hu : unsettled acc.2 [e] = [e] := by simp [unsettled, Log.Event.isUndo, hev]
        have hm : maskStep T e = e :: T := by unfold maskStep; rw [hev]
        rw [hs1]
        simp only
        rw [hu, List.foldl_cons, List.foldl_nil, hm, List.filter_cons, hXA e List.mem_cons_self]
        simp only [Bool.not_false, if_true]
        rw [hT]
    · intro x hx n hn
      unfold settledStep at hn
      cases hev : e.ev with
      | undo of_ id =>
        simp only [hev] at hn
        split at hn
        · rcases List.mem_cons.1 hn with rfl | hn
          · exact Ne.symm (hpe x hx)
          · exact hln x (List.mem_cons_of_mem _ hx) n hn
        · exact hln x (List.mem_cons_of_mem _ hx) n hn
      | _ => simp only [hev] at hn; exact hln x (List.mem_cons_of_mem _ hx) n hn

/-! ### Part 2: over the lines appended since -/

/-- **An undo appended since either finds its target among the tail's survivors or dangles past the folded ones.** -/
theorem part2 (K : Ckpt) (SA : List Entry)
    (hSA : ∀ u, reachOf K u = none → ∀ of_ id, u.ev = .undo of_ id → ∀ x ∈ SA, «matches» of_ id x = false) :
    ∀ (Y : List Entry) (acc : List Entry × List Entry), (∀ u ∈ (Y.foldl dangleStep acc).2, reachOf K u = none) →
      Y.foldl maskStep (acc.1 ++ SA) = (Y.foldl maskStep acc.1) ++ SA
  | [], _, _ => rfl
  | e :: Y, acc, h => by
    rw [List.foldl_cons, List.foldl_cons]
    rw [List.foldl_cons] at h
    have ih := part2 K SA hSA Y (dangleStep acc e) h
    cases hev : e.ev with
    | undo of_ id =>
      have hm1 : maskStep (acc.1 ++ SA) e = (acc.1 ++ SA).eraseP («matches» of_ id) := by unfold maskStep; rw [hev]
      have hm2 : maskStep acc.1 e = acc.1.eraseP («matches» of_ id) := by unfold maskStep; rw [hev]
      rw [hm1, hm2]
      by_cases hany : acc.1.any («matches» of_ id) = true
      · rw [List.eraseP_append, if_pos hany]
        have hd : dangleStep acc e = (acc.1.eraseP («matches» of_ id), acc.2) := by
          unfold dangleStep; simp [hev, hany]
        rw [hd] at ih; exact ih
      · have hd : dangleStep acc e = (acc.1, e :: acc.2) :=
          Replay.dangleStep_of_no_match acc e of_ id hev (by simpa using hany)
        have hre : reachOf K e = none := by
          rw [hd] at h
          exact h e (Replay.danglingOf_snd_mono Y _ e List.mem_cons_self)
        have hnoSA := hSA e hre of_ id hev
        have h1 : acc.1.eraseP («matches» of_ id) = acc.1 :=
          List.eraseP_of_forall_not (fun x hx hm => hany (List.any_eq_true.2 ⟨x, hx, hm⟩))
        have h2 : (acc.1 ++ SA).eraseP («matches» of_ id) = acc.1 ++ SA :=
          List.eraseP_of_forall_not (fun x hx hm => by
            rcases List.mem_append.1 hx with hx | hx
            · exact hany (List.any_eq_true.2 ⟨x, hx, hm⟩)
            · rw [hnoSA x hx] at hm; cases hm)
        rw [h1, h2]
        rw [hd] at ih; exact ih
    | _ =>
      have hm1 : maskStep (acc.1 ++ SA) e = e :: (acc.1 ++ SA) := by unfold maskStep; rw [hev]
      have hm2 : maskStep acc.1 e = e :: acc.1 := by unfold maskStep; rw [hev]
      have hd : dangleStep acc e = (e :: acc.1, acc.2) := by unfold dangleStep; rw [hev]
      rw [hm1, hm2]; rw [hd] at ih; exact ih

/-! ### The split -/

theorem mem_foldl_maskStep' : ∀ (xs st : List Entry) (x : Entry), x ∈ xs.foldl maskStep st → x ∈ st ∨ x ∈ xs
  | [], _, _, h => Or.inl h
  | e :: xs, st, x, h => by
    rw [List.foldl_cons] at h
    rcases mem_foldl_maskStep' xs _ x h with h | h
    · unfold maskStep at h
      split at h
      · exact Or.inl (List.mem_of_mem_eraseP h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr List.mem_cons_self
        · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem unsettled_append (S : List Nat) (X Y : List Entry) : unsettled S (X ++ Y) = unsettled S X ++ unsettled S Y := by
  unfold unsettled; rw [List.filter_append]

theorem unsettled_reverse (S : List Nat) (X : List Entry) : unsettled S.reverse X = unsettled S X := by
  unfold unsettled
  apply List.filter_congr
  intro x _
  simp [List.contains_iff_mem]

theorem unsettled_of_lines (S : List Nat) (X : List Entry) (h : ∀ x ∈ X, x.line ∉ S) : unsettled S X = X := by
  unfold unsettled
  apply List.filter_eq_self.2
  intro x hx
  simp [h x hx]

theorem settled_lines_sub (A : List Entry) : ∀ (X : List Entry) (acc : List Entry × List Nat) (n : Nat),
    n ∈ (X.foldl (settledStep A) acc).2 → n ∈ acc.2 ∨ ∃ x ∈ X, x.line = n
  | [], _, _, h => Or.inl h
  | e :: X, acc, n, h => by
    rw [List.foldl_cons] at h
    rcases settled_lines_sub A X _ n h with h | ⟨x, hx, hxn⟩
    · unfold settledStep at h
      cases hev : e.ev with
      | undo of_ id =>
        simp only [hev] at h
        split at h
        · rcases List.mem_cons.1 h with h | h
          · exact Or.inr ⟨e, List.mem_cons_self, h.symm⟩
          · exact Or.inl h
        · exact Or.inl h
      | _ => simp only [hev] at h; exact Or.inl h
    · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hxn⟩

theorem survivors_append_split (A R : List Entry) :
    survivors (A ++ R) = foldedSurvivors A R ++ ((R.zipIdx A.length).filter (fun p => !Replay.cancelledAt (A ++ R) p.2)).map Prod.fst := by
  rw [Replay.survivors_are_the_uncancelled_entries, List.zipIdx_append, List.filter_append, List.map_append]
  simp only [Nat.zero_add]
  rfl

theorem mem_zipIdx_fst {R : List Entry} {n : Nat} {p : Entry × Nat} (h : p ∈ R.zipIdx n) : p.1 ∈ R := by
  have : (R.zipIdx n).map Prod.fst = R := by simp
  rw [← this]; exact List.mem_map_of_mem h

/-- **The mask splits at the cut under G1** (§7.4's soundness): the whole log's survivors are the folded survivors, then
the survivors of the tail with its settled undos set aside. -/
theorem survivors_append_of_g1 (A R B' : List Entry)
    (hd : (A ++ (R ++ B')).Pairwise (fun x y => x.line < y.line))
    (K : Ckpt) (htl : K.tagLast = keptTags (foldedSurvivors A R))
    (hto : K.tagOverflow = decide ((keptTags (foldedSurvivors A R)).length < (tagLines (foldedSurvivors A R)).length))
    (hset : K.settled = settledOf A R) (hg : g1 K (unsettled K.settled (R ++ B')) = none) :
    survivors (A ++ (R ++ B')) = foldedSurvivors A R ++ survivors (unsettled K.settled (R ++ B')) := by
  obtain ⟨hdA, hdRB, hdX⟩ := List.pairwise_append.1 hd
  obtain ⟨hdR, hdB, hdRB'⟩ := List.pairwise_append.1 hdRB
  have hAx : ∀ x ∈ R ++ B', A.contains x = false := fun x hx => by
    have : x ∉ A := fun hxA => by have := hdX x hxA x hx; omega
    simpa using this
  have hAR : ∀ x ∈ R, A.contains x = false := fun x hx => hAx x (List.mem_append_left _ hx)
  have hRne : R.Pairwise (fun x y => x.line ≠ y.line) := hdR.imp (fun h => Nat.ne_of_lt h)
  let acc0 : List Entry × List Nat := (stackOf A, [])
  have hst1 : (R.foldl (settledStep A) acc0).1 = stackOf (A ++ R) := by
    rw [settledStep_fst, stackOf_append]
  have hA0 : (stackOf A).filter (fun x => !A.contains x) = [] :=
    List.filter_eq_nil_iff.2 (fun x hx => by
      rcases mem_foldl_maskStep' A [] x hx with h | h
      · cases h
      · simp [h])
  have hp1 := part1 A R acc0 [] hAR (fun x _ n hn => by cases hn) hRne hA0
  have hsplitR : Split A (stackOf (A ++ R)) := by
    rw [stackOf_append]
    refine Split.foldl R (stackOf A) ⟨[], stackOf A, rfl, (fun u hu => by cases hu), (fun v hv => ?_)⟩ hAR
    rcases mem_foldl_maskStep' A [] v hv with h | h
    · cases h
    · simp [h]
  generalize hS : (R.foldl (settledStep A) acc0).2 = S at hp1
  rw [hst1] at hp1
  generalize hSA : (stackOf (A ++ R)).filter (fun x => A.contains x) = SA
  have heq := hsplitR.eq
  rw [hp1, hSA] at heq
  have hset' : K.settled = S.reverse := by rw [hset, ← hS]; rfl
  -- the folded part of the stack, read back
  have hSAfs : SA.reverse = foldedSurvivors A R := by
    have h1 := survivors_append_split A R
    have h2 : survivors (A ++ R) = SA.reverse ++ (stackOf (unsettled S R)).reverse := by
      unfold survivors; show (stackOf (A ++ R)).reverse = _
      conv => lhs; rw [heq]
      simp [stackOf]
    have hc := congrArg (List.filter (fun x => A.contains x)) (h2.symm.trans h1)
    rw [List.filter_append, List.filter_append] at hc
    have e1 : SA.reverse.filter (fun x => A.contains x) = SA.reverse := List.filter_eq_self.2 (fun x hx => by
      rw [← hSA] at hx; exact (List.mem_filter.1 (List.mem_reverse.1 hx)).2)
    have e2 : (stackOf (unsettled S R)).reverse.filter (fun x => A.contains x) = [] := List.filter_eq_nil_iff.2 (fun x hx => by
      rcases mem_foldl_maskStep' _ [] x (List.mem_reverse.1 hx) with h | h
      · cases h
      · rw [hAR x ((List.mem_filter.1 h).1)]; simp)
    have e3 : (foldedSurvivors A R).filter (fun x => A.contains x) = foldedSurvivors A R := List.filter_eq_self.2 (fun x hx => by
      unfold foldedSurvivors at hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      have := mem_zipIdx_fst (List.mem_filter.1 hp).1
      simp [this])
    have e4 : (((R.zipIdx A.length).filter (fun p => !Replay.cancelledAt (A ++ R) p.2)).map Prod.fst).filter
        (fun x => A.contains x) = [] := List.filter_eq_nil_iff.2 (fun x hx => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      rw [hAR _ (mem_zipIdx_fst (List.mem_filter.1 hp).1)]; simp)
    rw [e1, e2, e3, e4] at hc
    simpa using hc
  -- the tail without its settled undos
  have hSlines : ∀ n ∈ S, ∃ x ∈ R, x.line = n := fun n hn => by
    rw [← hS] at hn
    rcases settled_lines_sub A R acc0 n hn with h | h
    · cases h
    · exact h
  have hN : unsettled K.settled (R ++ B') = unsettled S R ++ B' := by
    rw [hset', unsettled_reverse, unsettled_append, unsettled_of_lines S B' (fun x hx hxS => by
      obtain ⟨y, hy, hyl⟩ := hSlines x.line hxS
      have := hdRB' y hy x hx; omega)]
  -- appended since
  have hdang : ∀ u ∈ (B'.foldl dangleStep ((unsettled S R).foldl dangleStep ([], []))).2, reachOf K u = none := by
    intro u hu
    have hall := List.findSome?_eq_none_iff.1 hg
    have hu' : u ∈ (danglingOf (unsettled K.settled (R ++ B'))).2 := by
      rw [hN]; unfold danglingOf; rw [List.foldl_append]; exact hu
    exact hall u (List.mem_reverse.2 hu')
  have hSAm : ∀ u, reachOf K u = none → ∀ of_ id, u.ev = .undo of_ id → ∀ x ∈ SA, «matches» of_ id x = false := by
    intro u hu of_ id hev x hx
    have hxfs : x ∈ foldedSurvivors A R := by rw [← hSAfs]; exact List.mem_reverse.2 hx
    cases hm : «matches» of_ id x with
    | false => rfl
    | true =>
      exfalso
      have htag : x.ev.tag = of_ := by
        unfold «matches» at hm; simp only [Bool.and_eq_true, beq_iff_eq] at hm; exact hm.1
      unfold reachOf at hu
      rw [hev] at hu
      simp only at hu
      rcases tag_kept_or_overflow (foldedSurvivors A R) x hxfs with hk | ho
      · rw [htl] at hu
        obtain ⟨p, hp, hpe⟩ := List.any_eq_true.1 hk
        cases hf : (keptTags (foldedSurvivors A R)).find? (fun p => p.1 == of_) with
        | some q => rw [hf] at hu; cases hu
        | none =>
          have := List.find?_eq_none.1 hf p hp
          rw [htag] at hpe
          exact this hpe
      · cases hf : K.tagLast.find? (fun p => p.1 == of_) with
        | some q => rw [hf] at hu; cases hu
        | none =>
          rw [hf] at hu
          simp only at hu
          rw [hto, ← htag] at hu
          rw [ho] at hu
          cases hu
  have hp2 := part2 K SA hSAm B' ((unsettled S R).foldl dangleStep ([], [])) hdang
  rw [Replay.danglingOf_fst_go] at hp2
  rw [hN]
  unfold survivors
  show (stackOf (A ++ (R ++ B'))).reverse = foldedSurvivors A R ++ (stackOf (unsettled S R ++ B')).reverse
  rw [← List.append_assoc, stackOf_append, heq, stackOf_append]
  have e : stackOf (unsettled S R) = (unsettled S R).foldl maskStep [] := rfl
  rw [e, hp2, List.reverse_append, hSAfs]

end Seal
end Tm
