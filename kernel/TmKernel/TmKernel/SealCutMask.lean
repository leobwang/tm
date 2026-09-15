import TmKernel.SealCutBounds
/-!
# SealCutMask — the lines and the mask at the fold point (stage 5, D9, W2: law 6)

The fold point's folded and unfolded tail lines are the tail's entries below and at or after a line number
(`lineEntries_take`, `lineEntries_drop`), and the folded survivors under the call-wide mask are the stored ones then the
folded tail's (`foldedSurvivors_at_cut`).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (survivors)
open Log (Entry)

theorem lineEntries_ge (k : Nat) (b : List Log.Line) (h : Log.contiguousFrom k b = true) :
    ∀ e ∈ Log.lineEntries b, k ≤ e.line := (lineEntries_pairwise k b h).2

/-- **The first `j` lines' entries are the entries on lines below `k + j`.** -/
theorem lineEntries_take : ∀ (k : Nat) (b : List Log.Line) (j : Nat), Log.contiguousFrom k b = true →
    Log.lineEntries (b.take j) = (Log.lineEntries b).filter (fun e => decide (e.line < k + j))
  | _, [], _, _ => by simp [Log.lineEntries]
  | k, l :: b, 0, h => by
    rw [List.take_zero]
    symm
    exact List.filter_eq_nil_iff.2 (fun e he => by
      have := lineEntries_ge k (l :: b) h e he
      simp only [Nat.add_zero, decide_eq_true_eq]; omega)
  | k, l :: b, j + 1, h => by
    simp only [Log.contiguousFrom, Bool.and_eq_true, beq_iff_eq] at h
    rw [List.take_succ_cons]
    have ih := lineEntries_take (k + 1) b j h.2
    rw [show k + 1 + j = k + (j + 1) by omega] at ih
    unfold Log.lineEntries at ih ⊢
    rw [List.filterMap_cons, List.filterMap_cons]
    cases he : l.entry? with
    | none => simp only; exact ih
    | some e =>
      simp only
      have hel : e.line = l.n := Line.entry_line l e he
      rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; omega), ih]

/-- **The lines from the `j`-th on hold the entries on lines at or after `k + j`.** -/
theorem lineEntries_drop : ∀ (k : Nat) (b : List Log.Line) (j : Nat), Log.contiguousFrom k b = true →
    Log.lineEntries (b.drop j) = (Log.lineEntries b).filter (fun e => decide (k + j ≤ e.line))
  | _, [], _, _ => by simp [Log.lineEntries]
  | k, l :: b, 0, h => by
    rw [List.drop_zero]
    symm
    exact List.filter_eq_self.2 (fun e he => by
      have := lineEntries_ge k (l :: b) h e he
      simp only [Nat.add_zero, decide_eq_true_eq]; omega)
  | k, l :: b, j + 1, h => by
    simp only [Log.contiguousFrom, Bool.and_eq_true, beq_iff_eq] at h
    rw [List.drop_succ_cons, lineEntries_drop (k + 1) b j h.2, show k + 1 + j = k + (j + 1) by omega]
    unfold Log.lineEntries
    rw [List.filterMap_cons]
    cases he : l.entry? with
    | none => rfl
    | some e =>
      simp only
      have hel : e.line = l.n := Line.entry_line l e he
      rw [List.filter_cons_of_neg (by simp only [decide_eq_true_eq]; omega)]

/-- **The folded survivors under a mask are the mask's survivors among the folded entries.** -/
theorem foldedSurvivors_eq_filter (A R : List Entry) (hd : (A ++ R).Pairwise (fun x y => x.line < y.line)) :
    foldedSurvivors A R = (survivors (A ++ R)).filter (fun e => A.contains e) := by
  rw [survivors_append_split, List.filter_append]
  have hdA : ∀ x ∈ A, ∀ y ∈ R, x.line < y.line := (List.pairwise_append.1 hd).2.2
  rw [List.filter_eq_self.2 (fun e he => by
      simpa using (foldedSurvivors_sublist A R).subset he),
    List.filter_eq_nil_iff.2 (fun e he => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      have hpR := mem_zipIdx_fst (List.mem_filter.1 hp).1
      have : p.1 ∉ A := fun hA => Nat.lt_irrefl _ (hdA p.1 hA p.1 hpR)
      simpa using this), List.append_nil]

/-- **The folded survivors at a cut**: the stored ones, then the folded tail's (the call-wide mask restricted). -/
theorem foldedSurvivors_at_cut (As Bj Brest : List Entry)
    (hd : (As ++ (Bj ++ Brest)).Pairwise (fun x y => x.line < y.line)) (SA sv : List Entry)
    (hsurv : survivors (As ++ (Bj ++ Brest)) = SA ++ sv) (hSA : ∀ e ∈ SA, e ∈ As)
    (hsvB : ∀ e ∈ sv, e ∈ Bj ++ Brest) :
    foldedSurvivors (As ++ Bj) Brest = SA ++ sv.filter (fun e => Bj.contains e) := by
  have hdA : ∀ x ∈ As, ∀ y ∈ Bj ++ Brest, x.line < y.line := (List.pairwise_append.1 hd).2.2
  rw [foldedSurvivors_eq_filter (As ++ Bj) Brest (by rwa [List.append_assoc]), List.append_assoc, hsurv,
    List.filter_append]
  congr 1
  · exact List.filter_eq_self.2 (fun e he => by simp [hSA e he])
  · exact List.filter_congr (fun e he => by
      have hnA : e ∉ As := fun hA => Nat.lt_irrefl _ (hdA e hA e (hsvB e he))
      simp [hnA])

/-- **A dangling undo G1 accepted misses every folded survivor** (the soundness half of §7.4's G1). -/
theorem dangling_misses_the_folded (A R : List Entry) (K : Ckpt) (htl : K.tagLast = keptTags (foldedSurvivors A R))
    (hto : K.tagOverflow = decide ((keptTags (foldedSurvivors A R)).length < (tagLines (foldedSurvivors A R)).length))
    (u : Entry) (hu : reachOf K u = none) (of_ : List Char) (id : Option Log.Id) (hev : u.ev = .undo of_ id)
    (x : Entry) (hx : x ∈ foldedSurvivors A R) : Replay.«matches» of_ id x = false := by
  cases hm : Replay.«matches» of_ id x with
  | false => rfl
  | true =>
    exfalso
    have htag : x.ev.tag = of_ := by
      unfold Replay.«matches» at hm; simp only [Bool.and_eq_true, beq_iff_eq] at hm; exact hm.1
    unfold reachOf at hu
    rw [hev] at hu
    simp only at hu
    rcases tag_kept_or_overflow (foldedSurvivors A R) x hx with hk | ho
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

/-- One step of `undoTargets`. -/
def undoStep (acc : List Entry × List (Entry × Entry)) (e : Entry) : List Entry × List (Entry × Entry) :=
  match e.ev with
  | .undo of_ id =>
    match acc.1.find? (Replay.«matches» of_ id) with
    | some t => (acc.1.eraseP (Replay.«matches» of_ id), (e, t) :: acc.2)
    | none => acc
  | _ => (e :: acc.1, acc.2)

theorem undoTargets_eq (N : List Entry) : undoTargets N = (N.foldl undoStep ([], [])).2 := rfl

theorem undoStep_fst : ∀ (N : List Entry) (acc : List Entry × List (Entry × Entry)),
    (N.foldl undoStep acc).1 = N.foldl Replay.maskStep acc.1
  | [], _ => rfl
  | e :: N, acc => by
    rw [List.foldl_cons, List.foldl_cons, undoStep_fst N]
    congr 1
    unfold undoStep Replay.maskStep
    cases hev : e.ev with
    | undo of_ id =>
      simp only
      cases hf : acc.1.find? (Replay.«matches» of_ id) with
      | some t => rfl
      | none => exact (eraseP_eq_self_of_find?_none _ _ hf).symm
    | _ => rfl

theorem undoStep_snd_mono : ∀ (N : List Entry) (acc : List Entry × List (Entry × Entry)) (x : Entry × Entry),
    x ∈ acc.2 → x ∈ (N.foldl undoStep acc).2
  | [], _, _, h => h
  | e :: N, acc, x, h => by
    rw [List.foldl_cons]
    apply undoStep_snd_mono N
    unfold undoStep
    cases hev : e.ev with
    | undo of_ id =>
      simp only
      cases hf : acc.1.find? (Replay.«matches» of_ id) with
      | some t => exact List.mem_cons_of_mem _ h
      | none => exact h
    | _ => exact h

/-- **An undo's first match on the stack before it is its recorded target.** -/
theorem mem_undoTargets (N pre post : List Entry) (u : Entry) (of_ : List Char) (id : Option Log.Id)
    (hN : N = pre ++ u :: post) (hev : u.ev = .undo of_ id) (t : Entry)
    (ht : (pre.foldl Replay.maskStep []).find? (Replay.«matches» of_ id) = some t) : (u, t) ∈ undoTargets N := by
  show (u, t) ∈ (N.foldl undoStep ([], [])).2
  rw [hN, List.foldl_append, List.foldl_cons]
  apply undoStep_snd_mono
  have h1 := undoStep_fst pre ([], [])
  generalize pre.foldl undoStep ([], []) = acc at h1 ⊢
  simp only at h1
  unfold undoStep
  rw [hev]
  simp only
  rw [h1, ht]
  exact List.mem_cons_self

end Seal
end Tm
