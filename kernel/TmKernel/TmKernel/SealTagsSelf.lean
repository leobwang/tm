import TmKernel.SealCutStep
import TmKernel.SealReach
/-!
# SealTagsSelf — a checkpoint's own unfolded lines dangle no undo (stage 5, D9, W2: law 7)

A checkpoint's settled undos are its unfolded undos whose call-wide target is folded or absent (`settledOf`).  With them
set aside, the unfolded lines' own mask is the call-wide mask restricted to them (`tail_dangle_inv`): every other unfolded
undo finds its call-wide target among the unfolded lines, first.  So none dangles (`dangling_unsettled_self`), and G1's
condition holds of a checkpoint's own suffix (`tagsClear_self`).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (maskStep dangleStep danglingOf survivors)
open Log (Entry)

theorem settledStep_snd (A : List Entry) (acc : List Entry × List Nat) (e : Entry) :
    (settledStep A acc e).2 = acc.2 ∨ (settledStep A acc e).2 = e.line :: acc.2 := by
  unfold settledStep
  split
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- **An unfolded undo is settled exactly when its call-wide target is folded or absent.** -/
theorem mem_settledOf_iff (As Rs : List Entry) (hd : (As ++ Rs).Pairwise (fun x y => x.line < y.line))
    (P Q : List Entry) (u : Entry) (hs : Rs = P ++ u :: Q) (of_ : List Char) (id : Option Log.Id)
    (hev : u.ev = .undo of_ id) :
    u.line ∈ settledOf As Rs ↔
      ((stackOf (As ++ P)).find? (Replay.«matches» of_ id)).all (fun t => As.contains t) = true := by
  have hdR : Rs.Pairwise (fun x y => x.line < y.line) := (List.pairwise_append.1 hd).2.1
  have hsplit : Rs = (P ++ [u]) ++ Q := by rw [hs]; simp
  rw [hsplit] at hdR
  have hne : ∀ x ∈ P ++ [u], ∀ y ∈ Q, x.line ≠ y.line := fun x hx y hy =>
    Nat.ne_of_lt ((List.pairwise_append.1 hdR).2.2 x hx y hy)
  have hPu : ∀ x ∈ P, x.line < u.line := fun x hx =>
    (List.pairwise_append.1 (List.pairwise_append.1 hdR).1).2.2 x hx u (List.mem_singleton.2 rfl)
  unfold settledOf
  rw [List.mem_reverse, hsplit, settled_prefix_lines As (P ++ [u]) Q _ hne u (by simp), List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  have hfst : (P.foldl (settledStep As) (As.foldl maskStep [], [])).1 = stackOf (As ++ P) := by
    rw [settledStep_fst, stackOf_append]; rfl
  have hnot : u.line ∉ (P.foldl (settledStep As) (As.foldl maskStep [], [])).2 := by
    intro hm
    rcases settled_lines_sub As P _ _ hm with h | ⟨x, hx, hxl⟩
    · cases h
    · have := hPu x hx; omega
  generalize P.foldl (settledStep As) (As.foldl maskStep [], []) = acc at hfst hnot ⊢
  unfold settledStep
  simp only [hev]
  rw [hfst]
  split
  · rename_i hc; exact ⟨fun _ => hc, fun _ => List.mem_cons_self⟩
  · rename_i hc; exact ⟨fun h => absurd h hnot, fun h => absurd h hc⟩

theorem isUndo_iff (e : Log.Event) : e.isUndo = true ↔ ∃ of_ id, e = .undo of_ id := by
  cases e <;> simp [Log.Event.isUndo]

theorem maskStep_push (st : List Entry) (e : Entry) (h : e.ev.isUndo = false) : maskStep st e = e :: st := by
  unfold maskStep
  split
  · rename_i of_ id hev; simp [Log.Event.isUndo, hev] at h
  · rfl

theorem dangleStep_push (acc : List Entry × List Entry) (e : Entry) (h : e.ev.isUndo = false) :
    dangleStep acc e = (e :: acc.1, acc.2) := by
  unfold dangleStep
  split
  · rename_i of_ id hev; simp [Log.Event.isUndo, hev] at h
  · rfl

theorem stackOf_filter_nil (As : List Entry) : (stackOf As).filter (fun x => !As.contains x) = [] := by
  apply List.filter_eq_nil_iff.2
  intro x hx
  have hxA : x ∈ As := Replay.mem_of_mem_survivors As x (List.mem_reverse.2 hx)
  simp [hxA]

/-- **The unfolded lines' own mask is the call-wide mask restricted to them**, with the settled undos set aside, and
nothing dangles. -/
theorem tail_dangle_inv (As Rs : List Entry) (hd : (As ++ Rs).Pairwise (fun x y => x.line < y.line)) :
    ∀ n, (unsettled (settledOf As Rs) (Rs.take n)).foldl dangleStep ([], [])
      = ((stackOf (As ++ Rs.take n)).filter (fun x => !As.contains x), [])
  | 0 => by
    simp only [List.take_zero, List.append_nil]
    rw [stackOf_filter_nil]; rfl
  | n + 1 => by
    by_cases hn : n < Rs.length
    · have ih := tail_dangle_inv As Rs hd n
      have hRs : Rs = Rs.take n ++ Rs[n] :: Rs.drop (n + 1) := by
        rw [← List.drop_eq_getElem_cons hn, List.take_append_drop]
      have huA : As.contains Rs[n] = false := by
        cases hc : As.contains Rs[n]
        · rfl
        · have hmA : Rs[n] ∈ As := by simpa using hc
          have hmR : Rs[n] ∈ Rs := List.getElem_mem hn
          have := (List.pairwise_append.1 hd).2.2 _ hmA _ hmR
          omega
      rw [List.take_add_one, List.getElem?_eq_getElem hn, Option.toList_some, unsettled_append, List.foldl_append, ih,
        ← List.append_assoc, stackOf_snoc]
      generalize hst : stackOf (As ++ Rs.take n) = stP
      cases hu : (Rs[n]).ev.isUndo
      · have h1 : unsettled (settledOf As Rs) [Rs[n]] = [Rs[n]] := by
          unfold unsettled; simp [hu]
        rw [h1, List.foldl_cons, List.foldl_nil, dangleStep_push _ _ hu, maskStep_push _ _ hu]
        have hnm : Rs[n] ∉ As := by simpa using huA
        simp [hnm]
      · obtain ⟨of_, id, hev⟩ := (isUndo_iff _).1 hu
        have hiff := mem_settledOf_iff As Rs hd (Rs.take n) (Rs.drop (n + 1)) Rs[n] hRs of_ id hev
        rw [hst] at hiff
        have hmask : maskStep stP Rs[n] = stP.eraseP (Replay.«matches» of_ id) := by
          unfold maskStep; rw [hev]
        rw [hmask]
        by_cases hS : Rs[n].line ∈ settledOf As Rs
        · have h1 : unsettled (settledOf As Rs) [Rs[n]] = [] := by
            unfold unsettled; simp [hu, hS]
          rw [h1, List.foldl_nil]
          have hall := hiff.1 hS
          cases hf : stP.find? (Replay.«matches» of_ id) with
          | none => rw [eraseP_eq_self_of_find?_none _ _ hf]
          | some t =>
            rw [hf] at hall
            have ht : (!As.contains t) = false := by simpa using hall
            rw [eraseP_filter_of_first_not _ _ stP t hf ht]
        · have h1 : unsettled (settledOf As Rs) [Rs[n]] = [Rs[n]] := by
            unfold unsettled; simp [hS]
          rw [h1, List.foldl_cons, List.foldl_nil]
          have hnall : ¬ ((stP.find? (Replay.«matches» of_ id)).all (fun t => As.contains t) = true) :=
            fun h => hS (hiff.2 h)
          cases hf : stP.find? (Replay.«matches» of_ id) with
          | none => rw [hf] at hnall; exact absurd rfl hnall
          | some m =>
            rw [hf] at hnall
            have hmA : (!As.contains m) = true := by simpa using hnall
            have hmM : Replay.«matches» of_ id m = true := List.find?_some hf
            have hmS : m ∈ stP := List.mem_of_find?_eq_some hf
            have hany : (stP.filter (fun x => !As.contains x)).any (Replay.«matches» of_ id) = true :=
              List.any_eq_true.2 ⟨m, List.mem_filter.2 ⟨hmS, hmA⟩, hmM⟩
            have hfirst : ∀ x, stP.find? (Replay.«matches» of_ id) = some x → (!As.contains x) = true := by
              intro x hx; rw [hf] at hx; cases hx; exact hmA
            unfold dangleStep
            rw [hev]
            simp only [hany, ↓reduceIte]
            rw [eraseP_filter_of_first _ _ stP hfirst]
    · have h1 : Rs.take (n + 1) = Rs.take n := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      rw [h1]; exact tail_dangle_inv As Rs hd n

/-- **No unfolded undo of a checkpoint dangles in its own unsettled lines.** -/
theorem dangling_unsettled_self (As Rs : List Entry) (hd : (As ++ Rs).Pairwise (fun x y => x.line < y.line)) :
    (danglingOf (unsettled (settledOf As Rs) Rs)).2 = [] := by
  have := tail_dangle_inv As Rs hd Rs.length
  rw [List.take_length] at this
  unfold danglingOf
  rw [this]

/-- **G1's condition holds of a checkpoint's own unfolded lines.** -/
theorem tagsClear_self (z : Cal.Tz) (T₀ L : Nat) (a r : List Log.Line) (hc : Log.contiguousFrom 1 (a ++ r) = true) :
    tagsClear z T₀ L a r r = true := by
  have hd : (Log.lineEntries a ++ Log.lineEntries r).Pairwise (fun x y => x.line < y.line) := by
    have := (lineEntries_pairwise 1 (a ++ r) hc).1
    rwa [show Log.lineEntries (a ++ r) = Log.lineEntries a ++ Log.lineEntries r from List.filterMap_append] at this
  unfold tagsClear
  rw [dangling_unsettled_self _ _ hd]
  rfl

end Seal
end Tm
