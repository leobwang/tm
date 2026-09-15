import TmKernel.SealCutMachine
import TmKernel.SealCutMask
import TmKernel.SealLaw6Pair
/-!
# SealCutLows — what bounds the new ledger day, and the lines at the cut (stage 5, D9, W2: law 6)

The new ledger day is at most the old one or each day the unfolded lines head, name or read (`sealDayOf_le_max`, reading
`stepLows` through `mem_lows`).  Beside it: a line-sorted list splits at a line (`filter_line_split`), survivors are a
sublist, and a warning carries its line's number (`lineWarnings_take`).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State survivors)
open Log (Entry)

/-- One step of `stepLows`. -/
def lowsStep (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (P : Entry → Bool)
    (acc : State × List Nat) (e : Entry) : State × List Nat :=
  let fx := Replay.effectsWith z dy sl acc.1 e
  (Replay.applyEffects acc.1 fx,
   if P e then fx.filterMap (fun x => x.key.date?) ++ (stepQueries acc.1.machine e).map (fun q => q.sec / 86400 + 1)
     ++ acc.2 else acc.2)

theorem stepLows_eq (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (P : Entry → Bool) (st : State)
    (sv : List Entry) : stepLows z dy sl P st sv = (sv.foldl (lowsStep z dy sl P) (st, [])).2 := rfl

theorem lowsStep_mono (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (P : Entry → Bool) :
    ∀ (sv : List Entry) (acc : State × List Nat) (x : Nat), x ∈ acc.2 → x ∈ (sv.foldl (lowsStep z dy sl P) acc).2
  | [], _, _, h => h
  | e :: sv, acc, x, h => by
    rw [List.foldl_cons]
    apply lowsStep_mono z dy sl P sv
    unfold lowsStep
    dsimp only
    split
    · exact List.mem_append_right _ h
    · exact h

/-- **Every day an unfolded step names or reads is a low.** -/
theorem mem_lows (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (P : Entry → Bool) :
    ∀ (pre : List Entry) (acc : State × List Nat) (e : Entry) (post : List Entry), P e = true →
    (∀ x ∈ (Replay.effectsWith z dy sl (pre.foldl (Replay.stepWith z dy sl) acc.1) e).filterMap (fun x => x.key.date?),
      x ∈ ((pre ++ e :: post).foldl (lowsStep z dy sl P) acc).2) ∧
    (∀ q ∈ stepQueries (pre.foldl (Replay.stepWith z dy sl) acc.1).machine e,
      q.sec / 86400 + 1 ∈ ((pre ++ e :: post).foldl (lowsStep z dy sl P) acc).2)
  | [], acc, e, post, hP => by
    rw [List.nil_append, List.foldl_cons]
    refine ⟨fun x hx => lowsStep_mono z dy sl P post _ x ?_, fun q hq => lowsStep_mono z dy sl P post _ _ ?_⟩
    · unfold lowsStep; dsimp only; rw [if_pos hP]
      exact List.mem_append_left _ (List.mem_append_left _ hx)
    · unfold lowsStep; dsimp only; rw [if_pos hP]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨q, hq, rfl⟩))
  | p :: pre, acc, e, post, hP => by
    rw [List.cons_append, List.foldl_cons]
    exact mem_lows z dy sl P pre (lowsStep z dy sl P acc p) e post hP

theorem foldl_min_le_of_mem : ∀ (l : List Nat) (F x : Nat), x ∈ l → l.foldl Nat.min F ≤ x
  | [], _, _, h => by cases h
  | a :: l, F, x, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with hx | h
    · rw [hx]; exact Nat.le_trans (foldl_min_le l (Nat.min F a)) (Nat.min_le_right _ _)
    · exact foldl_min_le_of_mem l _ x h

/-- **The new ledger day is at most the old one or any low.** -/
theorem sealDayOf_le_max (z : Cal.Tz) (T : Nat) (K : Ckpt) (p : Policy) (r : Run) (j x : Nat)
    (hx : x ∈ (r.entries.filter (fun e => decide (K.cut + j < e.line))).map (fun e => Replay.dayOf z r.index e.t.val)
      ∨ x ∈ (r.entries.filter (fun e => decide (K.cut + j < e.line))).map (fun e => e.t.val.sec / 86400 + 1)
      ∨ x ∈ stepLows z (Replay.dayOf z r.index) r.slept (fun e => decide (K.cut + j < e.line))
          (restore K (K.items.length + K.openDays.length + r.entries.length)) r.survivors
      ∨ x ∈ machineDays ((r.survivors.filter (fun e => decide (e.line ≤ K.cut + j))).foldl
          (Replay.stepWith z (Replay.dayOf z r.index) r.slept)
          (restore K (K.items.length + K.openDays.length + r.entries.length))).machine) :
    sealDayOf z T K p r j ≤ Nat.max K.ledgerDay x := by
  have key : ∀ (l : List Nat) (F : Nat), x ∈ l → Nat.max K.ledgerDay (l.foldl Nat.min F) ≤ Nat.max K.ledgerDay x :=
    fun l F h => Nat.max_le.2 ⟨Nat.le_max_left _ _, Nat.le_trans (foldl_min_le_of_mem l F x h) (Nat.le_max_right _ _)⟩
  unfold sealDayOf
  dsimp only
  apply key
  simp only [List.mem_append]
  rcases hx with h | h | h | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- **A line-sorted list splits at a line.** -/
theorem filter_line_split (c : Nat) : ∀ (l : List Entry), l.Pairwise (fun x y => x.line < y.line) →
    l.filter (fun e => decide (e.line ≤ c)) ++ l.filter (fun e => decide (c < e.line)) = l
  | [], _ => rfl
  | a :: l, hs => by
    rw [List.pairwise_cons] at hs
    by_cases ha : a.line ≤ c
    · have hna : ¬ c < a.line := by omega
      simp only [List.filter_cons, ha, hna, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true, List.cons_append]
      rw [filter_line_split c l hs.2]
    · have hall : ∀ x ∈ l, c < x.line := fun x hx => by have := hs.1 x hx; omega
      have h1 : l.filter (fun e => decide (e.line ≤ c)) = [] :=
        List.filter_eq_nil_iff.2 (fun x hx h => by have := hall x hx; simp at h; omega)
      have h2 : l.filter (fun e => decide (c < e.line)) = l := List.filter_eq_self.2 (fun x hx => by simpa using hall x hx)
      have hca : c < a.line := by omega
      simp only [List.filter_cons, ha, hca, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true, h1, h2,
        List.nil_append]

theorem survivors_sublist (es : List Entry) : (survivors es).Sublist es := by
  rw [Replay.survivors_are_the_uncancelled_entries]
  have := (List.filter_sublist (p := fun p : Entry × Nat => !Replay.cancelledAt es p.2) (l := es.zipIdx)).map Prod.fst
  rwa [List.zipIdx_map_fst] at this

theorem unsettled_sublist (S : List Nat) (bs : List Entry) : (unsettled S bs).Sublist bs := List.filter_sublist

theorem readObject_warn (n : Nat) (kvs : List (List Char × JVal)) (m : Nat) (w : Log.LWarn)
    (h : Log.readObject n kvs = .warn m w) : m = n := by
  unfold Log.readObject at h
  repeat' split at h
  all_goals first | (simp only [Log.Verdict.warn.injEq] at h; exact h.1.symm) | cases h

theorem readValue_warn (n : Nat) (v : JVal) (m : Nat) (w : Log.LWarn) (h : Log.readValue n v = .warn m w) : m = n := by
  unfold Log.readValue at h
  split at h
  · split at h
    · exact readObject_warn n _ m w h
    · simp only [Log.Verdict.warn.injEq] at h; exact h.1.symm
  · simp only [Log.Verdict.warn.injEq] at h; exact h.1.symm

theorem readLine_warn (n : Nat) (raw : Option (List Char)) (m : Nat) (w : Log.LWarn)
    (h : Log.readLine n raw = .warn m w) : m = n := by
  unfold Log.readLine at h
  repeat' split at h
  all_goals first
    | (simp only [Log.Verdict.warn.injEq] at h; exact h.1.symm)
    | cases h
    | exact readValue_warn n _ m w h

/-- **A line warning carries its line's number.** -/
theorem Line.warning_line (l : Log.Line) (w : Nat × Log.LWarn) (h : l.warning? = some w) : w.1 = l.n := by
  unfold Log.Line.warning? Log.Line.verdict at h
  split at h
  · rename_i n' w' hv
    simp only [Option.some.injEq] at h
    subst h
    exact readLine_warn _ _ _ _ hv
  · cases h

theorem lineWarnings_ge : ∀ (k : Nat) (b : List Log.Line), Log.contiguousFrom k b = true →
    ∀ w ∈ Log.lineWarnings b, k ≤ w.1
  | _, [], _, w, hw => by simp [Log.lineWarnings] at hw
  | k, l :: b, h, w, hw => by
    simp only [Log.contiguousFrom, Bool.and_eq_true, beq_iff_eq] at h
    unfold Log.lineWarnings at hw
    rw [List.filterMap_cons] at hw
    cases hl : l.warning? with
    | none =>
      simp only [hl] at hw
      have := lineWarnings_ge (k + 1) b h.2 w hw; omega
    | some w' =>
      simp only [hl, List.mem_cons] at hw
      rcases hw with rfl | hw
      · have := Line.warning_line l w hl; omega
      · have := lineWarnings_ge (k + 1) b h.2 w hw; omega

/-- **The first `j` lines' warnings are the warnings on lines below `k + j`.** -/
theorem lineWarnings_take : ∀ (k : Nat) (b : List Log.Line) (j : Nat), Log.contiguousFrom k b = true →
    Log.lineWarnings (b.take j) = (Log.lineWarnings b).filter (fun w => decide (w.1 < k + j))
  | _, [], _, _ => by simp [Log.lineWarnings]
  | k, l :: b, 0, h => by
    rw [List.take_zero]
    symm
    exact List.filter_eq_nil_iff.2 (fun w hw => by
      have := lineWarnings_ge k (l :: b) h w hw
      simp only [Nat.add_zero, decide_eq_true_eq]; omega)
  | k, l :: b, j + 1, h => by
    simp only [Log.contiguousFrom, Bool.and_eq_true, beq_iff_eq] at h
    rw [List.take_succ_cons]
    have ih := lineWarnings_take (k + 1) b j h.2
    rw [show k + 1 + j = k + (j + 1) by omega] at ih
    unfold Log.lineWarnings at ih ⊢
    rw [List.filterMap_cons, List.filterMap_cons]
    cases hw : l.warning? with
    | none => simp only; exact ih
    | some w =>
      simp only
      have hwl : w.1 = l.n := Line.warning_line l w hw
      rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; omega), ih]

end Seal
end Tm
