import TmKernel.SealResume
/-!
# SealFoldPoint — the fold point is the greatest valid cut, and never folds an unterminated line (stage 5, D9, W2)

§14.5's `foldPoint_valid`, `foldPoint_greatest` and `the_unterminated_segment_is_never_folded`.  Specification only
(D9-21).
-/
namespace Tm
namespace Seal

open Log (Entry)

theorem foldl_last_valid (valid : Nat → Bool) : ∀ (l : List Nat) (acc : Nat),
    l.foldl (fun acc j => if valid j then j else acc) acc = ((l.filter valid).getLast?).getD acc
  | [], _ => rfl
  | x :: l, acc => by
    rw [List.foldl_cons, foldl_last_valid valid l]
    by_cases hx : valid x = true
    · rw [if_pos hx, List.filter_cons_of_pos hx, List.getLast?_cons]
      rfl
    · rw [if_neg hx, List.filter_cons_of_neg hx]

theorem getLast?_ge_of_sorted : ∀ (l : List Nat), l.Pairwise (· < ·) → ∀ m, l.getLast? = some m → ∀ x ∈ l, x ≤ m
  | [], _, _, h, _, _ => by simp at h
  | [a], _, m, h, x, hx => by
    simp at h hx; omega
  | a :: b :: l, hp, m, h, x, hx => by
    have ih := getLast?_ge_of_sorted (b :: l) hp.of_cons m (by simpa using h)
    rcases List.mem_cons.1 hx with rfl | hx
    · have hb := ih b List.mem_cons_self
      have := List.rel_of_pairwise_cons hp (List.mem_cons_self (a := b) (l := l))
      omega
    · exact ih x hx

/-- **The greatest valid `j ≤ n`**: every valid `j ≤ n` is at most it, it is at most `n`, and it is valid when any is. -/
theorem greatestValid_spec (n : Nat) (valid : Nat → Bool) :
    (∀ j, j ≤ n → valid j = true → j ≤ greatestValid n valid) ∧ greatestValid n valid ≤ n ∧
    ((∃ j, j ≤ n ∧ valid j = true) → valid (greatestValid n valid) = true) := by
  unfold greatestValid
  rw [foldl_last_valid]
  have hsorted : ((List.range (n + 1)).filter valid).Pairwise (· < ·) := (List.pairwise_lt_range).sublist List.filter_sublist
  refine ⟨fun j hj hv => ?_, ?_, fun ⟨j, hj, hv⟩ => ?_⟩
  · have hmem : j ∈ (List.range (n + 1)).filter valid := List.mem_filter.2 ⟨List.mem_range.2 (by omega), hv⟩
    cases hl : ((List.range (n + 1)).filter valid).getLast? with
    | none => rw [List.getLast?_eq_none_iff] at hl; rw [hl] at hmem; cases hmem
    | some m => exact getLast?_ge_of_sorted _ hsorted m hl j hmem
  · cases hl : ((List.range (n + 1)).filter valid).getLast? with
    | none => simp
    | some m =>
      have := List.mem_of_getLast? hl
      simp only [Option.getD_some]
      have := (List.mem_filter.1 this).1
      rw [List.mem_range] at this
      omega
  · have hmem : j ∈ (List.range (n + 1)).filter valid := List.mem_filter.2 ⟨List.mem_range.2 (by omega), hv⟩
    cases hl : ((List.range (n + 1)).filter valid).getLast? with
    | none => rw [List.getLast?_eq_none_iff] at hl; rw [hl] at hmem; cases hmem
    | some m =>
      simp only [Option.getD_some]
      exact (List.mem_filter.1 (List.mem_of_getLast? hl)).2

theorem foldPoint_eq (z : Cal.Tz) (T : Nat) (k : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run)
    (hr : resumeRun z T k b = .ok r) : foldPoint z T k b terminated p = foldPointOf z T k b terminated p r := by
  unfold foldPoint; rw [hr]

theorem sealDay_eq (z : Cal.Tz) (T : Nat) (k : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run)
    (hr : resumeRun z T k b = .ok r) :
    sealDay z T k b terminated p = sealDayOf z T k p r (foldPointOf z T k b terminated p r) := by
  unfold sealDay; rw [hr]

/-- **The fold point is a valid cut** whenever any cut of the tail is. -/
theorem foldPoint_valid (z : Cal.Tz) (T : Nat) (k : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy)
    (r : Run) (hr : resumeRun z T k b = .ok r) (j : Nat) (hj : j ≤ b.length)
    (hv : cutOk z T k b terminated p r j = true) :
    cutOk z T k b terminated p r (foldPoint z T k b terminated p) = true := by
  rw [foldPoint_eq z T k b terminated p r hr]
  exact (greatestValid_spec b.length _).2.2 ⟨j, hj, hv⟩

/-- **The fold point is the greatest valid cut.** -/
theorem foldPoint_greatest (z : Cal.Tz) (T : Nat) (k : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy)
    (r : Run) (hr : resumeRun z T k b = .ok r) (j : Nat) (hj : j ≤ b.length)
    (hv : cutOk z T k b terminated p r j = true) : j ≤ foldPoint z T k b terminated p := by
  rw [foldPoint_eq z T k b terminated p r hr]
  exact (greatestValid_spec b.length _).1 j hj hv

/-- A reseal is emitted exactly at a valid fold point, from an accepted run, under an unchanged classification. -/
theorem resealOf_some (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run)
    (s : Resealed) (h : resealOf z T K b terminated p r = some s) :
    migrationOk K T = true ∧ cutOk z T K b terminated p r (foldPointOf z T K b terminated p r) = true := by
  unfold resealOf at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact hc
  · cases h

theorem resume_some_reseal (z : Cal.Tz) (T : Nat) (k : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy)
    (v : Seal.Answer) (s : Resealed) (h : resume z T k b terminated (some p) = .ok (v, some s)) :
    ∃ r, resumeRun z T k b = .ok r ∧ resealOf z T k b terminated p r = some s ∧ r.answer = v := by
  unfold resume at h
  cases hr : resumeRun z T k b with
  | error e => rw [hr] at h; simp at h
  | ok r =>
    rw [hr] at h
    simp only [Except.ok.injEq, Prod.mk.injEq, Option.bind_some] at h
    exact ⟨r, rfl, h.2, h.1⟩

/-- **A valid cut's conditions, by name** (§9.4's (i)–(v) and (vi)). -/
theorem cutOk_parts {z : Cal.Tz} {T : Nat} {K : Ckpt} {b : List Log.Line} {terminated : Bool} {p : Policy} {r : Run}
    {j : Nat} (h : cutOk z T K b terminated p r j = true) :
    j ≤ b.length ∧
    (r.entries.filter (fun e => decide (e.line ≤ K.cut + j))).all
      (fun e => isFuture T e.t.val || decide (Replay.dayOf z r.index e.t.val < floorOf T p.keepDays (Replay.dayOf z r.index) r.survivors)) = true ∧
    (j == 0 || p.maxLine.all (fun m => decide (K.cut + j ≤ m))) = true ∧
    (Replay.wakeInstants (r.survivors.filter (fun e => decide (K.cut + j < e.line)))).all (fun w =>
      (maxOptI K.maxT (maxInstant? (((r.entries.filter (fun e => decide (e.line ≤ K.cut + j))).flatMap entryInstants).filter
        (fun q => !isFuture T q)))).all (· < w) &&
      (minOptI K.futureFloor (minInstant? (((r.entries.filter (fun e => decide (e.line ≤ K.cut + j))).flatMap
        entryInstants).filter (isFuture T)))).all (fun f => decide (w.sec + fenceSec < f.sec))) = true ∧
    (settledAt K r j).length ≤ maxSettled ∧
    (terminated = true ∨ j < b.length ∨ j = 0) ∧
    K.settled.all (fun n => decide (n ≤ K.cut + j)) = true ∧
    (undoTargets r.unsettledTail).all
      (fun ut => !(decide (ut.2.line ≤ K.cut + j) && decide (K.cut + j < ut.1.line))) = true := by
  unfold cutOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨of_decide_eq_true h0, h1, h2, h3, of_decide_eq_true h4, ?_, h6, h7⟩
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h5
  rcases h5 with (h5 | h5) | h5
  · exact Or.inl h5
  · exact Or.inr (Or.inl h5)
  · exact Or.inr (Or.inr h5)

/-- **The unterminated segment is never folded** (CRIT 8): a reseal of an unterminated tail leaves its last line
unfolded. -/
theorem the_unterminated_segment_is_never_folded (z : Cal.Tz) (T : Nat) (k : Ckpt) (b : List Log.Line) (p : Policy)
    (v : Seal.Answer) (s : Resealed) (hb : b ≠ []) (h : resume z T k b false (some p) = .ok (v, some s)) :
    foldPoint z T k b false p < b.length := by
  obtain ⟨r, hr, hs, -⟩ := resume_some_reseal z T k b false p v s h
  obtain ⟨-, hc⟩ := resealOf_some z T k b false p r s hs
  rw [foldPoint_eq z T k b false p r hr]
  have hlen : 0 < b.length := List.length_pos_iff.2 hb
  rcases (cutOk_parts hc).2.2.2.2.2.1 with h1 | h1 | h1
  · cases h1
  · exact h1
  · rw [h1]; exact hlen

end Seal
end Tm
