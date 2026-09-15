import TmKernel.SealMask
/-!
# SealBits — a line's mask bit is whether it survives (stage 5, D9, W2)

On entries with distinct lines, the entry at a position is cancelled exactly when it is not among the survivors
(`mem_survivors_iff_uncancelled`), so the whole log's bits split at the cut as its survivors do.  Specification only.
-/
namespace Tm
namespace Seal

open Replay (survivors cancelledAt)
open Log (Entry)

theorem idx_eq_of_pairwise_lt : ∀ (es : List Entry), es.Pairwise (fun x y => x.line < y.line) →
    ∀ (j k : Nat) (x : Entry), es[j]? = some x → es[k]? = some x → j = k
  | [], _, j, _, _, hj, _ => by simp at hj
  | a :: es, hp, j, k, x, hj, hk => by
    cases j with
    | zero =>
      cases k with
      | zero => rfl
      | succ k =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hj hk
        subst hj
        have := List.rel_of_pairwise_cons hp (List.mem_of_getElem? hk)
        omega
    | succ j =>
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hj hk
        subst hk
        have := List.rel_of_pairwise_cons hp (List.mem_of_getElem? hj)
        omega
      | succ k =>
        simp only [List.getElem?_cons_succ] at hj hk
        exact congrArg (· + 1) (idx_eq_of_pairwise_lt es hp.of_cons j k x hj hk)

theorem getElem?_of_mem_zipIdx {es : List Entry} {p : Entry × Nat} (h : p ∈ es.zipIdx) : es[p.2]? = some p.1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
  rw [List.getElem?_zipIdx] at hj
  cases hjj : es[j]? with
  | none => rw [hjj] at hj; cases hj
  | some x =>
    rw [hjj] at hj
    simp only [Option.map_some, Option.some.injEq] at hj
    subst hj; simpa using hjj

/-- **An entry survives exactly when its position is not cancelled**, on distinct lines. -/
theorem mem_survivors_iff_uncancelled (es : List Entry) (hd : es.Pairwise (fun x y => x.line < y.line))
    (i : Nat) (e : Entry) (he : es[i]? = some e) : e ∈ survivors es ↔ cancelledAt es i = false := by
  rw [Replay.survivors_are_the_uncancelled_entries]
  constructor
  · intro hm
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hm
    obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
    have hpi := getElem?_of_mem_zipIdx hp1
    rw [hpe] at hpi
    have hij := idx_eq_of_pairwise_lt es hd p.2 i e hpi he
    rw [← hij]; simpa using hp2
  · intro hc
    have hmem : (e, i) ∈ es.zipIdx := by
      rw [List.mem_iff_getElem?]
      exact ⟨i, by rw [List.getElem?_zipIdx, he]; simp⟩
    exact List.mem_map.2 ⟨(e, i), List.mem_filter.2 ⟨hmem, by simp [hc]⟩, rfl⟩

end Seal
end Tm
