import TmKernel.SealResume
/-! # Mask helpers: erasing the first match under a filter, and the tags a checkpoint keeps (W2) -/
namespace Tm
namespace Seal

open Log (Entry)

theorem eraseP_filter_of_first {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x, l.find? p = some x → q x = true) → (l.eraseP p).filter q = (l.filter q).eraseP p
  | [], _ => rfl
  | a :: t, h => by
    by_cases hpa : p a = true
    · have hqa : q a = true := h a (by simp [List.find?_cons, hpa])
      rw [List.eraseP_cons_of_pos hpa, List.filter_cons_of_pos hqa, List.eraseP_cons_of_pos hpa]
    · have hpa' : p a = false := by simpa using hpa
      have ht : ∀ x, t.find? p = some x → q x = true := fun x hx => h x (by simp [List.find?_cons, hpa', hx])
      rw [List.eraseP_cons_of_neg (by simpa using hpa)]
      by_cases hqa : q a = true
      · rw [List.filter_cons_of_pos hqa, List.filter_cons_of_pos hqa, List.eraseP_cons_of_neg (by simpa using hpa),
          eraseP_filter_of_first p q t ht]
      · rw [List.filter_cons_of_neg (by simpa using hqa), List.filter_cons_of_neg (by simpa using hqa),
          eraseP_filter_of_first p q t ht]

theorem eraseP_filter_of_first_not {α : Type} (p q : α → Bool) :
    ∀ (l : List α) (x : α), l.find? p = some x → q x = false → (l.eraseP p).filter q = l.filter q
  | [], _, h, _ => by cases h
  | a :: t, x, h, hq => by
    by_cases hpa : p a = true
    · simp only [List.find?_cons, hpa, Option.some.injEq] at h
      subst h
      rw [List.eraseP_cons_of_pos hpa, List.filter_cons_of_neg (by simpa using hq)]
    · have hpa' : p a = false := by simpa using hpa
      simp only [List.find?_cons, hpa'] at h
      rw [List.eraseP_cons_of_neg (by simpa using hpa)]
      by_cases hqa : q a = true
      · rw [List.filter_cons_of_pos hqa, List.filter_cons_of_pos hqa, eraseP_filter_of_first_not p q t x h hq]
      · rw [List.filter_cons_of_neg (by simpa using hqa), List.filter_cons_of_neg (by simpa using hqa),
          eraseP_filter_of_first_not p q t x h hq]

/-- **Every folded survivor's tag is kept, or it is unknown and the checkpoint overflowed** (G1's premise). -/
theorem tag_kept_or_overflow (sv : List Entry) (e : Entry) (he : e ∈ sv) :
    (keptTags sv).any (fun p => p.1 == e.ev.tag) = true ∨
      (!Log.isKnownTag e.ev.tag && decide ((keptTags sv).length < (tagLines sv).length)) = true := by
  have hmem : e.ev.tag ∈ canon idLt (sv.map (·.ev.tag)) :=
    (mem_canon idLt_strictTotal _ _).2 (List.mem_map.2 ⟨e, he, rfl⟩)
  let pr := (e.ev.tag, (sv.filter (fun x => decide (x.ev.tag = e.ev.tag))).foldl (fun _ x => x.line) 0)
  have hpr : pr ∈ tagLines sv := List.mem_map.2 ⟨e.ev.tag, hmem, rfl⟩
  unfold keptTags
  simp only
  by_cases hk : (Log.isKnownTag pr.1 || (((tagLines sv).filter (fun p => !Log.isKnownTag p.1 && decide (p.1.length ≤ maxTagChars))).take
      maxUnknownTags).contains pr) = true
  · left
    rw [List.any_eq_true]
    exact ⟨pr, List.mem_filter.2 ⟨hpr, hk⟩, by simp [pr]⟩
  · right
    have hknown : Log.isKnownTag e.ev.tag = false := by
      simp only [Bool.or_eq_true, not_or] at hk
      simpa [pr] using hk.1
    simp only [hknown, Bool.not_false, Bool.true_and, decide_eq_true_eq]
    have hlen : ((tagLines sv).filter (fun p => Log.isKnownTag p.1 ||
        (((tagLines sv).filter (fun p => !Log.isKnownTag p.1 && decide (p.1.length ≤ maxTagChars))).take maxUnknownTags).contains p)).length
        < (tagLines sv).length := by
      apply List.length_filter_lt_length_iff_exists.2
      exact ⟨pr, hpr, by simpa using hk⟩
    exact hlen

end Seal
end Tm
