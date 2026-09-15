import TmKernel.SealResume
/-! # The folded instants' latest and earliest (stage 5, D9, W2) -/
namespace Tm
namespace Seal

theorem instant_lt_or_le (a b : Cal.Instant) : a < b ∨ b ≤ a := by
  rw [Cal.Instant.lt_iff, Cal.Instant.le_iff]; omega

theorem foldl_max_spec : ∀ (l : List Cal.Instant) (acc : Option Cal.Instant) (m : Cal.Instant),
    l.foldl (fun acc t => some (match acc with | none => t | some a => if a < t then t else a)) acc = some m →
      (∀ x ∈ l, x ≤ m) ∧ (∀ a, acc = some a → a ≤ m)
  | [], acc, m, h => ⟨(fun _ hx => by cases hx), (fun a ha => by rw [ha] at h; cases h; exact Replay.instant_le_refl _)⟩
  | t :: l, acc, m, h => by
    rw [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := foldl_max_spec l _ m h
    have hnew := h2 _ rfl
    refine ⟨fun x hx => ?_, fun a ha => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · cases acc with
        | none => exact hnew
        | some a =>
          simp only at hnew
          split at hnew
          · exact hnew
          · rename_i hlt
            rcases instant_lt_or_le a x with h' | h'
            · exact absurd h' hlt
            · exact Replay.instant_le_trans h' hnew
      · exact h1 x hx
    · subst ha
      simp only at hnew
      split at hnew
      · rename_i hlt; exact Replay.instant_le_trans (Replay.instant_le_of_lt hlt) hnew
      · exact hnew

theorem maxInstant?_spec (l : List Cal.Instant) (m : Cal.Instant) (h : maxInstant? l = some m) : ∀ x ∈ l, x ≤ m :=
  (foldl_max_spec l none m h).1

theorem maxInstant?_none (l : List Cal.Instant) (h : maxInstant? l = none) : l = [] := by
  cases l with
  | nil => rfl
  | cons t l =>
    unfold maxInstant? at h
    rw [List.foldl_cons] at h
    have : ∀ (l : List Cal.Instant) (a : Cal.Instant),
        l.foldl (fun acc t => some (match acc with | none => t | some a => if a < t then t else a)) (some a) ≠ none := by
      intro l; induction l with
      | nil => intro a; simp
      | cons x xs ih => intro a; rw [List.foldl_cons]; exact ih _
    exact absurd h (this l _)

theorem foldl_min_spec : ∀ (l : List Cal.Instant) (acc : Option Cal.Instant) (f : Cal.Instant),
    l.foldl (fun acc t => some (match acc with | none => t | some a => if t < a then t else a)) acc = some f →
      (∀ x ∈ l, f ≤ x) ∧ (∀ a, acc = some a → f ≤ a)
  | [], acc, f, h => ⟨(fun _ hx => by cases hx), (fun a ha => by rw [ha] at h; cases h; exact Replay.instant_le_refl _)⟩
  | t :: l, acc, f, h => by
    rw [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := foldl_min_spec l _ f h
    have hnew := h2 _ rfl
    refine ⟨fun x hx => ?_, fun a ha => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · cases acc with
        | none => exact hnew
        | some a =>
          simp only at hnew
          split at hnew
          · exact hnew
          · rename_i hlt
            rcases instant_lt_or_le x a with h' | h'
            · exact absurd h' hlt
            · exact Replay.instant_le_trans hnew h'
      · exact h1 x hx
    · subst ha
      simp only at hnew
      split at hnew
      · rename_i hlt; exact Replay.instant_le_trans hnew (Replay.instant_le_of_lt hlt)
      · exact hnew

theorem minInstant?_spec (l : List Cal.Instant) (f : Cal.Instant) (h : minInstant? l = some f) : ∀ x ∈ l, f ≤ x :=
  (foldl_min_spec l none f h).1

theorem minInstant?_none (l : List Cal.Instant) (h : minInstant? l = none) : l = [] := by
  cases l with
  | nil => rfl
  | cons t l =>
    unfold minInstant? at h
    rw [List.foldl_cons] at h
    have : ∀ (l : List Cal.Instant) (a : Cal.Instant),
        l.foldl (fun acc t => some (match acc with | none => t | some a => if t < a then t else a)) (some a) ≠ none := by
      intro l; induction l with
      | nil => intro a; simp
      | cons x xs ih => intro a; rw [List.foldl_cons]; exact ih _
    exact absurd h (this l _)

/-- **G2's two instants bound every folded instant**: a tail wake after the latest non-future one and inside the fence
of the earliest future one is after every non-future folded instant and three days before every future one. -/
theorem sep_of_bounds (T₀ : Nat) (QA : List Cal.Instant) (w : Cal.Instant)
    (hm : ∀ m, maxInstant? (QA.filter (fun q => !isFuture T₀ q)) = some m → m < w)
    (hf : ∀ f, minInstant? (QA.filter (isFuture T₀)) = some f → w.sec + fenceSec < f.sec) :
    ∀ q ∈ QA, ((fun q => !isFuture T₀ q) q = true → q < w) ∧
      ((fun q => !isFuture T₀ q) q = false → w.sec + fenceSec < q.sec) := by
  intro q hq
  refine ⟨fun hP => ?_, fun hP => ?_⟩
  · have hmem : q ∈ QA.filter (fun q => !isFuture T₀ q) := List.mem_filter.2 ⟨hq, hP⟩
    cases hmx : maxInstant? (QA.filter (fun q => !isFuture T₀ q)) with
    | none => rw [maxInstant?_none _ hmx] at hmem; cases hmem
    | some m =>
      have hle := maxInstant?_spec _ m hmx q hmem
      have hlt := hm m hmx
      rw [Cal.Instant.le_iff] at hle; rw [Cal.Instant.lt_iff] at hlt ⊢; omega
  · have hmem : q ∈ QA.filter (isFuture T₀) := List.mem_filter.2 ⟨hq, by simpa using hP⟩
    cases hmn : minInstant? (QA.filter (isFuture T₀)) with
    | none => rw [minInstant?_none _ hmn] at hmem; cases hmem
    | some f =>
      have hle := minInstant?_spec _ f hmn q hmem
      have hlt := hf f hmn
      rw [Cal.Instant.le_iff] at hle; omega

end Seal
end Tm
