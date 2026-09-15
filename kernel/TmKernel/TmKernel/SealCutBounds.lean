import TmKernel.SealLaw6Pair
import TmKernel.SealLaw5A
/-!
# SealCutBounds — the resealed `maxT` and `futureFloor` (stage 5, D9, W2: law 6)

The latest non-future instant of the folded lines and the fold point's tail is the later of the stored one and the
tail's, once the stored checkpoint's classification holds at `T` (`migrationOk`); the earliest future one likewise.
Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Log (Entry)

theorem instant_antisymm {a b : Cal.Instant} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  cases a; cases b
  rw [Cal.Instant.le_iff] at h₁ h₂
  simp only at h₁ h₂
  simp only [Cal.Instant.mk.injEq]
  omega

theorem maxInstant?_some_of_ne_nil (l : List Cal.Instant) (h : l ≠ []) : ∃ m, maxInstant? l = some m := by
  cases hm : maxInstant? l with
  | none => exact absurd (maxInstant?_none l hm) h
  | some m => exact ⟨m, rfl⟩

theorem minInstant?_some_of_ne_nil (l : List Cal.Instant) (h : l ≠ []) : ∃ m, minInstant? l = some m := by
  cases hm : minInstant? l with
  | none => exact absurd (minInstant?_none l hm) h
  | some m => exact ⟨m, rfl⟩

theorem maxInstant?_append (X Y : List Cal.Instant) :
    maxInstant? (X ++ Y) = maxOptI (maxInstant? X) (maxInstant? Y) := by
  cases hX : maxInstant? X with
  | none =>
    rw [maxInstant?_none X hX, List.nil_append]
    cases maxInstant? Y <;> rfl
  | some a =>
    cases hY : maxInstant? Y with
    | none => rw [maxInstant?_none Y hY, List.append_nil, hX]; rfl
    | some b =>
      have ha := maxInstant?_mem X a hX
      obtain ⟨m, hm⟩ := maxInstant?_some_of_ne_nil (X ++ Y) (fun h => by
        have := List.append_eq_nil_iff.1 h; rw [this.1] at ha; cases ha)
      rw [hm]
      have hmm := maxInstant?_mem _ m hm
      have hmub := maxInstant?_spec _ m hm
      have hXub := maxInstant?_spec X a hX
      have hYub := maxInstant?_spec Y b hY
      have hb := maxInstant?_mem Y b hY
      show some m = some (if a < b then b else a)
      congr 1
      split
      · rename_i hab
        refine instant_antisymm (?_) (hmub b (List.mem_append_right _ hb))
        rcases List.mem_append.1 hmm with h | h
        · exact Replay.instant_le_trans (hXub m h) (Replay.instant_le_of_lt hab)
        · exact hYub m h
      · rename_i hab
        refine instant_antisymm (?_) (hmub a (List.mem_append_left _ ha))
        rcases List.mem_append.1 hmm with h | h
        · exact hXub m h
        · refine Replay.instant_le_trans (hYub m h) ?_
          rw [Cal.Instant.le_iff]; rw [Cal.Instant.lt_iff] at hab; omega

theorem minInstant?_append (X Y : List Cal.Instant) :
    minInstant? (X ++ Y) = minOptI (minInstant? X) (minInstant? Y) := by
  cases hX : minInstant? X with
  | none =>
    rw [minInstant?_none X hX, List.nil_append]
    cases minInstant? Y <;> rfl
  | some a =>
    cases hY : minInstant? Y with
    | none => rw [minInstant?_none Y hY, List.append_nil, hX]; rfl
    | some b =>
      have ha := minInstant?_mem X a hX
      obtain ⟨m, hm⟩ := minInstant?_some_of_ne_nil (X ++ Y) (fun h => by
        have := List.append_eq_nil_iff.1 h; rw [this.1] at ha; cases ha)
      rw [hm]
      have hmm := minInstant?_mem _ m hm
      have hmlb := minInstant?_spec _ m hm
      have hXlb := minInstant?_spec X a hX
      have hYlb := minInstant?_spec Y b hY
      have hb := minInstant?_mem Y b hY
      show some m = some (if b < a then b else a)
      congr 1
      split
      · rename_i hab
        refine instant_antisymm (hmlb b (List.mem_append_right _ hb)) ?_
        rcases List.mem_append.1 hmm with h | h
        · exact Replay.instant_le_trans (Replay.instant_le_of_lt hab) (hXlb m h)
        · exact hYlb m h
      · rename_i hab
        refine instant_antisymm (hmlb a (List.mem_append_left _ ha)) ?_
        rcases List.mem_append.1 hmm with h | h
        · exact hXlb m h
        · refine Replay.instant_le_trans ?_ (hYlb m h)
          rw [Cal.Instant.le_iff]; rw [Cal.Instant.lt_iff] at hab; omega

/-- **The classification holds at `T`**: under `migrationOk`, every folded instant is future at `T` exactly when it is
at `T₀`. -/
theorem isFuture_migrates (T₀ T : Nat) (QA : List Cal.Instant) (K : Ckpt)
    (hmaxT : K.maxT = maxInstant? (QA.filter (fun q => !isFuture T₀ q)))
    (hff : K.futureFloor = minInstant? (QA.filter (isFuture T₀))) (hmig : migrationOk K T = true) :
    ∀ q ∈ QA, isFuture T q = isFuture T₀ q := by
  unfold migrationOk at hmig
  simp only [Bool.and_eq_true] at hmig
  obtain ⟨hm, hf⟩ := hmig
  intro q hq
  cases hq0 : isFuture T₀ q
  · have hmem : q ∈ QA.filter (fun q => !isFuture T₀ q) := List.mem_filter.2 ⟨hq, by simp [hq0]⟩
    obtain ⟨m, hmx⟩ := maxInstant?_some_of_ne_nil _ (List.ne_nil_of_mem hmem)
    have hqm := maxInstant?_spec _ m hmx q hmem
    rw [← hmaxT] at hmx
    rw [hmx] at hm
    simp only [Option.all_some, Bool.not_eq_true', isFuture, decide_eq_false_iff_not] at hm
    simp only [isFuture, decide_eq_false_iff_not]
    rw [Cal.Instant.le_iff] at hqm
    omega
  · have hmem : q ∈ QA.filter (isFuture T₀) := List.mem_filter.2 ⟨hq, hq0⟩
    obtain ⟨f, hfx⟩ := minInstant?_some_of_ne_nil _ (List.ne_nil_of_mem hmem)
    have hfq := minInstant?_spec _ f hfx q hmem
    rw [← hff] at hfx
    rw [hfx] at hf
    simp only [Option.all_some, isFuture, decide_eq_true_eq] at hf
    simp only [isFuture, decide_eq_true_eq]
    rw [Cal.Instant.le_iff] at hfq
    omega

/-- **The resealed `maxT`** is the checkpoint of the fold point's (§9.4 (iii)'s `maxT'`). -/
theorem resealed_maxT (T₀ T : Nat) (QA QB : List Cal.Instant) (K : Ckpt)
    (hmaxT : K.maxT = maxInstant? (QA.filter (fun q => !isFuture T₀ q)))
    (hff : K.futureFloor = minInstant? (QA.filter (isFuture T₀))) (hmig : migrationOk K T = true) :
    maxOptI K.maxT (maxInstant? (QB.filter (fun q => !isFuture T q)))
      = maxInstant? ((QA ++ QB).filter (fun q => !isFuture T q)) := by
  have hfe : QA.filter (fun q => !isFuture T q) = QA.filter (fun q => !isFuture T₀ q) :=
    List.filter_congr (fun q hq => by rw [isFuture_migrates T₀ T QA K hmaxT hff hmig q hq])
  rw [List.filter_append, maxInstant?_append, hfe, ← hmaxT]

/-- **The resealed `futureFloor`.** -/
theorem resealed_futureFloor (T₀ T : Nat) (QA QB : List Cal.Instant) (K : Ckpt)
    (hmaxT : K.maxT = maxInstant? (QA.filter (fun q => !isFuture T₀ q)))
    (hff : K.futureFloor = minInstant? (QA.filter (isFuture T₀))) (hmig : migrationOk K T = true) :
    minOptI K.futureFloor (minInstant? (QB.filter (isFuture T)))
      = minInstant? ((QA ++ QB).filter (isFuture T)) := by
  have hfe : QA.filter (isFuture T) = QA.filter (isFuture T₀) :=
    List.filter_congr (fun q hq => by rw [isFuture_migrates T₀ T QA K hmaxT hff hmig q hq])
  rw [List.filter_append, minInstant?_append, hfe, ← hff]

end Seal
end Tm
