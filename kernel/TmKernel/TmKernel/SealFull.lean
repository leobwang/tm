import TmKernel.SealRestore
/-!
# SealFull — the whole log's fold, its keys, and the frame below the horizons (stage 5, D9, W2)

Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Effect Key)
open Log (Entry)

/-- **The replay's fold with nothing unfolded**, written as the fold over the survivors on their index. -/
theorem foldedState_nil (z : Cal.Tz) (E : List Entry) :
    foldedState z E [] = (Replay.survivors E).foldl
      (Replay.stepWith z (Replay.dayOf z (Replay.keptWakes z (Replay.wakeInstants (Replay.survivors E))))
        (Replay.KMap.get (Replay.sleptByDay z (Replay.keptWakes z (Replay.wakeInstants (Replay.survivors E)))
          (Replay.survivors E)))) (State.init E.length) := by
  have hs : foldedSurvivors E [] = Replay.survivors E := by
    unfold foldedSurvivors; rw [List.append_nil, ← Replay.survivors_are_the_uncancelled_entries]
  unfold foldedState foldedIndex
  rw [hs]
  rfl

/-! ### Keys that stay -/

/-- **A key of the days, items, last-done, dropped or done-date map is never removed by an effect.** -/
theorem applyEffect_keeps_keys (st : State) (x : Effect) :
    (∀ d, (st.days.get d).isSome → ((Replay.applyEffect st x).days.get d).isSome) ∧
    (∀ i, (st.items.get i).isSome → ((Replay.applyEffect st x).items.get i).isSome) ∧
    (∀ i, (st.lastDone.get i).isSome → ((Replay.applyEffect st x).lastDone.get i).isSome) ∧
    (∀ i, (st.dropped.get i).isSome → ((Replay.applyEffect st x).dropped.get i).isSome) ∧
    (∀ k, (st.doneDates.get k).isSome → ((Replay.applyEffect st x).doneDates.get k).isSome) := by
  cases x with
  | dayAdd d op =>
    refine ⟨fun d' h => ?_, fun i h => h, fun i h => h, fun i h => h, fun k h => h⟩
    simp only [Replay.applyEffect, Replay.HMap.get_alter]
    split
    · rename_i he; rw [← he]
      cases hg : st.days.get d' with
      | none => rw [hg] at h; cases h
      | some a => simp [Replay.DayOp.alterFn]
    · exact h
  | itemAdd i op =>
    refine ⟨fun d h => h, fun i' h => ?_, fun i h => h, fun i h => h, fun k h => h⟩
    simp only [Replay.applyEffect, Replay.HMap.get_alter]
    split
    · rename_i he; rw [← he]
      cases hg : st.items.get i' with
      | none => rw [hg] at h; cases h
      | some a => simp [Replay.ItemOp.alterFn]
    · exact h
  | itemDaySub i d m =>
    simp only [Replay.applyEffect]
    split <;> exact ⟨fun d h => h, fun i h => h, fun i h => h, fun i h => h, fun k h => h⟩
  | markDone i t =>
    refine ⟨fun d h => h, fun i h => h, fun i' h => ?_, fun i h => h, fun k h => h⟩
    simp only [Replay.applyEffect, Replay.HMap.get_alter]
    split
    · simp [Replay.lastMaxStep]; split <;> rfl
    · exact h
  | drop i =>
    refine ⟨fun d h => h, fun i h => h, fun i h => h, fun i' h => ?_, fun k h => h⟩
    simp only [Replay.applyEffect, Replay.HMap.get_alter]
    split
    · rfl
    · exact h
  | doneDate i d =>
    refine ⟨fun d h => h, fun i h => h, fun i h => h, fun i h => h, fun k h => ?_⟩
    simp only [Replay.applyEffect, Replay.HMap.get_alter]
    split
    · rfl
    · exact h
  | obs o => cases o <;> exact ⟨fun d h => h, fun i h => h, fun i h => h, fun i h => h, fun k h => h⟩
  | _ => exact ⟨fun d h => h, fun i h => h, fun i h => h, fun i h => h, fun k h => h⟩

theorem foldl_keeps_keys (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State),
      (∀ d, (st.days.get d).isSome → ((sv.foldl (Replay.stepWith z dy sl) st).days.get d).isSome) ∧
      (∀ i, (st.items.get i).isSome → ((sv.foldl (Replay.stepWith z dy sl) st).items.get i).isSome) ∧
      (∀ i, (st.lastDone.get i).isSome → ((sv.foldl (Replay.stepWith z dy sl) st).lastDone.get i).isSome) ∧
      (∀ i, (st.dropped.get i).isSome → ((sv.foldl (Replay.stepWith z dy sl) st).dropped.get i).isSome) ∧
      (∀ k, (st.doneDates.get k).isSome → ((sv.foldl (Replay.stepWith z dy sl) st).doneDates.get k).isSome)
  | [], _ => ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩
  | e :: sv, st => by
    rw [List.foldl_cons]
    have hstep : ∀ (fx : List Effect) (s : State),
        (∀ d, (s.days.get d).isSome → ((Replay.applyEffects s fx).days.get d).isSome) ∧
        (∀ i, (s.items.get i).isSome → ((Replay.applyEffects s fx).items.get i).isSome) ∧
        (∀ i, (s.lastDone.get i).isSome → ((Replay.applyEffects s fx).lastDone.get i).isSome) ∧
        (∀ i, (s.dropped.get i).isSome → ((Replay.applyEffects s fx).dropped.get i).isSome) ∧
        (∀ k, (s.doneDates.get k).isSome → ((Replay.applyEffects s fx).doneDates.get k).isSome) := by
      intro fx
      induction fx with
      | nil => intro s; exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩
      | cons x fx ih =>
        intro s
        rw [Replay.applyEffects_cons]
        obtain ⟨a1, a2, a3, a4, a5⟩ := applyEffect_keeps_keys s x
        obtain ⟨b1, b2, b3, b4, b5⟩ := ih (Replay.applyEffect s x)
        exact ⟨fun d h => b1 d (a1 d h), fun i h => b2 i (a2 i h), fun i h => b3 i (a3 i h), fun i h => b4 i (a4 i h),
          fun k h => b5 k (a5 k h)⟩
    obtain ⟨a1, a2, a3, a4, a5⟩ := hstep (Replay.effectsWith z dy sl st e) st
    obtain ⟨b1, b2, b3, b4, b5⟩ := foldl_keeps_keys z dy sl sv (Replay.stepWith z dy sl st e)
    exact ⟨fun d h => b1 d (a1 d h), fun i h => b2 i (a2 i h), fun i h => b3 i (a3 i h), fun i h => b4 i (a4 i h),
      fun k h => b5 k (a5 k h)⟩

/-! ### The frame below the horizons -/

/-- **Effects whose keys are all at or above the horizons leave every reading below them.** -/
theorem applyEffects_below (st : State) (fx : List Effect) (L H : Nat)
    (hfx : ∀ x ∈ fx, keyAtOrAbove L H x.key = true) :
    (∀ d, d < L → (Replay.applyEffects st fx).valueAt (.day d) = st.valueAt (.day d)) ∧
    (∀ i d, d < H → (Replay.applyEffects st fx).valueAt (.itemDay i d) = st.valueAt (.itemDay i d)) ∧
    (∀ i d, d < H → (Replay.applyEffects st fx).valueAt (.doneDate i d) = st.valueAt (.doneDate i d)) := by
  refine ⟨fun d hd => ?_, fun i d hd => ?_, fun i d hd => ?_⟩ <;>
  refine Replay.applyEffects_touches_only_named_keys st fx _ (fun hm => ?_) <;>
  obtain ⟨x, hx, hxk⟩ := List.mem_map.1 hm <;>
  have := hfx x hx <;> rw [hxk] at this <;> simp [keyAtOrAbove] at this <;> omega

/-- **A fold whose every step writes at or above the horizons leaves every reading below them.** -/
theorem foldl_below (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (L H : Nat) :
    ∀ (sv : List Entry) (st : State),
      (∀ (pre : List Entry) (e : Entry) (post : List Entry), sv = pre ++ e :: post →
        ∀ x ∈ Replay.effectsWith z dy sl (pre.foldl (Replay.stepWith z dy sl) st) e, keyAtOrAbove L H x.key = true) →
      (∀ d, d < L → (sv.foldl (Replay.stepWith z dy sl) st).valueAt (.day d) = st.valueAt (.day d)) ∧
      (∀ i d, d < H → (sv.foldl (Replay.stepWith z dy sl) st).valueAt (.itemDay i d) = st.valueAt (.itemDay i d)) ∧
      (∀ i d, d < H → (sv.foldl (Replay.stepWith z dy sl) st).valueAt (.doneDate i d) = st.valueAt (.doneDate i d))
  | [], _, _ => ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  | e :: sv, st, h => by
    rw [List.foldl_cons]
    have h0 := applyEffects_below st (Replay.effectsWith z dy sl st e) L H (h [] e sv rfl)
    have ih := foldl_below z dy sl L H sv (Replay.stepWith z dy sl st e) (fun pre e' post hs x hx => by
      have := h (e :: pre) e' post (by rw [hs]; rfl) x
      rw [List.foldl_cons] at this
      exact this hx)
    exact ⟨fun d hd => (ih.1 d hd).trans (h0.1 d hd), fun i d hd => (ih.2.1 i d hd).trans (h0.2.1 i d hd),
      fun i d hd => (ih.2.2 i d hd).trans (h0.2.2 i d hd)⟩

end Seal
end Tm
