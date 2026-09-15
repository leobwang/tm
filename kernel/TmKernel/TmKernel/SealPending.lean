import TmKernel.SealStep
/-!
# SealPending — a step's pending start observation is the old one, none, or on the step's day (stage 5, D9, W2)

Law 4 reads a day record below the ledger day through `OpenDay.finish`, which emits the machine's pending start
observation on its day.  A step keeps the open block's observation, closes it, or opens one on its own day
(`arm_pending`), so a fold's pending observation is its start state's or on one of its entries' days
(`foldl_pending`).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Machine Effect)
open Log (Entry)

theorem pending_none_of_pendLines (m : Machine) (h : Replay.pendLines m = []) : m.block.bind (·.obs) = none := by
  unfold Replay.pendLines at h
  cases hb : m.block.bind (·.obs) with
  | none => rfl
  | some o => rw [hb] at h; simp at h

/-- **An arm's machine keeps the pending observation, drops it, or holds one on the arm's day.** -/
theorem arm_pending (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At) (d : Nat)
    (m' : Machine) (hm : m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf?) :
    m'.block.bind (·.obs) = m.block.bind (·.obs) ∨ m'.block.bind (·.obs) = none ∨
      ∃ o, m'.block.bind (·.obs) = some o ∧ o.day = d := by
  unfold Replay.arm at hm
  cases hev : e.ev <;> simp only [hev] at hm
  case start id pred rep hsw sleptMin loc _ _ =>
    simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, List.nil_append, List.filterMap_cons,
      Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    right
    cases rep with
    | none => left; rfl
    | some rp => right; exact ⟨_, rfl, rfl⟩
  case pause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closeSub_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        left
        rw [← Replay.closeSub_pending dy m t]
        cases (Replay.closeSub dy m t).1.block <;> rfl
      · simp at hm
    · simp at hm
  case unpause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        left
        rw [← Replay.closePause_pending dy m t]
        cases (Replay.closePause dy m t).1.block <;> rfl
      · simp at hm
    · simp at hm
  case interrupt id =>
    simp only [List.filterMap_append, (Replay.closeSub_obs dy m t).2.2, (Replay.closePause_obs dy _ t).2.2,
      List.nil_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    left
    have h1 := Replay.closePause_pending dy (Replay.closeSub dy m t).1 t
    have h2 := Replay.closeSub_pending dy m t
    split
    · exact h1.trans h2
    · exact h1.trans h2
  case resume lost dropped =>
    split at hm <;>
    · simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
      subst hm
      left
      show (m.block.map (Replay.resumeBlock · t)).bind (·.obs) = m.block.bind (·.obs)
      cases m.block with
      | none => rfl
      | some b => exact Replay.resumeBlock_obs b t
  case stop id rem =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inr (Or.inl (pending_none_of_pendLines _ (Replay.cut_obs dy m t).2.2.2))
      · simp at hm
    · simp at hm
  case extend id by_ => simp [Effect.machineOf?] at hm
  case done id est actual went tags ci isPartial =>
    rw [doneFx_machines] at hm
    simp only [List.mem_singleton] at hm
    subst hm
    unfold Replay.doneClose
    split
    · split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · split
      · split
        · exact Or.inl rfl
        · exact Or.inl rfl
      · exact Or.inl rfl
  all_goals rw [(Replay.dayArm_obs dy sl e t d).1] at hm; simp at hm

/-- **A step's pending observation is its start's, none, or on the step's day.** -/
theorem stepWith_pending (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) :
    (Replay.stepWith z dy sl st e).machine.block.bind (·.obs) = st.machine.block.bind (·.obs) ∨
    (Replay.stepWith z dy sl st e).machine.block.bind (·.obs) = none ∨
    ∃ o, (Replay.stepWith z dy sl st e).machine.block.bind (·.obs) = some o ∧ o.day = dy e.t.val := by
  obtain ⟨-, -, h3⟩ := Replay.applyEffects_obs (Replay.effectsWith z dy sl st e) st
  have hfx : (Replay.effectsWith z dy sl st e).filterMap Effect.machineOf?
      = (Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf? := by
    unfold Replay.effectsWith
    simp [List.filterMap_cons, List.filterMap_append, Effect.machineOf?,
      (Replay.completionArm_obs z e (e.t.val, e.off.val) (dy e.t.val)).2.2]
  unfold Replay.stepWith
  rw [h3, hfx]
  cases hl : ((Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf?).getLast? with
  | none => exact Or.inl rfl
  | some m' =>
    rw [Option.getD_some]
    exact arm_pending dy sl st.machine e _ _ m' (List.mem_of_getLast? hl)

/-- **A fold's pending observation is its start state's, or on one of its entries' days.** -/
theorem foldl_pending (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State) (o : Replay.EnergyObs),
      (sv.foldl (Replay.stepWith z dy sl) st).machine.block.bind (·.obs) = some o →
        st.machine.block.bind (·.obs) = some o ∨ ∃ e ∈ sv, o.day = dy e.t.val
  | [], _, _, h => Or.inl h
  | e :: sv, st, o, h => by
    rw [List.foldl_cons] at h
    rcases foldl_pending z dy sl sv _ o h with h' | ⟨e', he', hd⟩
    · rcases stepWith_pending z dy sl st e with h1 | h1 | ⟨o', h1, h2⟩
      · rw [h1] at h'; exact Or.inl h'
      · rw [h1] at h'; cases h'
      · rw [h1] at h'
        cases h'
        exact Or.inr ⟨e, List.mem_cons_self, h2⟩
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hd⟩

end Seal
end Tm
