import TmKernel.SealPending
/-!
# SealCutMachine — a fold's machine days are its start's or its entries' days (stage 5, D9, W2: law 6)

The days a machine can still write (`machineDays`: its pending start observation's, its last cut's and its open
interruption's) are, after a step, the step's start state's or the step's own day (`stepWith_machineDays`), so a fold's
are its start state's or one of its entries' days (`foldl_machineDays`).  The reseal's ledger day reads them.
Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Machine Effect)
open Log (Entry)

theorem closeSub_keeps (dy : Cal.Instant → Nat) (m : Machine) (t : Replay.At) :
    (Replay.closeSub dy m t).1.lastCut = m.lastCut ∧ (Replay.closeSub dy m t).1.interrupt = m.interrupt := by
  unfold Replay.closeSub
  split
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem closePause_keeps (dy : Cal.Instant → Nat) (m : Machine) (t : Replay.At) :
    (Replay.closePause dy m t).1.lastCut = m.lastCut ∧ (Replay.closePause dy m t).1.interrupt = m.interrupt := by
  unfold Replay.closePause
  split
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem cut_keeps (dy : Cal.Instant → Nat) (m : Machine) (t : Replay.At) :
    (Replay.cut dy m t).1.interrupt = m.interrupt ∧
    ((Replay.cut dy m t).1.lastCut = m.lastCut ∨ ∃ c, (Replay.cut dy m t).1.lastCut = some c ∧ c.day = dy t.1) := by
  have h1 := closeSub_keeps dy m t
  have h2 := closePause_keeps dy (Replay.closeSub dy m t).1 t
  unfold Replay.cut
  dsimp only
  split
  · exact ⟨h2.2.trans h1.2, Or.inr ⟨_, rfl, rfl⟩⟩
  · exact ⟨h2.2.trans h1.2, Or.inl (h2.1.trans h1.1)⟩

/-- **An arm's machine keeps the last cut, drops it, or cuts on the arm's stamp's day.** -/
theorem arm_lastCut (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At) (d : Nat)
    (m' : Machine) (hm : m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf?) :
    m'.lastCut = m.lastCut ∨ m'.lastCut = none ∨ ∃ c, m'.lastCut = some c ∧ c.day = dy t.1 := by
  unfold Replay.arm at hm
  cases hev : e.ev <;> simp only [hev] at hm
  case start id pred rep hsw sleptMin loc _ _ =>
    simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, List.nil_append, List.filterMap_cons,
      Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    exact Or.inr (Or.inl rfl)
  case pause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closeSub_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inl (closeSub_keeps dy m t).1
      · simp at hm
    · simp at hm
  case unpause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inl (closePause_keeps dy m t).1
      · simp at hm
    · simp at hm
  case interrupt id =>
    simp only [List.filterMap_append, (Replay.closeSub_obs dy m t).2.2, (Replay.closePause_obs dy _ t).2.2,
      List.nil_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    left
    have h1 := (closePause_keeps dy (Replay.closeSub dy m t).1 t).1
    have h2 := (closeSub_keeps dy m t).1
    split
    · exact h1.trans h2
    · exact h1.trans h2
  case resume lost dropped =>
    split at hm <;>
    · simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
      subst hm
      exact Or.inl rfl
  case stop id rem =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        rcases (cut_keeps dy m t).2 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
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
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
      · exact Or.inl rfl
  case brk p a w =>
    rw [List.filterMap_append, (Replay.dayArm_obs dy sl e t d).1, List.append_nil] at hm
    exact Or.inl (Replay.brkFx_machine dy m t _ d m' hm).1
  case brkStart pl w =>
    simp only [Effect.machineOf?, List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    exact Or.inl rfl
  all_goals rw [(Replay.dayArm_obs dy sl e t d).1] at hm; simp at hm

/-- **An arm's machine keeps the open interruption, closes it, or opens one on the arm's day.** -/
theorem arm_interrupt (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At)
    (d : Nat) (m' : Machine) (hm : m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf?) :
    m'.interrupt = m.interrupt ∨ m'.interrupt = none ∨ ∃ i, m'.interrupt = some i ∧ i.2.1 = d := by
  unfold Replay.arm at hm
  cases hev : e.ev <;> simp only [hev] at hm
  case start id pred rep hsw sleptMin loc _ _ =>
    simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, List.nil_append, List.filterMap_cons,
      Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    exact Or.inl (cut_keeps dy m t).1
  case pause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closeSub_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inl (closeSub_keeps dy m t).2
      · simp at hm
    · simp at hm
  case unpause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inl (closePause_keeps dy m t).2
      · simp at hm
    · simp at hm
  case interrupt id =>
    simp only [List.filterMap_append, (Replay.closeSub_obs dy m t).2.2, (Replay.closePause_obs dy _ t).2.2,
      List.nil_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    have h1 := (closePause_keeps dy (Replay.closeSub dy m t).1 t).2
    have h2 := (closeSub_keeps dy m t).2
    split
    · exact Or.inr (Or.inr ⟨_, rfl, rfl⟩)
    · exact Or.inl (h1.trans h2)
  case resume lost dropped =>
    split at hm
    · simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
      subst hm
      exact Or.inr (Or.inl rfl)
    · simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
      subst hm
      exact Or.inl rfl
  case stop id rem =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inl (cut_keeps dy m t).1
      · simp at hm
    · simp at hm
  case extend id by_ => simp [Effect.machineOf?] at hm
  case done id est actual went tags ci isPartial =>
    rw [doneFx_machines] at hm
    simp only [List.mem_singleton] at hm
    subst hm
    have h1 := (closePause_keeps dy (Replay.closeSub dy m t).1 t).2
    have h2 := (closeSub_keeps dy m t).2
    unfold Replay.doneClose
    split
    · split
      · exact Or.inl (h1.trans h2)
      · exact Or.inl rfl
    · split
      · split
        · exact Or.inl rfl
        · exact Or.inl rfl
      · exact Or.inl rfl
  case brk p a w =>
    rw [List.filterMap_append, (Replay.dayArm_obs dy sl e t d).1, List.append_nil] at hm
    exact Or.inl (Replay.brkFx_machine dy m t _ d m' hm).2.1
  case brkStart pl w =>
    simp only [Effect.machineOf?, List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    exact Or.inl rfl
  all_goals rw [(Replay.dayArm_obs dy sl e t d).1] at hm; simp at hm

/-- **An arm's machine keeps the running break, ends it, or opens one on the arm's day** (the owner's D105, parity
P100): a `break_start` opens it on its own day, a `break` line ends it (`Replay.brkFx_brkOpen`), and every other arm
keeps it (`Replay.cut_brkOpen`, `Replay.closeSub_brkOpen`, `Replay.closePause_brkOpen`, `Replay.doneClose_brkOpen`). -/
theorem arm_brkOpen (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At)
    (d : Nat) (m' : Machine) (hm : m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf?) :
    m'.brkOpen = m.brkOpen ∨ m'.brkOpen = none ∨ ∃ b, m'.brkOpen = some b ∧ b.day = d := by
  unfold Replay.arm at hm
  cases hev : e.ev <;> simp only [hev] at hm
  case start id pred rep hsw sleptMin loc _ _ =>
    simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, List.nil_append, List.filterMap_cons,
      Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    exact Or.inl (Replay.cut_brkOpen dy m t)
  case pause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closeSub_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inl (Replay.closeSub_brkOpen dy m t)
      · simp at hm
    · simp at hm
  case unpause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inl (Replay.closePause_brkOpen dy m t)
      · simp at hm
    · simp at hm
  case interrupt id =>
    simp only [List.filterMap_append, (Replay.closeSub_obs dy m t).2.2, (Replay.closePause_obs dy _ t).2.2,
      List.nil_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    left
    have h1 := Replay.closePause_brkOpen dy (Replay.closeSub dy m t).1 t
    have h2 := Replay.closeSub_brkOpen dy m t
    split
    · exact h1.trans h2
    · exact h1.trans h2
  case resume lost dropped =>
    split at hm <;>
    · simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
      subst hm
      exact Or.inl rfl
  case stop id rem =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inl (Replay.cut_brkOpen dy m t)
      · simp at hm
    · simp at hm
  case extend id by_ => simp [Effect.machineOf?] at hm
  case done id est actual went tags ci isPartial =>
    rw [doneFx_machines] at hm
    simp only [List.mem_singleton] at hm
    subst hm
    exact Or.inl (Replay.doneClose_brkOpen dy m t id actual.val went)
  case brk p a w =>
    rw [List.filterMap_append, (Replay.dayArm_obs dy sl e t d).1, List.append_nil] at hm
    exact Or.inr (Or.inl (Replay.brkFx_brkOpen dy m t _ d m' hm))
  case brkStart pl w =>
    simp only [Effect.machineOf?, List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    exact Or.inr (Or.inr ⟨_, rfl, rfl⟩)
  all_goals rw [(Replay.dayArm_obs dy sl e t d).1] at hm; simp at hm

theorem stepWith_machine_eq (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) :
    (Replay.stepWith z dy sl st e).machine
      = (((Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf?).getLast?).getD
          st.machine := by
  obtain ⟨-, -, h3⟩ := Replay.applyEffects_obs (Replay.effectsWith z dy sl st e) st
  have hfx : (Replay.effectsWith z dy sl st e).filterMap Effect.machineOf?
      = (Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf? := by
    unfold Replay.effectsWith
    simp [List.filterMap_cons, List.filterMap_append, Effect.machineOf?,
      (Replay.completionArm_obs z e (e.t.val, e.off.val) (dy e.t.val)).2.2]
  unfold Replay.stepWith
  rw [h3, hfx]

/-- **A step's machine days are its start state's or the step's day.** -/
theorem stepWith_machineDays (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry)
    (x : Nat) (hx : x ∈ machineDays (Replay.stepWith z dy sl st e).machine) :
    x ∈ machineDays st.machine ∨ x = dy e.t.val := by
  rw [stepWith_machine_eq] at hx
  cases hl : ((Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf?).getLast? with
  | none => rw [hl] at hx; exact Or.inl hx
  | some m' =>
    rw [hl, Option.getD_some] at hx
    have hm := List.mem_of_getLast? hl
    unfold machineDays at hx ⊢
    simp only [List.mem_append, Option.mem_toList, Option.mem_def, Option.map_eq_some_iff] at hx ⊢
    rcases hx with ((⟨o, ho, rfl⟩ | ⟨c, hc, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨b, hb, rfl⟩
    · rcases arm_pending dy sl st.machine e _ _ m' hm with h | h | ⟨o', h, hd⟩
      · rw [h] at ho; exact Or.inl (Or.inl (Or.inl (Or.inl ⟨o, ho, rfl⟩)))
      · rw [h] at ho; cases ho
      · rw [h] at ho; cases ho; exact Or.inr hd
    · rcases arm_lastCut dy sl st.machine e _ _ m' hm with h | h | ⟨c', h, hd⟩
      · rw [h] at hc; exact Or.inl (Or.inl (Or.inl (Or.inr ⟨c, hc, rfl⟩)))
      · rw [h] at hc; cases hc
      · rw [h] at hc; cases hc; exact Or.inr hd
    · rcases arm_interrupt dy sl st.machine e _ _ m' hm with h | h | ⟨i', h, hd⟩
      · rw [h] at hi; exact Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩))
      · rw [h] at hi; cases hi
      · rw [h] at hi; cases hi; exact Or.inr hd
    · rcases arm_brkOpen dy sl st.machine e _ _ m' hm with h | h | ⟨b', h, hd⟩
      · rw [h] at hb; exact Or.inl (Or.inr ⟨b, hb, rfl⟩)
      · rw [h] at hb; cases hb
      · rw [h] at hb; cases hb; exact Or.inr hd

/-- **A fold's machine days are its start state's or one of its entries' days.** -/
theorem foldl_machineDays (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State) (x : Nat), x ∈ machineDays (sv.foldl (Replay.stepWith z dy sl) st).machine →
      x ∈ machineDays st.machine ∨ ∃ e ∈ sv, x = dy e.t.val
  | [], _, _, h => Or.inl h
  | e :: sv, st, x, h => by
    rw [List.foldl_cons] at h
    rcases foldl_machineDays z dy sl sv _ x h with h' | ⟨e', he', hd⟩
    · rcases stepWith_machineDays z dy sl st e x h' with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨e, List.mem_cons_self, h1⟩
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hd⟩

end Seal
end Tm
