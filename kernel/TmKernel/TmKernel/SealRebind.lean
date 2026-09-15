import TmKernel.SealResume
/-!
# SealRebind — late binding commutes with the fold (stage 5, D9, W2)

A fold's non-start energy observations read `slept_by_day` when emitted; rebinding them afterwards to another table is
folding with that table (`foldl_rebind`).  So a checkpoint's observations, bound by the folded lines' table, rebind to
the whole log's.  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Machine Effect EnergyObs)
open Log (Entry)

/-- An effect with its energy observation rebound. -/
def Effect.rebind (g : Nat → Option Nat) : Effect → Effect
  | .obs (.energy o) => .obs (.energy (rebindObs g o))
  | x => x

theorem applyEffect_rebind (g : Nat → Option Nat) (st : State) (x : Effect) :
    Replay.applyEffect (rebindState g st) (Effect.rebind g x) = rebindState g (Replay.applyEffect st x) := by
  cases x with
  | obs o => cases o <;> rfl
  | itemDaySub i d m =>
    simp only [Effect.rebind, Replay.applyEffect, rebindState]
    split <;> rfl
  | _ => rfl

theorem applyEffects_rebind (g : Nat → Option Nat) : ∀ (fx : List Effect) (st : State),
    Replay.applyEffects (rebindState g st) (fx.map (Effect.rebind g)) = rebindState g (Replay.applyEffects st fx)
  | [], _ => rfl
  | x :: fx, st => by
    rw [List.map_cons, Replay.applyEffects_cons, Replay.applyEffects_cons, applyEffect_rebind]
    exact applyEffects_rebind g fx _

theorem rebind_of_sleptOk (g : Nat → Option Nat) (x : Effect) (h : x.sleptOk g = true) : Effect.rebind g x = x := by
  cases x with
  | obs o =>
    cases o with
    | energy o =>
      simp only [Replay.Effect.sleptOk, Bool.or_eq_true, decide_eq_true_eq] at h
      simp only [Effect.rebind, rebindObs]
      rcases h with h | h
      · simp [h]
      · by_cases hf : o.fromStart = true
        · simp [hf]
        · obtain ⟨_, _, _, _, _, _, _, _, _, _, fs⟩ := o
          simp only at hf h ⊢
          simp [hf, ← h]
    | duration o => rfl
  | _ => rfl

theorem map_rebind_of_all (g : Nat → Option Nat) (fx : List Effect) (h : fx.all (Effect.sleptOk g) = true) :
    fx.map (Effect.rebind g) = fx := by
  rw [List.all_eq_true] at h
  conv => rhs; rw [← List.map_id fx]
  exact List.map_congr_left (fun x hx => rebind_of_sleptOk g x (h x hx))

/-- Only an `energy` line's arm reads `slept_by_day`. -/
theorem arm_sl (dy : Cal.Instant → Nat) (sl sl' : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At) (d : Nat)
    (h : ∀ pred rep hsw loc, e.ev ≠ .energy pred rep hsw loc) :
    Replay.arm dy sl m e t d = Replay.arm dy sl' m e t d := by
  unfold Replay.arm Replay.dayArm
  cases hev : e.ev <;> simp only
  case energy pred rep hsw loc => exact absurd hev (h _ _ _ _)

/-- A state whose open block's pending observation is a start's (C5's `SleptInv`, its second half). -/
def PendingStart (st : State) : Prop := ∀ o, st.machine.block.bind (·.obs) = some o → o.fromStart = true

theorem effectsWith_machine (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st₁ st₂ : State) (e : Entry)
    (h : st₁.machine = st₂.machine) : Replay.effectsWith z dy sl st₁ e = Replay.effectsWith z dy sl st₂ e := by
  unfold Replay.effectsWith; rw [h]

/-- **Rebinding a step's effects to `sl` is stepping with `sl`.** -/
theorem effectsWith_rebind (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl sl' : Nat → Option Nat) (st : State) (e : Entry)
    (hp : PendingStart st) :
    (Replay.effectsWith z dy sl' st e).map (Effect.rebind sl) = Replay.effectsWith z dy sl st e := by
  have harm : (Replay.arm dy sl' st.machine e (e.t.val, e.off.val) (dy e.t.val)).map (Effect.rebind sl)
      = Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val) := by
    by_cases he : ∃ pred rep hsw loc, e.ev = .energy pred rep hsw loc
    · obtain ⟨pred, rep, hsw, loc, hev⟩ := he
      unfold Replay.arm Replay.dayArm
      simp [hev, Effect.rebind, rebindObs]
    · have hn : ∀ pred rep hsw loc, e.ev ≠ .energy pred rep hsw loc := fun a b c d' h => he ⟨a, b, c, d', h⟩
      rw [arm_sl dy sl' sl st.machine e _ _ hn]
      exact map_rebind_of_all sl _ (Replay.arm_sleptOk dy sl st.machine e _ _ hp)
  unfold Replay.effectsWith
  simp only [List.map_cons, List.map_append, Effect.rebind]
  rw [map_rebind_of_all sl _ (Replay.completionArm_sleptOk sl z e _ _), harm]

theorem pendingStart_step (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry)
    (hp : PendingStart st) : PendingStart (Replay.stepWith z dy sl st e) := by
  have hall : (Replay.effectsWith z dy sl st e).all (Effect.sleptOk sl) = true := by
    unfold Replay.effectsWith
    simp only [List.all_cons, List.all_append, Replay.arm_sleptOk dy sl st.machine e _ _ hp,
      Replay.completionArm_sleptOk, Bool.and_true]
    rfl
  intro o ho
  obtain ⟨-, -, h3⟩ := Replay.applyEffects_obs (Replay.effectsWith z dy sl st e) st
  unfold Replay.stepWith at ho
  rw [h3] at ho
  cases hl : ((Replay.effectsWith z dy sl st e).filterMap Effect.machineOf?).getLast? with
  | none => rw [hl] at ho; exact hp o ho
  | some m =>
    rw [hl, Option.getD_some] at ho
    have hm := List.mem_of_getLast? hl
    obtain ⟨x, hx, hxm⟩ := List.mem_filterMap.1 hm
    cases x with
    | machine m0 =>
      simp only [Effect.machineOf?, Option.some.injEq] at hxm
      subst hxm
      have := (List.all_eq_true.1 hall) _ hx
      simp only [Replay.Effect.sleptOk] at this
      cases hb : m0.block.bind (·.obs) with
      | none => rw [hb] at ho; cases ho
      | some o' => rw [hb] at ho this; cases ho; simpa using this
    | _ => simp [Effect.machineOf?] at hxm

/-- **Stepping a rebound state with `sl` is rebinding the step with any table.** -/
theorem stepWith_rebind (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl sl' : Nat → Option Nat) (st : State) (e : Entry)
    (hp : PendingStart st) :
    Replay.stepWith z dy sl (rebindState sl st) e = rebindState sl (Replay.stepWith z dy sl' st e) := by
  unfold Replay.stepWith
  rw [effectsWith_machine z dy sl (rebindState sl st) st e rfl, ← effectsWith_rebind z dy sl sl' st e hp,
    applyEffects_rebind]

theorem foldl_rebind (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl sl' : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State), PendingStart st →
      sv.foldl (Replay.stepWith z dy sl) (rebindState sl st) = rebindState sl (sv.foldl (Replay.stepWith z dy sl') st)
  | [], _, _ => rfl
  | e :: sv, st, hp => by
    rw [List.foldl_cons, List.foldl_cons, stepWith_rebind z dy sl sl' st e hp]
    exact foldl_rebind z dy sl sl' sv _ (pendingStart_step z dy sl' st e hp)

theorem pendingStart_foldl (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State), PendingStart st → PendingStart (sv.foldl (Replay.stepWith z dy sl) st)
  | [], _, h => h
  | e :: sv, st, h => pendingStart_foldl z dy sl sv _ (pendingStart_step z dy sl st e h)

theorem rebind_rebind (g g' : Nat → Option Nat) (st : State) :
    rebindState g (rebindState g' st) = rebindState g st := by
  simp only [rebindState, List.map_map]
  congr 2
  funext o
  simp only [Function.comp_apply, rebindObs]
  by_cases h : o.fromStart = true <;> simp [h]

end Seal
end Tm
