import TmKernel.SealRebind
/-!
# SealAgree — two states that agree at and above the horizons step alike there (stage 5, D9, W2)

`AgreeAbove L H x y`: every day reading at `d ≥ L`, every window reading at `d ≥ H`, and every all-time reading agree,
maps through `get` (whatever their bucket counts) and lists day by day.  Applying one effect to both keeps it
(`AgreeAbove.apply`), whatever key the effect names: a write below the horizons changes nothing the relation reads.
Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Effect)
open Log (Entry)

structure AgreeAbove (L H : Nat) (x y : State) : Prop where
  days : ∀ d, L ≤ d → x.days.get d = y.days.get d
  seams : ∀ d, L ≤ d → x.seams.get d = y.seams.get d
  itemDays : ∀ d i, H ≤ d → x.itemDays.get (d, i) = y.itemDays.get (d, i)
  doneDates : ∀ d i, H ≤ d → x.doneDates.get (d, i) = y.doneDates.get (d, i)
  instances : ∀ k, (∀ d, Log.instDate? k.2 = some d → H ≤ d) → x.instances.get k = y.instances.get k
  items : ∀ k, x.items.get k = y.items.get k
  lastDone : ∀ k, x.lastDone.get k = y.lastDone.get k
  named : ∀ k, x.named.get k = y.named.get k
  dropped : ∀ k, x.dropped.get k = y.dropped.get k
  energy : ∀ d, L ≤ d → x.energy.filter (fun o => decide (o.day = d)) = y.energy.filter (fun o => decide (o.day = d))
  durations : ∀ d, L ≤ d →
    x.durations.filter (fun o => decide (o.day = d)) = y.durations.filter (fun o => decide (o.day = d))
  interrupts : ∀ d, L ≤ d →
    x.interrupts.filter (fun o => decide (o.day = d)) = y.interrupts.filter (fun o => decide (o.day = d))
  demotions : ∀ d, L ≤ d →
    x.demotions.filter (fun p => decide (p.1 = d)) = y.demotions.filter (fun p => decide (p.1 = d))
  closes : ∀ d, L ≤ d → x.closes.filter (fun p => decide (p.1 = d)) = y.closes.filter (fun p => decide (p.1 = d))
  machine : x.machine = y.machine
  lastEff : x.global.lastEffective = y.global.lastEffective
  rwarns : x.rwarns = y.rwarns
  longestLeak : x.longestLeak = y.longestLeak
  unknown : x.unknown = y.unknown

theorem filter_cons_day {α : Type} (f : α → Nat) (a : α) (l₁ l₂ : List α) (d : Nat)
    (h : l₁.filter (fun o => decide (f o = d)) = l₂.filter (fun o => decide (f o = d))) :
    (a :: l₁).filter (fun o => decide (f o = d)) = (a :: l₂).filter (fun o => decide (f o = d)) := by
  simp only [List.filter_cons, h]

theorem AgreeAbove.apply {L H : Nat} {x y : State} (h : AgreeAbove L H x y) (fx : Effect) :
    AgreeAbove L H (Replay.applyEffect x fx) (Replay.applyEffect y fx) := by
  cases fx with
  | dayAdd d op =>
    refine { h with days := fun d' hd' => ?_ }
    simp only [Replay.applyEffect, Replay.HMap.get_alter]
    split
    · rename_i he; rw [h.days d (he ▸ hd')]
    · exact h.days d' hd'
  | header d hr =>
    exact ⟨h.days, h.seams, h.itemDays, h.doneDates, h.instances, h.items, h.lastDone, h.named, h.dropped, h.energy,
      h.durations, h.interrupts, h.demotions, h.closes, h.machine, h.lastEff, h.rwarns, h.longestLeak, h.unknown⟩
  | itemAdd i op =>
    refine { h with items := fun k => ?_ }
    simp only [Replay.applyEffect, Replay.HMap.get_alter]
    split
    · rw [h.items i]
    · exact h.items k
  | itemDay i d m =>
    refine { h with itemDays := fun d' i' hd' => ?_ }
    simp only [Replay.applyEffect, Replay.HMap.get_alter]
    split
    · rename_i he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [h.itemDays d' i' hd']
    · exact h.itemDays d' i' hd'
  | itemDaySub i d m =>
    simp only [Replay.applyEffect]
    rw [h.items i]
    split
    · refine { h with itemDays := fun d' i' hd' => ?_ }
      simp only [Replay.HMap.get_alter]
      split
      · rename_i he
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rw [h.itemDays d' i' hd']
      · exact h.itemDays d' i' hd'
    · exact h
  | obs o =>
    cases o with
    | energy o => exact { h with energy := fun d hd => filter_cons_day _ o _ _ d (h.energy d hd) }
    | duration o => exact { h with durations := fun d hd => filter_cons_day _ o _ _ d (h.durations d hd) }
  | interruption r => exact { h with interrupts := fun d hd => filter_cons_day _ r _ _ d (h.interrupts d hd) }
  | machine m => exact { h with machine := rfl }
  | global t => exact { h with lastEff := rfl }
  | markDone i t =>
    refine { h with lastDone := fun k => ?_ }
    simp only [Replay.applyEffect, Replay.HMap.get_alter]
    split
    · rw [h.lastDone i]
    · exact h.lastDone k
  | doneDate i d =>
    refine { h with doneDates := fun d' i' hd' => ?_ }
    simp only [Replay.applyEffect, Replay.HMap.get_alter]
    split
    · rfl
    · exact h.doneDates d' i' hd'
  | inst item inst r =>
    refine { h with instances := fun k hk => ?_ }
    simp only [Replay.applyEffect, Replay.HMap.get_alter]
    split
    · rfl
    · exact h.instances k hk
  | named name id line t date =>
    refine { h with named := fun k => ?_ }
    simp only [Replay.applyEffect, Replay.HMap.get_alter]
    split
    · rw [h.named (name, id)]
    · exact h.named k
  | rwarn w => exact { h with rwarns := by simp only [Replay.applyEffect, h.rwarns] }
  | demote d r => exact { h with demotions := fun d' hd => filter_cons_day Prod.fst (d, r) _ _ d' (h.demotions d' hd) }
  | close d r => exact { h with closes := fun d' hd => filter_cons_day Prod.fst (d, r) _ _ d' (h.closes d' hd) }
  | drop i =>
    refine { h with dropped := fun k => ?_ }
    simp only [Replay.applyEffect, Replay.HMap.get_alter]
    split
    · rfl
    · exact h.dropped k
  | leak r => exact { h with longestLeak := by simp only [Replay.applyEffect, h.longestLeak] }
  | unknown => exact { h with unknown := by simp only [Replay.applyEffect, h.unknown] }
  | seam d op =>
    refine { h with seams := fun d' hd' => ?_ }
    simp only [Replay.applyEffect, Replay.HMap.get_alter]
    split
    · rename_i he; rw [h.seams d (he ▸ hd')]
    · exact h.seams d' hd'

theorem AgreeAbove.applyEffects {L H : Nat} {x y : State} (h : AgreeAbove L H x y) :
    ∀ (fx : List Effect), AgreeAbove L H (Replay.applyEffects x fx) (Replay.applyEffects y fx)
  | [] => h
  | f :: fx => by
    rw [Replay.applyEffects_cons, Replay.applyEffects_cons]
    exact AgreeAbove.applyEffects (h.apply f) fx

theorem AgreeAbove.stepWith {L H : Nat} {x y : State} (h : AgreeAbove L H x y) (z : Cal.Tz) (dy : Cal.Instant → Nat)
    (sl : Nat → Option Nat) (e : Entry) :
    AgreeAbove L H (Replay.stepWith z dy sl x e) (Replay.stepWith z dy sl y e) := by
  unfold Replay.stepWith
  rw [effectsWith_machine z dy sl x y e h.machine]
  exact h.applyEffects _

theorem AgreeAbove.foldl {L H : Nat} (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) {x y : State}, AgreeAbove L H x y →
      AgreeAbove L H (sv.foldl (Replay.stepWith z dy sl) x) (sv.foldl (Replay.stepWith z dy sl) y)
  | [], _, _, h => h
  | e :: sv, _, _, h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact AgreeAbove.foldl z dy sl sv (h.stepWith z dy sl e)

theorem AgreeAbove.trans {L H : Nat} {x y w : State} (h₁ : AgreeAbove L H x y) (h₂ : AgreeAbove L H y w) :
    AgreeAbove L H x w :=
  ⟨fun d hd => (h₁.days d hd).trans (h₂.days d hd), fun d hd => (h₁.seams d hd).trans (h₂.seams d hd),
   fun d i hd => (h₁.itemDays d i hd).trans (h₂.itemDays d i hd),
   fun d i hd => (h₁.doneDates d i hd).trans (h₂.doneDates d i hd),
   fun k hk => (h₁.instances k hk).trans (h₂.instances k hk), fun k => (h₁.items k).trans (h₂.items k),
   fun k => (h₁.lastDone k).trans (h₂.lastDone k), fun k => (h₁.named k).trans (h₂.named k),
   fun k => (h₁.dropped k).trans (h₂.dropped k), fun d hd => (h₁.energy d hd).trans (h₂.energy d hd),
   fun d hd => (h₁.durations d hd).trans (h₂.durations d hd), fun d hd => (h₁.interrupts d hd).trans (h₂.interrupts d hd),
   fun d hd => (h₁.demotions d hd).trans (h₂.demotions d hd), fun d hd => (h₁.closes d hd).trans (h₂.closes d hd),
   h₁.machine.trans h₂.machine, h₁.lastEff.trans h₂.lastEff, h₁.rwarns.trans h₂.rwarns,
   h₁.longestLeak.trans h₂.longestLeak, h₁.unknown.trans h₂.unknown⟩

theorem AgreeAbove.symm {L H : Nat} {x y : State} (h : AgreeAbove L H x y) : AgreeAbove L H y x :=
  ⟨fun d hd => (h.days d hd).symm, fun d hd => (h.seams d hd).symm, fun d i hd => (h.itemDays d i hd).symm,
   fun d i hd => (h.doneDates d i hd).symm, fun k hk => (h.instances k hk).symm, fun k => (h.items k).symm,
   fun k => (h.lastDone k).symm, fun k => (h.named k).symm, fun k => (h.dropped k).symm,
   fun d hd => (h.energy d hd).symm, fun d hd => (h.durations d hd).symm, fun d hd => (h.interrupts d hd).symm,
   fun d hd => (h.demotions d hd).symm, fun d hd => (h.closes d hd).symm, h.machine.symm, h.lastEff.symm,
   h.rwarns.symm, h.longestLeak.symm, h.unknown.symm⟩

theorem AgreeAbove.of_sameReadings {L H : Nat} {x y : State} (h : Replay.SameReadings x y) : AgreeAbove L H x y :=
  ⟨fun d _ => h.days d, fun d _ => h.seams d, fun d i _ => h.itemDays (d, i), fun d i _ => h.doneDates (d, i),
   fun k _ => h.instances k, h.items, h.lastDone, h.named, h.dropped, fun d _ => by rw [h.energy],
   fun d _ => by rw [h.durations], fun d _ => by rw [h.interrupts], fun d _ => by rw [h.demotions],
   fun d _ => by rw [h.closes], h.machine, by rw [h.global], h.rwarns, h.longestLeak, h.unknown⟩

/-- **Rebinding by two tables agreeing at and above the ledger day keeps agreement.** -/
theorem AgreeAbove.rebind {L H : Nat} {x y : State} (h : AgreeAbove L H x y) (g g' : Nat → Option Nat)
    (hg : ∀ d, L ≤ d → g d = g' d) : AgreeAbove L H (rebindState g x) (rebindState g' y) := by
  refine { h with energy := fun d hd => ?_ }
  simp only [rebindState]
  rw [List.filter_map, List.filter_map]
  have e1 : (fun o => decide (o.day = d)) ∘ rebindObs g = fun o => decide (o.day = d) := by
    funext o; simp only [Function.comp_apply, rebindObs]; split <;> rfl
  have e2 : (fun o => decide (o.day = d)) ∘ rebindObs g' = fun o => decide (o.day = d) := by
    funext o; simp only [Function.comp_apply, rebindObs]; split <;> rfl
  rw [e1, e2, h.energy d hd]
  apply List.map_congr_left
  intro o ho
  have hod : o.day = d := by simpa using (List.mem_filter.1 ho).2
  simp only [rebindObs]
  split
  · rfl
  · rw [hg o.day (by omega)]

end Seal
end Tm
