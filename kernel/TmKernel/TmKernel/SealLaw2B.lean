import TmKernel.SealLaw2A
import TmKernel.SealRebind
import TmKernel.SealAgg2
import TmKernel.SealHeaders
import TmKernel.SealFull
import TmKernel.SealSlept
import TmKernel.SealGroup
import TmKernel.SealBits
/-!
# SealLaw2B — law 2's glue: keys, the restored state below the horizons, and the index facts (stage 5, D9, W2)

Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Effect HMap KeyHash survivors wakeInstants keptWakes dayOf)
open Log (Entry)

theorem rebindState_init (g : Nat → Option Nat) (n : Nat) : rebindState g (State.init n) = State.init n := rfl

theorem Effect.key_rebind (g : Nat → Option Nat) (x : Effect) : (Effect.rebind g x).key = x.key := by
  cases x with
  | obs o =>
    cases o with
    | energy o =>
      simp only [Effect.rebind, Replay.Effect.key, Replay.Obs.day, rebindObs]
      split <;> rfl
    | duration o => rfl
  | _ => rfl

/-- **A step's keys do not read `slept_by_day`.** -/
theorem effectsWith_keys (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl sl' : Nat → Option Nat) (st : State) (e : Entry)
    (hp : PendingStart st) :
    (Replay.effectsWith z dy sl' st e).map Replay.Effect.key = (Replay.effectsWith z dy sl st e).map Replay.Effect.key := by
  rw [← effectsWith_rebind z dy sl sl' st e hp, List.map_map]
  exact List.map_congr_left (fun x _ => (Effect.key_rebind sl x).symm)

theorem pendingStart_init (n : Nat) : PendingStart (State.init n) := fun o h => by cases h

section Keyed

variable {α κ β : Type} [DecidableEq κ] [KeyHash κ]

omit [DecidableEq κ] in
theorem keyed_foldl_step (step : HMap κ β → α → HMap κ β) (hstep : ∀ m a, m.Keyed → (step m a).Keyed) :
    ∀ (l : List α) (m : HMap κ β), m.Keyed → (l.foldl step m).Keyed
  | [], _, h => h
  | a :: l, m, h => keyed_foldl_step step hstep l _ (hstep m a h)

theorem keyed_writeOpt (m : HMap κ β) (k : κ) (v : Option β) (h : m.Keyed) : (writeOpt m k v).Keyed := by
  cases v with
  | none => exact h
  | some x => exact Replay.HMap.keyed_alter _ _ _ h

theorem keyed_writeAll (l : List (κ × β)) (m : HMap κ β) (h : m.Keyed) : (writeAll l m).Keyed :=
  keyed_foldl_step _ (fun _m _ hm => Replay.HMap.keyed_alter _ _ _ hm) l m h

theorem get_foldl_alter_of_not_mem (k : κ) :
    ∀ (l : List (κ × β)) (m : HMap κ β), (∀ p ∈ l, p.1 ≠ k) →
      (l.foldl (fun m p => m.alter p.1 (fun _ => some p.2)) m).get k = m.get k
  | [], _, _ => rfl
  | p :: l, m, h => by
    rw [List.foldl_cons, get_foldl_alter_of_not_mem k l _ (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      Replay.HMap.get_alter, if_neg (fun he => h p List.mem_cons_self he.symm)]

theorem get_foldl_writeOpt_of_not_mem (f : α → κ) (g : α → Option β) (k : κ) :
    ∀ (l : List α) (m : HMap κ β), (∀ a ∈ l, f a ≠ k) →
      (l.foldl (fun m a => writeOpt m (f a) (g a)) m).get k = m.get k
  | [], _, _ => rfl
  | a :: l, m, h => by
    rw [List.foldl_cons, get_foldl_writeOpt_of_not_mem f g k l _ (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      get_writeOpt, if_neg (h a List.mem_cons_self)]

end Keyed

theorem allKeyed_restore (K : Ckpt) (n : Nat) : AllKeyed (restore K n) := by
  refine ⟨keyed_foldl_step _ (fun m o hm => keyed_writeOpt m _ _ hm) _ _ (Replay.HMap.keyed_empty n),
   keyed_foldl_step _ (fun m a hm => keyed_writeOpt m _ _ hm) _ _ (Replay.HMap.keyed_empty n),
   keyed_writeAll _ _ (Replay.HMap.keyed_empty n),
   keyed_foldl_step _ (fun m a hm => keyed_writeOpt m _ _ hm) _ _ (Replay.HMap.keyed_empty n),
   keyed_writeAll _ _ (Replay.HMap.keyed_empty n),
   keyed_writeAll _ _ (Replay.HMap.keyed_empty n),
   keyed_writeAll _ _ (Replay.HMap.keyed_empty n),
   keyed_foldl_step _ (fun m a hm => ?_) _ _ (Replay.HMap.keyed_empty n),
   keyed_foldl_step _ (fun m o hm => keyed_writeOpt m _ _ hm) _ _ (Replay.HMap.keyed_empty n)⟩
  split
  · exact Replay.HMap.keyed_alter _ _ _ hm
  · exact hm

theorem AllKeyed.rebind {st : State} (h : AllKeyed st) (g : Nat → Option Nat) : AllKeyed (rebindState g st) := h

theorem openDayOf_day (st : State) (hs : List (Nat × Replay.HeaderRec)) (d : Nat) : (openDayOf st hs d).day = d := rfl
theorem windowOf_day (st : State) (d : Nat) : (windowOf st d).day = d := rfl

/-- **A restored state holds no done date below the window horizon and no day below the ledger day.** -/
theorem restore_below (z : Cal.Tz) (T₀ L cut : Nat) (es er : List Entry) (ws : List (Nat × Log.LWarn)) (n : Nat) :
    (∀ d i, d < horizonOf L → (restore (ckptOfEntries z T₀ L cut es er ws) n).doneDates.get (d, i) = none) ∧
    (∀ d, d < L → (restore (ckptOfEntries z T₀ L cut es er ws) n).days.get d = none) := by
  have hWI := ckpt_window z T₀ L cut es er ws
  have hOD := ckpt_openDays z T₀ L cut es er ws
  generalize ckptOfEntries z T₀ L cut es er ws = K at *
  constructor
  · intro d i hd
    show (writeAll (windowDonePairs K) (HMap.empty n)).get (d, i) = none
    unfold writeAll windowDonePairs
    rw [get_foldl_alter_of_not_mem, Replay.HMap.get_empty]
    intro p hp heq
    obtain ⟨w, hw, hp'⟩ := List.mem_flatMap.1 hp
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hp'
    rw [hWI] at hw
    obtain ⟨d', _, hd', rfl⟩ := (mem_windowsFrom _ _ w).1 hw
    simp only [windowOf_day, Prod.mk.injEq] at heq
    omega
  · intro d hd
    show (K.openDays.foldl (fun m o => writeOpt m o.day o.acc) (HMap.empty n)).get d = none
    rw [get_foldl_writeOpt_of_not_mem OpenDay.day OpenDay.acc d, Replay.HMap.get_empty]
    intro o ho heq
    rw [hOD] at ho
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 ho
    have := of_decide_eq_true (List.mem_filter.1 hd').2
    rw [openDayOf_day] at heq
    omega

theorem AgreeAbove.refl (L H : Nat) (x : State) : AgreeAbove L H x x :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl,
   fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
   rfl, rfl, rfl, rfl, rfl⟩

theorem kmap_get_append (X Y : List (Nat × Nat)) (d : Nat) :
    Replay.KMap.get (X ++ Y) d = (Replay.KMap.get X d).or (Replay.KMap.get Y d) := by
  rw [kmap_get_eq, kmap_get_eq, kmap_get_eq, List.find?_append]
  cases X.find? (fun p => decide (p.1 = d)) <;> rfl

theorem foldedState_eq (z : Cal.Tz) (es er : List Entry) :
    foldedState z es er = (foldedSurvivors es er).foldl
      (Replay.stepWith z (dayOf z (foldedIndex z es er))
        (Replay.KMap.get (Replay.sleptByDay z (foldedIndex z es er) (foldedSurvivors es er)))) (State.init es.length) :=
  rfl

theorem pendingStart_restore (z : Cal.Tz) (T₀ L cut : Nat) (es er : List Entry) (ws : List (Nat × Log.LWarn))
    (n : Nat) : PendingStart (restore (ckptOfEntries z T₀ L cut es er ws) n) := by
  intro o ho
  have hm : (restore (ckptOfEntries z T₀ L cut es er ws) n).machine = (foldedState z es er).machine :=
    ckpt_machine z T₀ L cut es er ws
  rw [hm, foldedState_eq] at ho
  exact pendingStart_foldl z _ _ _ _ (pendingStart_init _) o ho

theorem foldedSurvivors_nil (E : List Entry) : foldedSurvivors E [] = survivors E := by
  unfold foldedSurvivors; rw [List.append_nil, ← Replay.survivors_are_the_uncancelled_entries]

theorem foldedIndex_nil (z : Cal.Tz) (E : List Entry) :
    foldedIndex z E [] = keptWakes z (wakeInstants (survivors E)) := by
  unfold foldedIndex; rw [foldedSurvivors_nil]

/-- **A folded entry survives the folded lines' mask exactly when its index is not cancelled there.** -/
theorem mem_foldedSurvivors_iff (As Rs : List Entry) (hd : (As ++ Rs).Pairwise (fun x y => x.line < y.line))
    (i : Nat) (e : Entry) (he : As[i]? = some e) : e ∈ foldedSurvivors As Rs ↔ Replay.cancelledAt (As ++ Rs) i = false := by
  have hdA : As.Pairwise (fun x y => x.line < y.line) := (List.pairwise_append.1 hd).1
  unfold foldedSurvivors
  constructor
  · intro hm
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hm
    obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
    have hpi := getElem?_of_mem_zipIdx hp1
    rw [hpe] at hpi
    have hij := idx_eq_of_pairwise_lt As hdA p.2 i e hpi he
    rw [← hij]; simpa using hp2
  · intro hc
    have hmem : (e, i) ∈ As.zipIdx := by
      rw [List.mem_iff_getElem?]
      exact ⟨i, by rw [List.getElem?_zipIdx, he]; simp⟩
    exact List.mem_map.2 ⟨(e, i), List.mem_filter.2 ⟨hmem, by simp [hc]⟩, rfl⟩

theorem map_zipIdx_eq {α β : Type} (f : α × Nat → β) (g : α → β) : ∀ (l : List α) (n : Nat),
    (∀ k e, l[k]? = some e → f (e, n + k) = g e) → (l.zipIdx n).map f = l.map g
  | [], _, _ => rfl
  | a :: l, n, h => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons]
    have h0 : f (a, n) = g a := by simpa using h 0 a rfl
    rw [h0, map_zipIdx_eq f g l (n + 1) (fun k e hk => by
      have := h (k + 1) e (by simpa using hk)
      rwa [show n + (k + 1) = n + 1 + k by omega] at this)]

end Seal
end Tm
