import TmKernel.SealAgree
import TmKernel.SealSlept
/-!
# SealGroup — two states agreeing at and above the horizons group alike there (stage 5, D9, W2)

The canonical lists `ckptOf` groups a state into (the window records at or after `H`, the non-date instances, the named
events, the open days at or after `L`) are one list for two keyed states that `AgreeAbove`.  Specification only.
-/
namespace Tm
namespace Seal

open Replay (State HMap KeyHash HeaderRec)
open Log (Entry)

theorem canon_filter {α : Type} {lt : α → α → Bool} (h : StrictTotal lt) (l : List α) (p : α → Bool) :
    (canon lt l).filter p = canon lt (l.filter p) :=
  eq_of_sorted_of_mem_iff h _ _ ((sorted_canon h l).sublist List.filter_sublist) (sorted_canon h _)
    (fun y => by rw [List.mem_filter, mem_canon h, mem_canon h, List.mem_filter])

theorem mem_keys_map_iff {κ β α : Type} [DecidableEq κ] [KeyHash κ] (m : HMap κ β) (hm : m.Keyed) (f : κ → α) (a : α) :
    a ∈ m.pairs.map (fun p => f p.1) ↔ ∃ k, f k = a ∧ (m.get k).isSome := by
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    exact ⟨p.1, rfl, (Replay.HMap.mem_keys_pairs_iff m hm p.1).1 (List.mem_map.2 ⟨p, hp, rfl⟩)⟩
  · rintro ⟨k, rfl, hk⟩
    obtain ⟨p, hp, hpk⟩ := List.mem_map.1 ((Replay.HMap.mem_keys_pairs_iff m hm k).2 hk)
    exact List.mem_map.2 ⟨p, hp, by rw [hpk]⟩

theorem mem_map_iff_filter_ne_nil {α : Type} (l : List α) (f : α → Nat) (d : Nat) :
    d ∈ l.map f ↔ l.filter (fun o => decide (f o = d)) ≠ [] := by
  constructor
  · intro h hnil
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 h
    have := List.filter_eq_nil_iff.1 hnil o ho
    simp at this
  · intro h
    obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ h
    exact List.mem_map.2 ⟨o, (List.mem_filter.1 ho).1, of_decide_eq_true (List.mem_filter.1 ho).2⟩

theorem mem_ids_of_day {β : Type} (m : HMap (Nat × Log.Id) β) (hm : m.Keyed) (d : Nat) (i : Log.Id) :
    i ∈ (m.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2) ↔ (m.get (d, i)).isSome := by
  rw [← Replay.HMap.mem_keys_pairs_iff m hm (d, i)]
  constructor
  · intro h'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h'
    have hpd := of_decide_eq_true (List.mem_filter.1 hp).2
    exact List.mem_map.2 ⟨p, (List.mem_filter.1 hp).1, by rw [← hpd]⟩
  · intro h'
    obtain ⟨p, hp, hpk⟩ := List.mem_map.1 h'
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by simp [hpk]⟩, by simp [hpk]⟩

theorem mem_keys_filter_iff {κ β : Type} [DecidableEq κ] [KeyHash κ] (m : HMap κ β) (hm : m.Keyed) (P : κ → Bool) (k : κ) :
    k ∈ (m.pairs.filter (fun p => P p.1)).map Prod.fst ↔ P k = true ∧ (m.get k).isSome := by
  rw [← Replay.HMap.mem_keys_pairs_iff m hm k]
  constructor
  · intro h'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h'
    exact ⟨(List.mem_filter.1 hp).2, List.mem_map.2 ⟨p, (List.mem_filter.1 hp).1, rfl⟩⟩
  · rintro ⟨hP, h'⟩
    obtain ⟨p, hp, hpk⟩ := List.mem_map.1 h'
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by rw [hpk]; exact hP⟩, hpk⟩

section Group

variable {L H : Nat} {x y : State} (hx : AllKeyed x) (hy : AllKeyed y) (h : AgreeAbove L H x y)
include hx hy h

theorem winKeys_filter_eq : (winKeys x).filter (fun d => decide (H ≤ d)) = (winKeys y).filter (fun d => decide (H ≤ d)) := by
  unfold winKeys
  rw [canon_filter natLt_strictTotal, canon_filter natLt_strictTotal]
  apply canon_eq_of_mem_iff natLt_strictTotal
  intro d
  simp only [List.mem_filter, List.mem_append, decide_eq_true_eq]
  have key : ∀ (u v : State) (hu : AllKeyed u) (hv : AllKeyed v) (huv : AgreeAbove L H u v), H ≤ d →
      ((d ∈ u.itemDays.pairs.map (·.1.1) ∨ d ∈ u.doneDates.pairs.map (·.1.1)) ∨
        d ∈ u.instances.pairs.filterMap (fun p => Log.instDate? p.1.2)) →
      ((d ∈ v.itemDays.pairs.map (·.1.1) ∨ d ∈ v.doneDates.pairs.map (·.1.1)) ∨
        d ∈ v.instances.pairs.filterMap (fun p => Log.instDate? p.1.2)) := by
    intro u v hu hv huv hd hm
    rcases hm with (hm | hm) | hm
    · obtain ⟨k, rfl, hk⟩ := (mem_keys_map_iff u.itemDays hu.2.2.1 (·.1) _).1 hm
      rw [huv.itemDays k.1 k.2 hd] at hk
      exact Or.inl (Or.inl ((mem_keys_map_iff v.itemDays hv.2.2.1 (·.1) _).2 ⟨k, rfl, hk⟩))
    · obtain ⟨k, rfl, hk⟩ := (mem_keys_map_iff u.doneDates hu.2.2.2.2.1 (·.1) _).1 hm
      rw [huv.doneDates k.1 k.2 hd] at hk
      exact Or.inl (Or.inr ((mem_keys_map_iff v.doneDates hv.2.2.2.2.1 (·.1) _).2 ⟨k, rfl, hk⟩))
    · obtain ⟨p, hp, hpd⟩ := List.mem_filterMap.1 hm
      have hk := (Replay.HMap.mem_keys_pairs_iff u.instances hu.2.2.2.2.2.1 p.1).1 (List.mem_map.2 ⟨p, hp, rfl⟩)
      rw [huv.instances p.1 (fun d' hd' => by rw [hpd] at hd'; cases hd'; exact hd)] at hk
      obtain ⟨q, hq, hqk⟩ := List.mem_map.1 ((Replay.HMap.mem_keys_pairs_iff v.instances hv.2.2.2.2.2.1 p.1).2 hk)
      exact Or.inr (List.mem_filterMap.2 ⟨q, hq, by rw [hqk]; exact hpd⟩)
  exact ⟨fun ⟨hm, hd⟩ => ⟨key x y hx hy h hd hm, hd⟩, fun ⟨hm, hd⟩ => ⟨key y x hy hx h.symm hd hm, hd⟩⟩

theorem windowOf_eq (d : Nat) (hd : H ≤ d) : windowOf x d = windowOf y d := by
  have hc1 : canon idLt ((x.itemDays.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2))
      = canon idLt ((y.itemDays.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2)) :=
    canon_eq_of_mem_iff idLt_strictTotal _ _ (fun i => by
      rw [mem_ids_of_day _ hx.2.2.1, mem_ids_of_day _ hy.2.2.1, h.itemDays d i hd])
  have hc2 : canon idLt ((x.doneDates.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2))
      = canon idLt ((y.doneDates.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2)) :=
    canon_eq_of_mem_iff idLt_strictTotal _ _ (fun i => by
      rw [mem_ids_of_day _ hx.2.2.2.2.1, mem_ids_of_day _ hy.2.2.2.2.1, h.doneDates d i hd])
  have hc3 : canon instKeyLt ((x.instances.pairs.filter (fun p => decide (Log.instDate? p.1.2 = some d))).map Prod.fst)
      = canon instKeyLt ((y.instances.pairs.filter (fun p => decide (Log.instDate? p.1.2 = some d))).map Prod.fst) :=
    canon_eq_of_mem_iff instKeyLt_strictTotal _ _ (fun k => by
      rw [mem_keys_filter_iff x.instances hx.2.2.2.2.2.1 (fun k => decide (Log.instDate? k.2 = some d)),
        mem_keys_filter_iff y.instances hy.2.2.2.2.2.1 (fun k => decide (Log.instDate? k.2 = some d))]
      constructor
      · rintro ⟨hk1, hk2⟩
        refine ⟨hk1, ?_⟩
        rw [← h.instances k (fun d' hd' => by rw [of_decide_eq_true hk1] at hd'; cases hd'; exact hd)]; exact hk2
      · rintro ⟨hk1, hk2⟩
        refine ⟨hk1, ?_⟩
        rw [h.instances k (fun d' hd' => by rw [of_decide_eq_true hk1] at hd'; cases hd'; exact hd)]; exact hk2)
  unfold windowOf
  rw [hc1, hc2, hc3]
  congr 1
  · exact filterMap_congr' _ _ _ (fun i _ => by rw [h.itemDays d i hd])
  · refine filterMap_congr' _ _ _ (fun k hk => ?_)
    have hk1 := ((mem_keys_filter_iff y.instances hy.2.2.2.2.2.1 (fun k => decide (Log.instDate? k.2 = some d)) k).1
      ((mem_canon instKeyLt_strictTotal _ _).1 hk)).1
    rw [h.instances k (fun d' hd' => by rw [of_decide_eq_true hk1] at hd'; cases hd'; exact hd)]

theorem windowsFrom_eq : windowsFrom x H = windowsFrom y H := by
  unfold windowsFrom
  rw [winKeys_filter_eq hx hy h]
  exact List.map_congr_left (fun d hd => windowOf_eq hx hy h d (of_decide_eq_true (List.mem_filter.1 hd).2))

theorem instOtherOf_eq : instOtherOf x = instOtherOf y := by
  have hc : canon instKeyLt ((x.instances.pairs.filter (fun p => (Log.instDate? p.1.2).isNone)).map Prod.fst)
      = canon instKeyLt ((y.instances.pairs.filter (fun p => (Log.instDate? p.1.2).isNone)).map Prod.fst) :=
    canon_eq_of_mem_iff instKeyLt_strictTotal _ _ (fun k => by
      rw [mem_keys_filter_iff x.instances hx.2.2.2.2.2.1 (fun k => (Log.instDate? k.2).isNone),
        mem_keys_filter_iff y.instances hy.2.2.2.2.2.1 (fun k => (Log.instDate? k.2).isNone)]
      constructor
      · rintro ⟨hk1, hk2⟩
        refine ⟨hk1, ?_⟩
        rw [← h.instances k (fun d' hd' => by rw [hd'] at hk1; cases hk1)]; exact hk2
      · rintro ⟨hk1, hk2⟩
        refine ⟨hk1, ?_⟩
        rw [h.instances k (fun d' hd' => by rw [hd'] at hk1; cases hk1)]; exact hk2)
  unfold instOtherOf
  rw [hc]
  refine filterMap_congr' _ _ _ (fun k hk => ?_)
  have hk1 := ((mem_keys_filter_iff y.instances hy.2.2.2.2.2.1 (fun k => (Log.instDate? k.2).isNone) k).1
    ((mem_canon instKeyLt_strictTotal _ _).1 hk)).1
  rw [h.instances k (fun d' hd' => by rw [hd'] at hk1; cases hk1)]

theorem namedOf_eq : namedOf x = namedOf y := by
  have hc : canon namedKeyLt (x.named.pairs.map Prod.fst) = canon namedKeyLt (y.named.pairs.map Prod.fst) :=
    canon_eq_of_mem_iff namedKeyLt_strictTotal _ _ (fun k => by
      rw [Replay.HMap.mem_keys_pairs_iff _ hx.2.2.2.2.2.2.1, Replay.HMap.mem_keys_pairs_iff _ hy.2.2.2.2.2.2.1, h.named k])
  unfold namedOf
  rw [hc]
  exact filterMap_congr' _ _ _ (fun k _ => by rw [h.named k])

theorem dayKeys_filter_eq (hsx hsy : List (Nat × HeaderRec))
    (hhs : ∀ d, L ≤ d → hsx.filter (fun p => decide (p.1 = d)) = hsy.filter (fun p => decide (p.1 = d))) :
    (dayKeys x hsx).filter (fun d => decide (L ≤ d)) = (dayKeys y hsy).filter (fun d => decide (L ≤ d)) := by
  unfold dayKeys
  rw [canon_filter natLt_strictTotal, canon_filter natLt_strictTotal]
  apply canon_eq_of_mem_iff natLt_strictTotal
  intro d
  simp only [List.mem_filter, List.mem_append, decide_eq_true_eq]
  constructor
  · rintro ⟨hm, hd⟩
    refine ⟨?_, hd⟩
    rw [Replay.HMap.mem_keys_pairs_iff _ hx.1, Replay.HMap.mem_keys_pairs_iff _ hx.2.2.2.2.2.2.2.2,
      mem_map_iff_filter_ne_nil x.energy, mem_map_iff_filter_ne_nil x.durations, mem_map_iff_filter_ne_nil x.interrupts,
      mem_map_iff_filter_ne_nil x.demotions, mem_map_iff_filter_ne_nil x.closes, mem_map_iff_filter_ne_nil hsx,
      h.days d hd, h.seams d hd, h.energy d hd, h.durations d hd, h.interrupts d hd, h.demotions d hd, h.closes d hd,
      hhs d hd, h.machine] at hm
    rw [Replay.HMap.mem_keys_pairs_iff _ hy.1, Replay.HMap.mem_keys_pairs_iff _ hy.2.2.2.2.2.2.2.2,
      mem_map_iff_filter_ne_nil y.energy, mem_map_iff_filter_ne_nil y.durations, mem_map_iff_filter_ne_nil y.interrupts,
      mem_map_iff_filter_ne_nil y.demotions, mem_map_iff_filter_ne_nil y.closes, mem_map_iff_filter_ne_nil hsy]
    exact hm
  · rintro ⟨hm, hd⟩
    refine ⟨?_, hd⟩
    rw [Replay.HMap.mem_keys_pairs_iff _ hy.1, Replay.HMap.mem_keys_pairs_iff _ hy.2.2.2.2.2.2.2.2,
      mem_map_iff_filter_ne_nil y.energy, mem_map_iff_filter_ne_nil y.durations, mem_map_iff_filter_ne_nil y.interrupts,
      mem_map_iff_filter_ne_nil y.demotions, mem_map_iff_filter_ne_nil y.closes, mem_map_iff_filter_ne_nil hsy,
      ← h.days d hd, ← h.seams d hd, ← h.energy d hd, ← h.durations d hd, ← h.interrupts d hd, ← h.demotions d hd,
      ← h.closes d hd, ← hhs d hd, ← h.machine] at hm
    rw [Replay.HMap.mem_keys_pairs_iff _ hx.1, Replay.HMap.mem_keys_pairs_iff _ hx.2.2.2.2.2.2.2.2,
      mem_map_iff_filter_ne_nil x.energy, mem_map_iff_filter_ne_nil x.durations, mem_map_iff_filter_ne_nil x.interrupts,
      mem_map_iff_filter_ne_nil x.demotions, mem_map_iff_filter_ne_nil x.closes, mem_map_iff_filter_ne_nil hsx]
    exact hm

theorem openDayOf_eq (hsx hsy : List (Nat × HeaderRec))
    (hhs : ∀ d, L ≤ d → hsx.filter (fun p => decide (p.1 = d)) = hsy.filter (fun p => decide (p.1 = d)))
    (d : Nat) (hd : L ≤ d) : openDayOf x hsx d = openDayOf y hsy d := by
  unfold openDayOf
  rw [h.days d hd, h.seams d hd, h.energy d hd, h.durations d hd, h.interrupts d hd, h.demotions d hd, h.closes d hd,
    hhs d hd]

theorem daysFrom_eq (hsx hsy : List (Nat × HeaderRec))
    (hhs : ∀ d, L ≤ d → hsx.filter (fun p => decide (p.1 = d)) = hsy.filter (fun p => decide (p.1 = d))) :
    (daysFrom x hsx L).map (OpenDay.finish x.machine) = (daysFrom y hsy L).map (OpenDay.finish y.machine) := by
  unfold daysFrom
  rw [dayKeys_filter_eq hx hy h hsx hsy hhs, h.machine, List.map_map, List.map_map]
  exact List.map_congr_left (fun d hd => by
    simp only [Function.comp_apply]
    rw [openDayOf_eq hx hy h hsx hsy hhs d (of_decide_eq_true (List.mem_filter.1 hd).2)])

end Group

end Seal
end Tm
