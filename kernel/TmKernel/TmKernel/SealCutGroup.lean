import TmKernel.SealLaw2D
import TmKernel.SealLaw2E
/-!
# SealCutGroup — a checkpoint's groups at a later ledger day (stage 5, D9, W2: law 6)

Agreement above the horizons is agreement above any later ones (`AgreeAbove.mono`, with `horizonOf_mono`); the items and
open days a resumed state groups are the whole log's before `finish` too (`items_merged_eq_raw`, `daysFrom_eq_raw`); a
range of days or dates is a filter of the days or dates from its start.  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State)

theorem AgreeAbove.mono {L H L' H' : Nat} {x y : State} (h : AgreeAbove L H x y) (hL : L ≤ L') (hH : H ≤ H') :
    AgreeAbove L' H' x y :=
  ⟨fun d hd => h.days d (Nat.le_trans hL hd), fun d hd => h.seams d (Nat.le_trans hL hd),
   fun d i hd => h.itemDays d i (Nat.le_trans hH hd), fun d i hd => h.doneDates d i (Nat.le_trans hH hd),
   fun k hk => h.instances k (fun d hd => Nat.le_trans hH (hk d hd)), h.items, h.lastDone, h.named, h.dropped,
   fun d hd => h.energy d (Nat.le_trans hL hd), fun d hd => h.durations d (Nat.le_trans hL hd),
   fun d hd => h.interrupts d (Nat.le_trans hL hd), fun d hd => h.demotions d (Nat.le_trans hL hd),
   fun d hd => h.closes d (Nat.le_trans hL hd), h.machine, h.lastEff, h.rwarns, h.longestLeak, h.unknown⟩

theorem horizonOf_mono {L L' : Nat} (h : L ≤ L') : horizonOf L ≤ horizonOf L' := by
  unfold horizonOf
  have h1 := monthStart_mono h
  have h2 := isoMonday_mono h
  omega

theorem daysFrom_eq_raw {L H : Nat} {x y : State} (hx : AllKeyed x) (hy : AllKeyed y) (h : AgreeAbove L H x y)
    (hsx hsy : List (Nat × Replay.HeaderRec))
    (hhs : ∀ d, L ≤ d → hsx.filter (fun p => decide (p.1 = d)) = hsy.filter (fun p => decide (p.1 = d))) :
    daysFrom x hsx L = daysFrom y hsy L := by
  unfold daysFrom
  rw [dayKeys_filter_eq hx hy h hsx hsy hhs]
  exact List.map_congr_left (fun d hd =>
    openDayOf_eq hx hy h hsx hsy hhs d (of_decide_eq_true (List.mem_filter.1 hd).2))

theorem daysIn_eq_filter (st : State) (hs : List (Nat × Replay.HeaderRec)) (lo hi : Nat) :
    daysIn st hs lo hi = (daysFrom st hs lo).filter (fun o => decide (o.day < hi)) := by
  unfold daysIn daysFrom
  rw [List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro d _
  simp only [Function.comp_apply, openDayOf_day]
  by_cases h1 : lo ≤ d <;> by_cases h2 : d < hi <;> simp [h1, h2]

theorem windowsIn_eq_filter (st : State) (lo hi : Nat) :
    windowsIn st lo hi = (windowsFrom st lo).filter (fun w => decide (w.day < hi)) := by
  unfold windowsIn windowsFrom
  rw [List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro d _
  simp only [Function.comp_apply, windowOf_day]
  by_cases h1 : lo ≤ d <;> by_cases h2 : d < hi <;> simp [h1, h2]

/-- **The items of a resumed state, before `finish`, are the whole log's.** -/
theorem items_merged_eq_raw {L H : Nat} (K : Ckpt) {p x y : State} (hp : AllKeyed p) (hx : AllKeyed x) (hy : AllKeyed y)
    (hKitems : K.items = (itemIds p).map (itemAggOf p)) (hKwin : K.window = windowsFrom p H)
    (h : AgreeAbove L H x y)
    (hbdd : ∀ d i, d < H → y.doneDates.get (d, i) = p.doneDates.get (d, i))
    (hki : ∀ i, (p.items.get i).isSome → (y.items.get i).isSome)
    (hkl : ∀ i, (p.lastDone.get i).isSome → (y.lastDone.get i).isSome)
    (hkdr : ∀ i, (p.dropped.get i).isSome → (y.dropped.get i).isSome)
    (hkdd : ∀ k, (p.doneDates.get k).isSome → (y.doneDates.get k).isSome)
    (hxdd : ∀ d i, d < H → x.doneDates.get (d, i) = none) :
    (canon idLt (K.items.map (·.id) ++ itemIds x)).map (aggMerged K x) = (itemIds y).map (itemAggOf y) := by
  have hmem : ∀ i, i ∈ K.items.map (·.id) ++ itemIds x ↔ i ∈ itemIds y := by
    intro i
    rw [List.mem_append, hKitems, List.map_map]
    have hK1 : i ∈ (itemIds p).map ((·.id) ∘ itemAggOf p) ↔ i ∈ itemIds p := by
      simp only [List.mem_map, Function.comp]
      exact ⟨fun ⟨j, hj, e⟩ => e ▸ hj, fun h => ⟨i, h, rfl⟩⟩
    rw [hK1, mem_itemIds_iff p hp, mem_itemIds_iff x hx, mem_itemIds_iff y hy, h.items i, h.lastDone i, h.dropped i]
    constructor
    · rintro ((hi | hl | hd | hds) | (hi | hl | hd | hds))
      · exact Or.inl (hki i hi)
      · exact Or.inr (Or.inl (hkl i hl))
      · exact Or.inr (Or.inr (Or.inl (hkdr i hd)))
      · obtain ⟨d, hdm⟩ := List.exists_mem_of_ne_nil _ hds
        have := hkdd (d, i) ((mem_datesOf p hp i d).1 hdm)
        exact Or.inr (Or.inr (Or.inr (List.ne_nil_of_mem ((mem_datesOf y hy i d).2 this))))
      · exact Or.inl hi
      · exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr (Or.inl hd))
      · obtain ⟨d, hdm⟩ := List.exists_mem_of_ne_nil _ hds
        have hs := (mem_datesOf x hx i d).1 hdm
        have hH : H ≤ d := by
          refine Nat.le_of_not_lt (fun hlt => ?_)
          rw [hxdd d i hlt] at hs; cases hs
        rw [h.doneDates d i hH] at hs
        exact Or.inr (Or.inr (Or.inr (List.ne_nil_of_mem ((mem_datesOf y hy i d).2 hs))))
    · rintro (hi | hl | hd | hds)
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr (Or.inl hl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hd)))
      · obtain ⟨d, hdm⟩ := List.exists_mem_of_ne_nil _ hds
        have hs := (mem_datesOf y hy i d).1 hdm
        rcases Nat.lt_or_ge d H with hlt | hge
        · rw [hbdd d i hlt] at hs
          exact Or.inl (Or.inr (Or.inr (Or.inr (List.ne_nil_of_mem ((mem_datesOf p hp i d).2 hs)))))
        · rw [← h.doneDates d i hge] at hs
          exact Or.inr (Or.inr (Or.inr (Or.inr (List.ne_nil_of_mem ((mem_datesOf x hx i d).2 hs)))))
  have hids : canon idLt (K.items.map (·.id) ++ itemIds x) = itemIds y :=
    canon_eq_of_mem_iff idLt_strictTotal _ _ (fun i => (hmem i).trans (mem_canon idLt_strictTotal _ i))
  rw [hids]
  apply List.map_congr_left
  intro i _
  have hfind : findItem K.items i = if i ∈ itemIds p then some (itemAggOf p i) else none := by
    unfold findItem; rw [hKitems]; exact find?_items p i
  have hU1 := doneFirst_union hp hx hy hkdd h.doneDates hbdd hxdd i
  have hU2 := doneCount_union hp hx hy hkdd h.doneDates hbdd hxdd i
  rw [aggMerged_eq, itemAggOf_eq, hfind, hKwin, window_done_count p hp H i, h.items i, h.lastDone i, h.dropped i]
  by_cases hip : i ∈ itemIds p
  · rw [if_pos hip]
    simp only [Option.bind_some, Option.map_some, Option.getD_some, itemAggOf_eq]
    rw [hU1, hU2]
  · rw [if_neg hip]
    have hdp : datesOf p i = [] := Classical.byContradiction (fun hne =>
      hip ((mem_itemIds_iff p hp i).2 (Or.inr (Or.inr (Or.inr hne)))))
    rw [hdp] at hU1 hU2
    simp only [Option.bind_none, Option.map_none, Option.getD_none, hdp, List.filter_nil, List.length_nil] at hU1 hU2 ⊢
    rw [← hU1, ← hU2]
    rfl

end Seal
end Tm
