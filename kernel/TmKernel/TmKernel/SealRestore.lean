import TmKernel.SealAgree
/-!
# SealRestore — a checkpoint's restored state agrees with its fold at and above the horizons (stage 5, D9, W2)

`restore K n` rebuilds the bucketed maps and the per-day lists from the canonical lists a checkpoint stores.  For the
specification checkpoint of any folded entries, it reads, at and above the horizons and for every all-time fact, as
the fold that made it (`restore_agrees`).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State HMap KeyHash)
open Log (Entry)

section FoldAlter

variable {α κ β : Type} [DecidableEq κ] [KeyHash κ]

/-- **A map written once per element of a list with distinct keys reads each element's value**, for any step that
writes an element's value, when it has one, at the element's key. -/
theorem get_foldl_step (f : α → κ) (g : α → Option β) (step : HMap κ β → α → HMap κ β)
    (hstep : ∀ m a k, (step m a).get k = if f a = k then (g a).or (m.get k) else m.get k) :
    ∀ (l : List α) (m : HMap κ β) (k : κ), (l.map f).Nodup →
      (l.foldl step m).get k = ((l.find? (fun a => decide (f a = k))).bind g).or (m.get k)
  | [], m, k, _ => by simp
  | a :: t, m, k, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons, get_foldl_step f g step hstep t _ k hnd.2, hstep]
    by_cases hak : f a = k
    · have ht : t.find? (fun a => decide (f a = k)) = none := by
        rw [List.find?_eq_none]
        intro x hx hfx
        exact hnd.1 (List.mem_map.2 ⟨x, hx, (of_decide_eq_true hfx).trans hak.symm⟩)
      rw [ht, List.find?_cons_of_pos (by simpa using hak), if_pos hak]
      cases hg : g a <;> simp [hg]
    · rw [List.find?_cons_of_neg (by simpa using hak), if_neg hak]

/-- The step of a write-if-present. -/
theorem get_writeOpt (m : HMap κ β) (key : κ) (v : Option β) (k : κ) :
    (writeOpt m key v).get k = if key = k then v.or (m.get k) else m.get k := by
  cases v with
  | none => by_cases h : key = k <;> simp [writeOpt, h]
  | some x =>
    simp only [writeOpt, Replay.HMap.get_alter]
    by_cases h : key = k
    · rw [if_pos h.symm, if_pos h]; rfl
    · rw [if_neg (Ne.symm h), if_neg h]

end FoldAlter

section Pairs
variable {κ β : Type} [DecidableEq κ] [KeyHash κ]

theorem get_foldl_pairs : ∀ (l : List (κ × β)) (m : HMap κ β) (k : κ), (l.map Prod.fst).Nodup →
    (l.foldl (fun m p => m.alter p.1 (fun _ => some p.2)) m).get k
      = ((l.find? (fun p => decide (p.1 = k))).map Prod.snd).or (m.get k)
  | [], m, k, _ => by simp
  | p :: t, m, k, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons, get_foldl_pairs t _ k hnd.2, Replay.HMap.get_alter]
    by_cases hpk : p.1 = k
    · have ht : t.find? (fun p => decide (p.1 = k)) = none := by
        rw [List.find?_eq_none]
        intro x hx hfx
        exact hnd.1 (List.mem_map.2 ⟨x, hx, (of_decide_eq_true hfx).trans hpk.symm⟩)
      rw [ht, List.find?_cons_of_pos (by simpa using hpk), if_pos hpk.symm]
      simp
    · rw [List.find?_cons_of_neg (by simpa using hpk), if_neg (Ne.symm hpk)]

theorem find?_pairs_of_mem (l : List (κ × β)) (k : κ) (v : β) (hm : (k, v) ∈ l) (hnd : (l.map Prod.fst).Nodup) :
    l.find? (fun p => decide (p.1 = k)) = some (k, v) := by
  induction l with
  | nil => cases hm
  | cons p t ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hm with rfl | hm
    · simp
    · have hne : p.1 ≠ k := fun h => hnd.1 (List.mem_map.2 ⟨(k, v), hm, by simp [h]⟩)
      rw [List.find?_cons_of_neg (by simpa using hne), ih hm hnd.2]

theorem find?_pairs_none (l : List (κ × β)) (k : κ) (h : ∀ v, (k, v) ∉ l) :
    l.find? (fun p => decide (p.1 = k)) = none := by
  rw [List.find?_eq_none]
  intro p hp hpk
  have : p.1 = k := of_decide_eq_true hpk
  exact h p.2 (by rw [← this]; simpa using hp)

/-- **A map written from pairs with distinct keys reads a key's pair's value, and nothing else.** -/
theorem get_writeAll_empty (l : List (κ × β)) (n : Nat) (hnd : (l.map Prod.fst).Nodup) (k : κ) (v : Option β)
    (hv : ∀ x, (k, x) ∈ l ↔ v = some x) :
    (writeAll l (HMap.empty n)).get k = v := by
  unfold writeAll
  rw [get_foldl_pairs l _ k hnd, Replay.HMap.get_empty, Option.or_none]
  cases v with
  | none => rw [find?_pairs_none l k (fun x hx => by simpa using (hv x).1 hx)]; rfl
  | some x => rw [find?_pairs_of_mem l k x ((hv x).2 rfl) hnd]; rfl

end Pairs

theorem find?_openDays (st : State) (hs : List (Nat × Replay.HeaderRec)) (L d : Nat) (hd : L ≤ d) :
    (daysFrom st hs L).find? (fun o => decide (o.day = d))
      = if d ∈ dayKeys st hs then some (openDayOf st hs d) else none := by
  unfold daysFrom
  rw [find?_map_filter_of_nodup (openDayOf st hs) OpenDay.day (fun _ => rfl) _ d (dayKeys st hs)
    (nodup_canon natLt_strictTotal _)]
  by_cases h : d ∈ dayKeys st hs <;> simp [h, hd]

theorem openDays_days_nodup (st : State) (hs : List (Nat × Replay.HeaderRec)) (L : Nat) :
    ((daysFrom st hs L).map OpenDay.day).Nodup := by
  unfold daysFrom
  rw [List.map_map]
  have : (OpenDay.day ∘ openDayOf st hs) = id := by funext d; rfl
  rw [this, List.map_id]
  exact (nodup_canon natLt_strictTotal _).sublist List.filter_sublist

/-- **The restored days read the fold's at and above the ledger day.** -/
theorem restore_days (st : State) (hs : List (Nat × Replay.HeaderRec)) (hk : AllKeyed st) (L n d : Nat) (hd : L ≤ d) :
    ((daysFrom st hs L).foldl (fun m o => writeOpt m o.day o.acc) (HMap.empty n)).get d = st.days.get d := by
  rw [get_foldl_step OpenDay.day OpenDay.acc _ (fun m o k => get_writeOpt m o.day o.acc k) _ _ d
    (openDays_days_nodup st hs L), find?_openDays st hs L d hd, Replay.HMap.get_empty]
  by_cases h : d ∈ dayKeys st hs
  · rw [if_pos h]; simp [openDayOf]
  · rw [if_neg h]
    simp only [Option.bind_none, Option.or_none]
    exact (get_eq_none_of_not_mem_keys _ hk.1 d (not_mem_dayKeys h).1).symm

theorem restore_seams (st : State) (hs : List (Nat × Replay.HeaderRec)) (hk : AllKeyed st) (L n d : Nat) (hd : L ≤ d) :
    ((daysFrom st hs L).foldl (fun m o => writeOpt m o.day o.seam) (HMap.empty n)).get d = st.seams.get d := by
  rw [get_foldl_step OpenDay.day OpenDay.seam _ (fun m o k => get_writeOpt m o.day o.seam k) _ _ d
    (openDays_days_nodup st hs L), find?_openDays st hs L d hd, Replay.HMap.get_empty]
  by_cases h : d ∈ dayKeys st hs
  · rw [if_pos h]; simp [openDayOf]
  · rw [if_neg h]
    simp only [Option.bind_none, Option.or_none]
    exact (get_eq_none_of_not_mem_keys _ hk.2.2.2.2.2.2.2.2 d (not_mem_dayKeys h).2.1).symm

/-! ### The all-time maps -/

theorem items_ids_nodup (st : State) : (((itemIds st).map (itemAggOf st)).map ItemAgg.id).Nodup := by
  rw [List.map_map]
  have : (ItemAgg.id ∘ itemAggOf st) = id := by funext i; rfl
  rw [this, List.map_id]
  exact nodup_canon idLt_strictTotal _

theorem find?_items (st : State) (i : Log.Id) :
    ((itemIds st).map (itemAggOf st)).find? (fun a => decide (a.id = i))
      = if i ∈ itemIds st then some (itemAggOf st i) else none := by
  have h := find?_map_of_nodup (itemAggOf st) ItemAgg.id (fun _ => rfl) i (itemIds st) (nodup_canon idLt_strictTotal _)
  by_cases hi : i ∈ itemIds st
  · rw [if_pos hi] at h ⊢; exact h
  · rw [if_neg hi] at h ⊢; exact h

theorem restore_items (st : State) (hk : AllKeyed st) (n : Nat) (i : Log.Id) :
    (((itemIds st).map (itemAggOf st)).foldl (fun m a => writeOpt m a.id a.acc) (HMap.empty n)).get i = st.items.get i := by
  rw [get_foldl_step ItemAgg.id ItemAgg.acc _ (fun m a k => get_writeOpt m a.id a.acc k) _ _ i (items_ids_nodup st),
    find?_items, Replay.HMap.get_empty]
  by_cases h : i ∈ itemIds st
  · rw [if_pos h]; simp [itemAggOf]
  · rw [if_neg h]
    simp only [Option.bind_none, Option.or_none]
    exact (get_eq_none_of_not_mem_keys _ hk.2.1 i (not_mem_itemIds h).1).symm

theorem restore_lastDone (st : State) (hk : AllKeyed st) (n : Nat) (i : Log.Id) :
    (((itemIds st).map (itemAggOf st)).foldl (fun m a => writeOpt m a.id a.lastDone) (HMap.empty n)).get i
      = st.lastDone.get i := by
  rw [get_foldl_step ItemAgg.id ItemAgg.lastDone _ (fun m a k => get_writeOpt m a.id a.lastDone k) _ _ i
    (items_ids_nodup st), find?_items, Replay.HMap.get_empty]
  by_cases h : i ∈ itemIds st
  · rw [if_pos h]; simp [itemAggOf]
  · rw [if_neg h]
    simp only [Option.bind_none, Option.or_none]
    exact (get_eq_none_of_not_mem_keys _ hk.2.2.2.1 i (not_mem_itemIds h).2.1).symm

theorem restore_dropped (st : State) (hk : AllKeyed st) (n : Nat) (i : Log.Id) :
    (((itemIds st).map (itemAggOf st)).foldl (fun m a => if a.dropped then m.alter a.id (fun _ => some ()) else m)
      (HMap.empty n)).get i = st.dropped.get i := by
  rw [get_foldl_step ItemAgg.id (fun a => if a.dropped then some () else none) _ (fun m a k => by
      by_cases hd : a.dropped = true
      · simp only [hd, if_true, Replay.HMap.get_alter]
        by_cases h : a.id = k
        · rw [if_pos h.symm, if_pos h]; rfl
        · rw [if_neg (Ne.symm h), if_neg h]
      · simp only [hd, Bool.false_eq_true, if_false]
        by_cases h : a.id = k <;> simp [h]) _ _ i (items_ids_nodup st), find?_items, Replay.HMap.get_empty]
  by_cases h : i ∈ itemIds st
  · rw [if_pos h]
    simp only [Option.bind_some, itemAggOf, Option.or_none]
    cases st.dropped.get i <;> rfl
  · rw [if_neg h]
    simp only [Option.bind_none, Option.or_none]
    exact (get_eq_none_of_not_mem_keys _ hk.2.2.2.2.2.2.2.1 i (not_mem_itemIds h).2.2.1).symm

theorem filterMap_pair_fst_sublist {κ β : Type} (g : κ → Option β) : ∀ (l : List κ),
    ((l.filterMap (fun k => (g k).map (fun v => (k, v)))).map Prod.fst).Sublist l
  | [] => List.Sublist.slnil
  | k :: l => by
    rw [List.filterMap_cons]
    cases g k with
    | none => exact (filterMap_pair_fst_sublist g l).cons k
    | some v => simpa using (filterMap_pair_fst_sublist g l).cons_cons k

theorem mem_filterMap_pair {κ β : Type} [DecidableEq κ] [KeyHash κ] (m : HMap κ β) (hm : m.Keyed) {lt : κ → κ → Bool}
    (hlt : StrictTotal lt) (P : κ → Bool) (k : κ) (x : β) (hP : P k = true) :
    (k, x) ∈ (canon lt ((m.pairs.filter (fun p => P p.1)).map Prod.fst)).filterMap (fun j => (m.get j).map (fun v => (j, v)))
      ↔ m.get k = some x := by
  constructor
  · intro h
    obtain ⟨j, _, hj⟩ := List.mem_filterMap.1 h
    cases hg : m.get j with
    | none => rw [hg] at hj; cases hj
    | some v => rw [hg] at hj; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hj; obtain ⟨rfl, rfl⟩ := hj; exact hg
  · intro h
    refine List.mem_filterMap.2 ⟨k, ?_, by rw [h]; rfl⟩
    rw [mem_canon hlt]
    obtain ⟨p, hp, hpk⟩ := List.mem_map.1 (mem_keys_of_get m hm k x h)
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by rw [hpk]; exact hP⟩, hpk⟩

theorem restore_named (st : State) (hk : AllKeyed st) (n : Nat) (k : List Char × Option Log.Id) :
    (writeAll (namedOf st) (HMap.empty n)).get k = st.named.get k := by
  have hnd : ((namedOf st).map Prod.fst).Nodup :=
    (nodup_canon namedKeyLt_strictTotal _).sublist (filterMap_pair_fst_sublist _ _)
  apply get_writeAll_empty _ n hnd k
  intro x
  have h := mem_filterMap_pair st.named hk.2.2.2.2.2.2.1 namedKeyLt_strictTotal (fun _ => true) k x rfl
  have hfe : st.named.pairs.filter (fun p => (fun _ => true) p.1) = st.named.pairs := List.filter_eq_self.2 (fun _ _ => rfl)
  rw [hfe] at h
  unfold namedOf
  rw [h]

/-! ### The window maps -/

theorem mem_windowsFrom (st : State) (H : Nat) (w : WindowRecord) :
    w ∈ windowsFrom st H ↔ ∃ d, d ∈ winKeys st ∧ H ≤ d ∧ w = windowOf st d := by
  unfold windowsFrom
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨d, ⟨hd, hH⟩, rfl⟩; exact ⟨d, hd, hH, rfl⟩
  · rintro ⟨d, hd, hH, rfl⟩; exact ⟨d, ⟨hd, hH⟩, rfl⟩

theorem mem_itemMin (st : State) (hk : AllKeyed st) (d : Nat) (i : Log.Id) (x : Nat) :
    (i, x) ∈ (windowOf st d).itemMin ↔ st.itemDays.get (d, i) = some x := by
  show (i, x) ∈ (canon idLt ((st.itemDays.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2))).filterMap
      (fun i => (st.itemDays.get (d, i)).map (fun m => (i, m))) ↔ _
  constructor
  · intro h
    obtain ⟨j, _, hj⟩ := List.mem_filterMap.1 h
    cases hg : st.itemDays.get (d, j) with
    | none => rw [hg] at hj; cases hj
    | some v => rw [hg] at hj; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hj; obtain ⟨rfl, rfl⟩ := hj; exact hg
  · intro h
    refine List.mem_filterMap.2 ⟨i, ?_, by rw [h]; rfl⟩
    rw [mem_canon idLt_strictTotal]
    obtain ⟨p, hp, hpk⟩ := List.mem_map.1 (mem_keys_of_get st.itemDays hk.2.2.1 (d, i) x h)
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by simp [hpk]⟩, by simp [hpk]⟩

theorem mem_winKeys_of_itemDay (st : State) (hk : AllKeyed st) (d : Nat) (i : Log.Id) (x : Nat)
    (h : st.itemDays.get (d, i) = some x) : d ∈ winKeys st := by
  unfold winKeys
  rw [mem_canon natLt_strictTotal]
  obtain ⟨p, hp, hpk⟩ := List.mem_map.1 (mem_keys_of_get st.itemDays hk.2.2.1 (d, i) x h)
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨p, hp, by simp [hpk]⟩))

theorem nodup_flatMap_keyed {γ δ : Type} (day : γ → Nat) (inner : γ → List δ) :
    ∀ (ws : List γ), (ws.map day).Nodup → (∀ w ∈ ws, (inner w).Nodup) →
      (ws.flatMap (fun w => (inner w).map (fun x => (day w, x)))).Nodup
  | [], _, _ => List.nodup_nil
  | w :: ws, hdays, hin => by
    rw [List.map_cons, List.nodup_cons] at hdays
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨List.Pairwise.map _ (fun a b h he => h (by simpa using he)) (hin w List.mem_cons_self),
      nodup_flatMap_keyed day inner ws hdays.2 (fun w' hw' => hin w' (List.mem_cons_of_mem _ hw')), ?_⟩
    intro a ha b hb hab
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 ha
    obtain ⟨w', hw', hb'⟩ := List.mem_flatMap.1 hb
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hb'
    simp only [Prod.mk.injEq] at hab
    exact hdays.1 (List.mem_map.2 ⟨w', hw', hab.1.symm⟩)

theorem windows_days_nodup (st : State) (H : Nat) : ((windowsFrom st H).map WindowRecord.day).Nodup := by
  unfold windowsFrom
  rw [List.map_map]
  have : (WindowRecord.day ∘ windowOf st) = id := by funext d; rfl
  rw [this, List.map_id]
  exact (nodup_canon natLt_strictTotal _).sublist List.filter_sublist

theorem itemMin_ids_nodup (st : State) (d : Nat) : ((windowOf st d).itemMin.map Prod.fst).Nodup :=
  (nodup_canon idLt_strictTotal _).sublist (filterMap_pair_fst_sublist _ _)

/-- **The restored item minutes read the fold's at and above the window horizon.** -/
theorem restore_itemDays (st : State) (hk : AllKeyed st) (H n d : Nat) (i : Log.Id) (hH : H ≤ d) :
    (writeAll ((windowsFrom st H).flatMap (fun w => w.itemMin.map (fun p => ((w.day, p.1), p.2)))) (HMap.empty n)).get (d, i)
      = st.itemDays.get (d, i) := by
  have hnd : (((windowsFrom st H).flatMap (fun w => w.itemMin.map (fun p => ((w.day, p.1), p.2)))).map Prod.fst).Nodup := by
    rw [List.map_flatMap]
    have e : (fun w : WindowRecord => (w.itemMin.map (fun p => ((w.day, p.1), p.2))).map Prod.fst)
        = (fun w => (w.itemMin.map Prod.fst).map (fun x => (w.day, x))) := by
      funext w; simp [List.map_map]
    rw [e]
    refine nodup_flatMap_keyed WindowRecord.day (fun w => w.itemMin.map Prod.fst) _ (windows_days_nodup st H) ?_
    intro w hw
    obtain ⟨d', _, _, rfl⟩ := (mem_windowsFrom st H w).1 hw
    exact itemMin_ids_nodup st d'
  apply get_writeAll_empty _ n hnd (d, i)
  intro x
  constructor
  · intro hm
    obtain ⟨w, hw, hp⟩ := List.mem_flatMap.1 hm
    obtain ⟨p, hp', hpe⟩ := List.mem_map.1 hp
    obtain ⟨d', _, _, rfl⟩ := (mem_windowsFrom st H w).1 hw
    simp only [Prod.mk.injEq] at hpe
    obtain ⟨⟨hd', hi⟩, hx⟩ := hpe
    have : (windowOf st d').day = d' := rfl
    rw [this] at hd'
    subst hd'; subst hi; subst hx
    exact (mem_itemMin st hk _ _ _).1 hp'
  · intro hv
    refine List.mem_flatMap.2 ⟨windowOf st d, (mem_windowsFrom st H _).2 ⟨d, mem_winKeys_of_itemDay st hk d i x hv, hH, rfl⟩, ?_⟩
    exact List.mem_map.2 ⟨(i, x), (mem_itemMin st hk d i x).2 hv, rfl⟩

theorem mem_doneIds (st : State) (hk : AllKeyed st) (d : Nat) (i : Log.Id) :
    i ∈ (windowOf st d).doneIds ↔ st.doneDates.get (d, i) = some () := by
  show i ∈ canon idLt ((st.doneDates.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2)) ↔ _
  rw [mem_canon idLt_strictTotal]
  constructor
  · intro h
    obtain ⟨p, hp, hpi⟩ := List.mem_map.1 h
    have hpd := of_decide_eq_true (List.mem_filter.1 hp).2
    have hkey : (d, i) ∈ st.doneDates.pairs.map Prod.fst := List.mem_map.2 ⟨p, (List.mem_filter.1 hp).1, by
      rw [← hpd, ← hpi]⟩
    have := (Replay.HMap.mem_keys_pairs_iff _ hk.2.2.2.2.1 (d, i)).1 hkey
    cases hg : st.doneDates.get (d, i) with
    | none => rw [hg] at this; cases this
    | some u => rfl
  · intro h
    obtain ⟨p, hp, hpk⟩ := List.mem_map.1 (mem_keys_of_get st.doneDates hk.2.2.2.2.1 (d, i) () h)
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by simp [hpk]⟩, by simp [hpk]⟩

theorem mem_winKeys_of_doneDate (st : State) (hk : AllKeyed st) (d : Nat) (i : Log.Id)
    (h : st.doneDates.get (d, i) = some ()) : d ∈ winKeys st := by
  unfold winKeys
  rw [mem_canon natLt_strictTotal]
  obtain ⟨p, hp, hpk⟩ := List.mem_map.1 (mem_keys_of_get st.doneDates hk.2.2.2.2.1 (d, i) () h)
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨p, hp, by simp [hpk]⟩))

/-- **The restored done dates read the fold's at and above the window horizon.** -/
theorem restore_doneDates (st : State) (hk : AllKeyed st) (H n d : Nat) (i : Log.Id) (hH : H ≤ d) :
    (writeAll ((windowsFrom st H).flatMap (fun w => w.doneIds.map (fun j => ((w.day, j), ())))) (HMap.empty n)).get (d, i)
      = st.doneDates.get (d, i) := by
  have hnd : (((windowsFrom st H).flatMap (fun w => w.doneIds.map (fun j => ((w.day, j), ())))).map Prod.fst).Nodup := by
    rw [List.map_flatMap]
    have e : (fun w : WindowRecord => (w.doneIds.map (fun j => ((w.day, j), ()))).map Prod.fst)
        = (fun w => w.doneIds.map (fun x => (w.day, x))) := by
      funext w; simp [List.map_map]
    rw [e]
    refine nodup_flatMap_keyed WindowRecord.day (fun w => w.doneIds) _ (windows_days_nodup st H) ?_
    intro w hw
    obtain ⟨d', _, _, rfl⟩ := (mem_windowsFrom st H w).1 hw
    exact nodup_canon idLt_strictTotal _
  apply get_writeAll_empty _ n hnd (d, i)
  intro x
  cases x
  constructor
  · intro hm
    obtain ⟨w, hw, hp⟩ := List.mem_flatMap.1 hm
    obtain ⟨j, hj, hje⟩ := List.mem_map.1 hp
    obtain ⟨d', _, _, rfl⟩ := (mem_windowsFrom st H w).1 hw
    simp only [Prod.mk.injEq] at hje
    obtain ⟨⟨hd', hi⟩, -⟩ := hje
    have : (windowOf st d').day = d' := rfl
    rw [this] at hd'
    subst hd'; subst hi
    exact (mem_doneIds st hk _ _).1 hj
  · intro hv
    refine List.mem_flatMap.2 ⟨windowOf st d, (mem_windowsFrom st H _).2 ⟨d, mem_winKeys_of_doneDate st hk d i hv, hH, rfl⟩, ?_⟩
    exact List.mem_map.2 ⟨i, (mem_doneIds st hk d i).2 hv, rfl⟩

/-! ### The instances -/

theorem mem_windowInst (st : State) (hk : AllKeyed st) (d : Nat) (key : List Char × List Char) (x : Replay.InstRec) :
    (key, x) ∈ (windowOf st d).inst ↔ Log.instDate? key.2 = some d ∧ st.instances.get key = some x := by
  show (key, x) ∈ (canon instKeyLt ((st.instances.pairs.filter (fun p => decide (Log.instDate? p.1.2 = some d))).map
      Prod.fst)).filterMap (fun key => (st.instances.get key).map (fun r => (key, r))) ↔ _
  constructor
  · intro h
    obtain ⟨j, hj, hjx⟩ := List.mem_filterMap.1 h
    cases hg : st.instances.get j with
    | none => rw [hg] at hjx; cases hjx
    | some v =>
      rw [hg] at hjx
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hjx
      obtain ⟨rfl, rfl⟩ := hjx
      rw [mem_canon instKeyLt_strictTotal] at hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
      exact ⟨of_decide_eq_true (List.mem_filter.1 hp).2, hg⟩
  · rintro ⟨hd, hg⟩
    refine List.mem_filterMap.2 ⟨key, ?_, by rw [hg]; rfl⟩
    rw [mem_canon instKeyLt_strictTotal]
    obtain ⟨p, hp, hpk⟩ := List.mem_map.1 (mem_keys_of_get st.instances hk.2.2.2.2.2.1 key x hg)
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by rw [hpk]; simp [hd]⟩, hpk⟩

theorem mem_instOther (st : State) (hk : AllKeyed st) (key : List Char × List Char) (x : Replay.InstRec) :
    (key, x) ∈ instOtherOf st ↔ Log.instDate? key.2 = none ∧ st.instances.get key = some x := by
  show (key, x) ∈ (canon instKeyLt ((st.instances.pairs.filter (fun p => (Log.instDate? p.1.2).isNone)).map
      Prod.fst)).filterMap (fun key => (st.instances.get key).map (fun r => (key, r))) ↔ _
  constructor
  · intro h
    obtain ⟨j, hj, hjx⟩ := List.mem_filterMap.1 h
    cases hg : st.instances.get j with
    | none => rw [hg] at hjx; cases hjx
    | some v =>
      rw [hg] at hjx
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hjx
      obtain ⟨rfl, rfl⟩ := hjx
      rw [mem_canon instKeyLt_strictTotal] at hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
      exact ⟨by simpa using (List.mem_filter.1 hp).2, hg⟩
  · rintro ⟨hd, hg⟩
    refine List.mem_filterMap.2 ⟨key, ?_, by rw [hg]; rfl⟩
    rw [mem_canon instKeyLt_strictTotal]
    obtain ⟨p, hp, hpk⟩ := List.mem_map.1 (mem_keys_of_get st.instances hk.2.2.2.2.2.1 key x hg)
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by rw [hpk]; simp [hd]⟩, hpk⟩

theorem mem_winKeys_of_inst (st : State) (hk : AllKeyed st) (key : List Char × List Char) (x : Replay.InstRec) (d : Nat)
    (hd : Log.instDate? key.2 = some d) (h : st.instances.get key = some x) : d ∈ winKeys st := by
  unfold winKeys
  rw [mem_canon natLt_strictTotal]
  obtain ⟨p, hp, hpk⟩ := List.mem_map.1 (mem_keys_of_get st.instances hk.2.2.2.2.2.1 key x h)
  exact List.mem_append_right _ (List.mem_filterMap.2 ⟨p, hp, by rw [hpk, hd]⟩)

/-- **The restored instances read the fold's**, every non-date key and every date key at or above the horizon. -/
theorem restore_instances (st : State) (hk : AllKeyed st) (H n : Nat) (key : List Char × List Char)
    (hkey : ∀ d, Log.instDate? key.2 = some d → H ≤ d) :
    (writeAll ((windowsFrom st H).flatMap (·.inst) ++ instOtherOf st) (HMap.empty n)).get key = st.instances.get key := by
  have hnd : (((windowsFrom st H).flatMap (·.inst) ++ instOtherOf st).map Prod.fst).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨?_, (nodup_canon instKeyLt_strictTotal _).sublist (filterMap_pair_fst_sublist _ _), ?_⟩
    · -- window keys: each names its window's date, and each window's are distinct
      rw [List.map_flatMap]
      have hws := windows_days_nodup st H
      generalize hW : windowsFrom st H = ws at hws
      have hin : ∀ w ∈ ws, ∃ d, w = windowOf st d := fun w hw => by
        rw [← hW] at hw; obtain ⟨d, _, _, rfl⟩ := (mem_windowsFrom st H w).1 hw; exact ⟨d, rfl⟩
      clear hW
      induction ws with
      | nil => exact List.nodup_nil
      | cons w ws ih =>
        rw [List.map_cons, List.nodup_cons] at hws
        rw [List.flatMap_cons, List.nodup_append]
        obtain ⟨d, rfl⟩ := hin w List.mem_cons_self
        refine ⟨(nodup_canon instKeyLt_strictTotal _).sublist (filterMap_pair_fst_sublist _ _),
          ih hws.2 (fun w' hw' => hin w' (List.mem_cons_of_mem _ hw')), ?_⟩
        intro a ha b hb hab
        subst hab
        obtain ⟨pa, hpa, rfl⟩ := List.mem_map.1 ha
        obtain ⟨w', hw', hb'⟩ := List.mem_flatMap.1 hb
        obtain ⟨pb, hpb, hpbe⟩ := List.mem_map.1 hb'
        obtain ⟨d', rfl⟩ := hin w' (List.mem_cons_of_mem _ hw')
        have h1 := ((mem_windowInst st hk d pa.1 pa.2).1 hpa).1
        have h2 := ((mem_windowInst st hk d' pb.1 pb.2).1 hpb).1
        rw [hpbe, h1] at h2
        cases h2
        exact hws.1 (List.mem_map.2 ⟨windowOf st d, hw', rfl⟩)
    · intro a ha b hb hab
      subst hab
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      obtain ⟨q, hq, hqa⟩ := List.mem_map.1 hb
      obtain ⟨w, hw, hpw⟩ := List.mem_flatMap.1 hp
      obtain ⟨d, _, _, rfl⟩ := (mem_windowsFrom st H w).1 hw
      have h1 := ((mem_windowInst st hk d p.1 p.2).1 hpw).1
      have h2 := ((mem_instOther st hk q.1 q.2).1 hq).1
      rw [hqa, h1] at h2
      cases h2
  apply get_writeAll_empty _ n hnd key
  intro x
  constructor
  · intro hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨w, hw, hpw⟩ := List.mem_flatMap.1 hm
      obtain ⟨d, _, _, rfl⟩ := (mem_windowsFrom st H w).1 hw
      exact ((mem_windowInst st hk d key x).1 hpw).2
    · exact ((mem_instOther st hk key x).1 hm).2
  · intro hv
    cases hd : Log.instDate? key.2 with
    | none => exact List.mem_append_right _ ((mem_instOther st hk key x).2 ⟨hd, hv⟩)
    | some d =>
      refine List.mem_append_left _ (List.mem_flatMap.2 ⟨windowOf st d, (mem_windowsFrom st H _).2
        ⟨d, mem_winKeys_of_inst st hk key x d hd hv, hkey d hd, rfl⟩, ?_⟩)
      exact (mem_windowInst st hk d key x).2 ⟨hd, hv⟩

/-! ### The per-day lists -/

theorem filter_flatMap_days {α : Type} (f : α → Nat) (l : List α) (d : Nat) :
    ∀ (ks : List Nat), ks.Nodup →
      (ks.flatMap (fun d' => l.filter (fun o => decide (f o = d')))).filter (fun o => decide (f o = d))
        = if d ∈ ks then l.filter (fun o => decide (f o = d)) else []
  | [], _ => by simp
  | k :: ks, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons, List.filter_append, filter_flatMap_days f l d ks hnd.2]
    by_cases hk : k = d
    · subst hk
      have hff : (l.filter (fun o => decide (f o = k))).filter (fun o => decide (f o = k))
          = l.filter (fun o => decide (f o = k)) := List.filter_eq_self.2 (fun o ho => (List.mem_filter.1 ho).2)
      rw [hff, if_neg hnd.1]; simp
    · have hff : (l.filter (fun o => decide (f o = k))).filter (fun o => decide (f o = d)) = [] :=
        List.filter_eq_nil_iff.2 (fun o ho hod => by
          have h1 := of_decide_eq_true (List.mem_filter.1 ho).2
          have h2 := of_decide_eq_true hod
          exact hk (h1.symm.trans h2))
      rw [hff, List.nil_append]
      simp [List.mem_cons, Ne.symm hk]

theorem dayKeys_filter_nodup (st : State) (hs : List (Nat × Replay.HeaderRec)) (L : Nat) :
    ((dayKeys st hs).filter (fun d => decide (L ≤ d))).Nodup :=
  (nodup_canon natLt_strictTotal _).sublist List.filter_sublist

theorem mem_dayKeys_filter (st : State) (hs : List (Nat × Replay.HeaderRec)) (L d : Nat) (hd : L ≤ d) :
    d ∈ (dayKeys st hs).filter (fun d => decide (L ≤ d)) ↔ d ∈ dayKeys st hs := by
  simp [List.mem_filter, hd]

theorem restore_list {α : Type} (f : α → Nat) (l : List α) (st : State) (hs : List (Nat × Replay.HeaderRec)) (L d : Nat)
    (hd : L ≤ d) (hnil : d ∉ dayKeys st hs → l.filter (fun o => decide (f o = d)) = []) :
    (((dayKeys st hs).filter (fun d => decide (L ≤ d))).flatMap (fun d' => l.filter (fun o => decide (f o = d')))).filter
      (fun o => decide (f o = d)) = l.filter (fun o => decide (f o = d)) := by
  rw [filter_flatMap_days f l d _ (dayKeys_filter_nodup st hs L)]
  by_cases h : d ∈ dayKeys st hs
  · rw [if_pos ((mem_dayKeys_filter st hs L d hd).2 h)]
  · rw [if_neg (fun h' => h ((mem_dayKeys_filter st hs L d hd).1 h')), hnil h]

theorem map_pair_of_fst {β : Type} (X : List (Nat × β)) (d : Nat) (h : ∀ p ∈ X, p.1 = d) :
    X.map (fun p => (d, p.2)) = X := by
  conv => rhs; rw [← List.map_id X]
  exact List.map_congr_left (fun p hp => by rw [← h p hp]; rfl)

/-! ### The specification checkpoint, field by field -/

section CkptProj

variable (z : Cal.Tz) (T₀ L cut : Nat) (es er : List Entry) (ws : List (Nat × Log.LWarn))

theorem ckpt_openDays : (ckptOfEntries z T₀ L cut es er ws).openDays
    = daysFrom (foldedState z es er) (foldedHeaders z es er) L := by simp only [ckptOfEntries]
theorem ckpt_items : (ckptOfEntries z T₀ L cut es er ws).items
    = (itemIds (foldedState z es er)).map (itemAggOf (foldedState z es er)) := by simp only [ckptOfEntries]
theorem ckpt_window : (ckptOfEntries z T₀ L cut es er ws).window = windowsFrom (foldedState z es er) (horizonOf L) := by
  simp only [ckptOfEntries]
theorem ckpt_instOther : (ckptOfEntries z T₀ L cut es er ws).instOther = instOtherOf (foldedState z es er) := by
  simp only [ckptOfEntries]
theorem ckpt_named : (ckptOfEntries z T₀ L cut es er ws).named = namedOf (foldedState z es er) := by
  simp only [ckptOfEntries]
theorem ckpt_machine : (ckptOfEntries z T₀ L cut es er ws).machine = (foldedState z es er).machine := by
  simp only [ckptOfEntries]
theorem ckpt_lastEff : (ckptOfEntries z T₀ L cut es er ws).lastEff = (foldedState z es er).global.lastEffective := by
  simp only [ckptOfEntries]
theorem ckpt_rwarns : (ckptOfEntries z T₀ L cut es er ws).rwarns = (foldedState z es er).rwarns.reverse := by
  simp only [ckptOfEntries]
theorem ckpt_longestLeak : (ckptOfEntries z T₀ L cut es er ws).longestLeak = (foldedState z es er).longestLeak := by
  simp only [ckptOfEntries]
theorem ckpt_unknown : (ckptOfEntries z T₀ L cut es er ws).unknown = (foldedState z es er).unknown := by
  simp only [ckptOfEntries]
theorem ckpt_ledgerDay : (ckptOfEntries z T₀ L cut es er ws).ledgerDay = L := by simp only [ckptOfEntries]

end CkptProj

theorem openDays_flatMap {γ : Type} (st : State) (hs : List (Nat × Replay.HeaderRec)) (L : Nat) (g : OpenDay → List γ) :
    (daysFrom st hs L).flatMap g = ((dayKeys st hs).filter (fun d => decide (L ≤ d))).flatMap (fun d => g (openDayOf st hs d)) := by
  unfold daysFrom
  exact flatMap_map_eq _ _ _

/-- **A checkpoint's restored state agrees with the fold that made it** at and above its horizons, whatever the bucket
count. -/
theorem restore_agrees (z : Cal.Tz) (T₀ L cut : Nat) (es er : List Entry) (ws : List (Nat × Log.LWarn)) (n : Nat) :
    AgreeAbove L (horizonOf L) (restore (ckptOfEntries z T₀ L cut es er ws) n) (foldedState z es er) := by
  have hk := allKeyed_foldedState z es er
  have hMA := ckpt_machine z T₀ L cut es er ws
  have hLE := ckpt_lastEff z T₀ L cut es er ws
  have hRW := ckpt_rwarns z T₀ L cut es er ws
  have hLL := ckpt_longestLeak z T₀ L cut es er ws
  have hUN := ckpt_unknown z T₀ L cut es er ws
  have hOD := ckpt_openDays z T₀ L cut es er ws
  have hIT := ckpt_items z T₀ L cut es er ws
  have hWI := ckpt_window z T₀ L cut es er ws
  have hIO := ckpt_instOther z T₀ L cut es er ws
  have hNA := ckpt_named z T₀ L cut es er ws
  generalize ckptOfEntries z T₀ L cut es er ws = K at *
  generalize foldedState z es er = st at *
  generalize foldedHeaders z es er = hs at *
  have hlist : ∀ {α : Type} (f : α → Nat) (l : List α) (g : OpenDay → List α),
      (∀ d', g (openDayOf st hs d') = l.filter (fun o => decide (f o = d'))) →
      (∀ d, d ∉ dayKeys st hs → l.filter (fun o => decide (f o = d)) = []) →
      ∀ d, L ≤ d → (K.openDays.flatMap g).filter (fun o => decide (f o = d)) = l.filter (fun o => decide (f o = d)) := by
    intro α f l g hg hnil d hd
    rw [hOD, openDays_flatMap]
    have e : (fun d' => g (openDayOf st hs d')) = (fun d' => l.filter (fun o => decide (f o = d'))) := funext hg
    rw [e]
    exact restore_list f l st hs L d hd (hnil d)
  refine ⟨fun d hd => ?_, fun d hd => ?_, fun d i hd => ?_, fun d i hd => ?_, fun key hkey => ?_, fun i => ?_,
    fun i => ?_, fun key => ?_, fun i => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (K.openDays.foldl (fun m o => writeOpt m o.day o.acc) (HMap.empty n)).get d = _
    rw [hOD]; exact restore_days st hs hk L n d hd
  · show (K.openDays.foldl (fun m o => writeOpt m o.day o.seam) (HMap.empty n)).get d = _
    rw [hOD]; exact restore_seams st hs hk L n d hd
  · show (writeAll (K.window.flatMap (fun w => w.itemMin.map (fun p => ((w.day, p.1), p.2)))) (HMap.empty n)).get (d, i) = _
    rw [hWI]; exact restore_itemDays st hk _ n d i hd
  · show (writeAll (K.window.flatMap (fun w => w.doneIds.map (fun j => ((w.day, j), ())))) (HMap.empty n)).get (d, i) = _
    rw [hWI]; exact restore_doneDates st hk _ n d i hd
  · show (writeAll (K.window.flatMap (·.inst) ++ K.instOther) (HMap.empty n)).get key = _
    rw [hWI, hIO]; exact restore_instances st hk _ n key hkey
  · show (K.items.foldl (fun m a => writeOpt m a.id a.acc) (HMap.empty n)).get i = _
    rw [hIT]; exact restore_items st hk n i
  · show (K.items.foldl (fun m a => writeOpt m a.id a.lastDone) (HMap.empty n)).get i = _
    rw [hIT]; exact restore_lastDone st hk n i
  · show (writeAll K.named (HMap.empty n)).get key = _
    rw [hNA]; exact restore_named st hk n key
  · show (K.items.foldl (fun m a => if a.dropped then m.alter a.id (fun _ => some ()) else m) (HMap.empty n)).get i = _
    rw [hIT]; exact restore_dropped st hk n i
  · intro d hd
    show (K.openDays.flatMap (fun o => o.energy.reverse)).filter _ = _
    exact hlist (·.day) st.energy (fun o => o.energy.reverse) (fun d' => by
        show ((st.energy.filter (fun o => decide (o.day = d'))).reverse).reverse = _
        rw [List.reverse_reverse])
      (fun d h => filter_day_eq_nil st.energy (fun x => x.day) d (not_mem_dayKeys h).2.2.1) d hd
  · intro d hd
    show (K.openDays.flatMap (fun o => o.durations.reverse)).filter _ = _
    exact hlist (·.day) st.durations (fun o => o.durations.reverse) (fun d' => by
        show ((st.durations.filter (fun o => decide (o.day = d'))).reverse).reverse = _
        rw [List.reverse_reverse])
      (fun d h => filter_day_eq_nil st.durations (fun x => x.day) d (not_mem_dayKeys h).2.2.2.1) d hd
  · intro d hd
    show (K.openDays.flatMap (fun o => o.interrupts.reverse)).filter _ = _
    exact hlist (·.day) st.interrupts (fun o => o.interrupts.reverse) (fun d' => by
        show ((st.interrupts.filter (fun o => decide (o.day = d'))).reverse).reverse = _
        rw [List.reverse_reverse])
      (fun d h => filter_day_eq_nil st.interrupts (fun x => x.day) d (not_mem_dayKeys h).2.2.2.2.1) d hd
  · intro d hd
    show (K.openDays.flatMap (fun o => (o.demotions.map (fun r => (o.day, r))).reverse)).filter _ = _
    refine hlist Prod.fst st.demotions _ (fun d' => ?_)
      (fun d h => filter_day_eq_nil st.demotions Prod.fst d (not_mem_dayKeys h).2.2.2.2.2.1) d hd
    show ((((st.demotions.filter (fun p => decide (p.1 = d'))).map Prod.snd).reverse.map (fun r => (d', r))).reverse) = _
    rw [List.map_reverse, List.reverse_reverse, List.map_map]
    exact map_pair_of_fst _ d' (fun p hp => of_decide_eq_true (List.mem_filter.1 hp).2)
  · intro d hd
    show (K.openDays.flatMap (fun o => (o.closes.map (fun r => (o.day, r))).reverse)).filter _ = _
    refine hlist Prod.fst st.closes _ (fun d' => ?_)
      (fun d h => filter_day_eq_nil st.closes Prod.fst d (not_mem_dayKeys h).2.2.2.2.2.2.1) d hd
    show ((((st.closes.filter (fun p => decide (p.1 = d'))).map Prod.snd).reverse.map (fun r => (d', r))).reverse) = _
    rw [List.map_reverse, List.reverse_reverse, List.map_map]
    exact map_pair_of_fst _ d' (fun p hp => of_decide_eq_true (List.mem_filter.1 hp).2)
  · exact hMA
  · exact hLE
  · show K.rwarns.reverse = _; rw [hRW, List.reverse_reverse]
  · exact hLL
  · exact hUN

end Seal
end Tm
