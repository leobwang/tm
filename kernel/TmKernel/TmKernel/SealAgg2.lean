import TmKernel.SealAgg
import TmKernel.SealGroup
import TmKernel.SealRestore
/-!
# SealAgg2 — the resumed answer's items and last day are the whole log's (stage 5, D9, W2)

Three keyed states: the checkpoint's fold `p`, the resumed state `x` (nothing below the horizons) and the whole log's
fold `y`, with `x` agreeing with `y` at and above the horizons, `y` agreeing with `p` below them, and every key of
`p` still a key of `y`.  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State HMap KeyHash)
open Log (Entry)

/-- An item's done dates in a state.  **Widened at stage 6 step K3b**: the body
moved to `Replay.doneDatesIn`, which `Facts.doneDatesOf` and `factsView`'s
`doneFirst`/`doneCount` rows now also call, so the three spellings of one list
are one function (AGENTS §5.3).  The statement is unchanged and every law below
is the same law. -/
def datesOf (st : State) (i : Log.Id) : List Nat := Replay.doneDatesIn st.doneDates i

theorem mem_datesOf (st : State) (hk : AllKeyed st) (i : Log.Id) (d : Nat) :
    d ∈ datesOf st i ↔ (st.doneDates.get (d, i)).isSome := by
  unfold datesOf
  rw [← Replay.HMap.mem_keys_pairs_iff _ hk.2.2.2.2.1 (d, i)]
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    have hqi := of_decide_eq_true (List.mem_filter.1 hq).2
    exact List.mem_map.2 ⟨q, (List.mem_filter.1 hq).1, by rw [← hqi]⟩
  · intro h
    obtain ⟨q, hq, hqk⟩ := List.mem_map.1 h
    exact List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, by simp [hqk]⟩, by simp [hqk]⟩

theorem datesOf_nodup (st : State) (hk : AllKeyed st) (i : Log.Id) : (datesOf st i).Nodup := by
  unfold datesOf
  have hnd := Replay.HMap.nodup_keys_pairs st.doneDates hk.2.2.2.2.1
  have hsub : ((st.doneDates.pairs.filter (fun p => decide (p.1.2 = i))).map Prod.fst).Nodup :=
    hnd.sublist (List.Sublist.map _ List.filter_sublist)
  have hpw := List.pairwise_map.1 hsub
  exact List.pairwise_map.2 (List.Pairwise.imp_of_mem
    (fun {a b} ha hb (hab : a.1 ≠ b.1) (heq : a.1.1 = b.1.1) => hab (Prod.ext heq
      ((of_decide_eq_true (List.mem_filter.1 ha).2).trans (of_decide_eq_true (List.mem_filter.1 hb).2).symm))) hpw)

theorem length_eq_of_mem_iff {l₁ l₂ : List Nat} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : ∀ d, d ∈ l₁ ↔ d ∈ l₂) :
    l₁.length = l₂.length :=
  ((List.perm_ext_iff_of_nodup h₁ h₂).2 h).length_eq

theorem length_filter_split (l : List Nat) (P : Nat → Bool) :
    l.length = (l.filter (fun d => !P d)).length + (l.filter P).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filter_cons, List.length_cons]
    cases hP : P a <;> simp [hP] <;> omega

/-- **Every done date of the whole log is a checkpoint date below the horizon or a resumed one at or above it.** -/
theorem dates_union {H : Nat} {p x y : State} (hp : AllKeyed p) (hx : AllKeyed x) (hy : AllKeyed y)
    (hkeep : ∀ k, (p.doneDates.get k).isSome → (y.doneDates.get k).isSome)
    (hxy : ∀ d i, H ≤ d → x.doneDates.get (d, i) = y.doneDates.get (d, i))
    (hbelow : ∀ d i, d < H → y.doneDates.get (d, i) = p.doneDates.get (d, i))
    (hxb : ∀ d i, d < H → x.doneDates.get (d, i) = none) (i : Log.Id) (d : Nat) :
    d ∈ datesOf p i ++ datesOf x i ↔ d ∈ datesOf y i := by
  rw [List.mem_append, mem_datesOf p hp, mem_datesOf x hx, mem_datesOf y hy]
  constructor
  · rintro (h | h)
    · exact hkeep _ h
    · by_cases hd : H ≤ d
      · rw [← hxy d i hd]; exact h
      · rw [hxb d i (by omega)] at h; cases h
  · intro h
    by_cases hd : H ≤ d
    · right; rw [hxy d i hd]; exact h
    · left; rw [← hbelow d i (by omega)]; exact h

theorem doneFirst_union {H : Nat} {p x y : State} (hp : AllKeyed p) (hx : AllKeyed x) (hy : AllKeyed y)
    (hkeep : ∀ k, (p.doneDates.get k).isSome → (y.doneDates.get k).isSome)
    (hxy : ∀ d i, H ≤ d → x.doneDates.get (d, i) = y.doneDates.get (d, i))
    (hbelow : ∀ d i, d < H → y.doneDates.get (d, i) = p.doneDates.get (d, i))
    (hxb : ∀ d i, d < H → x.doneDates.get (d, i) = none) (i : Log.Id) :
    minOpt (Replay.minDay? (datesOf p i)) (Replay.minDay? (datesOf x i)) = Replay.minDay? (datesOf y i) := by
  rw [← minDay?_append]
  exact minDay?_eq_of_mem_iff _ _ (dates_union hp hx hy hkeep hxy hbelow hxb i)

theorem doneCount_union {H : Nat} {p x y : State} (hp : AllKeyed p) (hx : AllKeyed x) (hy : AllKeyed y)
    (_hkeep : ∀ k, (p.doneDates.get k).isSome → (y.doneDates.get k).isSome)
    (hxy : ∀ d i, H ≤ d → x.doneDates.get (d, i) = y.doneDates.get (d, i))
    (hbelow : ∀ d i, d < H → y.doneDates.get (d, i) = p.doneDates.get (d, i))
    (hxb : ∀ d i, d < H → x.doneDates.get (d, i) = none) (i : Log.Id) :
    (datesOf p i).length - ((datesOf p i).filter (fun d => decide (H ≤ d))).length + (datesOf x i).length
      = (datesOf y i).length := by
  have hsp := length_filter_split (datesOf p i) (fun d => decide (H ≤ d))
  have hsy := length_filter_split (datesOf y i) (fun d => decide (H ≤ d))
  have h1 : ((datesOf y i).filter (fun d => !decide (H ≤ d))).length = ((datesOf p i).filter (fun d => !decide (H ≤ d))).length :=
    length_eq_of_mem_iff ((datesOf_nodup y hy i).sublist List.filter_sublist) ((datesOf_nodup p hp i).sublist List.filter_sublist)
      (fun d => by
        simp only [List.mem_filter, mem_datesOf y hy, mem_datesOf p hp, Bool.not_eq_true', decide_eq_false_iff_not]
        constructor
        · rintro ⟨h, hd⟩; exact ⟨by rw [← hbelow d i (by omega)]; exact h, hd⟩
        · rintro ⟨h, hd⟩; exact ⟨by rw [hbelow d i (by omega)]; exact h, hd⟩)
  have h2 : ((datesOf y i).filter (fun d => decide (H ≤ d))).length = (datesOf x i).length :=
    length_eq_of_mem_iff ((datesOf_nodup y hy i).sublist List.filter_sublist) (datesOf_nodup x hx i)
      (fun d => by
        simp only [List.mem_filter, mem_datesOf y hy, mem_datesOf x hx, decide_eq_true_eq]
        constructor
        · rintro ⟨h, hd⟩; rw [hxy d i hd]; exact h
        · intro h
          by_cases hd : H ≤ d
          · exact ⟨by rw [← hxy d i hd]; exact h, hd⟩
          · rw [hxb d i (by omega)] at h; cases h)
  omega

theorem lastDay_union {L : Nat} {p x y : State} (hp : AllKeyed p) (hx : AllKeyed x) (hy : AllKeyed y)
    (hkeep : ∀ d, (p.days.get d).isSome → (y.days.get d).isSome)
    (hxy : ∀ d, L ≤ d → x.days.get d = y.days.get d)
    (hbelow : ∀ d, d < L → y.days.get d = p.days.get d)
    (hxb : ∀ d, d < L → x.days.get d = none) :
    maxOpt (Replay.maxDay? (p.days.pairs.map Prod.fst)) (Replay.maxDay? (x.days.pairs.map Prod.fst))
      = Replay.maxDay? (y.days.pairs.map Prod.fst) := by
  rw [← maxDay?_append]
  apply maxDay?_eq_of_mem_iff
  intro d
  rw [List.mem_append, Replay.HMap.mem_keys_pairs_iff _ hp.1, Replay.HMap.mem_keys_pairs_iff _ hx.1,
    Replay.HMap.mem_keys_pairs_iff _ hy.1]
  constructor
  · rintro (h | h)
    · exact hkeep d h
    · by_cases hd : L ≤ d
      · rw [← hxy d hd]; exact h
      · rw [hxb d (by omega)] at h; cases h
  · intro h
    by_cases hd : L ≤ d
    · right; rw [hxy d hd]; exact h
    · left; rw [← hbelow d (by omega)]; exact h

theorem mem_itemIds_iff (st : State) (hk : AllKeyed st) (i : Log.Id) :
    i ∈ itemIds st ↔ (st.items.get i).isSome ∨ (st.lastDone.get i).isSome ∨ (st.dropped.get i).isSome ∨
      datesOf st i ≠ [] := by
  unfold itemIds
  rw [mem_canon idLt_strictTotal]
  simp only [List.mem_append]
  rw [Replay.HMap.mem_keys_pairs_iff _ hk.2.1, Replay.HMap.mem_keys_pairs_iff _ hk.2.2.2.1,
    Replay.HMap.mem_keys_pairs_iff _ hk.2.2.2.2.2.2.2.1]
  have hd : i ∈ st.doneDates.pairs.map (·.1.2) ↔ datesOf st i ≠ [] := by
    constructor
    · intro h hnil
      obtain ⟨q, hq, hqi⟩ := List.mem_map.1 h
      have : q.1.1 ∈ datesOf st i := List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, by simp [hqi]⟩, rfl⟩
      rw [hnil] at this; cases this
    · intro h
      obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ h
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hd
      exact List.mem_map.2 ⟨q, (List.mem_filter.1 hq).1, of_decide_eq_true (List.mem_filter.1 hq).2⟩
  rw [hd]
  constructor
  · rintro (((h | h) | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

end Seal
end Tm
