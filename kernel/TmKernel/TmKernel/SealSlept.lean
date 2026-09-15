import TmKernel.SealIndex
/-! # The slept table a resume reads (stage 5, D9, W2) -/
namespace Tm
namespace Seal

open Replay (KMap sleptByDay)
open Log (Entry)

theorem kmap_get_eq (l : List (Nat × Nat)) (d : Nat) : KMap.get l d = (l.find? (fun p => decide (p.1 = d))).map Prod.snd := rfl

/-- **The stored slept table reads the fold's at and after the ledger day.** -/
theorem get_storedSlept (sl : List (Nat × Nat)) (L d : Nat) (hd : L ≤ d) :
    KMap.get (storedSlept sl L) d = KMap.get sl d := by
  unfold storedSlept
  rw [kmap_get_eq, find?_filterMap_of_nodup (fun d => KMap.get sl d) d _
    ((nodup_canon natLt_strictTotal _).sublist List.filter_sublist)]
  by_cases h : d ∈ (canon natLt (sl.map Prod.fst)).filter (fun d => decide (L ≤ d))
  · rw [if_pos h]; cases KMap.get sl d <;> rfl
  · rw [if_neg h]
    have hn : d ∉ sl.map Prod.fst := fun hm => h (List.mem_filter.2 ⟨(mem_canon natLt_strictTotal _ _).2 hm, by simp [hd]⟩)
    simp only [Option.map_none]
    exact (KMap.get_eq_none_of_keys sl d (fun q hq hqd => hn (List.mem_map.2 ⟨q, hq, hqd⟩))).symm

theorem sleptByDay_append (z : Cal.Tz) (kw : List Cal.Instant) (X Y : List Entry) :
    sleptByDay z kw (X ++ Y) = sleptByDay z kw X ++ sleptByDay z kw Y := by
  unfold sleptByDay; rw [List.filterMap_append]

theorem filterMap_congr' {α β : Type} (f g : α → Option β) : ∀ (l : List α), (∀ a ∈ l, f a = g a) →
    l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a List.mem_cons_self,
      filterMap_congr' f g l (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem sleptByDay_congr (z : Cal.Tz) (kw kw' : List Cal.Instant) (sv : List Entry)
    (h : ∀ e ∈ sv, Replay.isWake e = true → Replay.dayOf z kw e.t.val = Replay.dayOf z kw' e.t.val) :
    sleptByDay z kw sv = sleptByDay z kw' sv := by
  unfold sleptByDay
  apply filterMap_congr'
  intro e he
  cases hs : Replay.sleptOf e with
  | none => rfl
  | some v =>
    have hw : Replay.isWake e = true := by
      unfold Replay.sleptOf at hs; unfold Replay.isWake; split at hs <;> simp_all
    simp [h e he hw]

end Seal
end Tm
