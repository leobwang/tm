import TmKernel.SealGroup
import TmKernel.SealSlept
/-!
# SealCutSlept — the resealed `slept_by_day` (stage 5, D9, W2: law 6)

A stored `slept_by_day` depends only on its days at or after the ledger day and each such day's first entry
(`storedSlept_congr`).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

theorem kmap_get_isSome_of_mem (sl : List (Nat × Nat)) (d : Nat) (h : d ∈ sl.map Prod.fst) :
    (Replay.KMap.get sl d).isSome := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  rw [kmap_get_eq]
  cases hf : sl.find? (fun q => decide (q.1 = p.1)) with
  | none => exact absurd (List.find?_eq_none.1 hf p hp) (by simp)
  | some q => simp

theorem mem_storedSlept_keys (sl : List (Nat × Nat)) (L d : Nat) :
    d ∈ (storedSlept sl L).map Prod.fst ↔ L ≤ d ∧ d ∈ sl.map Prod.fst := by
  unfold storedSlept
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    obtain ⟨d', hd', hpd⟩ := List.mem_filterMap.1 hp
    obtain ⟨hmem, hL⟩ := List.mem_filter.1 hd'
    cases hg : Replay.KMap.get sl d' with
    | none => rw [hg] at hpd; cases hpd
    | some s =>
      rw [hg] at hpd
      simp only [Option.map_some, Option.some.injEq] at hpd
      subst hpd
      exact ⟨by simpa using hL, (mem_canon natLt_strictTotal _ _).1 hmem⟩
  · rintro ⟨hL, hm⟩
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 (kmap_get_isSome_of_mem sl d hm)
    exact List.mem_map.2 ⟨(d, s), List.mem_filterMap.2 ⟨d, List.mem_filter.2
      ⟨(mem_canon natLt_strictTotal _ _).2 hm, by simpa using hL⟩, by rw [hs]; rfl⟩, rfl⟩

/-- **A stored `slept_by_day` reads only its days at or after the ledger day.** -/
theorem storedSlept_congr (sl₁ sl₂ : List (Nat × Nat)) (L : Nat)
    (hkeys : ∀ d, L ≤ d → (d ∈ sl₁.map Prod.fst ↔ d ∈ sl₂.map Prod.fst))
    (hget : ∀ d, L ≤ d → Replay.KMap.get sl₁ d = Replay.KMap.get sl₂ d) :
    storedSlept sl₁ L = storedSlept sl₂ L := by
  unfold storedSlept
  have hc : (canon natLt (sl₁.map Prod.fst)).filter (fun d => decide (L ≤ d))
      = (canon natLt (sl₂.map Prod.fst)).filter (fun d => decide (L ≤ d)) := by
    rw [canon_filter natLt_strictTotal, canon_filter natLt_strictTotal]
    apply canon_eq_of_mem_iff natLt_strictTotal
    intro d
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨h, hL⟩; exact ⟨(hkeys d hL).1 h, hL⟩
    · rintro ⟨h, hL⟩; exact ⟨(hkeys d hL).2 h, hL⟩
  rw [hc]
  apply filterMap_congr'
  intro d hd
  rw [hget d (by simpa using (List.mem_filter.1 hd).2)]

theorem mem_keys_iff_get (sl : List (Nat × Nat)) (d : Nat) :
    d ∈ sl.map Prod.fst ↔ (Replay.KMap.get sl d).isSome := by
  refine ⟨kmap_get_isSome_of_mem sl d, fun h => ?_⟩
  rw [kmap_get_eq] at h
  cases hf : sl.find? (fun q => decide (q.1 = d)) with
  | none => rw [hf] at h; cases h
  | some q => exact List.mem_map.2 ⟨q, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

/-- **A stored `slept_by_day` reads only its table at and after the ledger day.** -/
theorem storedSlept_congr_get (sl₁ sl₂ : List (Nat × Nat)) (L : Nat)
    (hget : ∀ d, L ≤ d → Replay.KMap.get sl₁ d = Replay.KMap.get sl₂ d) :
    storedSlept sl₁ L = storedSlept sl₂ L :=
  storedSlept_congr sl₁ sl₂ L (fun d hd => by rw [mem_keys_iff_get, mem_keys_iff_get, hget d hd]) hget

end Seal
end Tm
