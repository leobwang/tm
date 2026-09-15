import TmKernel.SealIndex
/-!
# SealCutWakes — the resealed stored wakes (stage 5, D9, W2: law 6)

Storing the wakes at a later ledger day from the stored wakes and the folded tail's is storing them from the whole
folded index (`storedWakes_at_cut`), once the tail's wakes are after every folded instant not future and more than the
fence before every future one.  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (keptWakes sortWakes dedupFrom)

theorem headSec_mono {L L' : Nat} (h : L ≤ L') : headSec L ≤ headSec L' := by
  unfold headSec; exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_right h 1)

/-- **A prefix before the head second, ending before the stored head, is absorbed.** -/
theorem storedWakes_prefix_absorb (L' : Nat) (P0 S : List Cal.Instant) (hP0 : ∀ p ∈ P0, p.sec < headSec L')
    (hS : P0 ≠ [] → ∃ h rest, S = h :: rest ∧ h.sec < headSec L') :
    storedWakes L' (P0 ++ S) = storedWakes L' S := by
  by_cases hP : P0 = []
  · subst hP; rfl
  · obtain ⟨h, rest, rfl, hh⟩ := hS hP
    unfold storedWakes
    rw [List.filter_append, List.filter_append]
    have e1 : P0.filter (fun w => decide (headSec L' ≤ w.sec)) = [] :=
      List.filter_eq_nil_iff.2 (fun p hp => by have := hP0 p hp; simp; omega)
    have hne : ((h :: rest).filter (fun w => decide (w.sec < headSec L'))) ≠ [] :=
      List.ne_nil_of_mem (List.mem_filter.2 ⟨List.mem_cons_self, by simpa using hh⟩)
    rw [e1, List.nil_append, List.getLast?_append]
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 (by
      intro hn; exact hne (List.getLast?_eq_none_iff.1 hn))
    rw [hx]; rfl

/-- **Storing at a later ledger day forgets the earlier storing.** -/
theorem storedWakes_storedWakes (L L' : Nat) (hLL : L ≤ L') (K : List Cal.Instant) (hs : K.Pairwise (· ≤ ·)) :
    storedWakes L' (storedWakes L K) = storedWakes L' K := by
  obtain ⟨P0, hK, hle, hhead⟩ := storedWakes_suffix L K hs
  conv => rhs; rw [hK]
  refine (storedWakes_prefix_absorb L' P0 _ (fun p hp => ?_) (fun hne => ?_)).symm
  · obtain ⟨h, rest, hS, hh⟩ := hhead (List.ne_nil_of_mem hp)
    have := sec_le_of_le (hle p hp h (by rw [hS]; exact List.mem_cons_self))
    have := headSec_mono hLL
    omega
  · obtain ⟨h, rest, hS, hh⟩ := hhead hne
    exact ⟨h, rest, hS, Nat.lt_of_lt_of_le hh (headSec_mono hLL)⟩

theorem lastKept_eq_getLast (z : Cal.Tz) : ∀ (l : List Cal.Instant) (prev : Option Cal.Instant),
    lastKept z prev l = (dedupFrom z prev l).getLast?.or prev
  | [], prev => rfl
  | w :: ws, none => by
    rw [lastKept_cons, dedupFrom_cons]
    simp only
    rw [lastKept_eq_getLast z ws (some w), List.getLast?_cons]
    cases (dedupFrom z (some w) ws).getLast? <;> rfl
  | w :: ws, some k => by
    rw [lastKept_cons, dedupFrom_cons]
    simp only
    split
    · exact lastKept_eq_getLast z ws (some k)
    · rw [lastKept_eq_getLast z ws (some w), List.getLast?_cons]
      cases (dedupFrom z (some w) ws).getLast? <;> rfl

theorem dedupFrom_far_noRuns (z : Cal.Tz) (x : Option Cal.Instant) (ws : List Cal.Instant)
    (hx : ∀ a ∈ x, ∀ w ∈ ws, a.sec + fenceSec < w.sec) (hn : noRuns z none ws = true) : dedupFrom z x ws = ws := by
  rw [dedupFrom_far z x none ws hx (fun a ha => by cases ha)]
  exact dedupFrom_of_noRuns z none ws hn

theorem getLast?_storedWakes (L : Nat) (K : List Cal.Instant) (hs : K.Pairwise (· ≤ ·)) :
    (storedWakes L K).getLast? = K.getLast? := by
  obtain ⟨P0, hK, -, -⟩ := storedWakes_suffix L K hs
  by_cases hS : storedWakes L K = []
  · have hKn : K = [] := Classical.byContradiction (fun hne => storedWakes_ne_nil L K hne hS)
    rw [hS, hKn]
  · conv => rhs; rw [hK]
    rw [List.getLast?_append]
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 (fun hn => hS (List.getLast?_eq_none_iff.1 hn))
    rw [hx]; rfl

/-- **The resealed stored wakes** (§9.2 at `L'`): storing at `L' ≥ L` the index of the stored wakes and the folded
tail's is storing the whole folded index, once the tail's wakes are after every folded instant not future and more
than the fence before every future one, and at or after the head second of `L`. -/
theorem storedWakes_at_cut (z : Cal.Tz) (L L' : Nat) (hLL : L ≤ L') (P : Cal.Instant → Bool)
    (QA WA WB : List Cal.Instant) (hWA : ∀ w ∈ WA, w ∈ QA)
    (hsep : ∀ w ∈ WB, ∀ q ∈ QA, (P q = true → q < w) ∧ (P q = false → w.sec + fenceSec < q.sec))
    (hhead : ∀ w ∈ WB, headSec L ≤ w.sec) :
    storedWakes L' (keptWakes z (storedWakes L (keptWakes z WA) ++ WB)) = storedWakes L' (keptWakes z (WA ++ WB)) := by
  have hsKA := Replay.keptWakes_sorted z WA
  have hnKA : noRuns z none (keptWakes z WA) = true := by rw [keptWakes_eq]; exact noRuns_dedupFrom z _ none
  cases WB with
  | nil =>
    rw [List.append_nil, List.append_nil]
    have hS := sorted_storedWakes L (keptWakes z WA) hsKA
    have hN := noRuns_storedWakes z L (keptWakes z WA) hsKA hnKA
    rw [keptWakes_eq z (storedWakes L _), sortWakes_of_sorted _ hS, dedupFrom_of_noRuns z none _ hN]
    exact storedWakes_storedWakes L L' hLL _ hsKA
  | cons w₀ WB' =>
    generalize hWB : w₀ :: WB' = WB at hsep hhead ⊢
    have hw₀ : w₀ ∈ WB := by rw [← hWB]; exact List.mem_cons_self
    let lo := WA.filter P
    let hi := WA.filter (fun q => !P q)
    have hlo_mid : ∀ a ∈ lo, ∀ b ∈ WB, a < b := fun a ha b hb =>
      (hsep b hb a (hWA a (List.mem_filter.1 ha).1)).1 (List.mem_filter.1 ha).2
    have hmid_hi : ∀ b ∈ WB, ∀ c ∈ hi, b.sec + fenceSec < c.sec := fun b hb c hc =>
      (hsep b hb c (hWA c (List.mem_filter.1 hc).1)).2 (by simpa using (List.mem_filter.1 hc).2)
    have hlo_hi : ∀ a ∈ lo, ∀ c ∈ hi, a.sec + fenceSec < c.sec := fun a ha c hc =>
      far_of_lt_of_far (hlo_mid a ha w₀ hw₀) (hmid_hi w₀ hw₀ c hc)
    have hperm : (lo ++ hi).Perm WA := List.filter_append_perm P WA
    have hsA : sortWakes WA = sortWakes lo ++ sortWakes hi := by
      rw [sortWakes_eq_of_perm (hperm.symm.trans (by simp : (lo ++ hi).Perm (lo ++ [] ++ hi))),
        sortWakes_three lo [] hi (fun _ _ _ h => by cases h) (fun a ha c hc => lt_of_far (hlo_hi a ha c hc))
          (fun _ h => by cases h)]
      rw [show sortWakes ([] : List Cal.Instant) = [] from rfl, List.append_nil]
    have hsF : sortWakes (WA ++ WB) = sortWakes lo ++ sortWakes WB ++ sortWakes hi := by
      have hp : (WA ++ WB).Perm (lo ++ WB ++ hi) := by
        refine (List.Perm.append_right WB hperm.symm).trans ?_
        rw [List.append_assoc, List.append_assoc]
        exact List.Perm.append_left lo List.perm_append_comm
      rw [sortWakes_eq_of_perm hp, sortWakes_three lo WB hi hlo_mid (fun a ha c hc => lt_of_far (hlo_hi a ha c hc))
        (fun b hb c hc => lt_of_far (hmid_hi b hb c hc))]
    have hSLlo : ∀ a ∈ sortWakes lo, a ∈ lo := fun a ha => (mem_sortWakes lo a).1 ha
    have hSHhi : ∀ c ∈ sortWakes hi, c ∈ hi := fun c hc => (mem_sortWakes hi c).1 hc
    have hSWwb : ∀ b ∈ sortWakes WB, b ∈ WB := fun b hb => (mem_sortWakes WB b).1 hb
    generalize hDL : dedupFrom z none (sortWakes lo) = DL
    generalize hDH : dedupFrom z none (sortWakes hi) = DH
    generalize hlk : lastKept z none (sortWakes lo) = lk
    have hlk_mem : ∀ a ∈ lk, a ∈ lo := fun a ha => by
      rw [← hlk] at ha
      rcases lastKept_mem z _ none a ha with h | h
      · cases h
      · exact hSLlo a h
    have hKA : keptWakes z WA = DL ++ DH := by
      rw [keptWakes_eq, hsA, dedupFrom_append', hlk,
        dedupFrom_far z lk none _ (fun a ha c hc => hlo_hi a (hlk_mem a ha) c (hSHhi c hc)) (fun a ha => by cases ha),
        hDL, hDH]
    generalize hM : dedupFrom z lk (sortWakes WB) = M
    have hKF : keptWakes z (WA ++ WB) = DL ++ M ++ DH := by
      rw [keptWakes_eq, hsF, dedupFrom_append', dedupFrom_append', hlk, hDL, hM, lastKept_append, hlk,
        dedupFrom_far z (lastKept z lk (sortWakes WB)) none _ (fun a ha c hc => by
          rcases lastKept_mem z _ lk a ha with h | h
          · exact hlo_hi a (hlk_mem a h) c (hSHhi c hc)
          · exact hmid_hi a (hSWwb a h) c (hSHhi c hc)) (fun a ha => by cases ha), hDH]
    have hsDL : DL.Pairwise (· ≤ ·) := by rw [← hDL]; exact dedupFrom_sorted z none _ (Replay.sortWakes_sorted lo)
    have hnDL : noRuns z none DL = true := by rw [← hDL]; exact noRuns_dedupFrom z _ none
    have hsDH : DH.Pairwise (· ≤ ·) := by rw [← hDH]; exact dedupFrom_sorted z none _ (Replay.sortWakes_sorted hi)
    have hnDH : noRuns z none DH = true := by rw [← hDH]; exact noRuns_dedupFrom z _ none
    have hDLlo : ∀ a ∈ DL, a ∈ lo := fun a ha => by
      rw [← hDL] at ha; exact hSLlo a (mem_of_mem_dedupFrom z none _ a ha)
    have hDHhi : ∀ c ∈ DH, c ∈ hi := fun c hc => by
      rw [← hDH] at hc; exact hSHhi c (mem_of_mem_dedupFrom z none _ c hc)
    have hDH_ge : ∀ c ∈ DH, headSec L ≤ c.sec := fun c hc => by
      have := hmid_hi w₀ hw₀ c (hDHhi c hc); have := hhead w₀ hw₀; unfold fenceSec at *; omega
    rw [hKA, storedWakes_append_of_ge L DL DH hDH_ge, hKF]
    generalize hSDL : storedWakes L DL = SDL
    have hsSDL : SDL.Pairwise (· ≤ ·) := by rw [← hSDL]; exact sorted_storedWakes L DL hsDL
    have hnSDL : noRuns z none SDL = true := by rw [← hSDL]; exact noRuns_storedWakes z L DL hsDL hnDL
    have hSDLlo : ∀ a ∈ SDL, a ∈ lo := fun a ha => by
      obtain ⟨P0, hDLs, -, -⟩ := storedWakes_suffix L DL hsDL
      rw [← hSDL] at ha
      exact hDLlo a (by rw [hDLs]; exact List.mem_append_right _ ha)
    -- the stored inner index
    have hsort2 : sortWakes (SDL ++ DH ++ WB) = SDL ++ sortWakes WB ++ DH := by
      have hp : (SDL ++ DH ++ WB).Perm (SDL ++ WB ++ DH) := by
        rw [List.append_assoc, List.append_assoc]; exact List.Perm.append_left SDL List.perm_append_comm
      rw [sortWakes_eq_of_perm hp, sortWakes_three SDL WB DH (fun a ha b hb => hlo_mid a (hSDLlo a ha) b hb)
        (fun a ha c hc => lt_of_far (hlo_hi a (hSDLlo a ha) c (hDHhi c hc)))
        (fun b hb c hc => lt_of_far (hmid_hi b hb c (hDHhi c hc))),
        sortWakes_of_sorted SDL hsSDL, sortWakes_of_sorted DH hsDH]
    have hlkS : lastKept z none SDL = lk := by
      rw [lastKept_eq_getLast, dedupFrom_of_noRuns z none SDL hnSDL, ← hSDL, getLast?_storedWakes L DL hsDL, ← hlk,
        lastKept_eq_getLast, hDL]
    have hinner : keptWakes z (SDL ++ DH ++ WB) = SDL ++ M ++ DH := by
      rw [keptWakes_eq, hsort2, dedupFrom_append', dedupFrom_append', dedupFrom_of_noRuns z none SDL hnSDL, hlkS, hM,
        lastKept_append, hlkS, dedupFrom_far_noRuns z _ DH (fun a ha c hc => by
          rcases lastKept_mem z _ lk a ha with h | h
          · exact hlo_hi a (hlk_mem a h) c (hDHhi c hc)
          · exact hmid_hi a (hSWwb a h) c (hDHhi c hc)) hnDH]
    rw [hinner]
    obtain ⟨P0, hDLs, hle, hhd⟩ := storedWakes_suffix L DL hsDL
    rw [hSDL] at hDLs hle hhd
    conv => rhs; rw [hDLs, List.append_assoc, List.append_assoc]
    rw [List.append_assoc]
    refine (storedWakes_prefix_absorb L' P0 _ (fun p hp => ?_) (fun hne => ?_)).symm
    · obtain ⟨h, rest, hS, hh⟩ := hhd (List.ne_nil_of_mem hp)
      have := sec_le_of_le (hle p hp h (by rw [hS]; exact List.mem_cons_self))
      have := headSec_mono hLL
      omega
    · obtain ⟨h, rest, hS, hh⟩ := hhd hne
      exact ⟨h, rest ++ (M ++ DH), by rw [hS]; rfl, Nat.lt_of_lt_of_le hh (headSec_mono hLL)⟩

end Seal
end Tm
