import TmKernel.SealRsDefs
import TmKernel.SealCutLows
import TmKernel.SealLaw5A
/-!
# SealLaw6Ctx — an accepted resume and a valid cut, unpacked (stage 5, D9, W2: laws 6 and 7)

The laws on a reseal read a resume's run and a valid cut `j` through the same entries: the tail's entries split into the
folded and unfolded ones at line `|a| + j`, and so do its survivors; the unfolded surviving wakes are separated from every
folded instant (§9.4's (iii)); the stored settled undos are folded, and no undo is cut from its target (vi)
(`rs_context`).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State survivors wakeInstants keptWakes dayOf)
open Log (Entry)

/-- **An accepted resume and a valid cut, as entries.** -/
theorem rs_context (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line) (term : Bool) (p : Policy) (run : Run) (j : Nat)
    (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b)
    (hrun : resumeRun z T (ckptOf z T₀ L a r) b = .ok run)
    (hmig : migrationOk (ckptOf z T₀ L a r) T = true)
    (hcut : cutOk z T (ckptOf z T₀ L a r) b term p run j = true) :
    ∃ (B' : List Entry) (n : Nat) (sv : List Entry) (kw : List Cal.Instant) (sl : Nat → Option Nat)
      (Bj Brest svj svr : List Entry),
      Log.lineEntries b = Log.lineEntries r ++ B' ∧
      (Log.lineEntries a ++ (Log.lineEntries r ++ B')).Pairwise (fun x y => x.line < y.line) ∧
      run.entries = Log.lineEntries r ++ B' ∧
      run.unsettledTail = unsettled (ckptOf z T₀ L a r).settled (Log.lineEntries r ++ B') ∧
      run.survivors = sv ∧ sv = survivors (unsettled (ckptOf z T₀ L a r).settled (Log.lineEntries r ++ B')) ∧
      run.index = kw ∧ kw = tailIndex z (ckptOf z T₀ L a r) sv ∧
      run.slept = sl ∧ sl = tailSlept z (ckptOf z T₀ L a r) kw sv ∧
      n = (ckptOf z T₀ L a r).items.length + (ckptOf z T₀ L a r).openDays.length + (Log.lineEntries r ++ B').length ∧
      (ckptOf z T₀ L a r).tzKey = z.val.key ∧ L ≤ T ∧
      g1 (ckptOf z T₀ L a r) (unsettled (ckptOf z T₀ L a r).settled (Log.lineEntries r ++ B')) = none ∧
      (∀ pre e post, sv = pre ++ e :: post →
        (stepCheck z (dayOf z kw) sl (ckptOf z T₀ L a r)
          (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOf z T₀ L a r) n)) e).2 = none) ∧
      headerCheck (dayOf z kw) (ckptOf z T₀ L a r) (Log.lineEntries r ++ B') = none ∧
      j ≤ b.length ∧
      Bj = (Log.lineEntries r ++ B').filter (fun e => decide (e.line ≤ a.length + j)) ∧
      Brest = (Log.lineEntries r ++ B').filter (fun e => decide (a.length + j < e.line)) ∧
      Log.lineEntries r ++ B' = Bj ++ Brest ∧
      svj = sv.filter (fun e => decide (e.line ≤ a.length + j)) ∧
      svr = sv.filter (fun e => decide (a.length + j < e.line)) ∧
      sv = svj ++ svr ∧ (∀ e ∈ svj, e ∈ Bj) ∧ (∀ e ∈ svr, e ∈ Brest) ∧
      (∀ w ∈ wakeInstants svr, ∀ q ∈ (Log.lineEntries a ++ Bj).flatMap entryInstants,
        ((fun q => !isFuture T q) q = true → q < w) ∧ ((fun q => !isFuture T q) q = false → w.sec + fenceSec < q.sec)) ∧
      (∀ m ∈ settledOf (Log.lineEntries a) (Log.lineEntries r), m ≤ a.length + j) ∧
      (∀ ut ∈ undoTargets (unsettled (settledOf (Log.lineEntries a) (Log.lineEntries r)) (Log.lineEntries r ++ B')),
        ¬ (ut.2.line ≤ a.length + j ∧ a.length + j < ut.1.line)) ∧
      (∀ x ∈ Log.lineEntries a, x.line ≤ a.length + j) ∧ (∀ x ∈ Bj, x.line ≤ a.length + j) ∧
      (∀ x ∈ Brest, a.length + j < x.line) ∧
      Log.lineEntries (b.take j) = Bj ∧ Log.lineEntries (b.drop j) = Brest ∧
      Log.lineWarnings (b.take j) = (Log.lineWarnings b).filter (fun w => decide (w.1 ≤ a.length + j)) := by
  obtain ⟨t, rfl⟩ := hr
  have hLE : ∀ x y : List Log.Line, Log.lineEntries (x ++ y) = Log.lineEntries x ++ Log.lineEntries y :=
    fun x y => List.filterMap_append
  have hd : (Log.lineEntries a ++ (Log.lineEntries r ++ Log.lineEntries t)).Pairwise (fun x y => x.line < y.line) := by
    have := (lineEntries_pairwise 1 (a ++ (r ++ t)) hc).1
    rwa [hLE, hLE] at this
  obtain ⟨hz, -, hLT, hg, hfold, hhdr, hrunq⟩ := resumeRun_ok z T _ _ run hrun
  rw [hLE r t] at hg hfold hhdr hrunq
  have hcp := cutOk_parts hcut
  rw [hrunq] at hcp
  dsimp only at hcp
  have hKcut : (ckptOf z T₀ L a r).cut = a.length := rfl
  have hKL : (ckptOf z T₀ L a r).ledgerDay = L := rfl
  have hKset : (ckptOf z T₀ L a r).settled = settledOf (Log.lineEntries a) (Log.lineEntries r) := rfl
  rw [hKcut] at hcp
  rw [hKL] at hLT
  obtain ⟨sv, hsv⟩ : ∃ sv, sv = survivors (unsettled (ckptOf z T₀ L a r).settled
      (Log.lineEntries r ++ Log.lineEntries t)) := ⟨_, rfl⟩
  obtain ⟨kw, hkw⟩ : ∃ kw, kw = tailIndex z (ckptOf z T₀ L a r) sv := ⟨_, rfl⟩
  obtain ⟨sl, hsl⟩ : ∃ sl, sl = tailSlept z (ckptOf z T₀ L a r) kw sv := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = (ckptOf z T₀ L a r).items.length + (ckptOf z T₀ L a r).openDays.length
      + (Log.lineEntries r ++ Log.lineEntries t).length := ⟨_, rfl⟩
  rw [← hsv, ← hkw, ← hsl, ← hn] at hfold
  rw [← hsv, ← hkw] at hhdr
  rw [← hsv] at hcp
  have hsteps := (tailFold_snd z (dayOf z kw) sl _ sv (restore _ n, none) hfold).2
  obtain ⟨Bj, hBj⟩ : ∃ Bj, Bj = (Log.lineEntries r ++ Log.lineEntries t).filter
      (fun e => decide (e.line ≤ a.length + j)) := ⟨_, rfl⟩
  obtain ⟨Brest, hBrest⟩ : ∃ Brest, Brest = (Log.lineEntries r ++ Log.lineEntries t).filter
      (fun e => decide (a.length + j < e.line)) := ⟨_, rfl⟩
  obtain ⟨svj, hsvj⟩ : ∃ svj, svj = sv.filter (fun e => decide (e.line ≤ a.length + j)) := ⟨_, rfl⟩
  obtain ⟨svr, hsvr⟩ : ∃ svr, svr = sv.filter (fun e => decide (a.length + j < e.line)) := ⟨_, rfl⟩
  have hdB : (Log.lineEntries r ++ Log.lineEntries t).Pairwise (fun x y => x.line < y.line) :=
    (List.pairwise_append.1 hd).2.1
  have hsvsub : sv.Sublist (Log.lineEntries r ++ Log.lineEntries t) := by
    rw [hsv]; exact (survivors_sublist _).trans (unsettled_sublist _ _)
  have hsplit : Log.lineEntries r ++ Log.lineEntries t = Bj ++ Brest := by
    rw [hBj, hBrest]; exact (filter_line_split _ _ hdB).symm
  have hsvs : sv = svj ++ svr := by
    rw [hsvj, hsvr]; exact (filter_line_split _ _ (hdB.sublist hsvsub)).symm
  have hsvjB : ∀ e ∈ svj, e ∈ Bj := fun e he => by
    rw [hsvj] at he; rw [hBj]
    exact List.mem_filter.2 ⟨hsvsub.subset (List.mem_filter.1 he).1, (List.mem_filter.1 he).2⟩
  have hsvrB : ∀ e ∈ svr, e ∈ Brest := fun e he => by
    rw [hsvr] at he; rw [hBrest]
    exact List.mem_filter.2 ⟨hsvsub.subset (List.mem_filter.1 he).1, (List.mem_filter.1 he).2⟩
  -- (iii): the unfolded surviving wakes against the folded instants
  have hmaxT : (ckptOf z T₀ L a r).maxT
      = maxInstant? (((Log.lineEntries a).flatMap entryInstants).filter (fun q => !isFuture T₀ q)) :=
    ckpt_maxT z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a)
  have hff : (ckptOf z T₀ L a r).futureFloor
      = minInstant? (((Log.lineEntries a).flatMap entryInstants).filter (isFuture T₀)) :=
    ckpt_futureFloor z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a)
  have hsep : ∀ w ∈ wakeInstants svr, ∀ q ∈ (Log.lineEntries a ++ Bj).flatMap entryInstants,
      ((fun q => !isFuture T q) q = true → q < w) ∧ ((fun q => !isFuture T q) q = false → w.sec + fenceSec < q.sec) := by
    intro w hw
    have hiii := hcp.2.2.2.1
    rw [← hsvr, ← hBj] at hiii
    have hw' := List.all_eq_true.1 hiii w hw
    simp only [Bool.and_eq_true] at hw'
    rw [resealed_maxT T₀ T _ _ _ hmaxT hff hmig, resealed_futureFloor T₀ T _ _ _ hmaxT hff hmig] at hw'
    rw [List.flatMap_append]
    refine sep_of_bounds T _ w (fun m hm => ?_) (fun f hf => ?_)
    · rw [hm] at hw'; simpa using hw'.1
    · rw [hf] at hw'; simpa using hw'.2
  have hsettled : ∀ m ∈ settledOf (Log.lineEntries a) (Log.lineEntries r), m ≤ a.length + j := by
    intro m hm
    have := List.all_eq_true.1 hcp.2.2.2.2.2.2.1 m (by rw [hKset]; exact hm)
    simpa using this
  have hvi : ∀ ut ∈ undoTargets (unsettled (settledOf (Log.lineEntries a) (Log.lineEntries r))
      (Log.lineEntries r ++ Log.lineEntries t)), ¬ (ut.2.line ≤ a.length + j ∧ a.length + j < ut.1.line) := by
    intro ut hut hlt
    have := List.all_eq_true.1 hcp.2.2.2.2.2.2.2 ut (by rw [hKset]; exact hut)
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
    rcases this with h1 | h1
    · exact h1 hlt.1
    · exact h1 hlt.2
  -- the lines at the cut
  have hcb : Log.contiguousFrom (1 + a.length) (r ++ t) = true := contiguousFrom_append 1 a (r ++ t) hc
  have hAc : ∀ x ∈ Log.lineEntries a, x.line ≤ a.length + j := by
    intro x hx
    have htk := lineEntries_take 1 (a ++ (r ++ t)) a.length hc
    rw [List.take_left' rfl] at htk
    rw [htk] at hx
    have := of_decide_eq_true (List.mem_filter.1 hx).2
    omega
  have hTake : Log.lineEntries ((r ++ t).take j) = Bj := by
    rw [lineEntries_take (1 + a.length) (r ++ t) j hcb, hLE r t, hBj]
    exact List.filter_congr (fun e _ => by simp only [decide_eq_decide]; omega)
  have hDrop : Log.lineEntries ((r ++ t).drop j) = Brest := by
    rw [lineEntries_drop (1 + a.length) (r ++ t) j hcb, hLE r t, hBrest]
    exact List.filter_congr (fun e _ => by simp only [decide_eq_decide]; omega)
  have hWs : Log.lineWarnings ((r ++ t).take j) = (Log.lineWarnings (r ++ t)).filter
      (fun w => decide (w.1 ≤ a.length + j)) := by
    rw [lineWarnings_take (1 + a.length) (r ++ t) j hcb]
    exact List.filter_congr (fun w _ => by simp only [decide_eq_decide]; omega)
  refine ⟨Log.lineEntries t, n, sv, kw, sl, Bj, Brest, svj, svr, hLE r t, hd, by rw [hrunq], by rw [hrunq],
    by rw [hrunq, hsv], hsv, by rw [hrunq, hkw, hsv], hkw, by rw [hrunq, hsl, hkw, hsv], hsl, hn, hz, hLT, hg,
    hsteps, hhdr, hcp.1, hBj, hBrest, hsplit, hsvj, hsvr, hsvs, hsvjB, hsvrB, hsep, hsettled, hvi, hAc,
    fun x hx => by rw [hBj] at hx; exact of_decide_eq_true (List.mem_filter.1 hx).2,
    fun x hx => by rw [hBrest] at hx; exact of_decide_eq_true (List.mem_filter.1 hx).2, hTake, hDrop, hWs⟩

end Seal
end Tm
