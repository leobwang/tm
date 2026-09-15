import TmKernel.SealLaw6Ctx
import TmKernel.SealCutState
import TmKernel.SealCutHeaders
import TmKernel.SealCutSteps
import TmKernel.SealCutStep
import TmKernel.SealReach
import TmKernel.SealLaw5B
/-!
# SealLaw6Seal — a resealed checkpoint is sealable and meets the reach condition of its suffix (stage 5, D9, W2)

At a valid cut, the checkpoint of the lines up to the cut knowing the rest is sealable at the new ledger day
(`rs_sealable_reachFree`, law 6): every key and header of the unfolded lines, and every day the folded machine can still
write, is at or after `L'`, since `L'` is at most each of them or the old ledger day; and the unfolded lines cancel nothing
folded, so the records below `L'` are the folded lines' own.  The same bounds, with §9.4's (iii), are law 5's reach
condition on the suffix at `L'` (law 7's route).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Effect survivors wakeInstants keptWakes dayOf)
open Log (Entry)

/-- **A resealed checkpoint is sealable, and its suffix meets the reach condition at the new ledger day.** -/
theorem rs_sealable_reachFree (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line) (term : Bool) (p : Policy)
    (run : Run) (j : Nat) (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b)
    (hs : sealable z T₀ L a r = true)
    (hrun : resumeRun z T (ckptOf z T₀ L a r) b = .ok run)
    (hmig : migrationOk (ckptOf z T₀ L a r) T = true)
    (hcut : cutOk z T (ckptOf z T₀ L a r) b term p run j = true) :
    sealable z T (sealDayOf z T (ckptOf z T₀ L a r) p run j) (a ++ b.take j) (b.drop j) = true ∧
    reachFree z T (sealDayOf z T (ckptOf z T₀ L a r) p run j) (a ++ b.take j) (b.drop j) = true := by
  obtain ⟨B', n, sv, kw, sl, Bj, Brest, svj, svr, hbE, hd, hent, hNq, hsvq, hsv, hidxq, hkw, hslq, hsl, hn, hz, hLT,
    hg, hsteps, hhdr, hjle, hBj, hBrest, hsplit, hsvj, hsvr, hsvs, hsvjB, hsvrB, hsep, hsettled, hvi, hAc, hBjc,
    hBrestc, hTake, hDrop, hWs⟩ := rs_context z T₀ T L a r b term p run j hc hr hrun hmig hcut
  have hLE : ∀ x y : List Log.Line, Log.lineEntries (x ++ y) = Log.lineEntries x ++ Log.lineEntries y :=
    fun x y => List.filterMap_append
  have hKe : ckptOf z T₀ L a r = ckptOfEntries z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r)
      (Log.lineWarnings a) := rfl
  have hKcut : (ckptOf z T₀ L a r).cut = a.length := rfl
  have hKL : (ckptOf z T₀ L a r).ledgerDay = L := rfl
  have hLL : L ≤ sealDayOf z T (ckptOf z T₀ L a r) p run j := le_sealDayOf z T (ckptOf z T₀ L a r) p run j
  -- the lows of the new ledger day
  have hlowDay : ∀ e ∈ Brest, sealDayOf z T (ckptOf z T₀ L a r) p run j ≤ Nat.max L (dayOf z kw e.t.val) := by
    intro e he
    have := sealDayOf_le_max z T (ckptOf z T₀ L a r) p run j (dayOf z kw e.t.val)
      (Or.inl (List.mem_map.2 ⟨e, by rw [hent, hKcut, ← hBrest]; exact he, by rw [hidxq]⟩))
    rwa [hKL] at this
  have hlowSec : ∀ e ∈ Brest, sealDayOf z T (ckptOf z T₀ L a r) p run j ≤ Nat.max L (e.t.val.sec / 86400 + 1) := by
    intro e he
    have := sealDayOf_le_max z T (ckptOf z T₀ L a r) p run j (e.t.val.sec / 86400 + 1)
      (Or.inr (Or.inl (List.mem_map.2 ⟨e, by rw [hent, hKcut, ← hBrest]; exact he, rfl⟩)))
    rwa [hKL] at this
  have hlowStep : ∀ pre e post, sv = pre ++ e :: post → a.length + j < e.line →
      (∀ dd ∈ (Replay.effectsWith z (dayOf z kw) sl
          (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOf z T₀ L a r) n)) e).filterMap
          (fun x => x.key.date?), sealDayOf z T (ckptOf z T₀ L a r) p run j ≤ Nat.max L dd) ∧
      (∀ q ∈ stepQueries (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOf z T₀ L a r) n)).machine e,
        sealDayOf z T (ckptOf z T₀ L a r) p run j ≤ Nat.max L (q.sec / 86400 + 1)) := by
    intro pre e post hs hl
    have hP : (fun e : Entry => decide ((ckptOf z T₀ L a r).cut + j < e.line)) e = true := by
      simp only [hKcut, decide_eq_true_eq]; exact hl
    obtain ⟨h1, h2⟩ := mem_lows z (dayOf z kw) sl (fun e : Entry => decide ((ckptOf z T₀ L a r).cut + j < e.line)) pre
      (restore (ckptOf z T₀ L a r) n, []) e post hP
    have hlows : stepLows z (dayOf z run.index) run.slept (fun e => decide ((ckptOf z T₀ L a r).cut + j < e.line))
        (restore (ckptOf z T₀ L a r) ((ckptOf z T₀ L a r).items.length + (ckptOf z T₀ L a r).openDays.length
          + run.entries.length)) run.survivors
        = ((pre ++ e :: post).foldl (lowsStep z (dayOf z kw) sl (fun e : Entry => decide ((ckptOf z T₀ L a r).cut + j < e.line)))
            (restore (ckptOf z T₀ L a r) n, [])).2 := by
      rw [stepLows_eq, hidxq, hslq, hsvq, hs, hent, ← hn]
    refine ⟨fun dd hdd => ?_, fun q hq => ?_⟩
    · have := sealDayOf_le_max z T (ckptOf z T₀ L a r) p run j dd (Or.inr (Or.inr (Or.inl (by rw [hlows]; exact h1 dd hdd))))
      rwa [hKL] at this
    · have := sealDayOf_le_max z T (ckptOf z T₀ L a r) p run j _ (Or.inr (Or.inr (Or.inl (by rw [hlows]; exact h2 q hq))))
      rwa [hKL] at this
  have hlowMach : ∀ x ∈ machineDays (svj.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOf z T₀ L a r) n)).machine,
      sealDayOf z T (ckptOf z T₀ L a r) p run j ≤ Nat.max L x := by
    intro x hx
    have := sealDayOf_le_max z T (ckptOf z T₀ L a r) p run j x (Or.inr (Or.inr (Or.inr (by
      rw [hsvq, hKcut, ← hsvj, hidxq, hslq, hent, ← hn]; exact hx))))
    rwa [hKL] at this
  -- the goal's lines as entries
  unfold sealable reachFree
  rw [hLE, hTake, hDrop]
  generalize hsd : sealDayOf z T (ckptOf z T₀ L a r) p run j = L' at hLL hlowDay hlowSec hlowStep hlowMach ⊢
  -- the spec objects
  obtain ⟨hsurvAll, hI1, hI2, hheadAll⟩ := resume_index z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) B'
    (Log.lineWarnings a) n hd (ckptOf z T₀ L a r) hKe sv hsv hg kw hkw sl hsteps
  obtain ⟨KW, hKW⟩ : ∃ KW, KW = keptWakes z (wakeInstants (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r))
      ++ wakeInstants sv) := ⟨_, rfl⟩
  obtain ⟨SL, hSL⟩ : ∃ SL, SL = Replay.KMap.get (Replay.sleptByDay z KW
      (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ sv)) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r)).foldl
      (Replay.stepWith z (dayOf z KW) SL) (State.init (Log.lineEntries a ++ (Log.lineEntries r ++ B')).length) := ⟨_, rfl⟩
  rw [← hKW] at hI2
  have hRS := resume_steps z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) B' (Log.lineWarnings a) n hd
    (ckptOf z T₀ L a r) hKe sv hsv hg kw hkw sl hsteps KW hKW SL G hG
  obtain ⟨hAgree, hfs, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    cut_state_agrees z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) B' (Log.lineWarnings a) n hd
      (ckptOf z T₀ L a r) hKe sv hsv hg kw hkw sl hsteps Bj Brest svj svr hsplit hsvs hsvjB hsvrB
      (fun q => !isFuture T q) hsep
  have hhb := headerCheck_none (dayOf z kw) _ _ hhdr
  rw [hKL] at hhb
  have hsurvE : survivors ((Log.lineEntries a ++ Bj) ++ Brest)
      = (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ svj) ++ svr := by
    rw [List.append_assoc, ← hsplit, hsurvAll, hsvs, List.append_assoc]
  have hWE : wakeInstants ((foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ svj) ++ svr)
      = wakeInstants (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r)) ++ wakeInstants sv := by
    rw [List.append_assoc, ← hsvs, wakeInstants_append]
  have hSE : (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ svj) ++ svr
      = foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ sv := by
    rw [List.append_assoc, ← hsvs]
  have hlenE : ((Log.lineEntries a ++ Bj) ++ Brest).length = (Log.lineEntries a ++ (Log.lineEntries r ++ B')).length := by
    rw [List.append_assoc, ← hsplit]
  have hBr_notA : ∀ e ∈ Brest, e ∉ foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ svj := by
    intro e he hm
    have hel := hBrestc e he
    rcases List.mem_append.1 hm with hm | hm
    · have := hAc e ((foldedSurvivors_sublist _ _).subset hm); omega
    · have := hBjc e (hsvjB e hm); omega
  -- every unfolded step: its keys, at the new ledger day
  have hkeysAt : ∀ pre e post, svr = pre ++ e :: post →
      ∀ x ∈ Replay.effectsWith z (dayOf z KW) SL ((svj ++ pre).foldl (Replay.stepWith z (dayOf z KW) SL) G) e,
        keyAtOrAbove L' (horizonOf L') x.key = true := by
    intro pre e post hs x hx
    have hsv' : sv = (svj ++ pre) ++ e :: post := by rw [hsvs, hs, List.append_assoc]
    have hel : a.length + j < e.line := hBrestc e (hsvrB e (by rw [hs]; simp))
    obtain ⟨-, hk⟩ := hRS (svj ++ pre) e post hsv'
    have hmem : x.key ∈ (Replay.effectsWith z (dayOf z KW) SL
        ((svj ++ pre).foldl (Replay.stepWith z (dayOf z KW) SL) G) e).map Replay.Effect.key := List.mem_map.2 ⟨x, hx, rfl⟩
    rw [hk] at hmem
    obtain ⟨y, hy, hyk⟩ := List.mem_map.1 hmem
    have hc3 := (stepCheck_none z (dayOf z kw) sl _ _ e (hsteps (svj ++ pre) e post hsv')).2.2 y hy
    rw [hKL] at hc3
    rw [← hyk]
    exact keyAtOrAbove_later L L' y.key hLL hc3 (fun dd hdd =>
      (hlowStep (svj ++ pre) e post hsv' hel).1 dd (List.mem_filterMap.2 ⟨y, hy, hdd⟩))
  -- the unfolded survivors of the spec's lines
  have htv : ((Brest.zipIdx (Log.lineEntries a ++ Bj).length).filter
      (fun p => !Replay.cancelledAt ((Log.lineEntries a ++ Bj) ++ Brest) p.2)).map Prod.fst = svr := by
    have h1 := survivors_split (Log.lineEntries a ++ Bj) Brest
    rw [hsurvE, hfs] at h1
    exact (List.append_cancel_left h1).symm
  refine ⟨?_, ?_⟩
  · -- sealable at `L'`
    unfold sealableEntries
    have hsE := hs
    unfold sealable sealableEntries at hsE
    simp only [Bool.and_eq_true] at hsE
    obtain ⟨⟨⟨⟨-, -⟩, hsM⟩, -⟩, -⟩ := hsE
    have hg' : g1 (ckptOfEntries z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a))
        (unsettled (settledOf (Log.lineEntries a) (Log.lineEntries r)) (Log.lineEntries r ++ B')) = none := hg
    have hsurvCut := survivors_at_cut z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) B' (Log.lineWarnings a)
      hd hg' (a.length + j) hAc hsettled hvi Bj Brest hsplit hBjc hBrestc
    have hd1 : ((Log.lineEntries a ++ Bj) ++ Brest).Pairwise (fun (x y : Entry) => x.line < y.line) := by
      rw [List.append_assoc, ← hsplit]; exact hd
    have hd0 : ((Log.lineEntries a ++ Bj) ++ ([] : List Entry)).Pairwise (fun (x y : Entry) => x.line < y.line) := by
      rw [List.append_nil]; exact hd1.sublist (List.sublist_append_left _ _)
    have hfsnil : foldedSurvivors (Log.lineEntries a ++ Bj) [] = foldedSurvivors (Log.lineEntries a ++ Bj) Brest := by
      rw [foldedSurvivors_nil, hsurvCut]
    have hcongrS := foldedState_congr_er z (Log.lineEntries a ++ Bj) [] Brest hfsnil
    have hcongrH := foldedHeaders_congr_er z (Log.lineEntries a ++ Bj) [] Brest hd0 hd1 hfsnil
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · -- (i) the unfolded effects' keys
      rw [List.all_eq_true]
      intro x hx
      rw [unfoldedEffects_eq, htv, hfs, hWE, ← hKW, hSE] at hx
      rcases mem_collect z KW (Replay.sleptByDay z KW (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ sv))
          svr _ [] x hx with h | ⟨pre, e, post, hs', hxe⟩
      · simp at h
      · have hstep : Replay.step z KW (Replay.sleptByDay z KW (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ sv))
            = Replay.stepWith z (dayOf z KW) SL := by rw [hSL]; rfl
        have heff : Replay.effects z KW (Replay.sleptByDay z KW (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ sv))
            = Replay.effectsWith z (dayOf z KW) SL := by rw [hSL]; rfl
        rw [hstep, heff, hlenE, List.foldl_append, ← hG, ← List.foldl_append] at hxe
        exact hkeysAt pre e post hs' x hxe
    · -- (ii) the unfolded headers
      rw [List.all_eq_true]
      intro q hq
      unfold Replay.entryHeaders at hq
      rw [List.zipIdx_append, Nat.zero_add, List.map_append, List.drop_left' (by simp)] at hq
      obtain ⟨pr, hpr, rfl⟩ := List.mem_map.1 hq
      have he : pr.1 ∈ Brest := by
        rw [← List.zipIdx_map_fst (Log.lineEntries a ++ Bj).length Brest]
        exact List.mem_map.2 ⟨pr, hpr, rfl⟩
      have hDI : Replay.dayIndexOf z ((Log.lineEntries a ++ Bj) ++ Brest) = KW := by
        unfold Replay.dayIndexOf; rw [hsurvE, hWE, hKW]
      simp only [hDI, decide_eq_true_eq]
      have hh := hhb pr.1 (by rw [hsplit]; exact List.mem_append_right _ he)
      rw [hI2 _ hh.1]
      have hmx : Nat.max L (dayOf z kw pr.1.t.val) = dayOf z kw pr.1.t.val := Nat.max_eq_right hh.2
      have := hlowDay pr.1 he
      rw [hmx] at this
      exact this
    · -- (iii) the machine's days
      rw [List.all_eq_true]
      intro x hx
      rw [← hAgree.machine] at hx
      change x ∈ machineDays (svj.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOf z T₀ L a r) n)).machine at hx
      have hlow := hlowMach x hx
      have hLx : L ≤ x := by
        rcases foldl_machineDays z (dayOf z kw) sl svj _ x hx with h | ⟨e, he, rfl⟩
        · have hm : (restore (ckptOf z T₀ L a r) n).machine = (foldedState z (Log.lineEntries a) (Log.lineEntries r)).machine :=
            ckpt_machine z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a)
          rw [hm] at h
          simpa using List.all_eq_true.1 hsM x h
        · exact (hhb e (by rw [hsplit]; exact List.mem_append_left _ (hsvjB e he))).2
      have hmx : Nat.max L x = x := Nat.max_eq_right hLx
      rw [hmx] at hlow
      simpa using hlow
    · -- (iv) the records below `L'` are the folded lines' own
      rw [← hcongrS, ← hcongrH]
      unfold dayRecordsOfEntries
      exact beq_self_eq_true _
    · rw [← hcongrS]
      unfold windowRecordsOfEntries
      exact beq_self_eq_true _
  · -- the reach condition at `L'`
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [List.all_eq_true]
      intro w hw
      obtain ⟨hw1, hw2⟩ := List.mem_filter.1 hw
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hw2
      rw [hsurvE] at hw1
      have hwr : w ∈ svr := by
        rcases List.mem_append.1 hw1 with h | h
        · exact absurd h (hBr_notA w hw2.1)
        · exact h
      have hwi : w.t.val ∈ wakeInstants svr := List.mem_map.2 ⟨w, List.mem_filter.2 ⟨hwr, hw2.2⟩, rfl⟩
      rw [List.all_eq_true]
      intro q hq
      have := hsep w.t.val hwi q hq
      cases hfq : isFuture T q
      · simpa [hfq] using this.1 (by simp [hfq])
      · simpa [hfq] using this.2 (by simp [hfq])
    · rw [List.all_eq_true]
      intro e he
      have hh := hhb e (by rw [hsplit]; exact List.mem_append_right _ he)
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨headSec_later L L' e.t.val.sec hh.1 (hlowSec e he), ?_⟩
      rw [hsurvE, hWE, ← hKW, hI2 _ hh.1]
      have hmx : Nat.max L (dayOf z kw e.t.val) = dayOf z kw e.t.val := Nat.max_eq_right hh.2
      have := hlowDay e he
      rw [hmx] at this
      exact this
    · unfold tailStepsOk
      rw [hsurvE, hWE, ← hKW, hSE, ← hSL, hlenE]
      have hnotB : ∀ e ∈ foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ svj, Brest.contains e = false := by
        intro e he
        cases hcb : Brest.contains e
        · rfl
        · exact absurd he (hBr_notA e (by simpa using hcb))
      rw [← hSE, foldAll_append_vacuous _ _ _ _ _ (fun e he s => by
        simp only [hnotB e he, Bool.not_false, Bool.true_or])]
      intro pre e post hs'
      have heB : e ∈ Brest := hsvrB e (by rw [hs']; simp)
      have hsv' : sv = (svj ++ pre) ++ e :: post := by rw [hsvs, hs', List.append_assoc]
      have hstate : pre.foldl (Replay.stepWith z (dayOf z KW) SL)
          ((foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ svj).foldl (Replay.stepWith z (dayOf z KW) SL)
            (State.init (Log.lineEntries a ++ (Log.lineEntries r ++ B')).length))
          = (svj ++ pre).foldl (Replay.stepWith z (dayOf z KW) SL) G := by
        rw [hG, List.foldl_append, List.foldl_append]
      have hcB : Brest.contains e = true := by simpa using heB
      simp only [hstate, hcB, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
      obtain ⟨hm, -⟩ := hRS (svj ++ pre) e post hsv'
      refine ⟨fun q hq => ?_, fun x hx => hkeysAt pre e post hs' x hx⟩
      rw [hm] at hq
      have hc1 := (stepCheck_none z (dayOf z kw) sl _ _ e (hsteps (svj ++ pre) e post hsv')).1 q hq
      rw [hKL] at hc1
      exact headSec_later L L' q.sec hc1 ((hlowStep (svj ++ pre) e post hsv' (hBrestc e heB)).2 q hq)

end Seal
end Tm
