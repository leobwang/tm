import TmKernel.SealLaw6Ctx
import TmKernel.SealCutState
import TmKernel.SealCutHeaders
import TmKernel.SealCutTags2
import TmKernel.SealCutSlept
import TmKernel.SealCutWakes
import TmKernel.SealCutGroup
import TmKernel.SealCutStep
/-!
# SealLaw6Ckpt — a reseal's checkpoint and records are the seal's (stage 5, D9, W2: law 6)

At a valid cut `j`, the resealed checkpoint is the checkpoint of the lines up to the cut knowing the rest, at the new
ledger day, and the day and window records it emits are those lines' records of `[L, L')` and `[H, H')`
(`rs_state_parts`).  Field by field: the state at the cut agrees above the horizons (`cut_state_agrees`), the stored
wakes, `slept_by_day`, tag lines and settled undos compose (`storedWakes_at_cut`, `storedSlept_congr_get`,
`keptTags_append`, `tagOverflow_append`, `settled_at_cut`), and the unfolded lines cancel nothing folded
(`survivors_at_cut`).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State survivors wakeInstants keptWakes dayOf)
open Log (Entry)

/-- **The resealed checkpoint and records are the seal's.** -/
theorem rs_state_parts (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line) (term : Bool) (p : Policy) (run : Run)
    (j : Nat) (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b)
    (hrun : resumeRun z T (ckptOf z T₀ L a r) b = .ok run)
    (hmig : migrationOk (ckptOf z T₀ L a r) T = true)
    (hcut : cutOk z T (ckptOf z T₀ L a r) b term p run j = true) :
    rsCkpt z T (ckptOf z T₀ L a r) b p run j
        = ckptOf z T (sealDayOf z T (ckptOf z T₀ L a r) p run j) (a ++ b.take j) (b.drop j) ∧
    rsDays z T (ckptOf z T₀ L a r) p run j
        = dayRecordsBetween z T L (sealDayOf z T (ckptOf z T₀ L a r) p run j) (a ++ b.take j) ∧
    rsWindow z T (ckptOf z T₀ L a r) p run j
        = windowRecordsBetween z T (horizonOf L) (horizonOf (sealDayOf z T (ckptOf z T₀ L a r) p run j))
            (a ++ b.take j) := by
  obtain ⟨B', n, sv, kw, sl, Bj, Brest, svj, svr, hbE, hd, hent, hNq, hsvq, hsv, hidxq, hkw, hslq, hsl, hn, hz, hLT,
    hg, hsteps, hhdr, hjle, hBj, hBrest, hsplit, hsvj, hsvr, hsvs, hsvjB, hsvrB, hsep, hsettled, hvi, hAc, hBjc,
    hBrestc, hTake, hDrop, hWs⟩ := rs_context z T₀ T L a r b term p run j hc hr hrun hmig hcut
  have hLE : ∀ x y : List Log.Line, Log.lineEntries (x ++ y) = Log.lineEntries x ++ Log.lineEntries y :=
    fun x y => List.filterMap_append
  have hLW : ∀ x y : List Log.Line, Log.lineWarnings (x ++ y) = Log.lineWarnings x ++ Log.lineWarnings y :=
    fun x y => List.filterMap_append
  have hlen : (a ++ b.take j).length = a.length + j := by
    simp only [List.length_append, List.length_take]; omega
  have hspec : ckptOf z T (sealDayOf z T (ckptOf z T₀ L a r) p run j) (a ++ b.take j) (b.drop j)
      = ckptOfEntries z T (sealDayOf z T (ckptOf z T₀ L a r) p run j) (a.length + j) (Log.lineEntries a ++ Bj) Brest
          (Log.lineWarnings a ++ (Log.lineWarnings b).filter (fun w => decide (w.1 ≤ a.length + j))) := by
    unfold ckptOf; rw [hlen, hLE, hTake, hDrop, hLW, hWs]
  have hdays : dayRecordsBetween z T L (sealDayOf z T (ckptOf z T₀ L a r) p run j) (a ++ b.take j)
      = dayRecordsOfEntries z L (sealDayOf z T (ckptOf z T₀ L a r) p run j) (Log.lineEntries a ++ Bj) := by
    unfold dayRecordsBetween; rw [hLE, hTake]
  have hwin : windowRecordsBetween z T (horizonOf L) (horizonOf (sealDayOf z T (ckptOf z T₀ L a r) p run j))
        (a ++ b.take j)
      = windowRecordsOfEntries z (horizonOf L) (horizonOf (sealDayOf z T (ckptOf z T₀ L a r) p run j))
          (Log.lineEntries a ++ Bj) := by
    unfold windowRecordsBetween; rw [hLE, hTake]
  rw [hspec, hdays, hwin]
  have hKe : ckptOf z T₀ L a r = ckptOfEntries z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r)
      (Log.lineWarnings a) := rfl
  have hKcut : (ckptOf z T₀ L a r).cut = a.length := rfl
  have hKL : (ckptOf z T₀ L a r).ledgerDay = L := rfl
  have hLL : L ≤ sealDayOf z T (ckptOf z T₀ L a r) p run j := le_sealDayOf z T (ckptOf z T₀ L a r) p run j
  -- the reseal's parts, on the context's entries
  have hSvj : rsSvj (ckptOf z T₀ L a r) run j = svj := by unfold rsSvj; rw [hsvq, hKcut, hsvj]
  have hBjE : rsBj (ckptOf z T₀ L a r) run j = Bj := by unfold rsBj; rw [hent, hKcut, hBj]
  have hN : rsN (ckptOf z T₀ L a r) run = n := by unfold rsN; rw [hent, hn]
  have hSlept : rsSlept z (ckptOf z T₀ L a r) run j = (ckptOf z T₀ L a r).sleptByDay
      ++ Replay.sleptByDay z (keptWakes z ((ckptOf z T₀ L a r).wakes ++ wakeInstants svj)) svj := by
    unfold rsSlept rsKwj; rw [hSvj]
  have hSt : rsSt z (ckptOf z T₀ L a r) run j
      = rebindState (Replay.KMap.get ((ckptOf z T₀ L a r).sleptByDay
          ++ Replay.sleptByDay z (keptWakes z ((ckptOf z T₀ L a r).wakes ++ wakeInstants svj)) svj))
        (svj.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOf z T₀ L a r) n)) := by
    unfold rsSt rsRj; rw [hSlept, hSvj, hidxq, hslq, hN]
  have hHs : rsHs z (ckptOf z T₀ L a r) run j = storedHeaders (ckptOf z T₀ L a r)
      ++ (tailHeaders (dayOf z kw) (ckptOf z T₀ L a r).settled (Log.lineEntries r ++ B')).take Bj.length := by
    unfold rsHs; rw [hidxq, hent, hBjE]
  have hQA : rsQA (ckptOf z T₀ L a r) run j = Bj.flatMap entryInstants := by unfold rsQA; rw [hBjE]
  have hMerged : rsMerged (ckptOf z T₀ L a r) run j = mergeTagLines (ckptOf z T₀ L a r).tagLast (tagLines svj) := by
    unfold rsMerged; rw [hSvj]
  have hKwj : rsKwj z (ckptOf z T₀ L a r) run j = keptWakes z ((ckptOf z T₀ L a r).wakes ++ wakeInstants svj) := by
    unfold rsKwj; rw [hSvj]
  have hWsE : rsWs (ckptOf z T₀ L a r) b j = (Log.lineWarnings b).filter (fun w => decide (w.1 ≤ a.length + j)) := by
    unfold rsWs; rw [hKcut]
  have hSettled : settledAt (ckptOf z T₀ L a r) run j
      = (((Replay.danglingOf (unsettled (settledOf (Log.lineEntries a) (Log.lineEntries r)) (Log.lineEntries r ++ B'))).2.filter
          (fun u => decide (a.length + j < u.line))).map (·.line)).reverse := by
    unfold settledAt; rw [hNq, hKcut]; rfl
  unfold rsCkpt rsDays rsWindow
  rw [hSt, hHs, hQA, hMerged, hKwj, hSlept, hWsE, hBjE, hSettled]
  generalize hsd : sealDayOf z T (ckptOf z T₀ L a r) p run j = L' at hLL ⊢
  -- the state at the cut
  have hstepsj : ∀ pre e post, svj = pre ++ e :: post →
      (stepCheck z (dayOf z kw) sl (ckptOf z T₀ L a r)
        (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOf z T₀ L a r) n)) e).2 = none :=
    fun pre e post hs => hsteps pre e (post ++ svr) (by rw [hsvs, hs]; simp)
  have hg' : g1 (ckptOfEntries z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a))
      (unsettled (settledOf (Log.lineEntries a) (Log.lineEntries r)) (Log.lineEntries r ++ B')) = none := hg
  obtain ⟨hAgree, hfs, hIdx, hbd, hbdd, hkd, hki, hkl, hkdr, hkdd, hRd, hRdd, hSl⟩ :=
    cut_state_agrees z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) B' (Log.lineWarnings a) n hd
      (ckptOf z T₀ L a r) hKe sv hsv hg kw hkw sl hsteps Bj Brest svj svr hsplit hsvs hsvjB hsvrB
      (fun q => !isFuture T q) hsep
  have hsurvCut := survivors_at_cut z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) B' (Log.lineWarnings a) hd
    hg' (a.length + j) hAc hsettled hvi Bj Brest hsplit hBjc hBrestc
  have hd1 : ((Log.lineEntries a ++ Bj) ++ Brest).Pairwise (fun (x y : Entry) => x.line < y.line) := by
    rw [List.append_assoc, ← hsplit]; exact hd
  have hd0 : ((Log.lineEntries a ++ Bj) ++ ([] : List Entry)).Pairwise (fun (x y : Entry) => x.line < y.line) := by
    rw [List.append_nil]; exact hd1.sublist (List.sublist_append_left _ _)
  have hfsnil : foldedSurvivors (Log.lineEntries a ++ Bj) [] = foldedSurvivors (Log.lineEntries a ++ Bj) Brest := by
    rw [foldedSurvivors_nil, hsurvCut]
  have hcongrS := foldedState_congr_er z (Log.lineEntries a ++ Bj) [] Brest hfsnil
  have hcongrH := foldedHeaders_congr_er z (Log.lineEntries a ++ Bj) [] Brest hd0 hd1 hfsnil
  generalize hx : rebindState (Replay.KMap.get ((ckptOf z T₀ L a r).sleptByDay
      ++ Replay.sleptByDay z (keptWakes z ((ckptOf z T₀ L a r).wakes ++ wakeInstants svj)) svj))
      (svj.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOf z T₀ L a r) n)) = x at hAgree ⊢
  have hxk : AllKeyed x := by
    rw [← hx]; exact (AllKeyed.foldl z _ _ svj (allKeyed_restore _ n)).rebind _
  have hyk := allKeyed_foldedState z (Log.lineEntries a ++ Bj) Brest
  have hpk := allKeyed_foldedState z (Log.lineEntries a) (Log.lineEntries r)
  have hxd : ∀ d, d < L → x.days.get d = none := fun d hd' => by rw [← hx]; exact hRd d hd'
  have hxdd : ∀ d i, d < horizonOf L → x.doneDates.get (d, i) = none := fun d i hd' => by rw [← hx]; exact hRdd d i hd'
  -- the headers
  have hFH := foldedHeaders_at_cut z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) B' (Log.lineWarnings a) n hd
    (ckptOf z T₀ L a r) hKe sv hsv hg kw hkw sl hsteps hhdr Bj Brest hsplit hIdx
  have hhs : ∀ d, L ≤ d →
      (storedHeaders (ckptOf z T₀ L a r) ++ (tailHeaders (dayOf z kw) (ckptOf z T₀ L a r).settled
        (Log.lineEntries r ++ B')).take Bj.length).filter (fun p => decide (p.1 = d))
      = (foldedHeaders z (Log.lineEntries a ++ Bj) Brest).filter (fun p => decide (p.1 = d)) := by
    intro d hd'
    have hst : (storedHeaders (ckptOf z T₀ L a r)).filter (fun p => decide (p.1 = d))
        = (foldedHeaders z (Log.lineEntries a) (Log.lineEntries r)).filter (fun p => decide (p.1 = d)) :=
      storedHeaders_filter z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a) d hd'
    rw [hFH, List.filter_append, List.filter_append, hst]
  -- the stored checkpoint's fields
  have hmaxT : (ckptOf z T₀ L a r).maxT
      = maxInstant? (((Log.lineEntries a).flatMap entryInstants).filter (fun q => !isFuture T₀ q)) :=
    ckpt_maxT z T₀ L a.length _ _ _
  have hff : (ckptOf z T₀ L a r).futureFloor
      = minInstant? (((Log.lineEntries a).flatMap entryInstants).filter (isFuture T₀)) :=
    ckpt_futureFloor z T₀ L a.length _ _ _
  have hKtag : (ckptOf z T₀ L a r).tagLast = keptTags (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r)) :=
    ckpt_tagLast z T₀ L a.length _ _ _
  have hKover : (ckptOf z T₀ L a r).tagOverflow
      = decide ((keptTags (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r))).length
          < (tagLines (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r))).length) :=
    ckpt_tagOverflow z T₀ L a.length _ _ _
  have hKlast : (ckptOf z T₀ L a r).lastDay
      = Replay.maxDay? ((foldedState z (Log.lineEntries a) (Log.lineEntries r)).days.pairs.map Prod.fst) :=
    ckpt_lastDay z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a)
  have hKcount : (ckptOf z T₀ L a r).entryCount = (Log.lineEntries a).length :=
    ckpt_entryCount z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a)
  have hKwarn : (ckptOf z T₀ L a r).warnings = (Log.lineWarnings a).take maxWarnings :=
    ckpt_warnings z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a)
  have hKwov : (ckptOf z T₀ L a r).warnOverflow = (Log.lineWarnings a).length - maxWarnings :=
    ckpt_warnOverflow z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a)
  refine ⟨?_, ?_, ?_⟩
  · unfold ckptOfEntries
    dsimp only
    rw [Ckpt.mk.injEq]
    refine ⟨rfl, hz, by rw [hKcut], rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hAgree.machine, ?_, ?_, ?_, ?_, ?_, ?_,
      hAgree.lastEff, ?_, hAgree.unknown, hAgree.longestLeak, by rw [hAgree.rwarns], ?_, ?_⟩
    · rw [List.flatMap_append]; exact resealed_maxT T₀ T _ _ _ hmaxT hff hmig
    · rw [List.flatMap_append]; exact resealed_futureFloor T₀ T _ _ _ hmaxT hff hmig
    · -- the stored wakes
      have hKw : (ckptOf z T₀ L a r).wakes
          = storedWakes L (keptWakes z (wakeInstants (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r)))) :=
        ckpt_wakes z T₀ L a.length _ _ _
      have hFI : foldedIndex z (Log.lineEntries a ++ Bj) Brest
          = keptWakes z (wakeInstants (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r)) ++ wakeInstants svj) := by
        unfold foldedIndex; rw [hfs, wakeInstants_append]
      obtain ⟨hsepA, hheadA⟩ := resume_sep z (dayOf z kw) sl (ckptOf z T₀ L a r) (restore _ n) T₀
        ((Log.lineEntries a).flatMap entryInstants) svj hmaxT hff hstepsj
      rw [hKL] at hheadA
      rw [hKw, hFI]
      refine storedWakes_at_cut z L L' hLL (fun q => !isFuture T₀ q) ((Log.lineEntries a).flatMap entryInstants) _ _
        (fun w hw => ?_) hsepA hheadA
      obtain ⟨e, he, _, rfl⟩ := mem_wakeInstants hw
      exact List.mem_flatMap.2 ⟨e, (foldedSurvivors_sublist _ _).subset he, by simp [entryInstants]⟩
    · exact storedSlept_congr_get _ _ L' (fun d hd' => hSl d (Nat.le_trans hLL hd'))
    · rw [hfs, keptTags_append, hKtag]
    · rw [hfs, tagOverflow_append, hKtag, hKover]
    · exact settled_at_cut z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) B' (Log.lineWarnings a) hd hg'
        (a.length + j) hAc hsettled hvi Bj Brest hsplit hBjc hBrestc
    · exact items_merged_eq_raw (ckptOf z T₀ L a r) hpk hxk hyk (ckpt_items z T₀ L a.length _ _ _)
        (ckpt_window z T₀ L a.length _ _ _) hAgree hbdd hki hkl hkdr hkdd hxdd
    · exact windowsFrom_eq hxk hyk (hAgree.mono hLL (horizonOf_mono hLL))
    · exact instOtherOf_eq hxk hyk hAgree
    · exact namedOf_eq hxk hyk hAgree
    · exact daysFrom_eq_raw hxk hyk (hAgree.mono hLL (horizonOf_mono hLL)) _ _
        (fun d hd' => hhs d (Nat.le_trans hLL hd'))
    · rw [hKlast]
      exact lastDay_union hpk hxk hyk hkd hAgree.days hbd hxd
    · rw [hKcount, List.length_append]
    · rw [hKwarn]
      exact take_take_append _ _ _
    · rw [hKwarn, hKwov, List.length_take, List.length_append]
      omega
  · unfold dayRecordsOfEntries
    rw [hKL, hcongrS, hcongrH, daysIn_eq_filter, daysIn_eq_filter, daysFrom_eq_raw hxk hyk hAgree _ _ hhs,
      hAgree.machine]
  · unfold windowRecordsOfEntries
    rw [hKL, hcongrS, windowsIn_eq_filter, windowsIn_eq_filter, windowsFrom_eq hxk hyk hAgree]

end Seal
end Tm
