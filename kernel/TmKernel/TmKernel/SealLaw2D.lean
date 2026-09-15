import TmKernel.SealLaw2C
/-!
# SealLaw2D — law 2 in memory: an accepted resume answers as the whole log's checkpoint (stage 5, D9, W2)

Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Effect HMap HeaderRec survivors wakeInstants keptWakes dayOf)
open Log (Entry)

section CkptFields2

variable (z : Cal.Tz) (T₀ L cut : Nat) (es er : List Entry) (ws : List (Nat × Log.LWarn))

theorem ckpt_lastDay : (ckptOfEntries z T₀ L cut es er ws).lastDay
    = Replay.maxDay? ((foldedState z es er).days.pairs.map Prod.fst) := by simp only [ckptOfEntries]
theorem ckpt_entryCount : (ckptOfEntries z T₀ L cut es er ws).entryCount = es.length := by simp only [ckptOfEntries]
theorem ckpt_warnings : (ckptOfEntries z T₀ L cut es er ws).warnings = ws.take maxWarnings := by
  simp only [ckptOfEntries]
theorem ckpt_warnOverflow : (ckptOfEntries z T₀ L cut es er ws).warnOverflow = ws.length - maxWarnings := by
  simp only [ckptOfEntries]

theorem answer_ckptOfEntries : answer (ckptOfEntries z T₀ L cut es er ws) =
    ⟨L, horizonOf L, ((itemIds (foldedState z es er)).map (itemAggOf (foldedState z es er))).map ItemAgg.finish,
     windowsFrom (foldedState z es er) (horizonOf L), instOtherOf (foldedState z es er), namedOf (foldedState z es er),
     (daysFrom (foldedState z es er) (foldedHeaders z es er) L).map (OpenDay.finish (foldedState z es er).machine),
     (foldedState z es er).machine.block.map (fun b => ⟨b.id, b.started, b.workedMin, b.since, b.paused⟩),
     (foldedState z es er).machine.interrupt.map (fun i => ⟨0, some i.1, none, i.2.1, i.2.2, 0, []⟩),
     Replay.maxDay? ((foldedState z es er).days.pairs.map Prod.fst), (foldedState z es er).global.lastEffective,
     es.length, (foldedState z es er).unknown, (foldedState z es er).longestLeak, (foldedState z es er).rwarns.reverse,
     ws.take maxWarnings, ws.length - maxWarnings⟩ := by
  simp only [answer, ckptOfEntries]

end CkptFields2

theorem take_take_append {α : Type} (n : Nat) (x y : List α) : ((x.take n) ++ y).take n = (x ++ y).take n := by
  rw [List.take_append, List.take_append, List.take_take, Nat.min_self, List.length_take]
  congr 1
  congr 1
  omega

theorem lineEntries_nil : Log.lineEntries [] = [] := rfl

/-- **The windows holding an item's done date, counted, are its done dates at or after the horizon.** -/
theorem window_done_count (st : State) (hk : AllKeyed st) (H : Nat) (i : Log.Id) :
    ((windowsFrom st H).filter (fun w => w.doneIds.contains i)).length
      = ((datesOf st i).filter (fun d => decide (H ≤ d))).length := by
  have hn1 : (((windowsFrom st H).filter (fun w => w.doneIds.contains i)).map WindowRecord.day).Nodup :=
    (windows_days_nodup st H).sublist (List.Sublist.map _ List.filter_sublist)
  have hn2 : ((datesOf st i).filter (fun d => decide (H ≤ d))).Nodup := (datesOf_nodup st hk i).sublist List.filter_sublist
  have h := length_eq_of_mem_iff hn1 hn2 (fun d => by
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨w, ⟨hw, hc⟩, rfl⟩
      obtain ⟨d', hd', hH, rfl⟩ := (mem_windowsFrom st H w).1 hw
      rw [windowOf_day]
      have hi : i ∈ (windowOf st d').doneIds := by simpa using hc
      exact ⟨(mem_datesOf st hk i d').2 (by rw [(mem_doneIds st hk d' i).1 hi]; rfl), hH⟩
    · rintro ⟨hdm, hH⟩
      have hs := (mem_datesOf st hk i d).1 hdm
      have hsome : st.doneDates.get (d, i) = some () := by
        cases hg : st.doneDates.get (d, i) with
        | none => rw [hg] at hs; cases hs
        | some u => rfl
      exact ⟨windowOf st d, ⟨(mem_windowsFrom st H _).2 ⟨d, mem_winKeys_of_doneDate st hk d i hsome, hH, rfl⟩,
        by simpa using (mem_doneIds st hk d i).2 hsome⟩, windowOf_day st d⟩)
  rw [List.length_map] at h
  exact h

theorem aggMerged_eq (K : Ckpt) (x : State) (i : Log.Id) : aggMerged K x i =
    ⟨i, x.items.get i, x.lastDone.get i, (x.dropped.get i).isSome,
     minOpt ((findItem K.items i).bind (·.doneFirst)) (Replay.minDay? (datesOf x i)),
     ((findItem K.items i).map (·.doneCount)).getD 0 - (K.window.filter (fun w => w.doneIds.contains i)).length
       + (datesOf x i).length⟩ := rfl

theorem itemAggOf_eq (y : State) (i : Log.Id) : itemAggOf y i =
    ⟨i, y.items.get i, y.lastDone.get i, (y.dropped.get i).isSome, Replay.minDay? (datesOf y i), (datesOf y i).length⟩ :=
  rfl

/-- **The resumed items are the whole log's**: the checkpoint's ids with the state's, each merged. -/
theorem items_merged_eq {L H : Nat} (K : Ckpt) {p x y : State} (hp : AllKeyed p) (hx : AllKeyed x) (hy : AllKeyed y)
    (hKitems : K.items = (itemIds p).map (itemAggOf p)) (hKwin : K.window = windowsFrom p H)
    (h : AgreeAbove L H x y)
    (hbdd : ∀ d i, d < H → y.doneDates.get (d, i) = p.doneDates.get (d, i))
    (hki : ∀ i, (p.items.get i).isSome → (y.items.get i).isSome)
    (hkl : ∀ i, (p.lastDone.get i).isSome → (y.lastDone.get i).isSome)
    (hkdr : ∀ i, (p.dropped.get i).isSome → (y.dropped.get i).isSome)
    (hkdd : ∀ k, (p.doneDates.get k).isSome → (y.doneDates.get k).isSome)
    (hxdd : ∀ d i, d < H → x.doneDates.get (d, i) = none) :
    (canon idLt (K.items.map (·.id) ++ itemIds x)).map (fun i => (aggMerged K x i).finish)
      = ((itemIds y).map (itemAggOf y)).map ItemAgg.finish := by
  rw [List.map_map]
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
  show (aggMerged K x i).finish = (itemAggOf y i).finish
  congr 1
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

/-- **Law 2's headers**: the whole log's headers are the folded lines' then the tail's. -/
theorem resume_headers (z : Cal.Tz) (T₀ L cut : Nat) (As Rs B' : List Entry) (ws : List (Nat × Log.LWarn)) (n : Nat)
    (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (K : Ckpt) (hK : K = ckptOfEntries z T₀ L cut As Rs ws)
    (sv : List Entry) (hsv : sv = survivors (unsettled K.settled (Rs ++ B')))
    (hg : g1 K (unsettled K.settled (Rs ++ B')) = none)
    (kw : List Cal.Instant) (hkw : kw = tailIndex z K sv)
    (sl : Nat → Option Nat)
    (hsteps : ∀ pre e post, sv = pre ++ e :: post →
      (stepCheck z (dayOf z kw) sl K (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)) e).2 = none)
    (hhdr : headerCheck (dayOf z kw) K (Rs ++ B') = none) :
    foldedHeaders z (As ++ (Rs ++ B')) [] = foldedHeaders z As Rs ++ tailHeaders (dayOf z kw) K.settled (Rs ++ B') := by
  obtain ⟨hsurv, hI1, hI2, -⟩ := resume_index z T₀ L cut As Rs B' ws n hd K hK sv hsv hg kw hkw sl hsteps
  have hhb := headerCheck_none (dayOf z kw) K (Rs ++ B') hhdr
  have hKL : K.ledgerDay = L := by rw [hK]; exact ckpt_ledgerDay' z T₀ L cut As Rs ws
  rw [hKL] at hhb
  have hN : (unsettled K.settled (Rs ++ B')).Pairwise (fun x y => x.line < y.line) :=
    ((List.pairwise_append.1 hd).2.1).sublist List.filter_sublist
  have htail := tailHeadersSpec_eq (dayOf z kw) K.settled (unsettled K.settled (Rs ++ B')) hN (Rs ++ B') [] (by simp)
  simp only [List.length_nil] at htail
  rw [tailHeaders_eq_spec, htail, ← hsv]
  unfold foldedHeaders
  rw [List.append_nil, foldedIndex_nil, hsurv, wakeInstants_append, List.zipIdx_append, List.map_append, Nat.zero_add]
  have hdA : ∀ x ∈ As, ∀ y ∈ Rs ++ B', x.line < y.line := (List.pairwise_append.1 hd).2.2
  congr 1
  · apply List.map_congr_left
    intro p hp
    have hpi := getElem?_of_mem_zipIdx hp
    have hlt : p.2 < As.length := (List.getElem?_eq_some_iff.1 hpi).1
    have hEi : (As ++ (Rs ++ B'))[p.2]? = some p.1 := by rw [List.getElem?_append_left hlt]; exact hpi
    have hpA : p.1 ∈ As := List.mem_of_getElem? hpi
    have hq : p.1.t.val ∈ As.flatMap entryInstants := List.mem_flatMap.2 ⟨p.1, hpA, by simp [entryInstants]⟩
    have h1 := mem_survivors_iff_uncancelled _ hd p.2 p.1 hEi
    have h2 := mem_foldedSurvivors_iff As Rs (hd.sublist ((List.sublist_append_left Rs B').append_left As)) p.2 p.1 hpi
    have h3 : p.1 ∈ survivors (As ++ (Rs ++ B')) ↔ p.1 ∈ foldedSurvivors As Rs := by
      rw [hsurv, List.mem_append]
      refine ⟨fun h => h.elim id (fun hs => ?_), Or.inl⟩
      rw [hsv] at hs
      have hmem : p.1 ∈ Rs ++ B' := mem_unsettled_sub _ _ _ (Replay.mem_of_mem_survivors _ _ hs)
      exact absurd (hdA p.1 hpA p.1 hmem) (Nat.lt_irrefl _)
    have hc : Replay.cancelledAt (As ++ (Rs ++ B')) p.2 = Replay.cancelledAt (As ++ Rs) p.2 := by
      have hiff := h1.symm.trans (h3.trans h2)
      revert hiff
      cases Replay.cancelledAt (As ++ (Rs ++ B')) p.2 <;> cases Replay.cancelledAt (As ++ Rs) p.2 <;> simp
    rw [hI1 _ hq, hc]
  · apply map_zipIdx_eq
    intro k e hk
    have hkE : (As ++ (Rs ++ B'))[As.length + k]? = some e := by
      rw [List.getElem?_append_right (by omega)]; simpa using hk
    have heB : e ∈ Rs ++ B' := List.mem_of_getElem? hk
    have h1 := mem_survivors_iff_uncancelled _ hd (As.length + k) e hkE
    have h3 : e ∈ survivors (As ++ (Rs ++ B')) ↔ e ∈ sv := by
      rw [hsurv, List.mem_append]
      refine ⟨fun h => h.elim (fun hs => ?_) id, Or.inr⟩
      have hA : e ∈ As := (foldedSurvivors_sublist As Rs).subset hs
      exact absurd (hdA e hA e heB) (Nat.lt_irrefl _)
    have hc : Replay.cancelledAt (As ++ (Rs ++ B')) (As.length + k) = !decide (e ∈ sv) := by
      have hiff := h3.symm.trans h1
      by_cases hm : e ∈ sv
      · rw [hiff.1 hm]; simp [hm]
      · have : Replay.cancelledAt (As ++ (Rs ++ B')) (As.length + k) = true := by
          cases hcc : Replay.cancelledAt (As ++ (Rs ++ B')) (As.length + k)
          · exact absurd (hiff.2 hcc) hm
          · rfl
        rw [this]; simp [hm]
    dsimp only
    rw [hI2 _ (hhb e heB).1, hc]

/-- **Law 2, in memory** (§9.5): an accepted resume of the checkpoint of `a` over `b` answers as the checkpoint of
`a ++ b`. -/
theorem resume_answer_eq (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line) (run : Run)
    (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b)
    (h : resumeRun z T (ckptOf z T₀ L a r) b = .ok run) :
    run.answer = answer (ckptOf z T₀ L (a ++ b) []) := by
  obtain ⟨t, rfl⟩ := hr
  have hLE : ∀ x y : List Log.Line, Log.lineEntries (x ++ y) = Log.lineEntries x ++ Log.lineEntries y :=
    fun x y => List.filterMap_append
  have hLW : ∀ x y : List Log.Line, Log.lineWarnings (x ++ y) = Log.lineWarnings x ++ Log.lineWarnings y :=
    fun x y => List.filterMap_append
  have hd : (Log.lineEntries a ++ (Log.lineEntries r ++ Log.lineEntries t)).Pairwise (fun x y => x.line < y.line) := by
    have := (lineEntries_pairwise 1 (a ++ (r ++ t)) hc).1
    rwa [hLE, hLE] at this
  obtain ⟨-, -, -, hg, hfold, hhdr, hrun⟩ := resumeRun_ok z T _ _ run h
  subst hrun
  show resumedAnswer _ _ _ _ _ = _
  generalize hK : ckptOf z T₀ L a r = K at hg hfold hhdr ⊢
  rw [hLE r t] at hg hfold hhdr ⊢
  rw [hLW r t]
  generalize hsv : survivors (unsettled K.settled (Log.lineEntries r ++ Log.lineEntries t)) = sv at hfold hhdr ⊢
  generalize hkw : tailIndex z K sv = kw at hfold hhdr ⊢
  generalize hsl : tailSlept z K kw sv = sl at hfold ⊢
  generalize hn : K.items.length + K.openDays.length + (Log.lineEntries r ++ Log.lineEntries t).length = n at hfold ⊢
  have hsteps := (tailFold_snd z (dayOf z kw) sl K sv (restore K n, none) hfold).2
  have hK' : K = ckptOfEntries z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a) := hK.symm
  obtain ⟨hAgree, -, hbdd, hkd, hki, hkl, hkdr, hkdd, hRd, hRdd⟩ := resume_state_agrees z T₀ L a.length _ _ _ _ n hd
    K hK' sv hsv.symm hg kw hkw.symm sl hsl.symm hsteps
  have hbd := (resume_state_agrees z T₀ L a.length _ _ _ _ n hd K hK' sv hsv.symm hg kw hkw.symm sl hsl.symm hsteps).2.1
  have hHdr := resume_headers z T₀ L a.length _ _ _ _ n hd K hK' sv hsv.symm hg kw hkw.symm sl hsteps hhdr
  have hKL : K.ledgerDay = L := by rw [hK']; exact ckpt_ledgerDay' ..
  have hKitems : K.items = (itemIds (foldedState z (Log.lineEntries a) (Log.lineEntries r))).map
      (itemAggOf (foldedState z (Log.lineEntries a) (Log.lineEntries r))) := by rw [hK']; exact ckpt_items ..
  have hKwin : K.window = windowsFrom (foldedState z (Log.lineEntries a) (Log.lineEntries r)) (horizonOf L) := by
    rw [hK']; exact ckpt_window ..
  have hKlast : K.lastDay = Replay.maxDay? ((foldedState z (Log.lineEntries a) (Log.lineEntries r)).days.pairs.map Prod.fst) := by
    rw [hK']; exact ckpt_lastDay ..
  have hKcount : K.entryCount = (Log.lineEntries a).length := by rw [hK']; exact ckpt_entryCount ..
  have hKwarn : K.warnings = (Log.lineWarnings a).take maxWarnings := by rw [hK']; exact ckpt_warnings ..
  have hKover : K.warnOverflow = (Log.lineWarnings a).length - maxWarnings := by rw [hK']; exact ckpt_warnOverflow ..
  have hstored : ∀ d, L ≤ d → (storedHeaders K).filter (fun p => decide (p.1 = d))
      = (foldedHeaders z (Log.lineEntries a) (Log.lineEntries r)).filter (fun p => decide (p.1 = d)) := by
    intro d hd; rw [hK']; exact storedHeaders_filter z T₀ L a.length _ _ _ d hd
  have hhs : ∀ d, L ≤ d →
      (storedHeaders K ++ tailHeaders (dayOf z kw) K.settled (Log.lineEntries r ++ Log.lineEntries t)).filter
        (fun p => decide (p.1 = d))
      = (foldedHeaders z (Log.lineEntries a ++ (Log.lineEntries r ++ Log.lineEntries t)) []).filter
        (fun p => decide (p.1 = d)) := by
    intro d hd
    rw [hHdr, List.filter_append, List.filter_append, hstored d hd]
  have hx : AllKeyed (rebindState sl (sv.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n))) :=
    (AllKeyed.foldl z _ _ sv (allKeyed_restore K n)).rebind sl
  have hy := allKeyed_foldedState z (Log.lineEntries a ++ (Log.lineEntries r ++ Log.lineEntries t)) []
  have hp := allKeyed_foldedState z (Log.lineEntries a) (Log.lineEntries r)
  unfold ckptOf
  rw [hLE a (r ++ t), hLE r t, hLW a (r ++ t), hLW r t, lineEntries_nil, answer_ckptOfEntries]
  unfold resumedAnswer
  simp only [Seal.Answer.mk.injEq]
  refine ⟨hKL, by rw [hKL], ?_, by rw [hKL]; exact windowsFrom_eq hx hy hAgree, instOtherOf_eq hx hy hAgree,
    namedOf_eq hx hy hAgree, by rw [hKL]; exact daysFrom_eq hx hy hAgree _ _ hhs, by rw [hAgree.machine],
    by rw [hAgree.machine], ?_, hAgree.lastEff, by rw [hKcount]; simp only [List.length_append], hAgree.unknown,
    hAgree.longestLeak, by rw [hAgree.rwarns], by rw [hKwarn]; exact take_take_append _ _ _, ?_⟩
  · exact items_merged_eq K hp hx hy hKitems hKwin hAgree hbdd hki hkl hkdr hkdd hRdd
  · rw [hKlast]
    exact lastDay_union hp hx hy hkd hAgree.days hbd hRd
  · rw [hKwarn, hKover, List.length_take, List.length_append, List.length_append, List.length_append]
    omega

end Seal
end Tm
