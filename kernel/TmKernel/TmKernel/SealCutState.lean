import TmKernel.SealLaw5A
import TmKernel.SealCutMask
/-!
# SealCutState — the state at the cut (stage 5, D9, W2: law 6)

A reseal folds the tail's survivors up to its cut on the run's index and `slept_by_day`, and rebinds the observations to
the folded wakes' table.  Above the horizons that state agrees with the checkpoint of the lines up to the cut, knowing
the rest (`cut_state_agrees`): the unfolded surviving wakes are after the folded instants not future and more than the
fence before the future ones, so the run's index and the folded lines' own agree at every folded instant.
Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Effect survivors wakeInstants keptWakes dayOf)
open Log (Entry)

/-- **The folded instants' index at the cut**: with every unfolded surviving wake after the folded instants not future
and more than the fence before the future ones, the whole index and the folded survivors' own agree at every folded
instant. -/
theorem cut_index_agrees (z : Cal.Tz) (As Bj SA svj svr : List Entry) (hSA : ∀ e ∈ SA, e ∈ As)
    (hsvj : ∀ e ∈ svj, e ∈ Bj) (P : Cal.Instant → Bool)
    (hsep : ∀ w ∈ wakeInstants svr, ∀ q ∈ (As ++ Bj).flatMap entryInstants,
      (P q = true → q < w) ∧ (P q = false → w.sec + fenceSec < q.sec))
    (q : Cal.Instant) (hq : q ∈ (As ++ Bj).flatMap entryInstants) :
    dayOf z (keptWakes z (wakeInstants SA ++ wakeInstants (svj ++ svr))) q
      = dayOf z (keptWakes z (wakeInstants SA ++ wakeInstants svj)) q := by
  rw [wakeInstants_append, ← List.append_assoc]
  refine dayOf_folded_agrees z P ((As ++ Bj).flatMap entryInstants) _ _ (fun w hw => ?_) (fun q hq => ?_) hsep q hq
  · rcases List.mem_append.1 hw with hw | hw
    · obtain ⟨e, he, _, rfl⟩ := mem_wakeInstants hw
      exact List.mem_flatMap.2 ⟨e, List.mem_append_left _ (hSA e he), by simp [entryInstants]⟩
    · obtain ⟨e, he, _, rfl⟩ := mem_wakeInstants hw
      exact List.mem_flatMap.2 ⟨e, List.mem_append_right _ (hsvj e he), by simp [entryInstants]⟩
  · rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨e, _, hqe⟩ := List.mem_flatMap.1 hq
      exact entryInstants_ns e q hqe
    · obtain ⟨e, _, _, rfl⟩ := mem_wakeInstants hq
      exact ns_lt_of_wf _ e.t.property

/-- The machine a fold from a restored checkpoint reaches holds only instants of the folded lines and of the fold. -/
theorem restore_fold_mi (z : Cal.Tz) (T₀ L cut : Nat) (As Rs : List Entry) (ws : List (Nat × Log.LWarn)) (n : Nat)
    (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (pre : List Entry) (q : Cal.Instant)
    (hq : q ∈ machineInstants (pre.foldl (Replay.stepWith z dy sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n)).machine) :
    q ∈ As.flatMap entryInstants ∨ q ∈ pre.flatMap entryInstants := by
  rcases foldl_mi z dy sl pre _ q hq with h | h
  · left
    have hm : (restore (ckptOfEntries z T₀ L cut As Rs ws) n).machine = (foldedState z As Rs).machine :=
      ckpt_machine z T₀ L cut As Rs ws
    rw [hm, foldedState_eq] at h
    rcases foldl_mi z _ _ _ _ q h with h | h
    · simp [machineInstants, blockSince, blockPaused, State.init] at h
    · obtain ⟨e, he, hqe⟩ := List.mem_flatMap.1 h
      exact List.mem_flatMap.2 ⟨e, (foldedSurvivors_sublist As Rs).subset he, hqe⟩
  · exact Or.inr h

/-- **The state at the cut** (§9.4, law 6's route): a reseal's folded state, rebound to the folded wakes' table, agrees
above the horizons with the checkpoint's state of the lines up to the cut; below them the checkpoint's state is the
folded lines', whose keys it keeps, and the reseal's fold writes nothing there. -/
theorem cut_state_agrees (z : Cal.Tz) (T₀ L cut : Nat) (As Rs B' : List Entry) (ws : List (Nat × Log.LWarn))
    (n : Nat) (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (K : Ckpt) (hK : K = ckptOfEntries z T₀ L cut As Rs ws)
    (sv : List Entry) (hsv : sv = survivors (unsettled K.settled (Rs ++ B')))
    (hg : g1 K (unsettled K.settled (Rs ++ B')) = none)
    (kw : List Cal.Instant) (hkw : kw = tailIndex z K sv)
    (sl : Nat → Option Nat)
    (hsteps : ∀ pre e post, sv = pre ++ e :: post →
      (stepCheck z (dayOf z kw) sl K (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)) e).2 = none)
    (Bj Brest svj svr : List Entry) (hsplit : Rs ++ B' = Bj ++ Brest) (hsvs : sv = svj ++ svr)
    (hsvj : ∀ e ∈ svj, e ∈ Bj) (hsvr : ∀ e ∈ svr, e ∈ Brest) (P : Cal.Instant → Bool)
    (hsep : ∀ w ∈ wakeInstants svr, ∀ q ∈ (As ++ Bj).flatMap entryInstants,
      (P q = true → q < w) ∧ (P q = false → w.sec + fenceSec < q.sec)) :
    AgreeAbove L (horizonOf L)
      (rebindState (Replay.KMap.get (K.sleptByDay ++ Replay.sleptByDay z (keptWakes z (K.wakes ++ wakeInstants svj)) svj))
        (svj.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)))
      (foldedState z (As ++ Bj) Brest) ∧
    foldedSurvivors (As ++ Bj) Brest = foldedSurvivors As Rs ++ svj ∧
    (∀ q ∈ (As ++ Bj).flatMap entryInstants,
      dayOf z (keptWakes z (wakeInstants (foldedSurvivors As Rs) ++ wakeInstants sv)) q
        = dayOf z (foldedIndex z (As ++ Bj) Brest) q) ∧
    (∀ d, d < L → (foldedState z (As ++ Bj) Brest).days.get d = (foldedState z As Rs).days.get d) ∧
    (∀ d i, d < horizonOf L →
      (foldedState z (As ++ Bj) Brest).doneDates.get (d, i) = (foldedState z As Rs).doneDates.get (d, i)) ∧
    (∀ d, ((foldedState z As Rs).days.get d).isSome → ((foldedState z (As ++ Bj) Brest).days.get d).isSome) ∧
    (∀ i, ((foldedState z As Rs).items.get i).isSome → ((foldedState z (As ++ Bj) Brest).items.get i).isSome) ∧
    (∀ i, ((foldedState z As Rs).lastDone.get i).isSome → ((foldedState z (As ++ Bj) Brest).lastDone.get i).isSome) ∧
    (∀ i, ((foldedState z As Rs).dropped.get i).isSome → ((foldedState z (As ++ Bj) Brest).dropped.get i).isSome) ∧
    (∀ k, ((foldedState z As Rs).doneDates.get k).isSome → ((foldedState z (As ++ Bj) Brest).doneDates.get k).isSome) ∧
    (∀ d, d < L → (svj.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)).days.get d = none) ∧
    (∀ d i, d < horizonOf L → (svj.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)).doneDates.get (d, i) = none) ∧
    (∀ d, L ≤ d →
      Replay.KMap.get (K.sleptByDay ++ Replay.sleptByDay z (keptWakes z (K.wakes ++ wakeInstants svj)) svj) d
        = Replay.KMap.get (Replay.sleptByDay z (foldedIndex z (As ++ Bj) Brest) (foldedSurvivors (As ++ Bj) Brest)) d) := by
  obtain ⟨hsurv, hI1, hI2, hhead⟩ := resume_index z T₀ L cut As Rs B' ws n hd K hK sv hsv hg kw hkw sl hsteps
  subst hK
  have hL := ckpt_ledgerDay' z T₀ L cut As Rs ws
  have hPS := pendingStart_restore z T₀ L cut As Rs ws n
  generalize hKdef : ckptOfEntries z T₀ L cut As Rs ws = K at hsteps hPS hL hsv hg hkw
  -- the prefix's steps are checked
  have hstepsj : ∀ pre e post, svj = pre ++ e :: post →
      (stepCheck z (dayOf z kw) sl K (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)) e).2 = none :=
    fun pre e post hs => hsteps pre e (post ++ svr) (by rw [hsvs, hs]; simp)
  -- the mask at the cut
  have hd' : (As ++ (Bj ++ Brest)).Pairwise (fun x y => x.line < y.line) := by rwa [← hsplit]
  have hSA : ∀ e ∈ foldedSurvivors As Rs, e ∈ As := fun e he => (foldedSurvivors_sublist As Rs).subset he
  have hsvB : ∀ e ∈ sv, e ∈ Bj ++ Brest := fun e he => by
    rw [← hsplit, hsv] at *; exact mem_unsettled_sub _ _ _ (Replay.mem_of_mem_survivors _ _ he)
  have hdisj : ∀ x ∈ Bj, ∀ y ∈ Brest, x.line < y.line := (List.pairwise_append.1 (List.pairwise_append.1 hd').2.1).2.2
  have hfilt : sv.filter (fun e => Bj.contains e) = svj := by
    rw [hsvs, List.filter_append]
    have h1 : svj.filter (fun e => Bj.contains e) = svj :=
      List.filter_eq_self.2 (fun e he => by simpa using hsvj e he)
    have h2 : svr.filter (fun e => Bj.contains e) = [] := List.filter_eq_nil_iff.2 (fun e he hc => by
      have hB : e ∈ Bj := by simpa using hc
      exact Nat.lt_irrefl _ (hdisj e hB e (hsvr e he)))
    rw [h1, h2, List.append_nil]
  have hfs : foldedSurvivors (As ++ Bj) Brest = foldedSurvivors As Rs ++ svj := by
    rw [foldedSurvivors_at_cut As Bj Brest hd' (foldedSurvivors As Rs) sv (by rw [← hsplit]; exact hsurv) hSA hsvB,
      hfilt]
  -- the two indexes
  obtain ⟨KW, hKW⟩ : ∃ KW, KW = keptWakes z (wakeInstants (foldedSurvivors As Rs) ++ wakeInstants sv) := ⟨_, rfl⟩
  obtain ⟨KWj, hKWj⟩ : ∃ KWj, KWj = keptWakes z (wakeInstants (foldedSurvivors As Rs) ++ wakeInstants svj) := ⟨_, rfl⟩
  rw [← hKW] at hI1 hI2
  have hKWjI : foldedIndex z (As ++ Bj) Brest = KWj := by
    rw [hKWj]; unfold foldedIndex; rw [hfs, wakeInstants_append]
  have hQA : ∀ q ∈ (As ++ Bj).flatMap entryInstants, dayOf z KW q = dayOf z KWj q := by
    intro q hq
    rw [hKW, hKWj, hsvs]
    exact cut_index_agrees z As Bj (foldedSurvivors As Rs) svj svr hSA hsvj P hsep q hq
  have hIj1 : ∀ q ∈ As.flatMap entryInstants, dayOf z KWj q = dayOf z (foldedIndex z As Rs) q := fun q hq =>
    (hQA q (by rw [List.flatMap_append]; exact List.mem_append_left _ hq)).symm.trans (hI1 q hq)
  -- the queries of a prefix of the folded tail are folded instants after the head second
  have hmiQA : ∀ (dy' : Cal.Instant → Nat) (sl' : Nat → Option Nat) (pre : List Entry), (∀ e ∈ pre, e ∈ Bj) →
      ∀ q ∈ machineInstants (pre.foldl (Replay.stepWith z dy' sl') (restore K n)).machine,
        q ∈ (As ++ Bj).flatMap entryInstants := by
    intro dy' sl' pre hpre q hq
    rw [← hKdef] at hq
    rcases restore_fold_mi z T₀ L cut As Rs ws n dy' sl' pre q hq with h | h
    · rw [List.flatMap_append]; exact List.mem_append_left _ h
    · obtain ⟨e, he, hqe⟩ := List.mem_flatMap.1 h
      rw [List.flatMap_append]; exact List.mem_append_right _ (List.mem_flatMap.2 ⟨e, hpre e he, hqe⟩)
  have hpre : ∀ pre post, svj = pre ++ post →
      pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)
        = pre.foldl (Replay.stepWith z (dayOf z KWj) sl) (restore K n) := by
    intro pre post hs
    have hpreB : ∀ e ∈ pre, e ∈ Bj := fun e he => hsvj e (by rw [hs]; exact List.mem_append_left _ he)
    have h1 : pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)
        = pre.foldl (Replay.stepWith z (dayOf z KW) sl) (restore K n) :=
      resume_fold_congr z (dayOf z kw) (dayOf z KW) sl K _ pre
        (fun pre' e' post' h' => hstepsj pre' e' (post' ++ post) (by rw [hs, h']; simp))
        (fun q hq => (hI2 q (by rwa [hL] at hq)).symm)
    rw [h1]
    apply foldl_stepWith_congr
    intro q hq
    apply hQA
    rcases foldQueries_sub z _ _ pre _ q hq with h | h
    · exact hmiQA (dayOf z KW) sl [] (fun _ h => by cases h) q h
    · obtain ⟨e, he, hqe⟩ := List.mem_flatMap.1 h
      rw [List.flatMap_append]; exact List.mem_append_right _ (List.mem_flatMap.2 ⟨e, hpreB e he, hqe⟩)
  -- the folded part on the cut's index
  obtain ⟨SLj', hSLj'⟩ : ∃ SLj', SLj' = Replay.KMap.get (Replay.sleptByDay z KWj (foldedSurvivors As Rs ++ svj)) :=
    ⟨_, rfl⟩
  obtain ⟨Gj, hGjdef⟩ : ∃ Gj, Gj = (foldedSurvivors As Rs).foldl (Replay.stepWith z (dayOf z KWj) SLj')
      (State.init (As ++ Bj).length) := ⟨_, rfl⟩
  have hGj : AgreeAbove L (horizonOf L) Gj (rebindState SLj' (restore K n)) := by
    rw [hGjdef, ← hKdef]; exact folded_part_agrees z T₀ L cut As Rs ws n _ KWj SLj' hIj1
  have hFj : foldedState z (As ++ Bj) Brest = svj.foldl (Replay.stepWith z (dayOf z KWj) SLj') Gj := by
    rw [foldedState_eq, hKWjI, hfs, List.foldl_append, ← hSLj', hGjdef]
  -- `slept_by_day` at and above the ledger day
  have hslept : ∀ d, L ≤ d →
      Replay.KMap.get (K.sleptByDay ++ Replay.sleptByDay z (keptWakes z (K.wakes ++ wakeInstants svj)) svj) d
        = SLj' d := by
    intro d hdL
    rw [hSLj', kmap_get_append, sleptByDay_append, kmap_get_append, ← hKdef, ckpt_sleptByDay,
      get_storedSlept _ L d hdL]
    have e1 : Replay.sleptByDay z (foldedIndex z As Rs) (foldedSurvivors As Rs)
        = Replay.sleptByDay z KWj (foldedSurvivors As Rs) :=
      sleptByDay_congr z _ _ _ (fun e he _ =>
        (hIj1 e.t.val (List.mem_flatMap.2 ⟨e, hSA e he, by simp [entryInstants]⟩)).symm)
    have e2 : Replay.sleptByDay z (keptWakes z ((ckptOfEntries z T₀ L cut As Rs ws).wakes ++ wakeInstants svj)) svj
        = Replay.sleptByDay z KWj svj := by
      apply sleptByDay_congr
      intro e he hw
      have hwj : e.t.val ∈ wakeInstants svj := List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, hw⟩, rfl⟩
      have hwsv : e.t.val ∈ wakeInstants sv := by rw [hsvs, wakeInstants_append]; exact List.mem_append_left _ hwj
      obtain ⟨hsepA, -⟩ := resume_sep z (dayOf z kw) sl (ckptOfEntries z T₀ L cut As Rs ws) (restore _ n) T₀
        (As.flatMap entryInstants) svj (ckpt_maxT z T₀ L cut As Rs ws) (ckpt_futureFloor z T₀ L cut As Rs ws)
        (by rw [hKdef]; exact hstepsj)
      rw [ckpt_wakes, hKWj]
      unfold foldedIndex
      refine (dayOf_tail_agrees z L (fun q => !isFuture T₀ q) (As.flatMap entryInstants) _ (wakeInstants svj)
        (fun w hw => ?_) hsepA (fun w hw => ?_) e.t.val (hhead _ hwsv)).symm
      · obtain ⟨x, hx, _, rfl⟩ := mem_wakeInstants hw
        exact List.mem_flatMap.2 ⟨x, hSA x hx, by simp [entryInstants]⟩
      · exact hhead w (by rw [hsvs, wakeInstants_append]; exact List.mem_append_left _ hw)
    rw [e1, e2]
  -- the agreement
  have hAgree : AgreeAbove L (horizonOf L)
      (rebindState (Replay.KMap.get (K.sleptByDay ++ Replay.sleptByDay z (keptWakes z (K.wakes ++ wakeInstants svj)) svj))
        (svj.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)))
      (foldedState z (As ++ Bj) Brest) := by
    refine (AgreeAbove.rebind (AgreeAbove.refl L (horizonOf L) _) _ SLj' hslept).trans ?_
    rw [hpre svj [] (by simp), ← foldl_rebind z (dayOf z KWj) SLj' sl svj (restore K n) hPS, hFj]
    exact AgreeAbove.foldl z _ _ svj hGj.symm
  -- below the horizons
  have hkeys : ∀ pre e post, svj = pre ++ e :: post →
      ∀ x ∈ Replay.effectsWith z (dayOf z KWj) SLj' (pre.foldl (Replay.stepWith z (dayOf z KWj) SLj') Gj) e,
        keyAtOrAbove L (horizonOf L) x.key = true := by
    intro pre e post hs x hx
    have hc := stepCheck_none z (dayOf z kw) sl _ _ e (hstepsj pre e post hs)
    rw [hL] at hc
    obtain ⟨hhq, -, hck⟩ := hc
    have hm : (pre.foldl (Replay.stepWith z (dayOf z KWj) SLj') Gj).machine
        = (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)).machine := by
      rw [(AgreeAbove.foldl z _ _ pre hGj).machine, foldl_rebind z (dayOf z KWj) SLj' sl pre _ hPS,
        hpre pre (e :: post) hs]
      rfl
    rw [effectsWith_machine z _ _ _ _ e hm] at hx
    have hmem : x.key ∈ (Replay.effectsWith z (dayOf z KWj) SLj'
        (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)) e).map Replay.Effect.key :=
      List.mem_map.2 ⟨x, hx, rfl⟩
    have heB : e ∈ Bj := hsvj e (by rw [hs]; simp)
    have hpreB : ∀ e' ∈ pre, e' ∈ Bj := fun e' he' => hsvj e' (by rw [hs]; exact List.mem_append_left _ he')
    rw [effectsWith_keys z (dayOf z KWj) sl SLj' _ e (pendingStart_foldl z _ _ pre _ hPS),
      effectsWith_congr (dayOf z KWj) (dayOf z kw) z sl _ e (fun q hq => ?_)] at hmem
    · obtain ⟨y, hy, hyk⟩ := List.mem_map.1 hmem
      rw [← hyk]; exact hck y hy
    · have hqA : q ∈ (As ++ Bj).flatMap entryInstants := by
        rcases stepQueries_sub _ e q hq with h | h
        · rw [List.flatMap_append]; exact List.mem_append_right _ (List.mem_flatMap.2 ⟨e, heB, h⟩)
        · exact hmiQA (dayOf z kw) sl pre hpreB q h
      rw [← hQA q hqA]
      exact hI2 q (hhq q hq)
  have hbelowF := foldl_below z (dayOf z KWj) SLj' L (horizonOf L) svj Gj hkeys
  have hbelowR := foldl_below z (dayOf z kw) sl L (horizonOf L) svj (restore K n)
    (fun pre e post hs x hx => by
      have := (stepCheck_none z (dayOf z kw) sl _ _ e (hstepsj pre e post hs)).2.2 x hx
      rwa [hL] at this)
  have hkeep := foldl_keeps_keys z (dayOf z KWj) SLj' svj Gj
  obtain ⟨hRbd, hRbl⟩ := restore_below z T₀ L cut As Rs ws n
  rw [hKdef] at hRbd hRbl
  -- the folded part below the horizons is the folded lines'
  have hq1 : ∀ q ∈ foldQueries z (dayOf z KWj) SLj' (State.init (As ++ Bj).length) (foldedSurvivors As Rs),
      dayOf z KWj q = dayOf z (foldedIndex z As Rs) q := by
    intro q hq
    rcases foldQueries_sub z _ _ _ _ q hq with h | h
    · simp [machineInstants, blockSince, blockPaused, State.init] at h
    · obtain ⟨e, he, hqe⟩ := List.mem_flatMap.1 h
      exact hIj1 q (List.mem_flatMap.2 ⟨e, hSA e he, hqe⟩)
  obtain ⟨X, hXdef⟩ : ∃ X, X = (foldedSurvivors As Rs).foldl (Replay.stepWith z (dayOf z (foldedIndex z As Rs))
      (Replay.KMap.get (Replay.sleptByDay z (foldedIndex z As Rs) (foldedSurvivors As Rs))))
      (State.init (As ++ Bj).length) := ⟨_, rfl⟩
  have hGX : Gj = rebindState SLj' X := by
    rw [hGjdef, foldl_stepWith_congr z _ _ SLj' _ _ hq1, hXdef]
    have := foldl_rebind z (dayOf z (foldedIndex z As Rs)) SLj'
      (Replay.KMap.get (Replay.sleptByDay z (foldedIndex z As Rs) (foldedSurvivors As Rs))) (foldedSurvivors As Rs)
      (State.init (As ++ Bj).length) (pendingStart_init _)
    rwa [rebindState_init] at this
  have hXs : Replay.SameReadings X (foldedState z As Rs) := by
    rw [hXdef, foldedState_eq]; exact Replay.SameReadings.foldl z _ _ _ (Replay.sameReadings_init _ _)
  refine ⟨hAgree, hfs, fun q hq => by rw [hKWjI, ← hKW]; exact hQA q hq, fun d hd => ?_, fun d i hd => ?_, fun d h => ?_,
    fun i h => ?_, fun i h => ?_, fun i h => ?_, fun k h => ?_, fun d hd => ?_, fun d i hd => ?_, fun d hd => ?_⟩
  · rw [hFj, valueAt_day_get (hbelowF.1 d hd), hGX]; exact hXs.days d
  · rw [hFj, valueAt_doneDate_get (hbelowF.2.2 i d hd), hGX]; exact hXs.doneDates (d, i)
  · rw [hFj]; exact hkeep.1 d (by rw [hGX]; show (X.days.get d).isSome = true; rw [hXs.days d]; exact h)
  · rw [hFj]; exact hkeep.2.1 i (by rw [hGX]; show (X.items.get i).isSome = true; rw [hXs.items i]; exact h)
  · rw [hFj]; exact hkeep.2.2.1 i (by rw [hGX]; show (X.lastDone.get i).isSome = true; rw [hXs.lastDone i]; exact h)
  · rw [hFj]; exact hkeep.2.2.2.1 i (by rw [hGX]; show (X.dropped.get i).isSome = true; rw [hXs.dropped i]; exact h)
  · rw [hFj]; exact hkeep.2.2.2.2 k (by rw [hGX]; show (X.doneDates.get k).isSome = true; rw [hXs.doneDates k]; exact h)
  · rw [valueAt_day_get (hbelowR.1 d hd)]; exact hRbl d hd
  · rw [valueAt_doneDate_get (hbelowR.2.2 i d hd)]; exact hRbd d i hd
  · rw [hKWjI, hfs, ← hSLj']; exact hslept d hd

end Seal
end Tm
