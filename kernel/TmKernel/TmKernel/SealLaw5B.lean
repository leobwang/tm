import TmKernel.SealLaw5A
import TmKernel.SealReach
/-!
# SealLaw5B — law 5, both directions: acceptance is exactly `L ≤ T`, `reachFree` and `tagsClear` (stage 5, D9, W2)

Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Effect HMap survivors wakeInstants keptWakes dayOf isWake)
open Log (Entry)

theorem resume_isOk_eq (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (term : Bool) (p : Option Policy) :
    (resume z T K b term p).isOk = (resumeRun z T K b).isOk := by
  unfold resume
  cases resumeRun z T K b <;> rfl

theorem isOk_iff_exists {ε α : Type} (x : Except ε α) : x.isOk = true ↔ ∃ v, x = .ok v := by
  cases x <;> simp [Except.isOk, Except.toBool]

theorem foldAll_append_vacuous (step : State → Entry → State) (P : State → Entry → Bool) (A B : List Entry)
    (st : State) (hA : ∀ e ∈ A, ∀ s, P s e = true) :
    foldAll step P (A ++ B) st = true ↔
      ∀ pre e post, B = pre ++ e :: post → P (pre.foldl step (A.foldl step st)) e = true := by
  have h0 : ∀ (A : List Entry) (s : State), (∀ e ∈ A, ∀ s, P s e = true) →
      A.foldl (fun (acc : State × Bool) e => (step acc.1 e, acc.2 && P acc.1 e)) (s, true) = (A.foldl step s, true) := by
    intro A
    induction A with
    | nil => intro s _; rfl
    | cons e A ih =>
      intro s h
      have hPe := h e List.mem_cons_self s
      simp only [List.foldl_cons, hPe, Bool.and_self]
      exact ih _ (fun e' he' s' => h e' (List.mem_cons_of_mem _ he') s')
  unfold foldAll
  rw [List.foldl_append, h0 A st hA, foldAll_iff]
  simp

/-- **`reachFree`, read on the resume's split**: under the mask split, its three parts over the tail's survivors. -/
theorem reachFree_iff (z : Cal.Tz) (T₀ L : Nat) (a r t : List Log.Line) (sv : List Entry)
    (hd : (Log.lineEntries a ++ (Log.lineEntries r ++ Log.lineEntries t)).Pairwise (fun x y => x.line < y.line))
    (hsurv : survivors (Log.lineEntries a ++ (Log.lineEntries r ++ Log.lineEntries t))
      = foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ sv)
    (hsvB : ∀ e ∈ sv, e ∈ Log.lineEntries r ++ Log.lineEntries t)
    (KW : List Cal.Instant)
    (hKW : KW = keptWakes z (wakeInstants (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r)) ++ wakeInstants sv))
    (SL : Nat → Option Nat)
    (hSL : SL = Replay.KMap.get (Replay.sleptByDay z KW (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ sv)))
    (G : State)
    (hG : G = (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r)).foldl (Replay.stepWith z (dayOf z KW) SL)
      (State.init (Log.lineEntries a ++ (Log.lineEntries r ++ Log.lineEntries t)).length)) :
    reachFree z T₀ L a (r ++ t) = true ↔
      (∀ w ∈ wakeInstants sv, ∀ q ∈ (Log.lineEntries a).flatMap entryInstants,
        ((fun q => !isFuture T₀ q) q = true → q < w) ∧ ((fun q => !isFuture T₀ q) q = false → w.sec + fenceSec < q.sec)) ∧
      (∀ e ∈ Log.lineEntries r ++ Log.lineEntries t, headSec L ≤ e.t.val.sec ∧ L ≤ dayOf z KW e.t.val) ∧
      (∀ pre e post, sv = pre ++ e :: post →
        (∀ q ∈ stepQueries (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G).machine e, headSec L ≤ q.sec) ∧
        (∀ x ∈ Replay.effectsWith z (dayOf z KW) SL (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G) e,
          keyAtOrAbove L (horizonOf L) x.key = true)) := by
  have hLE : Log.lineEntries (r ++ t) = Log.lineEntries r ++ Log.lineEntries t := List.filterMap_append
  have hdA : ∀ x ∈ Log.lineEntries a, ∀ y ∈ Log.lineEntries r ++ Log.lineEntries t, x.line < y.line :=
    (List.pairwise_append.1 hd).2.2
  have hnotB : ∀ e ∈ foldedSurvivors (Log.lineEntries a) (Log.lineEntries r),
      (Log.lineEntries r ++ Log.lineEntries t).contains e = false := fun e he => by
    have heA := (foldedSurvivors_sublist _ _).subset he
    have : e ∉ Log.lineEntries r ++ Log.lineEntries t := fun hb => Nat.lt_irrefl _ (hdA e heA e hb)
    simpa using this
  have hinB : ∀ e ∈ sv, (Log.lineEntries r ++ Log.lineEntries t).contains e = true := fun e he => by
    simpa using hsvB e he
  unfold reachFree tailStepsOk
  rw [hLE, hsurv, wakeInstants_append, ← hKW, ← hSL]
  simp only [Bool.and_eq_true]
  refine (and_congr (and_congr ?_ ?_) ?_).trans and_assoc
  · rw [List.all_eq_true]
    constructor
    · intro h w hw q hq
      obtain ⟨e, he, hwk, rfl⟩ := mem_wakeInstants hw
      have hmem : e ∈ (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ sv).filter
          (fun e => (Log.lineEntries r ++ Log.lineEntries t).contains e && isWake e) :=
        List.mem_filter.2 ⟨List.mem_append_right _ he, by simp only [hinB e he, hwk, Bool.and_self]⟩
      have := List.all_eq_true.1 (h e hmem) q hq
      cases hfq : isFuture T₀ q
      · exact ⟨fun _ => by simpa [hfq] using this, fun h' => by simp at h'⟩
      · exact ⟨fun h' => by simp at h', fun _ => by simpa [hfq] using this⟩
    · intro h w hw
      obtain ⟨hw1, hw2⟩ := List.mem_filter.1 hw
      simp only [Bool.and_eq_true] at hw2
      have hwsv : w ∈ sv := by
        rcases List.mem_append.1 hw1 with h' | h'
        · rw [hnotB w h'] at hw2; exact absurd hw2.1 (by simp)
        · exact h'
      have hwi : w.t.val ∈ wakeInstants sv := List.mem_map.2 ⟨w, List.mem_filter.2 ⟨hwsv, hw2.2⟩, rfl⟩
      rw [List.all_eq_true]
      intro q hq
      have := h w.t.val hwi q hq
      cases hfq : isFuture T₀ q
      · simpa [hfq] using this.1 (by simp [hfq])
      · simpa [hfq] using this.2 (by simp [hfq])
  · rw [List.all_eq_true]
    constructor
    · intro h e he
      have := h e he
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this
    · intro h e he
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact h e he
  · rw [foldAll_append_vacuous _ _ _ _ _ (fun e he s => by simp only [hnotB e he, Bool.not_false, Bool.true_or]), ← hG]
    constructor
    · intro h pre e post hs
      have he : e ∈ sv := by rw [hs]; simp
      have := h pre e post hs
      simp only [hinB e he, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_eq] at this
      exact this
    · intro h pre e post hs
      have he : e ∈ sv := by rw [hs]; simp
      simp only [hinB e he, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
      exact h pre e post hs

/-- **Law 5, forwards**: an accepted resume's tail meets `reachFree`. -/
theorem reachFree_of_accepted (z : Cal.Tz) (T₀ T L : Nat) (a r t : List Log.Line)
    (hc : Log.contiguousFrom 1 (a ++ (r ++ t)) = true)
    (h : (resumeRun z T (ckptOf z T₀ L a r) (r ++ t)).isOk = true) : reachFree z T₀ L a (r ++ t) = true := by
  have hLE : ∀ x y : List Log.Line, Log.lineEntries (x ++ y) = Log.lineEntries x ++ Log.lineEntries y :=
    fun x y => List.filterMap_append
  have hd : (Log.lineEntries a ++ (Log.lineEntries r ++ Log.lineEntries t)).Pairwise (fun x y => x.line < y.line) := by
    have := (lineEntries_pairwise 1 (a ++ (r ++ t)) hc).1
    rwa [hLE, hLE] at this
  obtain ⟨run, hrun⟩ := (isOk_iff_exists _).1 h
  obtain ⟨-, -, -, hg, hfold, hhdr, -⟩ := resumeRun_ok z T _ _ run hrun
  rw [hLE r t] at hg hfold hhdr
  obtain ⟨sv, hsv⟩ : ∃ sv, sv = survivors (unsettled (ckptOf z T₀ L a r).settled
      (Log.lineEntries r ++ Log.lineEntries t)) := ⟨_, rfl⟩
  obtain ⟨kw, hkw⟩ : ∃ kw, kw = tailIndex z (ckptOf z T₀ L a r) sv := ⟨_, rfl⟩
  obtain ⟨sl, hsl⟩ : ∃ sl, sl = tailSlept z (ckptOf z T₀ L a r) kw sv := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = (ckptOf z T₀ L a r).items.length + (ckptOf z T₀ L a r).openDays.length
      + (Log.lineEntries r ++ Log.lineEntries t).length := ⟨_, rfl⟩
  rw [← hsv, ← hkw, ← hsl, ← hn] at hfold
  rw [← hsv, ← hkw] at hhdr
  have hsteps := (tailFold_snd z (dayOf z kw) sl _ sv (restore (ckptOf z T₀ L a r) n, none) hfold).2
  obtain ⟨hsurv, hI1, hI2, -⟩ := resume_index z T₀ L a.length _ _ _ (Log.lineWarnings a) n hd _ rfl sv hsv hg kw hkw
    sl hsteps
  obtain ⟨hsep, -⟩ := resume_sep z (dayOf z kw) sl (ckptOf z T₀ L a r) (restore _ n) T₀
    ((Log.lineEntries a).flatMap entryInstants) sv (ckpt_maxT z T₀ L a.length _ _ _)
    (ckpt_futureFloor z T₀ L a.length _ _ _) hsteps
  have hhb := headerCheck_none (dayOf z kw) _ _ hhdr
  have hKL : (ckptOf z T₀ L a r).ledgerDay = L := ckpt_ledgerDay' z T₀ L a.length _ _ _
  rw [hKL] at hhb
  obtain ⟨KW, hKW⟩ : ∃ KW, KW = keptWakes z (wakeInstants (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r))
      ++ wakeInstants sv) := ⟨_, rfl⟩
  obtain ⟨SL, hSL⟩ : ∃ SL, SL = Replay.KMap.get (Replay.sleptByDay z KW
      (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ sv)) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r)).foldl
      (Replay.stepWith z (dayOf z KW) SL) (State.init (Log.lineEntries a ++ (Log.lineEntries r ++ Log.lineEntries t)).length) :=
    ⟨_, rfl⟩
  rw [← hKW] at hI1 hI2
  have hGa : AgreeAbove L (horizonOf L) G (rebindState SL (restore (ckptOf z T₀ L a r) n)) := by
    rw [hG]; exact folded_part_agrees z T₀ L a.length _ _ (Log.lineWarnings a) n _ KW SL hI1
  have hcongr : ∀ pre post, sv = pre ++ post →
      pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOf z T₀ L a r) n)
        = pre.foldl (Replay.stepWith z (dayOf z KW) sl) (restore (ckptOf z T₀ L a r) n) := by
    intro pre post hs
    refine resume_fold_congr z (dayOf z kw) (dayOf z KW) sl _ _ pre
      (fun pre' e' post' h' => hsteps pre' e' (post' ++ post) (by rw [hs, h']; simp)) (fun q hq => ?_)
    exact (hI2 q (by rwa [hKL] at hq)).symm
  obtain ⟨hmach, hkeys⟩ := steps_agree z T₀ L a.length _ _ (Log.lineWarnings a) n sv KW (dayOf z kw) sl SL G hGa hI2
    hcongr
  have hsvB : ∀ e ∈ sv, e ∈ Log.lineEntries r ++ Log.lineEntries t := fun e he => by
    rw [hsv] at he; exact mem_unsettled_sub _ _ _ (Replay.mem_of_mem_survivors _ _ he)
  rw [reachFree_iff z T₀ L a r t sv hd hsurv hsvB KW hKW SL hSL G hG]
  refine ⟨hsep, fun e he => ?_, fun pre e post hs => ?_⟩
  · obtain ⟨h1, h2⟩ := hhb e he
    exact ⟨h1, by rw [hI2 _ h1]; exact h2⟩
  · have hc := stepCheck_none z (dayOf z kw) sl _ _ e (hsteps pre e post hs)
    rw [hKL] at hc
    obtain ⟨hq, -, hk⟩ := hc
    have hmm := hmach pre (e :: post) hs
    have hQ : ∀ q ∈ stepQueries (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G).machine e, headSec L ≤ q.sec := by
      rw [← hmm]; exact hq
    refine ⟨hQ, fun x hx => ?_⟩
    have hmem : x.key ∈ (Replay.effectsWith z (dayOf z KW) SL (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G) e).map
        Replay.Effect.key := List.mem_map.2 ⟨x, hx, rfl⟩
    rw [← hkeys pre e post hs hQ] at hmem
    obtain ⟨y, hy, hyk⟩ := List.mem_map.1 hmem
    rw [← hyk]; exact hk y hy

/-- **Law 5, backwards**: a tail meeting `reachFree`, past G4 and G1, is accepted. -/
theorem accepted_of_reachFree (z : Cal.Tz) (T₀ T L : Nat) (a r t : List Log.Line)
    (hc : Log.contiguousFrom 1 (a ++ (r ++ t)) = true) (hLT : L ≤ T)
    (hg : g1 (ckptOf z T₀ L a r) (unsettled (ckptOf z T₀ L a r).settled (Log.lineEntries (r ++ t))) = none)
    (hrf : reachFree z T₀ L a (r ++ t) = true) : (resumeRun z T (ckptOf z T₀ L a r) (r ++ t)).isOk = true := by
  have hLE : ∀ x y : List Log.Line, Log.lineEntries (x ++ y) = Log.lineEntries x ++ Log.lineEntries y :=
    fun x y => List.filterMap_append
  have hd : (Log.lineEntries a ++ (Log.lineEntries r ++ Log.lineEntries t)).Pairwise (fun x y => x.line < y.line) := by
    have := (lineEntries_pairwise 1 (a ++ (r ++ t)) hc).1
    rwa [hLE, hLE] at this
  have hKL : (ckptOf z T₀ L a r).ledgerDay = L := ckpt_ledgerDay' z T₀ L a.length _ _ _
  have hcut : (r ++ t).head?.all (fun l => l.n == (ckptOf z T₀ L a r).cut + 1) = true := by
    have h1 := head_of_contiguousFrom _ _ (contiguousFrom_append 1 a (r ++ t) hc)
    have hcut' : (ckptOf z T₀ L a r).cut = a.length := by simp only [ckptOf, ckptOfEntries]
    rw [hcut', Nat.add_comm a.length 1]; exact h1
  refine resumeRun_isOk_of z T _ (r ++ t) (by simp only [ckptOf, ckptOfEntries]) hcut (by rw [hKL]; exact hLT) hg ?_ ?_
  all_goals rw [hLE r t]
  all_goals rw [hLE r t] at hg
  all_goals
    obtain ⟨sv, hsv⟩ : ∃ sv, sv = survivors (unsettled (ckptOf z T₀ L a r).settled
        (Log.lineEntries r ++ Log.lineEntries t)) := ⟨_, rfl⟩
    obtain ⟨kw, hkw⟩ : ∃ kw, kw = tailIndex z (ckptOf z T₀ L a r) sv := ⟨_, rfl⟩
    obtain ⟨sl, hsl⟩ : ∃ sl, sl = tailSlept z (ckptOf z T₀ L a r) kw sv := ⟨_, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n, n = (ckptOf z T₀ L a r).items.length + (ckptOf z T₀ L a r).openDays.length
        + (Log.lineEntries r ++ Log.lineEntries t).length := ⟨_, rfl⟩
    have hsurv := resume_survivors z T₀ L a.length _ _ _ (Log.lineWarnings a) hd hg
    have hset' : (ckptOf z T₀ L a r).settled = settledOf (Log.lineEntries a) (Log.lineEntries r) :=
      ckpt_settled z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a)
    rw [← hset', ← hsv] at hsurv
    have hsvB : ∀ e ∈ sv, e ∈ Log.lineEntries r ++ Log.lineEntries t := fun e he => by
      rw [hsv] at he; exact mem_unsettled_sub _ _ _ (Replay.mem_of_mem_survivors _ _ he)
    obtain ⟨KW, hKW⟩ : ∃ KW, KW = keptWakes z (wakeInstants (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r))
        ++ wakeInstants sv) := ⟨_, rfl⟩
    obtain ⟨SL, hSL⟩ : ∃ SL, SL = Replay.KMap.get (Replay.sleptByDay z KW
        (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) ++ sv)) := ⟨_, rfl⟩
    obtain ⟨G, hG⟩ : ∃ G, G = (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r)).foldl
        (Replay.stepWith z (dayOf z KW) SL)
        (State.init (Log.lineEntries a ++ (Log.lineEntries r ++ Log.lineEntries t)).length) := ⟨_, rfl⟩
    obtain ⟨hsep, hB, hC⟩ := (reachFree_iff z T₀ L a r t sv hd hsurv hsvB KW hKW SL hSL G hG).1 hrf
    have hhead : ∀ w ∈ wakeInstants sv, headSec L ≤ w.sec := fun w hw => by
      obtain ⟨e, he, _, rfl⟩ := mem_wakeInstants hw
      exact (hB e (hsvB e he)).1
    obtain ⟨-, hI1, hI2⟩ := index_facts z T₀ L a.length _ _ _ (Log.lineWarnings a) hd _ rfl sv hsv hg kw hkw hsep hhead
    rw [← hKW] at hI1 hI2
    have hGa : AgreeAbove L (horizonOf L) G (rebindState SL (restore (ckptOf z T₀ L a r) n)) := by
      rw [hG]; exact folded_part_agrees z T₀ L a.length _ _ (Log.lineWarnings a) n _ KW SL hI1
    have hcongr := congr_of_spec z T₀ L a.length _ _ (Log.lineWarnings a) n sv KW (dayOf z kw) sl SL G hGa hI2
      (fun pre e post hs => (hC pre e post hs).1)
    obtain ⟨hmach, hkeys⟩ := steps_agree z T₀ L a.length _ _ (Log.lineWarnings a) n sv KW (dayOf z kw) sl SL G hGa
      hI2 hcongr
  · rw [← hsv, ← hkw, ← hsl, ← hn]
    apply tailFold_none_of
    intro pre e post hs
    have hmm : (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOf z T₀ L a r) n)).machine
        = (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G).machine := hmach pre (e :: post) hs
    have hkk : (Replay.effectsWith z (dayOf z kw) sl
          (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOf z T₀ L a r) n)) e).map Replay.Effect.key
        = (Replay.effectsWith z (dayOf z KW) SL (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G) e).map
            Replay.Effect.key := hkeys pre e post hs ((hC pre e post hs).1)
    apply stepCheck_eq_none
    · intro q hq
      rw [hKL]; rw [hmm] at hq; exact (hC pre e post hs).1 q hq
    · intro hw
      have hwi : e.t.val ∈ wakeInstants sv := List.mem_map.2 ⟨e, List.mem_filter.2 ⟨by rw [hs]; simp, hw⟩, rfl⟩
      refine ⟨fun m hm => ?_, fun f hf => ?_⟩
      · have hm' : maxInstant? (((Log.lineEntries a).flatMap entryInstants).filter (fun q => !isFuture T₀ q)) = some m := by
          rw [← ckpt_maxT z T₀ L a.length _ _ (Log.lineWarnings a)]; exact hm
        obtain ⟨hmQA, hmP⟩ := List.mem_filter.1 (maxInstant?_mem _ m hm')
        exact (hsep e.t.val hwi m hmQA).1 hmP
      · have hf' : minInstant? (((Log.lineEntries a).flatMap entryInstants).filter (isFuture T₀)) = some f := by
          rw [← ckpt_futureFloor z T₀ L a.length _ _ (Log.lineWarnings a)]; exact hf
        obtain ⟨hfQA, hfP⟩ := List.mem_filter.1 (minInstant?_mem _ f hf')
        exact (hsep e.t.val hwi f hfQA).2 (by simp [hfP])
    · intro x hx
      rw [hKL]
      have hmem : x.key ∈ (Replay.effectsWith z (dayOf z kw) sl
          (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOf z T₀ L a r) n)) e).map Replay.Effect.key :=
        List.mem_map.2 ⟨x, hx, rfl⟩
      rw [hkk] at hmem
      obtain ⟨y, hy, hyk⟩ := List.mem_map.1 hmem
      rw [← hyk]; exact (hC pre e post hs).2 y hy
  · rw [← hsv, ← hkw]
    apply headerCheck_none_of
    intro e he
    rw [hKL]
    obtain ⟨h1, h2⟩ := hB e he
    exact ⟨h1, by rw [← hI2 _ h1]; exact h2⟩

/-- **Law 5, both directions** (§5.8): acceptance is exactly `L ≤ T`, `reachFree` and `tagsClear`. -/
theorem resume_ok_iff (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line) (term : Bool) (p : Option Seal.Policy)
    (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b) (_hs : Seal.sealable z T₀ L a r = true) :
    (Seal.resume z T (Seal.ckptOf z T₀ L a r) b term p).isOk
      = (decide (L ≤ T) && Seal.reachFree z T₀ L a b && Seal.tagsClear z T₀ L a r b) := by
  obtain ⟨t, rfl⟩ := hr
  rw [resume_isOk_eq]
  have hKL : (ckptOf z T₀ L a r).ledgerDay = L := ckpt_ledgerDay' z T₀ L a.length _ _ _
  by_cases hLT : L ≤ T
  · rw [decide_eq_true hLT, Bool.true_and]
    by_cases htc : tagsClear z T₀ L a r (r ++ t) = true
    · rw [htc, Bool.and_true]
      have hg := (tagsClear_iff z T₀ L a r (r ++ t)).1 htc
      exact Bool.eq_iff_iff.2 ⟨reachFree_of_accepted z T₀ T L a r t hc, accepted_of_reachFree z T₀ T L a r t hc hLT hg⟩
    · rw [Bool.eq_false_iff.2 htc, Bool.and_false]
      cases hx : (resumeRun z T (ckptOf z T₀ L a r) (r ++ t)).isOk
      · rfl
      · obtain ⟨run, hrun⟩ := (isOk_iff_exists _).1 hx
        obtain ⟨-, -, -, hg, -⟩ := resumeRun_ok z T _ _ run hrun
        exact absurd ((tagsClear_iff z T₀ L a r (r ++ t)).2 hg) htc
  · rw [decide_eq_false hLT, Bool.false_and, Bool.false_and]
    cases hx : (resumeRun z T (ckptOf z T₀ L a r) (r ++ t)).isOk
    · rfl
    · obtain ⟨run, hrun⟩ := (isOk_iff_exists _).1 hx
      obtain ⟨-, -, hT, -⟩ := resumeRun_ok z T _ _ run hrun
      exact absurd (hKL ▸ hT) hLT

end Seal
end Tm
