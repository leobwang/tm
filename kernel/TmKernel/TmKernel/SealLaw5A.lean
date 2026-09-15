import TmKernel.SealLaw2D
/-!
# SealLaw5A — law 5's route: acceptance both ways, and the resume's steps against the whole log's (stage 5, D9, W2)

The resume's checks read its own state and index; the whole log's conditions (`reachFree`) read the replay's.  Under
G1, the stored index agrees with the whole log's at or after the head second, so once every step reads the index
there, the two folds step alike: their machines agree before every step and their effects name the same keys
(`steps_agree`).  "Every step reads the index there" can be had from either side: from the resume's head checks
(`resume_fold_congr`) or from the whole log's (`congr_of_spec`).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Effect HMap survivors wakeInstants keptWakes dayOf isWake)
open Log (Entry)

/-! ## Acceptance, both ways -/

theorem contiguousFrom_append (k : Nat) : ∀ (a b : List Log.Line), Log.contiguousFrom k (a ++ b) = true →
    Log.contiguousFrom (k + a.length) b = true
  | [], b, h => by simpa using h
  | l :: a, b, h => by
    simp only [List.cons_append, Log.contiguousFrom, Bool.and_eq_true] at h
    have := contiguousFrom_append (k + 1) a b h.2
    rwa [List.length_cons, show k + (a.length + 1) = k + 1 + a.length by omega]

theorem head_of_contiguousFrom (k : Nat) (b : List Log.Line) (h : Log.contiguousFrom k b = true) :
    b.head?.all (fun l => l.n == k) = true := by
  cases b with
  | nil => rfl
  | cons l b =>
    simp only [Log.contiguousFrom, Bool.and_eq_true] at h
    simpa using h.1

theorem stepCheck_eq_none (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt) (st : State)
    (e : Entry)
    (h1 : ∀ q ∈ stepQueries st.machine e, headSec K.ledgerDay ≤ q.sec)
    (h2 : isWake e = true → (∀ m, K.maxT = some m → m < e.t.val) ∧
      (∀ f, K.futureFloor = some f → e.t.val.sec + fenceSec < f.sec))
    (h3 : ∀ x ∈ Replay.effectsWith z dy sl st e, keyAtOrAbove K.ledgerDay (horizonOf K.ledgerDay) x.key = true) :
    (stepCheck z dy sl K st e).2 = none := by
  have e1 : (stepQueries st.machine e).find? (fun q => decide (q.sec < headSec K.ledgerDay)) = none :=
    List.find?_eq_none.2 (fun q hq => by have := h1 q hq; simp; omega)
  have e3 : (Replay.effectsWith z dy sl st e).find?
      (fun x => !keyAtOrAbove K.ledgerDay (horizonOf K.ledgerDay) x.key) = none :=
    List.find?_eq_none.2 (fun x hx => by simp [h3 x hx])
  have e2 : (if isWake e && !(K.maxT.all (· < e.t.val) &&
      K.futureFloor.all (fun f => decide (e.t.val.sec + fenceSec < f.sec)))
      then some (Refusal.wakeBehindCut e.line e.t.val) else none) = none := by
    cases hw : isWake e
    · simp
    · obtain ⟨hm, hf⟩ := h2 hw
      have am : K.maxT.all (· < e.t.val) = true := by
        cases hmx : K.maxT with
        | none => rfl
        | some m => simpa using hm m hmx
      have af : K.futureFloor.all (fun f => decide (e.t.val.sec + fenceSec < f.sec)) = true := by
        cases hfx : K.futureFloor with
        | none => rfl
        | some f => simpa using hf f hfx
      simp [am, af]
  simp only [stepCheck, e1, e2, e3, Option.map_none]
  rfl

theorem tailFold_none_of (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt) (st : State)
    (sv : List Entry)
    (h : ∀ pre e post, sv = pre ++ e :: post →
      (stepCheck z dy sl K (pre.foldl (Replay.stepWith z dy sl) st) e).2 = none) :
    (tailFold z dy sl K st sv).2 = none := by
  unfold tailFold
  suffices H : ∀ (l pre : List Entry) (acc : State × Option Refusal), sv = pre ++ l →
      acc.1 = pre.foldl (Replay.stepWith z dy sl) st → acc.2 = none →
      (l.foldl (tailFoldStep z dy sl K) acc).2 = none from H sv [] (st, none) rfl rfl rfl
  intro l
  induction l with
  | nil => intro pre acc _ _ h2; exact h2
  | cons e l ih =>
    intro pre acc hs h1 h2
    rw [List.foldl_cons]
    refine ih (pre ++ [e]) _ (by rw [hs]; simp) ?_ ?_
    · show Replay.applyEffects acc.1 (stepCheck z dy sl K acc.1 e).1 = (pre ++ [e]).foldl (Replay.stepWith z dy sl) st
      rw [List.foldl_append, ← h1]
      rfl
    · show (acc.2 <|> (stepCheck z dy sl K acc.1 e).2) = none
      rw [h2, h1, h pre e l hs]
      rfl

theorem headerCheck_none_of (dy : Cal.Instant → Nat) (K : Ckpt) (bs : List Entry)
    (h : ∀ e ∈ bs, headSec K.ledgerDay ≤ e.t.val.sec ∧ K.ledgerDay ≤ dy e.t.val) : headerCheck dy K bs = none := by
  unfold headerCheck
  rw [List.findSome?_eq_none_iff]
  intro e he
  obtain ⟨h1, h2⟩ := h e he
  rw [if_neg (by omega), if_neg (by omega)]

theorem resumeRun_isOk_of (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line)
    (hz : K.tzKey = z.val.key) (hcut : b.head?.all (fun l => l.n == K.cut + 1) = true) (hT : K.ledgerDay ≤ T)
    (hg : g1 K (unsettled K.settled (Log.lineEntries b)) = none)
    (hf : (tailFold z (dayOf z (tailIndex z K (survivors (unsettled K.settled (Log.lineEntries b)))))
        (tailSlept z K (tailIndex z K (survivors (unsettled K.settled (Log.lineEntries b))))
          (survivors (unsettled K.settled (Log.lineEntries b)))) K
        (restore K (K.items.length + K.openDays.length + (Log.lineEntries b).length))
        (survivors (unsettled K.settled (Log.lineEntries b)))).2 = none)
    (hh : headerCheck (dayOf z (tailIndex z K (survivors (unsettled K.settled (Log.lineEntries b))))) K
      (Log.lineEntries b) = none) :
    (resumeRun z T K b).isOk = true := by
  unfold resumeRun
  rw [if_neg (by simp [hz]), if_neg (by simp [hcut]), if_neg (by omega)]
  dsimp only
  rw [hg]
  dsimp only
  rw [hf, hh]
  rfl

/-! ## The index, from the whole log's conditions -/

/-- **The index facts from the separation and the head**, with no reference to the resume's checks. -/
theorem index_facts (z : Cal.Tz) (T₀ L cut : Nat) (As Rs B' : List Entry) (ws : List (Nat × Log.LWarn))
    (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (K : Ckpt) (hK : K = ckptOfEntries z T₀ L cut As Rs ws)
    (sv : List Entry) (hsv : sv = survivors (unsettled K.settled (Rs ++ B')))
    (hg : g1 K (unsettled K.settled (Rs ++ B')) = none)
    (kw : List Cal.Instant) (hkw : kw = tailIndex z K sv)
    (hsep : ∀ w ∈ wakeInstants sv, ∀ q ∈ As.flatMap entryInstants, ((fun q => !isFuture T₀ q) q = true → q < w) ∧
      ((fun q => !isFuture T₀ q) q = false → w.sec + fenceSec < q.sec))
    (hhead : ∀ w ∈ wakeInstants sv, headSec L ≤ w.sec) :
    survivors (As ++ (Rs ++ B')) = foldedSurvivors As Rs ++ sv ∧
    (∀ q ∈ As.flatMap entryInstants,
      dayOf z (keptWakes z (wakeInstants (foldedSurvivors As Rs) ++ wakeInstants sv)) q = dayOf z (foldedIndex z As Rs) q) ∧
    (∀ q, headSec L ≤ q.sec →
      dayOf z (keptWakes z (wakeInstants (foldedSurvivors As Rs) ++ wakeInstants sv)) q = dayOf z kw q) := by
  subst hK
  have hsurv := resume_survivors z T₀ L cut As Rs B' ws hd hg
  rw [← ckpt_settled z T₀ L cut As Rs ws, ← hsv] at hsurv
  have hWA : ∀ w ∈ wakeInstants (foldedSurvivors As Rs), w ∈ As.flatMap entryInstants := by
    intro w hw
    obtain ⟨e, he, _, rfl⟩ := mem_wakeInstants hw
    exact List.mem_flatMap.2 ⟨e, (foldedSurvivors_sublist As Rs).subset he, by simp [entryInstants]⟩
  have hns : ∀ q ∈ As.flatMap entryInstants ++ wakeInstants sv, q.ns < 2000000000 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨e, _, hqe⟩ := List.mem_flatMap.1 hq
      exact entryInstants_ns e q hqe
    · obtain ⟨e, _, _, rfl⟩ := mem_wakeInstants hq
      exact ns_lt_of_wf _ e.t.property
  refine ⟨hsurv, fun q hq => dayOf_folded_agrees z _ _ _ _ hWA hns hsep q hq, fun q hq => ?_⟩
  rw [hkw]
  unfold tailIndex
  rw [ckpt_wakes]
  exact dayOf_tail_agrees z L _ _ _ _ hWA hsep hhead q hq

/-- **The folded part of the whole log's fold agrees with the restored state**, rebound to any `slept_by_day`. -/
theorem folded_part_agrees (z : Cal.Tz) (T₀ L cut : Nat) (As Rs : List Entry) (ws : List (Nat × Log.LWarn)) (n N : Nat)
    (KW : List Cal.Instant) (SL : Nat → Option Nat)
    (hI1 : ∀ q ∈ As.flatMap entryInstants, dayOf z KW q = dayOf z (foldedIndex z As Rs) q) :
    AgreeAbove L (horizonOf L) ((foldedSurvivors As Rs).foldl (Replay.stepWith z (dayOf z KW) SL) (State.init N))
      (rebindState SL (restore (ckptOfEntries z T₀ L cut As Rs ws) n)) := by
  have hq1 : ∀ q ∈ foldQueries z (dayOf z KW) SL (State.init N) (foldedSurvivors As Rs),
      dayOf z KW q = dayOf z (foldedIndex z As Rs) q := by
    intro q hq
    rcases foldQueries_sub z _ _ _ _ q hq with h | h
    · simp [machineInstants, blockSince, blockPaused, State.init] at h
    · obtain ⟨e, he, hqe⟩ := List.mem_flatMap.1 h
      exact hI1 q (List.mem_flatMap.2 ⟨e, (foldedSurvivors_sublist As Rs).subset he, hqe⟩)
  have hGX : (foldedSurvivors As Rs).foldl (Replay.stepWith z (dayOf z KW) SL) (State.init N)
      = rebindState SL ((foldedSurvivors As Rs).foldl (Replay.stepWith z (dayOf z (foldedIndex z As Rs))
          (Replay.KMap.get (Replay.sleptByDay z (foldedIndex z As Rs) (foldedSurvivors As Rs)))) (State.init N)) := by
    rw [foldl_stepWith_congr z _ _ SL _ _ hq1]
    have := foldl_rebind z (dayOf z (foldedIndex z As Rs)) SL
      (Replay.KMap.get (Replay.sleptByDay z (foldedIndex z As Rs) (foldedSurvivors As Rs))) (foldedSurvivors As Rs)
      (State.init N) (pendingStart_init _)
    rwa [rebindState_init] at this
  have hXa : AgreeAbove L (horizonOf L) ((foldedSurvivors As Rs).foldl (Replay.stepWith z (dayOf z (foldedIndex z As Rs))
      (Replay.KMap.get (Replay.sleptByDay z (foldedIndex z As Rs) (foldedSurvivors As Rs)))) (State.init N))
      (foldedState z As Rs) := by
    rw [foldedState_eq]
    exact AgreeAbove.foldl z _ _ _ (AgreeAbove.of_sameReadings (Replay.sameReadings_init _ _))
  rw [hGX]
  exact AgreeAbove.rebind (hXa.trans (restore_agrees z T₀ L cut As Rs ws n).symm) SL SL (fun _ _ => rfl)

/-! ## The two folds, step by step -/

/-- **Once every prefix of the tail folds alike on the two indexes, the resume's steps and the whole log's agree**:
machines before every step, and the keys a step's effects name. -/
theorem steps_agree (z : Cal.Tz) (T₀ L cut : Nat) (As Rs : List Entry) (ws : List (Nat × Log.LWarn)) (n : Nat)
    (sv : List Entry) (KW : List Cal.Instant) (dy : Cal.Instant → Nat) (sl SL : Nat → Option Nat) (G : State)
    (hG : AgreeAbove L (horizonOf L) G (rebindState SL (restore (ckptOfEntries z T₀ L cut As Rs ws) n)))
    (hI2 : ∀ q, headSec L ≤ q.sec → dayOf z KW q = dy q)
    (hcongr : ∀ pre post, sv = pre ++ post →
      pre.foldl (Replay.stepWith z dy sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n)
        = pre.foldl (Replay.stepWith z (dayOf z KW) sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n)) :
    (∀ pre post, sv = pre ++ post →
      (pre.foldl (Replay.stepWith z dy sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n)).machine
        = (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G).machine) ∧
    (∀ pre e post, sv = pre ++ e :: post →
      (∀ q ∈ stepQueries (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G).machine e, headSec L ≤ q.sec) →
      (Replay.effectsWith z dy sl (pre.foldl (Replay.stepWith z dy sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n))
          e).map Replay.Effect.key
        = (Replay.effectsWith z (dayOf z KW) SL (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G) e).map
            Replay.Effect.key) := by
  have hPS := pendingStart_restore z T₀ L cut As Rs ws n
  have hm : ∀ pre post, sv = pre ++ post →
      (pre.foldl (Replay.stepWith z dy sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n)).machine
        = (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G).machine := by
    intro pre post hs
    have e1 := (AgreeAbove.foldl z (dayOf z KW) SL pre hG).machine
    rw [foldl_rebind z (dayOf z KW) SL sl pre _ hPS] at e1
    rw [e1, hcongr pre post hs]
    rfl
  refine ⟨hm, fun pre e post hs hq => ?_⟩
  have hmm := hm pre (e :: post) hs
  rw [← effectsWith_machine z (dayOf z KW) SL _ _ e hmm,
    effectsWith_keys z (dayOf z KW) sl SL _ e (pendingStart_foldl z _ _ pre _ hPS),
    effectsWith_congr (dayOf z KW) dy z sl _ e (fun q hq' => hI2 q (hq q (by rw [← hmm]; exact hq')))]

/-- **The prefixes fold alike when the whole log's steps read the index at or after the head second.** -/
theorem congr_of_spec (z : Cal.Tz) (T₀ L cut : Nat) (As Rs : List Entry) (ws : List (Nat × Log.LWarn)) (n : Nat)
    (sv : List Entry) (KW : List Cal.Instant) (dy : Cal.Instant → Nat) (sl SL : Nat → Option Nat) (G : State)
    (hG : AgreeAbove L (horizonOf L) G (rebindState SL (restore (ckptOfEntries z T₀ L cut As Rs ws) n)))
    (hI2 : ∀ q, headSec L ≤ q.sec → dayOf z KW q = dy q)
    (hQ : ∀ pre e post, sv = pre ++ e :: post →
      ∀ q ∈ stepQueries (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G).machine e, headSec L ≤ q.sec) :
    ∀ pre post, sv = pre ++ post →
      pre.foldl (Replay.stepWith z dy sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n)
        = pre.foldl (Replay.stepWith z (dayOf z KW) sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n) := by
  have hPS := pendingStart_restore z T₀ L cut As Rs ws n
  intro pre post hs
  refine (foldl_stepWith_congr z (dayOf z KW) dy sl pre _ (fun q hq => ?_)).symm
  obtain ⟨pre', e', post', hs', hq'⟩ := mem_foldQueries z (dayOf z KW) sl pre _ q hq
  have e1 := (AgreeAbove.foldl z (dayOf z KW) SL pre' hG).machine
  rw [foldl_rebind z (dayOf z KW) SL sl pre' _ hPS] at e1
  have hmach : (pre'.foldl (Replay.stepWith z (dayOf z KW) sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n)).machine
      = (pre'.foldl (Replay.stepWith z (dayOf z KW) SL) G).machine := by
    rw [e1]; rfl
  rw [hmach] at hq'
  exact hI2 q (hQ pre' e' (post' ++ post) (by rw [hs, hs']; simp) q hq')

theorem maxInstant?_mem (l : List Cal.Instant) (m : Cal.Instant) (h : maxInstant? l = some m) : m ∈ l := by
  unfold maxInstant? at h
  suffices H : ∀ (l : List Cal.Instant) (acc : Option Cal.Instant),
      l.foldl (fun acc t => some (match acc with | none => t | some a => if a < t then t else a)) acc = some m →
        m ∈ l ∨ acc = some m from (H l none h).resolve_right (by simp)
  intro l
  induction l with
  | nil => intro acc h; exact Or.inr h
  | cons t l ih =>
    intro acc h
    rw [List.foldl_cons] at h
    rcases ih _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · cases acc with
      | none => simp only [Option.some.injEq] at h; exact Or.inl (h ▸ List.mem_cons_self)
      | some a =>
        simp only [Option.some.injEq] at h
        split at h
        · exact Or.inl (h ▸ List.mem_cons_self)
        · exact Or.inr (by rw [h])

theorem minInstant?_mem (l : List Cal.Instant) (f : Cal.Instant) (h : minInstant? l = some f) : f ∈ l := by
  unfold minInstant? at h
  suffices H : ∀ (l : List Cal.Instant) (acc : Option Cal.Instant),
      l.foldl (fun acc t => some (match acc with | none => t | some a => if t < a then t else a)) acc = some f →
        f ∈ l ∨ acc = some f from (H l none h).resolve_right (by simp)
  intro l
  induction l with
  | nil => intro acc h; exact Or.inr h
  | cons t l ih =>
    intro acc h
    rw [List.foldl_cons] at h
    rcases ih _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · cases acc with
      | none => simp only [Option.some.injEq] at h; exact Or.inl (h ▸ List.mem_cons_self)
      | some a =>
        simp only [Option.some.injEq] at h
        split at h
        · exact Or.inl (h ▸ List.mem_cons_self)
        · exact Or.inr (by rw [h])

end Seal
end Tm
