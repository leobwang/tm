import TmKernel.SealLaw9B
/-!
# SealLaw9 — law 9: chunking and exact pops are invisible (stage 5, D9, W2)

Design §9.5's law 9 and §9.7.  Genesis' loop keeps law 9's invariant on every stack entry (`genLoop_ok`): a call pushes
an entry meeting it or keeps the stack, and a pop keeps a suffix.  The last call reads every line, so its answer is the
answer of the whole log's checkpoint at its ledger day, and the records genesis returns are the whole log's below that
checkpoint's horizons, with any extra at or above them; by law 1's partition the merged reading is the replay's
(`chunked_genesis_is_one_replay`).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

/-- **Genesis' loop keeps law 9's invariant.** -/
theorem genLoop_ok (z : Cal.Tz) (T : Nat) (ls : List Log.Line) (terminated : Bool) (p : Policy)
    (hc : Log.contiguousFrom 1 ls = true) :
    ∀ (fuel : Nat) (stack : List GenEntry) (ends : List Nat) (last : Option Seal.Answer)
      (res : List GenEntry × Seal.Answer),
      genLoop z T ls terminated p fuel stack ends last = .ok res →
      (∀ E ∈ stack, GenOk z T ls E) →
      (∀ E ∈ stack, ∀ e ∈ ends, E.known ≤ e) →
      ends.Pairwise (· ≤ ·) → (∀ e ∈ ends, e ≤ ls.length) →
      (ends ≠ [] → ends.getLast? = some ls.length) →
      (∀ v, last = some v → ∃ E rest e0, stack = E :: rest ∧ ResultOk z T ls e0 E v ∧ (ends = [] → e0 = ls.length)) →
      ∃ E rest, res.1 = E :: rest ∧ ResultOk z T ls ls.length E res.2
  | 0, _, _, _, _, h, _, _, _, _, _, _ => by simp [genLoop] at h
  | fuel + 1, stack, [], some v, res, h, _, _, _, _, _, hlast => by
    simp only [genLoop, Except.ok.injEq] at h
    subst h
    obtain ⟨E, rest, e0, hst, hres, he0⟩ := hlast v rfl
    exact ⟨E, rest, hst, by rw [← he0 rfl]; exact hres⟩
  | fuel + 1, stack, [], none, res, h, _, _, _, _, _, _ => by simp [genLoop] at h
  | fuel + 1, [], _ :: _, _, res, h, _, _, _, _, _, _ => by simp [genLoop] at h
  | fuel + 1, E :: rest, e :: ends, last, res, h, hok, hkn, hpw, hle, hlst, _ => by
    have hE := hok E List.mem_cons_self
    have hke := hkn E List.mem_cons_self e List.mem_cons_self
    have hel := hle e List.mem_cons_self
    have hge : ∀ e' ∈ ends, e ≤ e' := (List.pairwise_cons.1 hpw).1
    have hpw' := (List.pairwise_cons.1 hpw).2
    have hle' : ∀ e' ∈ ends, e' ≤ ls.length := fun e' he' => hle e' (List.mem_cons_of_mem _ he')
    have hlst' : ends ≠ [] → ends.getLast? = some ls.length := fun hne => by
      have := hlst (List.cons_ne_nil _ _)
      rw [List.getLast?_cons] at this
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (List.getLast?_isSome.2 hne)
      rw [hy] at this ⊢
      simpa using this
    have hlast0 : ends = [] → e = ls.length := fun he => by
      have := hlst (List.cons_ne_nil _ _)
      rw [he] at this
      simpa using this
    simp only [genLoop] at h
    split at h
    · rename_i v heq
      have hres := (genesis_call z T ls p hc E hE e hke hel _ v none heq).1 rfl
      exact genLoop_ok z T ls terminated p hc fuel (E :: rest) ends (some v) res h hok
        (fun E' hE' e' he' => Nat.le_trans (hkn E' hE' e List.mem_cons_self) (hge e' he')) hpw' hle' hlst'
        (fun v' hv' => by
          cases hv'
          exact ⟨E, rest, e, rfl, hres, hlast0⟩)
    · rename_i v s heq
      obtain ⟨hNok, hNres⟩ := (genesis_call z T ls p hc E hE e hke hel _ v (some s) heq).2 s rfl
      refine genLoop_ok z T ls terminated p hc fuel _ ends (some v) res h (fun E' hE' => ?_)
        (fun E' hE' e' he' => ?_) hpw' hle' hlst' (fun v' hv' => ?_)
      · rcases List.mem_cons.1 hE' with rfl | hE'
        · exact hNok
        · exact hok E' hE'
      · rcases List.mem_cons.1 hE' with rfl | hE'
        · exact hge e' he'
        · exact Nat.le_trans (hkn E' hE' e List.mem_cons_self) (hge e' he')
      · cases hv'
        exact ⟨_, _, e, rfl, hNres, hlast0⟩
    · rename_i r heq
      split at h
      · exact genLoop_ok z T ls terminated p hc fuel (popTo r rest) (e :: ends) none res h
          (fun E' hE' => hok E' (List.mem_cons_of_mem _ (popTo_sub r rest E' hE')))
          (fun E' hE' => hkn E' (List.mem_cons_of_mem _ (popTo_sub r rest E' hE'))) hpw hle hlst
          (fun v' hv' => by cases hv')
      · cases h

theorem genEnds_spec (chunks : List (List Log.Line)) :
    (genEnds chunks).Pairwise (· ≤ ·) ∧ (∀ e ∈ genEnds chunks, e ≤ chunks.flatten.length) ∧
      (genEnds chunks ≠ [] → (genEnds chunks).getLast? = some chunks.flatten.length) := by
  obtain ⟨h1, h2, h3, h4⟩ := endsFrom_spec 0 chunks
  unfold genEnds chunkEnds
  cases hce : endsFrom 0 chunks with
  | nil =>
    have hcs : chunks = [] := h4.1 hce
    subst hcs
    simp
  | cons a l =>
    have hcs : chunks ≠ [] := fun hn => by rw [hn] at hce; simp [endsFrom] at hce
    rw [hce] at h1 h2 h3
    dsimp only
    exact ⟨h1, fun e he => by have := h2 e he; omega, fun _ => by rw [h3 hcs, Nat.zero_add]⟩

/-- **Law 9** (§9.5, §15): chunking and exact pops are invisible. -/
theorem chunked_genesis_is_one_replay (z : Cal.Tz) (T : Nat) (chunks : List (List Log.Line)) (term : Bool)
    (p : Seal.Policy) (ds : List Seal.DayRecord) (ws : List Seal.WindowRecord) (v : Seal.Answer)
    (hc : Log.contiguousFrom 1 chunks.flatten = true)
    (h : Seal.genesis z T chunks term p = .ok (ds, ws, v)) (q : Seal.Q) :
    Seal.askMerged ds ws v q = Replay.ask (Seal.replayLines z chunks.flatten) q := by
  obtain ⟨hpw, hle, hlst⟩ := genEnds_spec chunks
  unfold genesis genesisOver at h
  generalize genEnds chunks = ends at h hpw hle hlst
  cases hl : genLoop z T chunks.flatten term p (2 * ends.length + 2) [⟨Ckpt.empty z, [], [], 0⟩] ends none with
  | error r => rw [hl] at h; simp at h
  | ok res =>
    obtain ⟨E', rest', hst, hres⟩ := genLoop_ok z T chunks.flatten term p hc _ _ ends none res hl
      (fun E hE => by
        rw [List.mem_singleton] at hE
        subst hE
        exact genOk_empty z T chunks.flatten)
      (fun E hE e _ => by
        rw [List.mem_singleton] at hE
        subst hE
        exact Nat.zero_le e)
      hpw hle hlst (fun v'' hv'' => by cases hv'')
    obtain ⟨stack, v'⟩ := res
    simp only at hst hres
    subst hst
    rw [hl] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨T₀, L, X, W, hv, hD, hX, hW, hWx⟩ := hres
    rw [List.take_length] at hv hD hW
    rw [hD, hW, hv, askMerged_extra _ X _ W _ q (fun r hr => hX r hr) (fun w hw => hWx w hw)]
    exact partition_is_the_replay z T₀ L chunks.flatten q

end Seal
end Tm
