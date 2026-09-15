import TmKernel.SealLaw2D
/-!
# SealLaw2F — law 2 through the disk, and law 8 (stage 5, D9, W2)

`resume_is_replay` reads the checkpoint back through `emitCkpt`, `jemit`, `jparse` and `readCkpt` as rewrites
(`jparse_jemit`, `readCkptFields_emit`), never evaluated (§14.0 item 4), then applies law 2 in memory
(`resume_answer_eq`).  Law 8 is law 2 from the checkpoint of nothing with law 1.  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Log (Entry)

theorem resume_ok_answer {z : Cal.Tz} {T : Nat} {k : Ckpt} {b : List Log.Line} {term : Bool} {p : Option Policy}
    {v : Seal.Answer} {x : Option Resealed} (h : resume z T k b term p = .ok (v, x)) :
    ∃ run, resumeRun z T k b = .ok run ∧ run.answer = v := by
  unfold resume at h
  cases hr : resumeRun z T k b with
  | error e => rw [hr] at h; simp at h
  | ok run =>
    rw [hr] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨run, rfl, h.1⟩

/-- **A checkpoint read back from its own emission is itself** (whatever `readCkpt` accepts). -/
theorem readCkpt_emitCkpt_eq (K k : Ckpt) (h : readCkpt (emitCkpt K) = .ok k) : k = K := by
  unfold readCkpt emitCkpt at h
  dsimp only at h
  rw [readCkptFields_emit] at h
  dsimp only at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h; exact h.symm

/-- **Law 2, two-run, through the disk** (AGENTS §5.9): resuming the stored checkpoint of `a` over `b` answers as the
checkpoint of `a ++ b`. -/
theorem resume_is_replay (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line) (term : Bool)
    (j : JVal) (k : Seal.Ckpt) (v : Seal.Answer)
    (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b) (_hs : Seal.sealable z T₀ L a r = true)
    (hwire : jparse (jemit (Seal.emitCkpt (Seal.ckptOf z T₀ L a r))) = .ok j)
    (hk : Seal.readCkpt j = .ok k)
    (h : Seal.resume z T k b term none = .ok (v, none)) :
    v = Seal.answer (Seal.ckptOf z T₀ L (a ++ b) []) := by
  rw [jparse_jemit] at hwire
  cases hwire
  have hkK := readCkpt_emitCkpt_eq _ _ hk
  subst hkK
  obtain ⟨run, hrun, rfl⟩ := resume_ok_answer h
  exact resume_answer_eq z T₀ T L a r b run hc hr hrun

/-- **Law 8, one code path**: a resume from the empty checkpoint is the replay. -/
theorem resume_from_empty_is_replay (z : Cal.Tz) (T : Nat) (ls : List Log.Line) (term : Bool) (v : Seal.Answer)
    (hc : Log.contiguousFrom 1 ls = true) (h : Seal.resume z T (Seal.Ckpt.empty z) ls term none = .ok (v, none))
    (q : Seal.Q) :
    Seal.askMerged [] [] v q = Replay.ask (Seal.replayLines z ls) q := by
  obtain ⟨run, hrun, rfl⟩ := resume_ok_answer h
  have hE : Ckpt.empty z = ckptOf z 0 0 [] [] := (the_checkpoint_of_nothing_is_the_empty_checkpoint z).symm
  rw [hE] at hrun
  have hv := resume_answer_eq z 0 T 0 [] [] ls run (by simpa using hc) List.nil_prefix hrun
  rw [List.nil_append] at hv
  rw [hv]
  have h0 : horizonOf 0 = 0 := Nat.le_zero.1 (horizonOf_le 0)
  have hq : q.atOrAbove 0 (horizonOf 0) = true := by
    rw [h0]; cases q <;> simp [Q.atOrAbove]
  unfold askMerged
  simp only [answer_reads_the_replay z 0 0 ls q hq]

end Seal
end Tm
