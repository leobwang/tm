import TmKernel.Planner
import TmKernel.SealLaw2E
import TmKernel.SealLaw2F
/-!
# TodayWhole — the planner's day record on a resumed run is the whole log's (stage 6, W-45 track Q, README gap 3583)

The planner request R3 sends from `tm plan`, `tm now` and the TUI carries ONE `log` section, and the planner reads
today's day record off that section's run (`Planner.PlanReq.todayRecord`, D24's seam).  The host builds the section
from the process checkpoint and the tail since its cut whenever it can (`kernel_log::capacity_log_section`), so the
record the planner reads is a RESUMED run's — and README gap 3583 asked whether a tail could leave today's record
partial: plan from `now` because the day's first `arrive` was before the cut, say.

It cannot, and this module says why in the kernel's own terms, as one law over the planner's own reading:

* `PlanReq.todayRecord_is_the_answers_reading` — the planner's day record IS the run answer's `.day today .record`
  reading (`Seal.askAnswer`), wherever that answer reads today at all;
* `PlanReq.todayRecord_on_a_resumed_run_is_the_whole_logs` — on a run that resumed the stored checkpoint of the
  lines `a` over the tail `b` (the hypotheses of `Seal.resume_is_replay`, law 2 through the disk), the planner's day
  record for the request's day is the whole log's replay's, `Replay.ask` over `a ++ b`: the accepted resume covers
  the request's day (`Seal.an_accepted_resume_covers_now`), and the answer reads the replay at and above its ledger
  day (`Seal.answer_reads_the_replay`, law 1).

No event is named: the arrival, the wake, the breaks, the segments and every other field of the record are read
off the one record the law equates.  What the host owes beside it — never to send a checkpoint whose ledger day is
after today, and never a tail the kernel refuses — is `kernel_log::resume_section_from`'s, and
`tm/tests/kernel_request_today_whole.rs` holds the host to both through the FFI.
-/
namespace Tm
namespace Planner

/-- **The planner's day record is the run answer's reading of today**, wherever the answer reads today at all — its
ledger day at or below the request's day.  Below it, the day is a sealed record's and the answer reads nothing
(`Seal.askAnswer` answers `none`). -/
theorem PlanReq.todayRecord_is_the_answers_reading (r : PlanReq) (h : r.run.answer.ledgerDay ≤ r.today) :
    Seal.askAnswer r.run.answer (.day r.today .record) = some (.dayRecord r.todayRecord) := by
  dsimp only [Seal.askAnswer]
  rw [if_neg (Nat.not_lt.mpr h)]
  rfl

/-- **README gap 3583, as a law over the planner's reading**: a planner request whose run is the resume of the stored
checkpoint of `a` over the tail `b` — at the request's own day `T`, as the `log` section of the request the host
builds is — reads today's record exactly as the whole log's replay reads it. -/
theorem PlanReq.todayRecord_on_a_resumed_run_is_the_whole_logs (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line)
    (term : Bool) (j : JVal) (k : Seal.Ckpt) (v : Seal.Answer)
    (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b) (hs : Seal.sealable z T₀ L a r = true)
    (hwire : jparse (jemit (Seal.emitCkpt (Seal.ckptOf z T₀ L a r))) = .ok j)
    (hk : Seal.readCkpt j = .ok k)
    (h : Seal.resume z T k b term none = .ok (v, none))
    (req : PlanReq) (hrun : req.run.answer = v) (hday : req.today = T) :
    Replay.ask (Seal.replayLines z (a ++ b)) (.day req.today .record) = .dayRecord req.todayRecord := by
  have hv := Seal.resume_is_replay z T₀ T L a r b term j k v hc hr hs hwire hk h
  have hkL : k.ledgerDay = L := by
    rw [jparse_jemit] at hwire
    cases hwire
    rw [Seal.readCkpt_emitCkpt_eq _ _ hk]
    rfl
  have hLT : L ≤ T := hkL ▸ (Seal.an_accepted_resume_covers_now z T k b term none (v, none) h).1
  have hvL : v.ledgerDay = L := by
    rw [hv, Seal.ckptOf_nil]
    exact Seal.answer_ledgerDay z T₀ L _ _ _ _
  have hq : Seal.Q.atOrAbove (Replay.Q.day T .record) L (Seal.horizonOf L) = true := by
    show decide (L ≤ T) = true
    exact decide_eq_true hLT
  have hread := Seal.answer_reads_the_replay z T₀ L (a ++ b) (.day T .record) hq
  rw [← hv] at hread
  have hplan := PlanReq.todayRecord_is_the_answers_reading req (by rw [hrun, hvL, hday]; exact hLT)
  rw [hrun, hday] at hplan
  rw [hday]
  rw [hplan] at hread
  exact (Option.some.inj hread).symm

end Planner
end Tm
