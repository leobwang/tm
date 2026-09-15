import TmKernel.SealLaw6
/-!
# SealGenesis — the chunked rebuild with exact pops (stage 5, D9, W2: law 9)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §9.7.  `genesis` resumes from the empty checkpoint through a log's
chunks, every call resealing, and keeps a stack of the checkpoints its calls sealed, each with the records sealed below
it and how far its call had read.  A guard refusal pops to the newest earlier checkpoint the refusal cannot name (the
oldest when none), and the lines from that checkpoint's cut through the refusing chunk's end go in one call.

Specification only: W3 wires the host's genesis, its resend cap (the design's 32,768 lines or 4 MiB, lowered at W3 by gap 102 to 8,192 lines or 1,536 KiB) and its files.  D9-21: the loop
runs at most twice per chunk (`genLoop`'s fuel), the stack holds at most one entry per chunk, and `endsFrom` recurses
over the chunks, not the lines.
-/
namespace Tm
namespace Seal

/-- **One entry of genesis' stack** (§9.7): a checkpoint, the day and window records sealed below its horizons, and how
many lines its call had read. -/
structure GenEntry where
  ckpt : Ckpt
  days : List DayRecord
  window : List WindowRecord
  known : Nat

/-- **A start a refusal cannot name** (§9.7's pop table; the fence is G2's). -/
def popOk (e : Refusal) (k : Ckpt) : Bool :=
  match e with
  | .undoReach _ below => decide (k.cut < below)
  | .wakeBehindCut _ t => k.maxT.all (· < t) && k.futureFloor.all (fun f => decide (t.sec + fenceSec < f.sec))
  | .sealedDay _ day => decide (k.ledgerDay ≤ day)
  | .sealedWindow _ day => decide (horizonOf k.ledgerDay ≤ day)
  | _ => false

/-- **Pop to what a refusal names**: the newest entry it cannot name, else the oldest. -/
def popTo (e : Refusal) : List GenEntry → List GenEntry
  | [] => []
  | [x] => [x]
  | x :: y :: rest => if popOk e x.ckpt then x :: y :: rest else popTo e (y :: rest)

/-- The lines a call from a checkpoint reads through a chunk end. -/
def genLines (ls : List Log.Line) (k : Ckpt) (e : Nat) : List Log.Line := (ls.drop k.cut).take (e - k.cut)

/-- The chunks' ends after `s` lines, as line counts (a chunk list is short: one chunk per 8,192 lines). -/
def endsFrom (s : Nat) : List (List Log.Line) → List Nat
  | [] => []
  | c :: cs => (s + c.length) :: endsFrom (s + c.length) cs

/-- The chunks' ends, as line counts. -/
def chunkEnds (chunks : List (List Log.Line)) : List Nat := endsFrom 0 chunks

/-- **Genesis' loop** (§9.7).  Each call resumes the stack's top through the next chunk end, resealing: a reseal pushes
its checkpoint with the records it emitted; a guard refusal pops below the top and retries the same end; any other
refusal is genesis' own.  The loop's fuel is spent only where it cannot run out (each round consumes an end or pops an
entry every earlier push consumed an end for), so its `cutMismatch` branches are unreachable. -/
def genLoop (z : Cal.Tz) (T : Nat) (ls : List Log.Line) (terminated : Bool) (p : Policy) :
    Nat → List GenEntry → List Nat → Option Seal.Answer → Except Refusal (List GenEntry × Seal.Answer)
  | 0, _, _, _ => .error .cutMismatch
  | _ + 1, stack, [], some v => .ok (stack, v)
  | _ + 1, _, [], none => .error .cutMismatch
  | _ + 1, [], _ :: _, _ => .error .cutMismatch
  | fuel + 1, E :: rest, e :: ends, _ =>
    match resume z T E.ckpt (genLines ls E.ckpt e) (if e < ls.length then true else terminated) (some p) with
    | .ok (v, none) => genLoop z T ls terminated p fuel (E :: rest) ends (some v)
    | .ok (v, some s) =>
      genLoop z T ls terminated p fuel (⟨s.ckpt, E.days ++ s.days, E.window ++ s.window, e⟩ :: E :: rest) ends (some v)
    | .error r =>
      if r.isGuard && !rest.isEmpty then genLoop z T ls terminated p fuel (popTo r rest) (e :: ends) none
      else .error r

/-- The ends genesis calls through: the chunks' ends, and an empty log's one empty chunk. -/
def genEnds (chunks : List (List Log.Line)) : List Nat :=
  match chunkEnds chunks with
  | [] => [0]
  | es => es

/-- Genesis over lines, through given ends: the records sealed below the last call's checkpoint, and that call's
answer. -/
def genesisOver (z : Cal.Tz) (T : Nat) (ls : List Log.Line) (terminated : Bool) (p : Policy) (ends : List Nat) :
    Except Refusal (List DayRecord × List WindowRecord × Seal.Answer) :=
  match genLoop z T ls terminated p (2 * ends.length + 2) [⟨Ckpt.empty z, [], [], 0⟩] ends none with
  | .ok (E :: _, v) => .ok (E.days, E.window, v)
  | .ok ([], _) => .error .cutMismatch
  | .error r => .error r

/-- **Genesis** (§9.7, §15): the log's chunks resumed from the empty checkpoint with exact pops; the records sealed below
the last call's checkpoint, and that call's answer. -/
def genesis (z : Cal.Tz) (T : Nat) (chunks : List (List Log.Line)) (terminated : Bool) (p : Policy) :
    Except Refusal (List DayRecord × List WindowRecord × Seal.Answer) :=
  genesisOver z T chunks.flatten terminated p (genEnds chunks)

end Seal
end Tm
