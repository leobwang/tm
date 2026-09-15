import TmKernel.SealLaw
/-!
# SealResume — resuming a checkpoint over its tail (stage 5, D9, W2)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §9.3 (the guards), §9.4 (the reseal) and §9.5 (the laws).
`resume z T K b term p` restores the state a checkpoint `K` holds (`restore`), masks the tail `b` with the settled undos
set aside (`unsettled`), refuses by G1 an undo whose target could be folded (`g1`), and steps the tail's survivors on
the stored wakes and the tail's (`tailIndex`, `tailSlept`), refusing by G2 a wake behind the cut or inside the fence,
and by G3 a reading of the index before the head second or a key below the horizons (`stepCheck`); every tail entry's
header is checked too (`headerCheck`).  The answer (`resumedAnswer`) is the resumed state grouped as `ckptOf` groups a
state, with the checkpoint's all-time aggregates below the horizons (`aggMerged`).

Nothing here is on the wire yet (W3 wires it).  D9-21: `restore` and the tail fold are `foldl`s; `unsettled` is
`filterTR`; `g1` reads `danglingOf` (a `foldl` whose steps scan the stack: quadratic on a hostile tail of undos, W5
measures it); `resumedAnswer` groups with `canon` (each insertion scans; W4's lever).
-/
namespace Tm
namespace Seal

open Replay (State Machine Effect HeaderRec EnergyObs Obs)
open Log (Entry)

/-! ## The guards' vocabulary -/

/-- **The fence** (G2): a surviving tail wake must be more than three days before every folded future instant, since
two instants on one local date are less than three days apart under any zone table (offsets are under a day). -/
def fenceSec : Nat := 259200

/-- The open block's running sub-segment start, if any. -/
def blockSince (m : Machine) : List Cal.Instant := ((m.block.bind (·.since)).map (·.1)).toList

/-- The open block's pause start, if any. -/
def blockPaused (m : Machine) : List Cal.Instant := ((m.block.bind (·.pausedAt)).map (·.1)).toList

/-- **Every instant a step reads the day index at**: the entry's own (`entryInstants`), and the open block's sub-segment
and pause starts when the step closes them (`closeSub`, `closePause`). -/
def stepQueries (m : Machine) (e : Entry) : List Cal.Instant :=
  entryInstants e ++
    match e.ev with
    | .start .. => blockSince m ++ blockPaused m
    | .pause id =>
      match m.block with
      | some b => if b.id = id ∧ b.paused = false then blockSince m else []
      | none => []
    | .unpause id =>
      match m.block with
      | some b => if b.id = id ∧ b.paused = true then blockPaused m else []
      | none => []
    | .interrupt _ => blockSince m ++ blockPaused m
    | .stop id _ =>
      match m.block with
      | some b => if b.id = id then blockSince m ++ blockPaused m else []
      | none => []
    | .done id .. =>
      match m.block with
      | some b => if b.id = id then blockSince m ++ blockPaused m else []
      | none => []
    | _ => []

/-- **The tail without its settled undos** (§7.4): a settled undo cancels nothing after the cut. -/
def unsettled (settled : List Nat) (bs : List Entry) : List Entry :=
  bs.filter (fun e => !(e.ev.isUndo && settled.contains e.line))

/-- G1 for one dangling tail undo: refused when a folded survivor may carry its tag. -/
def reachOf (K : Ckpt) (u : Entry) : Option Refusal :=
  match u.ev with
  | .undo of_ _ =>
    match K.tagLast.find? (fun p => p.1 == of_) with
    | some p => some (.undoReach u.line p.2)
    | none => if !Log.isKnownTag of_ && K.tagOverflow then some (.undoReach u.line 0) else none
  | _ => none

/-- **G1** (§7.4): the first undo of the unsettled tail that dangles there and whose tag a folded survivor may carry. -/
def g1 (K : Ckpt) (N : List Entry) : Option Refusal := ((Replay.danglingOf N).2.reverse).findSome? (reachOf K)

/-- **The tail's day index**: the stored wakes and the tail's surviving wakes. -/
def tailIndex (z : Cal.Tz) (K : Ckpt) (sv : List Entry) : List Cal.Instant :=
  Replay.keptWakes z (K.wakes ++ Replay.wakeInstants sv)

/-- **The tail's `slept_by_day`**: a day's first folded wake's, else its first tail wake's. -/
def tailSlept (z : Cal.Tz) (K : Ckpt) (kw : List Cal.Instant) (sv : List Entry) : Nat → Option Nat :=
  fun d => (Replay.KMap.get K.sleptByDay d).or (Replay.KMap.get (Replay.sleptByDay z kw sv) d)

/-- The refusal for a key below the horizons. -/
def keyRefusal (line : Nat) : Replay.Key → Refusal
  | .day d => .sealedDay line d
  | .itemDay _ d => .sealedWindow line d
  | .doneDate _ d => .sealedWindow line d
  | .instDate _ _ d => .sealedWindow line d
  | _ => .sealedDay line 0

/-- **One checked tail step**: its effects, and the first guard it fails (G3's head, G2, G3's keys). -/
def stepCheck (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt) (st : State) (e : Entry) :
    List Effect × Option Refusal :=
  let fx := Replay.effectsWith z dy sl st e
  (fx, (((stepQueries st.machine e).find? (fun q => decide (q.sec < headSec K.ledgerDay))).map
          (fun _ => Refusal.sealedDay e.line (K.ledgerDay - 1)))
    <|> (if Replay.isWake e && !(K.maxT.all (· < e.t.val) && K.futureFloor.all (fun f => decide (e.t.val.sec + fenceSec < f.sec)))
         then some (.wakeBehindCut e.line e.t.val) else none)
    <|> ((fx.find? (fun x => !keyAtOrAbove K.ledgerDay (horizonOf K.ledgerDay) x.key)).map (fun x => keyRefusal e.line x.key)))

def tailFoldStep (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt)
    (acc : State × Option Refusal) (e : Entry) : State × Option Refusal :=
  let r := stepCheck z dy sl K acc.1 e
  (Replay.applyEffects acc.1 r.1, acc.2 <|> r.2)

/-- **The tail's survivors stepped from a state**, with the first refusal. -/
def tailFold (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt) (st : State) (sv : List Entry) :
    State × Option Refusal :=
  sv.foldl (tailFoldStep z dy sl K) (st, none)

/-- **Every tail entry's header** (G3, cancelled entries included): at or after the head second, on a day at or after
the ledger day. -/
def headerCheck (dy : Cal.Instant → Nat) (K : Ckpt) (bs : List Entry) : Option Refusal :=
  bs.findSome? (fun e => if e.t.val.sec < headSec K.ledgerDay then some (.sealedDay e.line (K.ledgerDay - 1))
    else if dy e.t.val < K.ledgerDay then some (.sealedDay e.line (dy e.t.val)) else none)

/-- **The tail's headers**: each entry's day on the tail's index and its mask bit (a settled undo is cancelled, as every
undo is; any other entry reads the unsettled tail's mask). -/
def tailHeaders (dy : Cal.Instant → Nat) (settled : List Nat) (bs : List Entry) : List (Nat × HeaderRec) :=
  let dead := Replay.maskFast (unsettled settled bs)
  (bs.foldl (fun (acc : List (Nat × HeaderRec) × Nat) e =>
    if e.ev.isUndo && settled.contains e.line then ((dy e.t.val, HeaderRec.of e true) :: acc.1, acc.2)
    else ((dy e.t.val, HeaderRec.of e (Replay.deadAt dead acc.2)) :: acc.1, acc.2 + 1)) ([], 0)).1.reverse

/-- The stored headers of a checkpoint's open days. -/
def storedHeaders (K : Ckpt) : List (Nat × HeaderRec) := K.openDays.flatMap (fun o => o.headers.map (fun h => (o.day, h)))

/-! ## The restored state -/

/-- Write every pair's value at its key, in order. -/
def writeAll {κ β : Type} [DecidableEq κ] [Replay.KeyHash κ] (l : List (κ × β)) (m : Replay.HMap κ β) : Replay.HMap κ β :=
  l.foldl (fun m p => m.alter p.1 (fun _ => some p.2)) m

/-- A checkpoint's window item minutes, as pairs. -/
def windowItemPairs (K : Ckpt) : List ((Nat × Log.Id) × Nat) :=
  K.window.flatMap (fun w => w.itemMin.map (fun p => ((w.day, p.1), p.2)))

/-- A checkpoint's window done dates, as pairs. -/
def windowDonePairs (K : Ckpt) : List ((Nat × Log.Id) × Unit) :=
  K.window.flatMap (fun w => w.doneIds.map (fun i => ((w.day, i), ())))

/-- A checkpoint's instances, the date-keyed then the others. -/
def instPairs (K : Ckpt) : List ((List Char × List Char) × Replay.InstRec) := K.window.flatMap (·.inst) ++ K.instOther

/-- Write a value at a key when there is one. -/
def writeOpt {κ β : Type} [DecidableEq κ] [Replay.KeyHash κ] (m : Replay.HMap κ β) (k : κ) : Option β → Replay.HMap κ β
  | some x => m.alter k (fun _ => some x)
  | none => m


def restore (K : Ckpt) (n : Nat) : State :=
  ⟨K.openDays.foldl (fun m o => writeOpt m o.day o.acc) (Replay.HMap.empty n),
   K.items.foldl (fun m a => writeOpt m a.id a.acc) (Replay.HMap.empty n),
   writeAll (windowItemPairs K) (Replay.HMap.empty n),
   K.openDays.flatMap (fun o => o.energy.reverse),
   K.openDays.flatMap (fun o => o.durations.reverse),
   K.openDays.flatMap (fun o => o.interrupts.reverse),
   [], K.machine, ⟨K.lastEff, 0⟩,
   K.items.foldl (fun m a => writeOpt m a.id a.lastDone) (Replay.HMap.empty n),
   writeAll (windowDonePairs K) (Replay.HMap.empty n),
   writeAll (instPairs K) (Replay.HMap.empty n),
   writeAll K.named (Replay.HMap.empty n),
   K.rwarns.reverse,
   K.openDays.flatMap (fun o => (o.demotions.map (fun r => (o.day, r))).reverse),
   K.openDays.flatMap (fun o => (o.closes.map (fun r => (o.day, r))).reverse),
   K.items.foldl (fun m a => if a.dropped then m.alter a.id (fun _ => some ()) else m) (Replay.HMap.empty n),
   K.longestLeak, K.unknown,
   K.openDays.foldl (fun m o => writeOpt m o.day o.seam) (Replay.HMap.empty n)⟩

/-- A non-start energy observation rebound to a `slept_by_day` (late binding, C5). -/
def rebindObs (g : Nat → Option Nat) (o : EnergyObs) : EnergyObs :=
  if o.fromStart then o else { o with sleptMin := g o.day }

/-- **A state's observations rebound** to a `slept_by_day`. -/
def rebindState (g : Nat → Option Nat) (st : State) : State := { st with energy := st.energy.map (rebindObs g) }

/-! ## The resumed answer -/

def minOpt : Option Nat → Option Nat → Option Nat
  | none, b => b
  | some a, none => some a
  | some a, some b => some (Nat.min a b)

def maxOpt : Option Nat → Option Nat → Option Nat
  | none, b => b
  | some a, none => some a
  | some a, some b => some (Nat.max a b)

/-- **One item's all-time facts after a resume**: the state's, with the first done date and the count of done dates
taking the checkpoint's dates below the horizon. -/
def aggMerged (K : Ckpt) (st : State) (i : Log.Id) : ItemAgg :=
  let old := findItem K.items i
  let ds := (st.doneDates.pairs.filter (fun p => decide (p.1.2 = i))).map (·.1.1)
  ⟨i, st.items.get i, st.lastDone.get i, (st.dropped.get i).isSome,
   minOpt (old.bind (·.doneFirst)) (Replay.minDay? ds),
   ((old.map (·.doneCount)).getD 0) - (K.window.filter (fun w => w.doneIds.contains i)).length + ds.length⟩

/-- **The answer of a resumed state** (§11.1's `Hot`): grouped as `ckptOf` groups a state, above the checkpoint's
horizons, with its aggregates below them. -/
def resumedAnswer (K : Ckpt) (st : State) (hs : List (Nat × HeaderRec)) (entries : Nat) (ws : List (Nat × Log.LWarn)) :
    Seal.Answer :=
  ⟨K.ledgerDay, horizonOf K.ledgerDay,
   (canon idLt (K.items.map (·.id) ++ itemIds st)).map (fun i => (aggMerged K st i).finish),
   windowsFrom st (horizonOf K.ledgerDay), instOtherOf st, namedOf st,
   (daysFrom st hs K.ledgerDay).map (OpenDay.finish st.machine),
   st.machine.block.map (fun b => ⟨b.id, b.started, b.workedMin, b.since, b.paused⟩),
   st.machine.interrupt.map (fun i => ⟨0, some i.1, none, i.2.1, i.2.2, 0, []⟩),
   maxOpt K.lastDay (Replay.maxDay? (st.days.pairs.map Prod.fst)),
   st.global.lastEffective, K.entryCount + entries, st.unknown, st.longestLeak, st.rwarns.reverse,
   (K.warnings ++ ws).take maxWarnings, K.warnings.length + K.warnOverflow + ws.length - maxWarnings⟩

/-! ## Resume -/

/-- What a resume computed, for its answer and its reseal. -/
structure Run where
  entries : List Entry
  unsettledTail : List Entry
  survivors : List Entry
  index : List Cal.Instant
  slept : Nat → Option Nat
  state : State
  headers : List (Nat × HeaderRec)
  answer : Seal.Answer

/-- **Resume, the guards and the answer** (§9.3): G0 (the zone, the cut), G4 (`now` below the ledger day), G1, then the
tail's steps (G2, G3) and headers (G3). -/
def resumeRun (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) : Except Refusal Run :=
  if K.tzKey ≠ z.val.key then .error .zone
  else if !(b.head?.all (fun l => l.n == K.cut + 1)) then .error .cutMismatch
  else if T < K.ledgerDay then .error (.nowBelowLedger T K.ledgerDay)
  else
    let bs := Log.lineEntries b
    let N := unsettled K.settled bs
    match g1 K N with
    | some r => .error r
    | none =>
      let sv := Replay.survivors N
      let kw := tailIndex z K sv
      let dy := Replay.dayOf z kw
      let sl := tailSlept z K kw sv
      let r := tailFold z dy sl K (restore K (K.items.length + K.openDays.length + bs.length)) sv
      match r.2 <|> headerCheck dy K bs with
      | some x => .error x
      | none =>
        let hs := storedHeaders K ++ tailHeaders dy K.settled bs
        let st := rebindState sl r.1
        .ok ⟨bs, N, sv, kw, sl, st, hs, resumedAnswer K st hs bs.length (Log.lineWarnings b)⟩

/-! ## The reseal (§9.4)

A run's fold point `j` counts the tail lines it folds; the folded tail is the tail's entries on lines `K.cut + 1 ..
K.cut + j`.  A cut is valid (`cutOk`) when
- (i) every folded entry not future at `T` is on a day before `F` (`floorOf`, bounded by `now`, CRIT 1);
- (ii) it is within the policy's `maxLine`;
- (iii) every unfolded surviving wake is after the folded instants not future at `T` and more than the fence before the
  future ones;
- (iv) the new `settled` fits;
- (v) it does not fold an unterminated last line (CRIT 8);
- (vi) no unfolded undo's target is folded: the stored `settled` undos are folded, and no undo of the tail is cut from
  its tail target (W1's disagreement 11, settled by the cut, not by the ledger day).
The fold point is the greatest valid cut (`greatestValid`), and the new ledger day (`sealDayOf`) is the least of `F`,
the days the unfolded lines head, name and read, and the folded machine's days, never below `L`.  A reseal is emitted
when the stored checkpoint's future classification is unchanged at `T` (`migrationOk`) and the fold point is valid. -/

/-- The later of two optional instants. -/
def maxOptI : Option Cal.Instant → Option Cal.Instant → Option Cal.Instant
  | none, b => b
  | some a, none => some a
  | some a, some b => some (if a < b then b else a)

/-- The earlier of two optional instants. -/
def minOptI : Option Cal.Instant → Option Cal.Instant → Option Cal.Instant
  | none, b => b
  | some a, none => some a
  | some a, some b => some (if b < a then b else a)

/-- **The stored checkpoint's future classification holds at `T`**: its latest non-future instant is not future at `T`
and its earliest future one still is, so every folded instant keeps its side. -/
def migrationOk (K : Ckpt) (T : Nat) : Bool := K.maxT.all (fun m => !isFuture T m) && K.futureFloor.all (isFuture T)

/-- **`F`** (§9.4's G-w): `T − keepDays`, and `M − keepDays` for `M` the greatest day the call's surviving entries not
future at `T` head (`T` when there is none). -/
def floorOf (T keep : Nat) (dy : Cal.Instant → Nat) (sv : List Entry) : Nat :=
  let ds := (sv.filter (fun e => !isFuture T e.t.val)).map (fun e => dy e.t.val)
  Nat.min (T - keep) ((match ds with | [] => T | d :: rest => rest.foldl Nat.max d) - keep)

/-- Each undo of a list with the target it cancels there (stack order, as the mask cancels). -/
def undoTargets (N : List Entry) : List (Entry × Entry) :=
  (N.foldl (fun (acc : List Entry × List (Entry × Entry)) e =>
    match e.ev with
    | .undo of_ id =>
      match acc.1.find? (Replay.«matches» of_ id) with
      | some t => (acc.1.eraseP (Replay.«matches» of_ id), (e, t) :: acc.2)
      | none => acc
    | _ => (e :: acc.1, acc.2)) ([], [])).2

/-- **The new `settled` at cut `j`**: the unfolded undos of the unsettled tail that dangle there, ascending. -/
def settledAt (K : Ckpt) (r : Run) (j : Nat) : List Nat :=
  (((Replay.danglingOf r.unsettledTail).2.filter (fun u => decide (K.cut + j < u.line))).map (·.line)).reverse

/-- The days a tail's steps bound the new ledger day by, for the entries `P` selects: every date an effect's key names,
and the day after every instant the step reads the index at (so the head second is at or before it). -/
def stepLows (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (P : Entry → Bool) (st : State)
    (sv : List Entry) : List Nat :=
  (sv.foldl (fun (acc : State × List Nat) e =>
    let fx := Replay.effectsWith z dy sl acc.1 e
    (Replay.applyEffects acc.1 fx,
     if P e then fx.filterMap (fun x => x.key.date?) ++ (stepQueries acc.1.machine e).map (fun q => q.sec / 86400 + 1)
       ++ acc.2 else acc.2)) (st, [])).2

/-- **A valid cut** (§9.4's conditions (i)–(v), and (vi)). -/
def cutOk (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run) (j : Nat) :
    Bool :=
  let dy := Replay.dayOf z r.index
  let Bj := r.entries.filter (fun e => decide (e.line ≤ K.cut + j))
  let svr := r.survivors.filter (fun e => decide (K.cut + j < e.line))
  let QAj := Bj.flatMap entryInstants
  let maxT' := maxOptI K.maxT (maxInstant? (QAj.filter (fun q => !isFuture T q)))
  let ff' := minOptI K.futureFloor (minInstant? (QAj.filter (isFuture T)))
  decide (j ≤ b.length)
  && Bj.all (fun e => isFuture T e.t.val || decide (dy e.t.val < floorOf T p.keepDays dy r.survivors))
  && (j == 0 || p.maxLine.all (fun m => decide (K.cut + j ≤ m)))
  && (Replay.wakeInstants svr).all (fun w => maxT'.all (· < w) && ff'.all (fun f => decide (w.sec + fenceSec < f.sec)))
  && decide ((settledAt K r j).length ≤ maxSettled)
  && (terminated || decide (j < b.length) || j == 0)
  && K.settled.all (fun n => decide (n ≤ K.cut + j))
  && (undoTargets r.unsettledTail).all (fun ut => !(decide (ut.2.line ≤ K.cut + j) && decide (K.cut + j < ut.1.line)))

/-- **The greatest `j ≤ n` a check accepts**, or `0` (specification: every cut is checked). -/
def greatestValid (n : Nat) (valid : Nat → Bool) : Nat :=
  (List.range (n + 1)).foldl (fun acc j => if valid j then j else acc) 0

/-- A run's fold point: its greatest valid cut. -/
def foldPointOf (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run) : Nat :=
  greatestValid b.length (cutOk z T K b terminated p r)

/-- **The new ledger day `L'`** at cut `j` (§9.4, with W2's head-second and read-day bounds): the least of `F`, every
unfolded line's day and the day after its stamp, every date an unfolded surviving step names and the day after every
instant it reads, and the folded machine's days; never below `L`. -/
def sealDayOf (z : Cal.Tz) (T : Nat) (K : Ckpt) (p : Policy) (r : Run) (j : Nat) : Nat :=
  let dy := Replay.dayOf z r.index
  let n := K.items.length + K.openDays.length + r.entries.length
  let Brest := r.entries.filter (fun e => decide (K.cut + j < e.line))
  let svj := r.survivors.filter (fun e => decide (e.line ≤ K.cut + j))
  let lows := Brest.map (fun e => dy e.t.val) ++ Brest.map (fun e => e.t.val.sec / 86400 + 1)
    ++ stepLows z dy r.slept (fun e => decide (K.cut + j < e.line)) (restore K n) r.survivors
    ++ machineDays (svj.foldl (Replay.stepWith z dy r.slept) (restore K n)).machine
  Nat.max K.ledgerDay (lows.foldl Nat.min (floorOf T p.keepDays dy r.survivors))

/-- The tag filter of `keptTags`, over a tag-line list: every known tag, and the first unknown tags of bounded length. -/
def keepTags (all : List (List Char × Nat)) : List (List Char × Nat) :=
  let unknownKept := ((all.filter (fun p => !Log.isKnownTag p.1 && decide (p.1.length ≤ maxTagChars))).take maxUnknownTags)
  all.filter (fun p => Log.isKnownTag p.1 || unknownKept.contains p)

/-- Two tag-line lists merged by tag, the newer list's line winning. -/
def mergeTagLines (old new : List (List Char × Nat)) : List (List Char × Nat) :=
  (canon idLt (old.map Prod.fst ++ new.map Prod.fst)).map (fun t =>
    (t, ((new.find? (fun p => p.1 == t)).map Prod.snd).getD (((old.find? (fun p => p.1 == t)).map Prod.snd).getD 0)))

/-- **The reseal of a run** (§9.4): the checkpoint at the fold point and the records it seals. -/
def resealOf (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run) :
    Option Resealed :=
  let j := foldPointOf z T K b terminated p r
  if migrationOk K T && cutOk z T K b terminated p r j then
    let dy := Replay.dayOf z r.index
    let n := K.items.length + K.openDays.length + r.entries.length
    let Bj := r.entries.filter (fun e => decide (e.line ≤ K.cut + j))
    let svj := r.survivors.filter (fun e => decide (e.line ≤ K.cut + j))
    let Rj := svj.foldl (Replay.stepWith z dy r.slept) (restore K n)
    let kwj := Replay.keptWakes z (K.wakes ++ Replay.wakeInstants svj)
    let sleptj := K.sleptByDay ++ Replay.sleptByDay z kwj svj
    let st := rebindState (Replay.KMap.get sleptj) Rj
    let hsj := storedHeaders K ++ (tailHeaders dy K.settled r.entries).take Bj.length
    let L' := sealDayOf z T K p r j
    let QAj := Bj.flatMap entryInstants
    let merged := mergeTagLines K.tagLast (tagLines svj)
    let ws := (Log.lineWarnings b).filter (fun w => decide (w.1 ≤ K.cut + j))
    let ck : Ckpt := ⟨ckptVersion, K.tzKey, K.cut + j, L', T,
      maxOptI K.maxT (maxInstant? (QAj.filter (fun q => !isFuture T q))),
      minOptI K.futureFloor (minInstant? (QAj.filter (isFuture T))),
      storedWakes L' kwj, storedSlept sleptj L', keepTags merged,
      K.tagOverflow || decide ((keepTags merged).length < merged.length),
      settledAt K r j, st.machine,
      (canon idLt (K.items.map (·.id) ++ itemIds st)).map (aggMerged K st),
      windowsFrom st (horizonOf L'), instOtherOf st, namedOf st, daysFrom st hsj L',
      maxOpt K.lastDay (Replay.maxDay? (st.days.pairs.map Prod.fst)), st.global.lastEffective,
      K.entryCount + Bj.length, st.unknown, st.longestLeak, st.rwarns.reverse,
      (K.warnings ++ ws).take maxWarnings, K.warnings.length + K.warnOverflow + ws.length - maxWarnings⟩
    some ⟨ck, ck.meta, (daysIn st hsj K.ledgerDay L').map (OpenDay.finish st.machine),
      windowsIn st (horizonOf K.ledgerDay) (horizonOf L')⟩
  else none

/-- **How many tail lines a reseal folds** (§15): the resume's greatest valid cut. -/
def foldPoint (z : Cal.Tz) (T : Nat) (k : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) : Nat :=
  match resumeRun z T k b with
  | .ok r => foldPointOf z T k b terminated p r
  | .error _ => 0

/-- **The new ledger day `L'`** (§15), at the fold point. -/
def sealDay (z : Cal.Tz) (T : Nat) (k : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) : Nat :=
  match resumeRun z T k b with
  | .ok r => sealDayOf z T k p r (foldPointOf z T k b terminated p r)
  | .error _ => k.ledgerDay

/-- **Resume** (§9.4): the answer, and with a policy, the reseal. -/
def resume (z : Cal.Tz) (T : Nat) (k : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Option Policy) :
    Except Refusal (Seal.Answer × Option Resealed) :=
  match resumeRun z T k b with
  | .error e => .error e
  | .ok r => .ok (r.answer, p.bind (fun q => resealOf z T k b terminated q r))

end Seal
end Tm
