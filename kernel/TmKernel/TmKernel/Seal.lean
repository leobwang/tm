import TmKernel.Replay
/-!
# Seal — the checkpoint, the sealed records and their codecs (stage 5, D9 track, phase W)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §9 (windowing), §10.4 (the bounds), §11 (what the kernel hands
back), §14.5's W1 row and §15's W block.  **W1** (this module's first step) builds the types, the codecs and the
specification the window laws read; **W2** builds `resume`, the fold point and the reseal, and discharges the sixteen
laws W1 states in `Goals.lean`; **W3** puts them on the wire.  **Nothing in the binary reads this module yet**: Rust is
still the only reader of the log until the switch (S).

## What is stored, and where each fact lives (§8.4, §9.2)

* **A checkpoint** (`Ckpt`) is the fold of lines `1..cut` with every dated fact below its horizon removed: the machine
  (its last cut included), the all-time facts (A: `items`, `instOther`, `named`, `lastDay`, `lastEff`, `unknown`,
  `longestLeak`, the replay warnings, the entry count), the window facts of dates `≥ horizonOf ledgerDay` (W:
  `window`), and the open days `≥ ledgerDay` (O: `openDays`), with the guards' bookkeeping (`maxT`, `futureFloor`,
  `wakes`, `sleptByDay`, `tagLast`, `settled`).
* **A day record** (`DayRecord`) is one day's eight readings, finished, exactly as `Replay.ask` answers them; a day
  below the ledger day is stored by Rust once, as this.  Under the owner's D14 it carries the ported fields: they are
  the fork record's (`Replay.DayAcc`) and the day's interruptions and closes.
* **A window record** (`WindowRecord`) is one date's item minutes, done ids and date-keyed instances.
* **An open day** (`OpenDay`) is a day record's readings as the fold leaves them: `acc` and `seam` unfinished (their
  lists newest first, the segments unsorted), the observation, interruption, demotion, close and header lists in file
  order, and no pending start observation (it lives in the machine's block).  `OpenDay.finish` is fork
  `Machine::finish` on one day, so a resumed fold (W2) needs no inverse of a sort.

## The carried notes (README "Stage 5 D9 C6" and "C7")

1. **The global longest leak lives in the checkpoint** (A), whole.  It is a first maximum in file order over every
   day; a tail can only extend the fold, and G1 keeps a tail from cancelling a folded leak, so the running maximum
   continues exactly.  `the_answer_reads_the_replays_longest_leak` proves the answer's reading is the replay's for
   every log and ledger day.
2. **The machine's last cut is carried** in `Ckpt.machine` (`a_checkpoint_carries_the_last_cut`); no view reads it.
3. **`Log.Line`** is new: a physical line's number and characters, as the host sends them.  `Seal.replayLines` is
   `Replay.replayDoc` over `Log.lineEntries`, and `Seal.Q` is `Replay.Q`.
4. **Every map is a canonical list**, one pair a key, sorted by the key (`canon`), and read through `get` when it is
   built.  A checkpoint therefore does not depend on how many buckets the fold sized its maps with, and the laws
   compare answers and views, never `Facts` values (C7's `SameReadings` is W2's tool for a resumed fold).

## The codecs (law 10, R10)

A `Codec` is an encoder, a decoder, a bound predicate `ok` and the round trip `dec (enc a) = some a`, **for every
value**, proved once per combinator (`cNat`, `cStr`, `cOpt`, `cList`, tuples as flat arrays through `cIso`).  Records
are positional arrays with numeral tags; the checkpoint is an object whose keys come in build order.  The readers are
smart (R10): field by field, a field absent, out of order or of the wrong shape refused `badCkpt <field>` and never
defaulted, then every bound of §10.4 (`Ckpt.fault`, `DayRecord.fault`, `WindowRecord.fault`).  So
`readCkpt_emitCkpt` holds for every checkpoint within its bounds, `readCkpt_wf` says the decoder returns only such
checkpoints, and `readCkpt_emitCkpt_iff` is both directions; likewise for the two records.  A kernel emission beyond a
bound refuses `counterOverflow` (W3), so the round trip needs no hypothesis beyond `wf`.

## The specification the laws read (§9.5)

`ckptOf z T₀ L ls r` is the checkpoint of lines `ls` sealed at `T₀` with ledger day `L`, knowing the unfolded lines
`r`: the replay's fold over the survivors of the call-wide mask that lie in `ls` (`foldedState`), grouped by where
each fact lives.  With `r = []` it is the replay's own fold (`replay_eq_finish_foldedState`).  `dayRecordsBetween` and
`windowRecordsBetween` are the finished records of a range, `answer` the finished checkpoint, `askAnswer` a query on
it (`none` below its horizons), and `askMerged` the records below and the answer above.  `sealable` is the hypothesis
of every law on a checkpoint: no unfolded survivor names a key below the horizons, the machine writes no day below
the ledger day, and what the unfolded undos cancel changes no record below the horizons.

## Rule D9-21 (functions here over a list the wire can make large)

On the wire (W3): the codecs' encoders (`List.map`, compiled as `mapTR`), `listStep` (a `foldl` a list), the tuple
codecs (recursion over a fixed schema of at most 28 fields), `Ckpt.fault` and the records' faults (`all`, `filter`,
`map`, `length`, and `ascending`, a `foldl`), `readCkptFields`, `readDayFields` and `readWindowFields` (fixed
schemas), `answer` (`map`) and `OpenDay.finish` (`sortObs`, compiled as core's merge sort; `appendTR`),
`maxInstant?` and `minInstant?` (`foldl`), and `Log.lineEntries`/`Log.lineWarnings` (`filterMap`, compiled as
`filterMapTR`).  **Specification only, never on the wire**: `Log.contiguousFrom` (structural), `insUniq` and `canon`
(each insertion scans), `foldedSurvivors`, `foldedIndex`, `foldedState` and `foldedHeaders` (the replay's spec
functions), `dayKeys`, `openDayOf`, `daysIn`, `daysFrom`, `winKeys`, `windowOf`, `windowsIn`, `windowsFrom`,
`itemIds`, `itemAggOf`, `instOtherOf`, `namedOf`, `storedWakes`, `storedSlept`, `tagLines`, `keptTags`, `targetStep`,
`undoTargets` and `settledOf` (`filter`, `map`, `eraseP`, `find?`), `ckptOfEntries`, `ckptOf`, the records and
`sealable` (W2's `resume` builds checkpoints, and `reseal_is_seal` says they are these), `askAnswer`, `dayRead`,
`winRead`, `askMerged`, `Replay.sortByLine` and `Replay.Doc.obs` (`find?`, `insSort`).
-/
namespace Tm

namespace Cal

/-- **The first day of `d`'s month** (§9.1's `monthStart`). -/
def monthStart (d : Nat) : Nat := d + 1 - (ofDay d).day

/-- **The Monday of `d`'s ISO week** (§9.1's `isoMonday`): day 0 is a Monday. -/
def isoMonday (d : Nat) : Nat := 7 * (d / 7)

end Cal

/-! ## Lines (carried note 3: no `Log.Line` existed; the laws quantify over what the host sends) -/

namespace Log

/-- **A physical line of `.tm/log.jsonl`**, as the host sends it (§10.1): its number and its characters, or `none` for
a line that is not UTF-8. -/
structure Line where
  n : Nat
  text : Option (List Char)
deriving DecidableEq, Repr

/-- **The lines are numbered `k, k+1, …`** (specification only). -/
def contiguousFrom : Nat → List Line → Bool
  | _, [] => true
  | k, l :: ls => l.n == k && contiguousFrom (k + 1) ls

/-- A line's verdict, read at its number (`readLine`, the `log` op's reader). -/
def Line.verdict (l : Line) : Verdict := readLine l.n l.text

def Line.entry? (l : Line) : Option Entry :=
  match l.verdict with
  | .entry e => some e
  | _ => none

def Line.warning? (l : Line) : Option (Nat × LWarn) :=
  match l.verdict with
  | .warn n w => some (n, w)
  | _ => none

/-- **The entries of lines**, in file order: every line that reads as an entry. -/
def lineEntries (ls : List Line) : List Entry := ls.filterMap Line.entry?

/-- The line warnings of lines, in file order. -/
def lineWarnings (ls : List Line) : List (Nat × LWarn) := ls.filterMap Line.warning?

end Log

namespace Replay

/-- An observation's line. -/
def Obs.line : Obs → Nat
  | .energy o => o.line
  | .duration o => o.line

def obsLineLe (a b : Obs) : Bool := decide (a.line ≤ b.line)

/-- **Observations by line** (a stable sort, as fork `energy.sort_by_key` and §11.2's Rust sort). -/
def sortByLine (l : List Obs) : List Obs := insSort obsLineLe l

/-- **A replayed log's observations** (§11.2): the energy observations, then the duration observations, by line. -/
def Doc.obs (doc : Doc) : List Obs :=
  sortByLine (doc.facts.energy.map Obs.energy ++ doc.facts.durations.map Obs.duration)

end Replay

namespace Seal

open Replay (At StartRec SegKind Segment EnergyObs DurationObs Interruption BreakRec IdleRec LeakRec Demotion
  CloseRec InstRec RWarn NamedRec Ci6 DayAcc ItemAcc Block Cut Machine HeaderRec IdleMark SeamAcc OpenBlock State Doc Obs)
open Log (Entry)

/-! ## The codec library: a value and its JSON, with the round trip proved once per combinator -/

/-- The most elements of a list the checkpoint does not bound by name (§10.4's "every length"). -/
def maxList : Nat := 65536

/-- **A codec**: a value's JSON, its decoder, its bound (`ok`, what §10.4 allows), and the round trip, for every
value.  The decoder does not check the bound: the smart readers check it after (`Ckpt.fault`). -/
structure Codec (α : Type) where
  enc : α → JVal
  dec : JVal → Option α
  ok : α → Bool
  rt : ∀ a, dec (enc a) = some a

/-- The encoder never writes `null` (what an `Option` codec needs of its element). -/
def Codec.NonNull {α : Type} (c : Codec α) : Prop := ∀ a, c.enc a ≠ .null

/-- A numeral. -/
def cNat : Codec Nat := ⟨.num, fun j => match j with | .num n => some n | _ => none, fun _ => true,
  fun _ => rfl⟩
theorem cNat_nonnull : cNat.NonNull := fun _ => nofun

/-- A boolean. -/
def cBool : Codec Bool := ⟨.bool, fun j => match j with | .bool b => some b | _ => none, fun _ => true,
  fun _ => rfl⟩

/-- Every string in a checkpoint or record is at most 65,536 characters (§10.4). -/
def maxStr : Nat := 65536

/-- A string of at most `maxStr` characters. -/
def cStr : Codec (List Char) := ⟨.str, fun j => match j with | .str s => some s | _ => none,
  fun s => decide (s.length ≤ maxStr), fun _ => rfl⟩
theorem cStr_nonnull : cStr.NonNull := fun _ => nofun

/-- A bounded numeral (`U8`, `U32`), read through its range check. -/
def cFin (n : Nat) : Codec (Fin n) :=
  ⟨fun a => .num a.val, fun j => match j with | .num k => if h : k < n then some ⟨k, h⟩ else none | _ => none,
   fun _ => true, fun a => by simp [a.isLt]⟩

/-- `null` is `none`; anything else is the element's. -/
def optDec {α : Type} (c : Codec α) (j : JVal) : Option (Option α) :=
  match j with
  | .null => some none
  | j => (c.dec j).map some

/-- An option: `null`, or the element (whose encoder never writes `null`). -/
def cOpt {α : Type} (c : Codec α) (h : c.NonNull) : Codec (Option α) where
  enc o := match o with | none => .null | some a => c.enc a
  dec := optDec c
  ok o := match o with | none => true | some a => c.ok a
  rt o := by
    cases o with
    | none => rfl
    | some a =>
      show optDec c (c.enc a) = some (some a)
      unfold optDec
      split
      · exact absurd ‹_› (h a)
      · rw [c.rt]; rfl

/-- One step of reading an array, reversed; a `foldl` (D9-21). -/
def listStep {α : Type} (c : Codec α) (acc : Option (List α)) (x : JVal) : Option (List α) :=
  match acc with
  | none => none
  | some ys => (c.dec x).map (· :: ys)

theorem foldl_listStep_map {α : Type} (c : Codec α) : ∀ (l acc : List α),
    (l.map c.enc).foldl (listStep c) (some acc) = some (l.reverse ++ acc)
  | [], acc => rfl
  | a :: l, acc => by
    simp only [List.map_cons, List.foldl_cons, listStep, c.rt, Option.map_some]
    rw [foldl_listStep_map c l (a :: acc)]; simp

/-- **A list of at most `n` elements**: an array, read by a `foldl`. -/
def cList {α : Type} (n : Nat) (c : Codec α) : Codec (List α) where
  enc l := .arr (l.map c.enc)
  dec j := match j with
    | .arr xs => (xs.foldl (listStep c) (some [])).map List.reverse
    | _ => none
  ok l := decide (l.length ≤ n) && l.all c.ok
  rt l := by simp only [foldl_listStep_map, Option.map_some, List.append_nil, List.reverse_reverse]
theorem cList_nonnull {α : Type} (n : Nat) (c : Codec α) : (cList n c).NonNull := fun _ => nofun

/-- **A tuple codec**: a value as the elements of one flat array, the round trip for every value. -/
structure TCodec (α : Type) where
  enc : α → List JVal
  dec : List JVal → Option α
  ok : α → Bool
  rt : ∀ a, dec (enc a) = some a

/-- The end of a tuple. -/
def tNil : TCodec Unit := ⟨fun _ => [], fun xs => match xs with | [] => some () | _ => none, fun _ => true,
  fun _ => rfl⟩

/-- One more field in front of a tuple. -/
def tCons {α β : Type} (c : Codec α) (t : TCodec β) : TCodec (α × β) where
  enc p := c.enc p.1 :: t.enc p.2
  dec xs := match xs with
    | x :: xs => match c.dec x, t.dec xs with
      | some a, some b => some (a, b)
      | _, _ => none
    | [] => none
  ok p := c.ok p.1 && t.ok p.2
  rt p := by simp only [c.rt, t.rt]

/-- A tuple as an array. -/
def cTuple {α : Type} (t : TCodec α) : Codec α where
  enc a := .arr (t.enc a)
  dec j := match j with | .arr xs => t.dec xs | _ => none
  ok := t.ok
  rt a := t.rt a
theorem cTuple_nonnull {α : Type} (t : TCodec α) : (cTuple t).NonNull := fun _ => nofun

/-- **A structure as its fields**: a codec through a map with a left inverse (for a structure, `rfl`). -/
def cIso {α β : Type} (c : Codec β) (f : α → β) (g : β → α) (h : ∀ a, g (f a) = a) : Codec α where
  enc a := c.enc (f a)
  dec j := (c.dec j).map g
  ok a := c.ok (f a)
  rt a := by simp [c.rt, h]
theorem cIso_nonnull {α β : Type} (c : Codec β) (f : α → β) (g : β → α) (h : ∀ a, g (f a) = a)
    (hc : c.NonNull) : (cIso c f g h).NonNull := fun a => hc (f a)

/-- A pair as a two-element array. -/
def cPair {α β : Type} (a : Codec α) (b : Codec β) : Codec (α × β) :=
  cIso (cTuple (tCons a (tCons b tNil))) (fun p => (p.1, p.2, ())) (fun p => (p.1, p.2.1)) (fun _ => rfl)

/-- **A stamp as the fork keeps it** (§9.2): `[sec, ns, west, offSec]`, the written offset kept for display. -/
def cAt : Codec At :=
  cIso (cTuple (tCons cNat (tCons cNat (tCons cBool (tCons cNat tNil)))))
    (fun t => (t.1.sec, t.1.ns, t.2.west, t.2.sec, ())) (fun p => (⟨p.1, p.2.1⟩, ⟨p.2.2.1, p.2.2.2.1⟩)) (fun _ => rfl)


/-! ### The replay's records -/


theorem cBool_nonnull : cBool.NonNull := fun _ => nofun
theorem cFin_nonnull (n : Nat) : (cFin n).NonNull := fun _ => nofun
theorem cPair_nonnull {α β : Type} (a : Codec α) (b : Codec β) : (cPair a b).NonNull := fun _ => nofun

abbrev cU8 : Codec Log.U8 := cFin 256

/-- A bare instant: `[sec, ns]`. -/
def cInstant : Codec Cal.Instant :=
  cIso (cTuple <| tCons cNat <| tCons cNat <| tNil) (fun t => (t.sec, t.ns, ())) (fun p => ⟨p.1, p.2.1⟩) (fun _ => rfl)
theorem cInstant_nonnull : cInstant.NonNull := fun _ => nofun
theorem cAt_nonnull : cAt.NonNull := fun _ => nofun

/-- A stamp as written, read through `Cal.mkInstant?` and `Cal.mkOffset?` (R10): `[sec, ns]` and `[west, sec]`. -/
def cVInstant : Codec Cal.VInstant where
  enc t := .arr [.num t.val.sec, .num t.val.ns]
  dec j := match j with
    | .arr [.num s, .num n] => Cal.mkInstant? s n
    | _ => none
  ok _ := true
  rt t := by simp [Cal.mkInstant?, t.property]
theorem cVInstant_nonnull : cVInstant.NonNull := fun _ => nofun

def cVOffset : Codec Cal.VOffset where
  enc o := .arr [.bool o.val.west, .num o.val.sec]
  dec j := match j with
    | .arr [.bool w, .num s] => Cal.mkOffset? w s
    | _ => none
  ok _ := true
  rt o := by simp [Cal.mkOffset?, o.property]
theorem cVOffset_nonnull : cVOffset.NonNull := fun _ => nofun

/-- `hsw`, lexical: the numeral as read. -/
def cNum : Codec Log.Num where
  enc n := match n with | .nat k => .num k | .dec d => .dec d
  dec j := match j with | .num k => some (.nat k) | .dec d => some (.dec d) | _ => none
  ok _ := true
  rt n := by cases n <;> rfl
theorem cNum_nonnull : cNum.NonNull := fun n => by cases n <;> nofun

abbrev cOptStr : Codec (Option (List Char)) := cOpt cStr cStr_nonnull
abbrev cOptAt : Codec (Option At) := cOpt cAt cAt_nonnull
abbrev cOptNat : Codec (Option Nat) := cOpt cNat cNat_nonnull
abbrev cOptU8 : Codec (Option Log.U8) := cOpt cU8 (cFin_nonnull 256)
abbrev cStrs : Codec (List (List Char)) := cList maxList cStr

def cStartRec : Codec StartRec :=
  cIso (cTuple <| tCons cAt <| tCons cStr <| tCons cU8 <| tCons cOptU8 <| tNil)
    (fun r => (r.t, r.id, r.pred, r.rep, ())) (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1⟩) (fun _ => rfl)

/-- A segment's kind: `[0, id]` block, `[1, id]` pause, `[2, id?]` interrupt, `[3, where?]` break,
`[4, item, inst]` routine, `[5, attributed]` idle. -/
def cSegKind : Codec SegKind where
  enc k := match k with
    | .block id => .arr [.num 0, cStr.enc id]
    | .pause id => .arr [.num 1, cStr.enc id]
    | .interrupt id => .arr [.num 2, cOptStr.enc id]
    | .brk w => .arr [.num 3, cOptStr.enc w]
    | .routine item inst => .arr [.num 4, cStr.enc item, cStr.enc inst]
    | .idle a => .arr [.num 5, cStr.enc a]
  dec j := match j with
    | .arr [.num 0, x] => (cStr.dec x).map .block
    | .arr [.num 1, x] => (cStr.dec x).map .pause
    | .arr [.num 2, x] => (cOptStr.dec x).map .interrupt
    | .arr [.num 3, x] => (cOptStr.dec x).map .brk
    | .arr [.num 4, x, y] => match cStr.dec x, cStr.dec y with
      | some a, some b => some (.routine a b)
      | _, _ => none
    | .arr [.num 5, x] => (cStr.dec x).map .idle
    | _ => none
  ok k := match k with
    | .block id | .pause id | .idle id => cStr.ok id
    | .interrupt id | .brk id => cOptStr.ok id
    | .routine a b => cStr.ok a && cStr.ok b
  rt k := by cases k <;> simp only [Codec.rt] <;> rfl

def cSegment : Codec Segment :=
  cIso (cTuple <| tCons cAt <| tCons cAt <| tCons cSegKind <| tNil)
    (fun s => (s.start, s.stop, s.kind, ())) (fun p => ⟨p.1, p.2.1, p.2.2.1⟩) (fun _ => rfl)

def cEnergyObs : Codec EnergyObs :=
  cIso (cTuple <| tCons cNat <| tCons cAt <| tCons cNat <| tCons cU8 <| tCons cU8 <| tCons cNum <| tCons cStr <| tCons cOptNat <| tCons cOptU8 <| tCons cOptStr <| tCons cBool <| tNil)
    (fun o => (o.line, o.t, o.day, o.pred, o.rep, o.hsw, o.loc, o.sleptMin, o.went, o.id, o.fromStart, ()))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1⟩) (fun _ => rfl)
theorem cEnergyObs_nonnull : cEnergyObs.NonNull := fun _ => nofun

def cDurationObs : Codec DurationObs :=
  cIso (cTuple <| tCons cNat <| tCons cAt <| tCons cNat <| tCons cStr <| tCons cU8 <| tCons cStrs <| tCons cNat <| tCons cNat <| tCons cOptU8 <| tCons cBool <| tNil)
    (fun o => (o.line, o.t, o.day, o.id, o.ci, o.tags, o.estMin, o.actualMin, o.went, o.isPartial, ()))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1⟩) (fun _ => rfl)

def cInterruption : Codec Interruption :=
  cIso (cTuple <| tCons cNat <| tCons cOptAt <| tCons cOptAt <| tCons cNat <| tCons cOptStr <| tCons cNat <| tCons cStrs <| tNil)
    (fun r => (r.line, r.start, r.stop, r.day, r.id, r.lostMin, r.dropped, ()))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1⟩) (fun _ => rfl)

def cBreakRec : Codec BreakRec :=
  cIso (cTuple <| tCons cAt <| tCons cNat <| tCons cNat <| tCons cOptNat <| tCons cOptStr <| tNil)
    (fun r => (r.t, r.day, r.plannedMin, r.actualMin, r.where_, ()))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1⟩) (fun _ => rfl)

def cIdleRec : Codec IdleRec :=
  cIso (cTuple <| tCons cAt <| tCons cNat <| tCons cStr <| tCons cNat <| tNil)
    (fun r => (r.t, r.day, r.attributed, r.min, ())) (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1⟩) (fun _ => rfl)

def cLeakRec : Codec LeakRec :=
  cIso (cTuple <| tCons cAt <| tCons cNat <| tCons cNat <| tNil)
    (fun r => (r.t, r.day, r.min, ())) (fun p => ⟨p.1, p.2.1, p.2.2.1⟩) (fun _ => rfl)
theorem cLeakRec_nonnull : cLeakRec.NonNull := fun _ => nofun

/-- A demotion's stamp: `[0, week]` or `[1, day]` (fork `stamp_from_key`). -/
def cStamp : Codec Field.Stamp where
  enc s := match s with | .week n => .arr [.num 0, .num n] | .day n => .arr [.num 1, .num n]
  dec j := match j with
    | .arr [.num 0, .num n] => some (.week n)
    | .arr [.num 1, .num n] => some (.day n)
    | _ => none
  ok _ := true
  rt s := by cases s <;> rfl
theorem cStamp_nonnull : cStamp.NonNull := fun s => by cases s <;> nofun

def cDemotion : Codec Demotion :=
  cIso (cTuple <| tCons cNat <| tCons cAt <| tCons cStr <| tCons cStr <| tCons cStr <| tCons cNat <| tCons (cOpt cStamp cStamp_nonnull) <| tNil)
    (fun r => (r.line, r.t, r.id, r.from_, r.to, r.estMin, r.stamp, ()))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1⟩) (fun _ => rfl)

def cCloseRec : Codec CloseRec :=
  cIso (cTuple <| tCons cNat <| tCons cAt <| tCons cStr <| tCons cStr <| tNil)
    (fun r => (r.line, r.t, r.period, r.key, ())) (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1⟩) (fun _ => rfl)

/-- A routine status as a numeral: done 0, pending 1, missed 2, expired 3, skipped 4. -/
def cStatus : Codec Log.InstanceStatus where
  enc s := match s with
    | .done => .num 0 | .pending => .num 1 | .missed => .num 2 | .expired => .num 3 | .skipped => .num 4
  dec j := match j with
    | .num 0 => some .done | .num 1 => some .pending | .num 2 => some .missed | .num 3 => some .expired
    | .num 4 => some .skipped | _ => none
  ok _ := true
  rt s := by cases s <;> rfl

def cInstRec : Codec InstRec :=
  cIso (cTuple <| tCons cAt <| tCons cStatus <| tCons cStr <| tCons cOptNat <| tNil)
    (fun r => (r.t, r.status, r.raw, r.actualMin, ())) (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1⟩) (fun _ => rfl)

def cRWarn : Codec RWarn :=
  cIso (cTuple <| tCons cNat <| tCons cStr <| tNil)
    (fun w => match w with | .unknownInstanceStatus l r => (l, r, ()))
    (fun p => .unknownInstanceStatus p.1 p.2.1) (fun w => by cases w; rfl)

def cNamedRec : Codec NamedRec :=
  cIso (cTuple <| tCons (cPair cNat cAt) <| tCons (cPair cNat (cPair cNat cAt)) <| tNil)
    (fun r => (r.latest, r.dated, ())) (fun p => ⟨p.1, p.2.1⟩) (fun _ => rfl)

def cCi6 : Codec Ci6 :=
  cIso (cTuple <| tCons cNat <| tCons cNat <| tCons cNat <| tCons cNat <| tCons cNat <| tCons cNat <| tNil)
    (fun c => (c.c0, c.c1, c.c2, c.c3, c.c4, c.c5, ()))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1⟩) (fun _ => rfl)


def cDayAcc : Codec DayAcc :=
  cIso (cTuple <| tCons cOptAt <| tCons (cList maxList cStartRec) <| tCons cNat <| tCons cNat <| tCons cNat
      <| tCons cCi6 <| tCons (cList maxList (cPair cStr cNat)) <| tCons cStrs <| tCons cNat <| tCons cStrs
      <| tCons (cList maxList cSegment) <| tCons cOptAt <| tCons cOptNat <| tCons cOptNat <| tCons cOptAt
      <| tCons cOptStr <| tCons (cOpt (cPair cStr cStr) (cPair_nonnull cStr cStr)) <| tCons cOptNat
      <| tCons (cList maxList (cPair cAt cStr)) <| tCons cNat <| tCons cNat <| tCons (cList maxList cIdleRec)
      <| tCons (cList maxList cBreakRec) <| tCons cNat <| tCons cNat <| tCons cNat <| tCons cNat <| tCons cOptStr
      <| tNil)
    (fun a => (a.firstStart, a.starts, a.blockMin, a.blocksDone, a.loadFifths, a.byCi, a.ciUnknown, a.done, a.lostMin,
      a.dropped, a.segments, a.wake, a.sleptMin, a.onsetMin, a.arrival, a.loc, a.window, a.budget, a.locChanges,
      a.leakMin, a.longestLeak, a.idle, a.breaks, a.routineMin, a.plans, a.replansToday, a.driftMin, a.lastPlanHash, ()))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩)
    (fun _ => rfl)
theorem cDayAcc_nonnull : cDayAcc.NonNull := fun _ => nofun

def cItemAcc : Codec ItemAcc :=
  cIso (cTuple <| tCons cNat <| tCons cNat <| tCons (cList maxList cAt) <| tCons (cList maxList cAt) <| tCons cNat
      <| tCons cNat <| tNil)
    (fun a => (a.minutes, a.blocks, a.doneAt, a.partialDoneAt, a.stops, a.extendedMin, ()))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1⟩) (fun _ => rfl)
theorem cItemAcc_nonnull : cItemAcc.NonNull := fun _ => nofun

def cBlock : Codec Block :=
  cIso (cTuple <| tCons cStr <| tCons cAt <| tCons cOptAt <| tCons cBool <| tCons cOptAt <| tCons cNat
      <| tCons (cOpt cEnergyObs cEnergyObs_nonnull) <| tNil)
    (fun b => (b.id, b.started, b.since, b.paused, b.pausedAt, b.workedMin, b.obs, ()))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1⟩) (fun _ => rfl)
theorem cBlock_nonnull : cBlock.NonNull := fun _ => nofun

def cCut : Codec Cut :=
  cIso (cTuple <| tCons cStr <| tCons cAt <| tCons cNat <| tCons cNat <| tNil)
    (fun c => (c.id, c.t, c.day, c.min, ())) (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1⟩) (fun _ => rfl)
theorem cCut_nonnull : cCut.NonNull := fun _ => nofun

/-- An open interruption: `[start, day, id?]`. -/
def cOpenInt : Codec (At × Nat × Option Log.Id) :=
  cIso (cTuple <| tCons cAt <| tCons cNat <| tCons cOptStr <| tNil)
    (fun i => (i.1, i.2.1, i.2.2, ())) (fun p => (p.1, p.2.1, p.2.2.1)) (fun _ => rfl)
theorem cOpenInt_nonnull : cOpenInt.NonNull := fun _ => nofun

/-- The machine (fork `Machine`): the open block, **the last cut** (carried note 2: no Rust field reads it, so the
view omits it, and only the checkpoint carries it), and the open interruption. -/
def cMachine : Codec Machine :=
  cIso (cTuple <| tCons (cOpt cBlock cBlock_nonnull) <| tCons (cOpt cCut cCut_nonnull)
      <| tCons (cOpt cOpenInt cOpenInt_nonnull) <| tNil)
    (fun m => (m.block, m.lastCut, m.interrupt, ())) (fun p => ⟨p.1, p.2.1, p.2.2.1⟩) (fun _ => rfl)

def cHeaderRec : Codec HeaderRec :=
  cIso (cTuple <| tCons cNat <| tCons cStr <| tCons cOptStr <| tCons cBool <| tCons cVInstant <| tCons cVOffset <| tNil)
    (fun h => (h.line, h.tag, h.id, h.cancelled, h.t, h.off, ()))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1⟩) (fun _ => rfl)

/-- An idle mark: `[0, t]` pause, `[1, t]` interrupt, `[2, t]` unpause, `[3, t]` resume, `[4, t, actual?]` break. -/
def cIdleMark : Codec IdleMark where
  enc m := match m with
    | .pause t => .arr [.num 0, cAt.enc t]
    | .interrupt t => .arr [.num 1, cAt.enc t]
    | .unpause t => .arr [.num 2, cAt.enc t]
    | .resume t => .arr [.num 3, cAt.enc t]
    | .brk t am => .arr [.num 4, cAt.enc t, cOptNat.enc am]
  dec j := match j with
    | .arr [.num 0, x] => (cAt.dec x).map .pause
    | .arr [.num 1, x] => (cAt.dec x).map .interrupt
    | .arr [.num 2, x] => (cAt.dec x).map .unpause
    | .arr [.num 3, x] => (cAt.dec x).map .resume
    | .arr [.num 4, x, y] => match cAt.dec x, cOptNat.dec y with
      | some t, some am => some (.brk t am)
      | _, _ => none
    | _ => none
  ok _ := true
  rt m := by cases m <;> simp only [Codec.rt] <;> rfl

def cSeamAcc : Codec SeamAcc :=
  cIso (cTuple <| tCons cOptAt <| tCons (cList maxList cIdleMark) <| tCons cOptAt <| tNil)
    (fun a => (a.sinceBreak, a.idleMarks, a.lastT, ())) (fun p => ⟨p.1, p.2.1, p.2.2.1⟩) (fun _ => rfl)
theorem cSeamAcc_nonnull : cSeamAcc.NonNull := fun _ => nofun

/-! ### Line warnings (the checkpoint keeps the first 256 folded ones) -/

/-- A character, as a one-character string. -/
def cChar : Codec Char where
  enc c := .str [c]
  dec j := match j with | .str [c] => some c | _ => none
  ok _ := true
  rt _ := rfl

def cJEsc : Codec JEsc where
  enc e := match e with
    | .truncatedEscape => .arr [.num 0]
    | .unknownEscape c => .arr [.num 1, cChar.enc c]
    | .badHexQuad a b c d => .arr [.num 2, cChar.enc a, cChar.enc b, cChar.enc c, cChar.enc d]
    | .surrogateEscape v => .arr [.num 3, .num v]
    | .rawQuote => .arr [.num 4]
    | .rawControl v => .arr [.num 5, .num v]
  dec j := match j with
    | .arr [.num 0] => some .truncatedEscape
    | .arr [.num 1, .str [c]] => some (.unknownEscape c)
    | .arr [.num 2, .str [a], .str [b], .str [c], .str [d]] => some (.badHexQuad a b c d)
    | .arr [.num 3, .num v] => some (.surrogateEscape v)
    | .arr [.num 4] => some .rawQuote
    | .arr [.num 5, .num v] => some (.rawControl v)
    | _ => none
  ok _ := true
  rt e := by cases e <;> rfl

def cJErr : Codec JErr where
  enc e := match e with
    | .outOfFuel => .arr [.num 0]
    | .emptyInput => .arr [.num 1]
    | .notAValue c => .arr [.num 2, cChar.enc c]
    | .badNumber => .arr [.num 3]
    | .unterminatedString => .arr [.num 4]
    | .badEscape x => .arr [.num 5, cJEsc.enc x]
    | .unterminatedArray => .arr [.num 6]
    | .expectedCommaOrBracket c => .arr [.num 7, cChar.enc c]
    | .unterminatedObject => .arr [.num 8]
    | .expectedCommaOrBrace c => .arr [.num 9, cChar.enc c]
    | .expectedColon c => .arr [.num 10, cChar.enc c]
    | .expectedKey c => .arr [.num 11, cChar.enc c]
    | .trailingGarbage c => .arr [.num 12, cChar.enc c]
    | .leadingZero => .arr [.num 13]
    | .missingDigit c => .arr [.num 14, cChar.enc c]
  dec j := match j with
    | .arr [.num 0] => some .outOfFuel
    | .arr [.num 1] => some .emptyInput
    | .arr [.num 2, .str [c]] => some (.notAValue c)
    | .arr [.num 3] => some .badNumber
    | .arr [.num 4] => some .unterminatedString
    | .arr [.num 5, x] => (cJEsc.dec x).map .badEscape
    | .arr [.num 6] => some .unterminatedArray
    | .arr [.num 7, .str [c]] => some (.expectedCommaOrBracket c)
    | .arr [.num 8] => some .unterminatedObject
    | .arr [.num 9, .str [c]] => some (.expectedCommaOrBrace c)
    | .arr [.num 10, .str [c]] => some (.expectedColon c)
    | .arr [.num 11, .str [c]] => some (.expectedKey c)
    | .arr [.num 12, .str [c]] => some (.trailingGarbage c)
    | .arr [.num 13] => some .leadingZero
    | .arr [.num 14, .str [c]] => some (.missingDigit c)
    | _ => none
  ok _ := true
  rt e := by cases e <;> simp only [Codec.rt] <;> rfl

def cStampErr : Codec LogStamp.StampErr where
  enc e := match e with
    | .tooShort => .num 0 | .badDate => .num 1 | .badSeparator => .num 2 | .badTime => .num 3
    | .badFraction => .num 4 | .badOffset => .num 5 | .tooLong => .num 6 | .beforeOrigin => .num 7
    | .pastYear9999 => .num 8
  dec j := match j with
    | .num 0 => some .tooShort | .num 1 => some .badDate | .num 2 => some .badSeparator | .num 3 => some .badTime
    | .num 4 => some .badFraction | .num 5 => some .badOffset | .num 6 => some .tooLong
    | .num 7 => some .beforeOrigin | .num 8 => some .pastYear9999 | _ => none
  ok _ := true
  rt e := by cases e <;> rfl

/-- A line warning: `[code]`, or `[code, argument]` for a parse error, a stamp error or a field key. -/
def cLWarn : Codec Log.LWarn where
  enc w := match w with
    | .invalidUtf8 => .arr [.num 0]
    | .lineTooLong => .arr [.num 1]
    | .lineTooDeep => .arr [.num 2]
    | .notJson e => .arr [.num 3, cJErr.enc e]
    | .numberOutOfRange => .arr [.num 4]
    | .notAnObject => .arr [.num 5]
    | .noT => .arr [.num 6]
    | .tNotString => .arr [.num 7]
    | .badT e => .arr [.num 8, cStampErr.enc e]
    | .duplicateT => .arr [.num 9]
    | .noEv => .arr [.num 10]
    | .evNotString => .arr [.num 11]
    | .missingField k => .arr [.num 12, cStr.enc k]
    | .badField k => .arr [.num 13, cStr.enc k]
  dec j := match j with
    | .arr [.num 0] => some .invalidUtf8
    | .arr [.num 1] => some .lineTooLong
    | .arr [.num 2] => some .lineTooDeep
    | .arr [.num 3, x] => (cJErr.dec x).map .notJson
    | .arr [.num 4] => some .numberOutOfRange
    | .arr [.num 5] => some .notAnObject
    | .arr [.num 6] => some .noT
    | .arr [.num 7] => some .tNotString
    | .arr [.num 8, x] => (cStampErr.dec x).map .badT
    | .arr [.num 9] => some .duplicateT
    | .arr [.num 10] => some .noEv
    | .arr [.num 11] => some .evNotString
    | .arr [.num 12, x] => (cStr.dec x).map .missingField
    | .arr [.num 13, x] => (cStr.dec x).map .badField
    | _ => none
  ok w := match w with
    | .missingField k | .badField k => cStr.ok k
    | _ => true
  rt w := by cases w <;> simp only [Codec.rt] <;> rfl


/-! ## The checkpoint and the sealed records (§9.2) -/

/-- **A header**: Replay's `HeaderRec` (C6), which keeps the written stamp; the display text is rendered at emission
(`LogStamp.displayStamp`), so a sealed header can be read back. -/
abbrev Header := HeaderRec

/-- **One day's readings, finished**: exactly what `Replay.ask` answers for the day's eight readings (§8.4's O): the
fork's record (if the day has one), its seam, and its observations, interruptions, demotions, closes and headers, each
list in file order.  A day `< L` is stored by Rust once, as this (§11.3); D14's ported fields are the record's and the
lists'. -/
structure DayRecord where
  day : Nat
  record : Option DayAcc
  seam : Option SeamAcc
  energy : List EnergyObs
  durations : List DurationObs
  interrupts : List Interruption
  demotions : List Demotion
  closes : List CloseRec
  headers : List Header
deriving DecidableEq, Repr

/-- **One open day in the checkpoint**: the same readings as the fold leaves them.  `acc` and `seam` are the
accumulators (their lists newest first, the segments unsorted: what `DayAcc.finish` and the seam's reverse finish);
the six lists are in file order.  `energy` holds the emitted observations only: a pending start observation lives in
the machine's block until it is emitted. -/
structure OpenDay where
  day : Nat
  acc : Option DayAcc
  seam : Option SeamAcc
  energy : List EnergyObs
  durations : List DurationObs
  interrupts : List Interruption
  demotions : List Demotion
  closes : List CloseRec
  headers : List Header
deriving DecidableEq, Repr

/-- **One date's window facts** (§8.4's W): the item minutes on the date, the ids done on it, and the instances whose
`inst` names it, each sorted by its key. -/
structure WindowRecord where
  day : Nat
  itemMin : List (Log.Id × Nat)
  doneIds : List Log.Id
  inst : List ((List Char × List Char) × InstRec)
deriving DecidableEq, Repr

/-- **One item's all-time facts** (§8.4's A): its record as the fold leaves it, `last_done`, whether it was dropped, and
its first done date and count of done dates over **every** date (a date below the horizon included). -/
structure ItemAgg where
  id : Log.Id
  acc : Option ItemAcc
  lastDone : Option At
  dropped : Bool
  doneFirst : Option Nat
  doneCount : Nat
deriving DecidableEq, Repr

/-- **The checkpoint** (§9.2): the fold of lines `1..cut`, with every dated fact below its horizon removed. -/
structure Ckpt where
  /-- the format version, `ckptVersion` -/
  v : Nat
  /-- the zone key it was attributed under (G0) -/
  tzKey : List Char
  /-- `c`: lines `1..cut` are folded -/
  cut : Nat
  /-- `L`; the window horizon `H` is `horizonOf ledgerDay`, never stored -/
  ledgerDay : Nat
  /-- the `T` of the call that sealed it (host back-off only) -/
  resealDay : Nat
  /-- the latest instant among folded entries that are not future-dated (G2) -/
  maxT : Option Cal.Instant
  /-- the earliest instant among folded future-dated entries (G2) -/
  futureFloor : Option Cal.Instant
  /-- the last kept wake dated `< L − 2`, then every kept wake dated `≥ L − 2`, in the index's order -/
  wakes : List Cal.Instant
  /-- fork `slept_by_day` for days `≥ L`: the first surviving wake in file order of each day, sorted by day -/
  sleptByDay : List (Nat × Nat)
  /-- per tag among folded survivors, its latest line, sorted by tag (G1) -/
  tagLast : List (List Char × Nat)
  /-- an unknown tag was not kept in `tagLast` -/
  tagOverflow : Bool
  /-- the lines of unfolded undos whose call-wide target is folded or absent, ascending -/
  settled : List Nat
  /-- the machine, **its last cut included** (carried note 2) -/
  machine : Machine
  /-- A: every item, sorted by id -/
  items : List ItemAgg
  /-- W: every date `≥ horizonOf ledgerDay` with a window fact, sorted by date -/
  window : List WindowRecord
  /-- A: the instances whose `inst` names no date, sorted by key -/
  instOther : List ((List Char × List Char) × InstRec)
  /-- A: fork `LatestNamed` per `(name, id?)`, sorted by key -/
  named : List ((List Char × Option Log.Id) × NamedRec)
  /-- O: every day `≥ ledgerDay` with a reading, sorted by day -/
  openDays : List OpenDay
  /-- A: the greatest day with a record, over every day (`days.keys().last`) -/
  lastDay : Option Nat
  /-- A: fork `last_effective_t` -/
  lastEff : Option At
  /-- A: the entries folded (`Replay::entry_count`) -/
  entryCount : Nat
  /-- A: fork `unknown` -/
  unknown : Nat
  /-- A: **the global longest leak** (carried note 1): a first maximum in file order over every day, kept whole -/
  longestLeak : Option LeakRec
  /-- A: the replay warnings, in file order -/
  rwarns : List RWarn
  /-- the first 256 folded line warnings -/
  warnings : List (Nat × Log.LWarn)
  /-- how many folded line warnings are not in `warnings` -/
  warnOverflow : Nat
deriving DecidableEq, Repr

/-- The format version a checkpoint carries; any other is `badCkpt v`. -/
def ckptVersion : Nat := 1

/-- **What the host reads beside the checkpoint** (§9.2): its cut, horizons, reseal day and G2 instants. -/
structure Meta where
  cut : Nat
  ledgerDay : Nat
  horizon : Nat
  resealDay : Nat
  maxT : Option Cal.Instant
  futureFloor : Option Cal.Instant
deriving DecidableEq, Repr

/-- **What a reseal emits** (§9.4): the new checkpoint and its meta, the day records of `[L, L')` and the window
records of `[H, H')`.  The new `settled` is the checkpoint's. -/
structure Resealed where
  ckpt : Ckpt
  «meta» : Meta
  days : List DayRecord
  window : List WindowRecord
deriving DecidableEq, Repr

/-- **The host's reseal policy** (§9.6): how many days stay unfolded, and the undo stack's pin. -/
structure Policy where
  keepDays : Nat
  maxLine : Option Nat
deriving DecidableEq, Repr

/-- The field a stored checkpoint or record is refused at (`badCkpt <field>`, §10.3–§10.4). -/
inductive CkField
  | shape | v | tzKey | cut | ledgerDay | resealDay | maxT | futureFloor | wakes | sleptByDay | tagLast
  | tagOverflow | settled | machine | items | window | instOther | named | openDays | lastDay | lastEff
  | entryCount | unknown | longestLeak | rwarns | warnings | warnOverflow
  | day | record | seam | energy | durations | interrupts | demotions | closes | headers | itemMin | doneIds | inst
deriving DecidableEq, Repr

/-- Why a stored checkpoint or record is refused. -/
inductive CkErr
  | badCkpt (f : CkField)
deriving DecidableEq, Repr

/-- **A refusal of the `log` op's resume** (§9.3, §10.3).  The first five are the guards; each names its bound, so the
host pops exactly to it (§9.7). -/
inductive Refusal
  | undoReach (line below : Nat)
  | wakeBehindCut (line : Nat) (t : Cal.Instant)
  | sealedDay (line day : Nat)
  | sealedWindow (line day : Nat)
  | nowBelowLedger (now ledgerDay : Nat)
  | badCkpt (f : CkField)
  | cutMismatch
  | zone
  | counterOverflow (f : CkField)
deriving DecidableEq, Repr

/-- The guards' refusals (G1–G4): a checkpoint built from a prefix could otherwise be wrong.  The rest are provenance
(G0) or a host defect. -/
def Refusal.isGuard : Refusal → Bool
  | .undoReach .. | .wakeBehindCut .. | .sealedDay .. | .sealedWindow .. | .nowBelowLedger .. => true
  | _ => false

/-- **The answer a verb reads on the hot path** (§11.1's `Hot` scope): A, W and O, finished. -/
structure Answer where
  ledgerDay : Nat
  horizon : Nat
  items : List ItemAgg
  window : List WindowRecord
  instOther : List ((List Char × List Char) × InstRec)
  named : List ((List Char × Option Log.Id) × NamedRec)
  days : List DayRecord
  openBlock : Option OpenBlock
  openInterrupt : Option Interruption
  lastDay : Option Nat
  lastEffective : Option At
  entryCount : Nat
  unknown : Nat
  longestLeak : Option LeakRec
  rwarns : List RWarn
  warnings : List (Nat × Log.LWarn)
  warnOverflow : Nat
deriving DecidableEq, Repr

/-! ## The horizons (§9.1) -/

/-- `AUTO_CLOSE_CATCHUP`: the oldest date `auto_close` can close is `T − 16`. -/
def autoCloseCatchup : Nat := 16

/-- **The window horizon of a ledger day** (§9.1): window facts are kept for dates `≥ H`, which covers every day, week
and month period containing `L` and every date `auto_close` can close at `L`. -/
def horizonOf (L : Nat) : Nat := min (min (Cal.monthStart L) (Cal.isoMonday L)) (L - autoCloseCatchup)

/-! ## The codecs (§9.2): positional records, a keyed checkpoint, and every bound of §10.4 -/

/-- Checkpoint bounds (§10.4). -/
def maxTzKey : Nat := 128
def maxItems : Nat := 65536
def maxWindow : Nat := 4096
def maxNamed : Nat := 16384
def maxOpenDays : Nat := 4096
def maxObs : Nat := 16384
def maxDemotions : Nat := 4096
def maxHeaders : Nat := 65536
def maxWakes : Nat := 4096
def maxTags : Nat := 89
def maxUnknownTags : Nat := 64
def maxTagChars : Nat := 128
def maxSettled : Nat := 1024
def maxWarnings : Nat := 256

/-- `a` before `b`, for each consecutive pair: a list strictly ascending in `lt` (a `foldl`). -/
def ascending {α : Type} (lt : α → α → Bool) (l : List α) : Bool :=
  (l.foldl (fun (acc : Bool × Option α) x => (acc.1 && acc.2.all (fun a => lt a x), some x)) (true, none)).1

/-- The lexicographic order of pairs. -/
def lexLt {α β : Type} [DecidableEq α] (lt₁ : α → α → Bool) (lt₂ : β → β → Bool) (a b : α × β) : Bool :=
  lt₁ a.1 b.1 || (decide (a.1 = b.1) && lt₂ a.2 b.2)

/-- `none` first, then `some` by `lt`. -/
def optLt {α : Type} (lt : α → α → Bool) : Option α → Option α → Bool
  | none, some _ => true
  | some a, some b => lt a b
  | _, _ => false

def natLt (a b : Nat) : Bool := decide (a < b)

/-- The first refusal of a list of checks. -/
def check (b : Bool) (f : CkField) : Option CkField := if b then none else some f

/-- Read one positional field. -/
def pos {α : Type} (c : Codec α) (f : CkField) : List JVal → Except CkErr (α × List JVal)
  | x :: xs =>
    match c.dec x with
    | some a => .ok (a, xs)
    | none => .error (.badCkpt f)
  | [] => .error (.badCkpt f)

theorem pos_enc {α : Type} (c : Codec α) (f : CkField) (a : α) (xs : List JVal) :
    pos c f (c.enc a :: xs) = .ok (a, xs) := by
  simp [pos, c.rt]

/-- Read one keyed field: the next pair must carry key `k` (the checkpoint's keys come in build order). -/
def key {α : Type} (k : List Char) (c : Codec α) (f : CkField) :
    List (List Char × JVal) → Except CkErr (α × List (List Char × JVal))
  | (k', x) :: kvs =>
    if k' = k then
      match c.dec x with
      | some a => .ok (a, kvs)
      | none => .error (.badCkpt f)
    else .error (.badCkpt f)
  | [] => .error (.badCkpt f)

theorem key_enc {α : Type} (k : List Char) (c : Codec α) (f : CkField) (a : α) (kvs : List (List Char × JVal)) :
    key k c f ((k, c.enc a) :: kvs) = .ok (a, kvs) := by
  simp [key, c.rt]

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem err_bind {ε α β : Type} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = .error e := rfl

theorem key_ne {α : Type} {k k' : List Char} (c : Codec α) (f : CkField) (h : k' ≠ k) (x : JVal)
    (kvs : List (List Char × JVal)) : key k c f ((k', x) :: kvs) = .error (.badCkpt f) := by
  simp [key, h]

/-! ### Day records and open days -/

abbrev cOptDayAcc : Codec (Option DayAcc) := cOpt cDayAcc cDayAcc_nonnull
abbrev cOptSeam : Codec (Option SeamAcc) := cOpt cSeamAcc cSeamAcc_nonnull
abbrev cEnergies : Codec (List EnergyObs) := cList maxObs cEnergyObs
abbrev cDurations : Codec (List DurationObs) := cList maxObs cDurationObs
abbrev cInterrupts : Codec (List Interruption) := cList maxList cInterruption
abbrev cDemotions : Codec (List Demotion) := cList maxDemotions cDemotion
abbrev cCloses : Codec (List CloseRec) := cList maxList cCloseRec
abbrev cHeaders : Codec (List Header) := cList maxHeaders cHeaderRec

/-- The first bound a day's readings break (§10.4's per-record bounds, every string ≤ 65,536). -/
def dayFault (acc : Option DayAcc) (seam : Option SeamAcc) (en : List EnergyObs) (du : List DurationObs)
    (it : List Interruption) (de : List Demotion) (cl : List CloseRec) (hd : List Header) : Option CkField :=
  check (cOptDayAcc.ok acc) .record <|> check (cOptSeam.ok seam) .seam <|> check (cEnergies.ok en) .energy
    <|> check (cDurations.ok du) .durations <|> check (cInterrupts.ok it) .interrupts
    <|> check (cDemotions.ok de) .demotions <|> check (cCloses.ok cl) .closes <|> check (cHeaders.ok hd) .headers

def DayRecord.fault (r : DayRecord) : Option CkField :=
  dayFault r.record r.seam r.energy r.durations r.interrupts r.demotions r.closes r.headers

def DayRecord.wf (r : DayRecord) : Bool := r.fault.isNone

/-- **A day record**: `[day, record, seam, energy, durations, interrupts, demotions, closes, headers]`. -/
def emitDayRecord (r : DayRecord) : JVal :=
  .arr [cNat.enc r.day, cOptDayAcc.enc r.record, cOptSeam.enc r.seam, cEnergies.enc r.energy,
        cDurations.enc r.durations, cInterrupts.enc r.interrupts, cDemotions.enc r.demotions, cCloses.enc r.closes,
        cHeaders.enc r.headers]

def readDayFields (xs : List JVal) : Except CkErr DayRecord := do
  let (day, xs) ← pos cNat .day xs
  let (record, xs) ← pos cOptDayAcc .record xs
  let (seam, xs) ← pos cOptSeam .seam xs
  let (energy, xs) ← pos cEnergies .energy xs
  let (durations, xs) ← pos cDurations .durations xs
  let (interrupts, xs) ← pos cInterrupts .interrupts xs
  let (demotions, xs) ← pos cDemotions .demotions xs
  let (closes, xs) ← pos cCloses .closes xs
  let (headers, xs) ← pos cHeaders .headers xs
  match xs with
  | [] => pure ⟨day, record, seam, energy, durations, interrupts, demotions, closes, headers⟩
  | _ => throw (.badCkpt .shape)

/-- **The smart decoder of a day record** (R10): field by field, then every bound (`DayRecord.fault`). -/
def readDayRecord (j : JVal) : Except CkErr DayRecord :=
  match j with
  | .arr xs =>
    match readDayFields xs with
    | .ok r =>
      match r.fault with
      | some f => .error (.badCkpt f)
      | none => .ok r
    | .error e => .error e
  | _ => .error (.badCkpt .shape)

theorem readDayFields_emit (r : DayRecord) :
    readDayFields [cNat.enc r.day, cOptDayAcc.enc r.record, cOptSeam.enc r.seam, cEnergies.enc r.energy,
        cDurations.enc r.durations, cInterrupts.enc r.interrupts, cDemotions.enc r.demotions, cCloses.enc r.closes,
        cHeaders.enc r.headers] = .ok r := by
  simp only [readDayFields, pos_enc, ok_bind]
  rfl

/-- **Law 10, day records: a record the kernel emits reads back as itself** — for every record within §10.4's
bounds. -/
theorem readDayRecord_emitDayRecord (d : DayRecord) (h : d.wf = true) : readDayRecord (emitDayRecord d) = .ok d := by
  have hf : d.fault = none := by simpa [DayRecord.wf] using h
  simp only [readDayRecord, emitDayRecord, readDayFields_emit, hf]

/-- **The decoder is smart**: whatever it returns is within the bounds. -/
theorem readDayRecord_wf (j : JVal) (d : DayRecord) (h : readDayRecord j = .ok d) : d.wf = true := by
  unfold readDayRecord at h
  split at h
  · split at h
    · split at h
      · exact absurd h (by simp)
      · rename_i r _ hf; simp only [Except.ok.injEq] at h; subst h; simp [DayRecord.wf, hf]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Both directions (§5.8): the round trip holds exactly for records within the bounds. -/
theorem readDayRecord_emitDayRecord_iff (d : DayRecord) : readDayRecord (emitDayRecord d) = .ok d ↔ d.wf = true :=
  ⟨readDayRecord_wf _ d, readDayRecord_emitDayRecord d⟩

/-- An open day as the checkpoint holds it: the day record's shape. -/
def cOpenDay : Codec OpenDay :=
  cIso (cTuple <| tCons cNat <| tCons cOptDayAcc <| tCons cOptSeam <| tCons cEnergies <| tCons cDurations
      <| tCons cInterrupts <| tCons cDemotions <| tCons cCloses <| tCons cHeaders <| tNil)
    (fun o => (o.day, o.acc, o.seam, o.energy, o.durations, o.interrupts, o.demotions, o.closes, o.headers, ()))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.1⟩) (fun _ => rfl)

def OpenDay.fault (o : OpenDay) : Option CkField :=
  dayFault o.acc o.seam o.energy o.durations o.interrupts o.demotions o.closes o.headers

/-! ### Window records -/

abbrev cItemMins : Codec (List (Log.Id × Nat)) := cList maxWindow (cPair cStr cNat)
abbrev cDoneIds : Codec (List Log.Id) := cList maxWindow cStr
abbrev cInsts : Codec (List ((List Char × List Char) × InstRec)) := cList maxWindow (cPair (cPair cStr cStr) cInstRec)

def WindowRecord.fault (w : WindowRecord) : Option CkField :=
  check (cItemMins.ok w.itemMin) .itemMin <|> check (cDoneIds.ok w.doneIds) .doneIds <|> check (cInsts.ok w.inst) .inst

def WindowRecord.wf (w : WindowRecord) : Bool := w.fault.isNone

/-- **A window record**: `[day, [[id, min]…], [id…], [[[item, inst], instance]…]]`. -/
def emitWindowRecord (w : WindowRecord) : JVal :=
  .arr [cNat.enc w.day, cItemMins.enc w.itemMin, cDoneIds.enc w.doneIds, cInsts.enc w.inst]

def readWindowFields (xs : List JVal) : Except CkErr WindowRecord := do
  let (day, xs) ← pos cNat .day xs
  let (itemMin, xs) ← pos cItemMins .itemMin xs
  let (doneIds, xs) ← pos cDoneIds .doneIds xs
  let (inst, xs) ← pos cInsts .inst xs
  match xs with
  | [] => pure ⟨day, itemMin, doneIds, inst⟩
  | _ => throw (.badCkpt .shape)

/-- **The smart decoder of a window record** (R10). -/
def readWindowRecord (j : JVal) : Except CkErr WindowRecord :=
  match j with
  | .arr xs =>
    match readWindowFields xs with
    | .ok w =>
      match w.fault with
      | some f => .error (.badCkpt f)
      | none => .ok w
    | .error e => .error e
  | _ => .error (.badCkpt .shape)

theorem readWindowFields_emit (w : WindowRecord) :
    readWindowFields [cNat.enc w.day, cItemMins.enc w.itemMin, cDoneIds.enc w.doneIds, cInsts.enc w.inst] = .ok w := by
  simp only [readWindowFields, pos_enc, ok_bind]
  rfl

/-- **Law 10, window records.** -/
theorem readWindowRecord_emitWindowRecord (w : WindowRecord) (h : w.wf = true) :
    readWindowRecord (emitWindowRecord w) = .ok w := by
  have hf : w.fault = none := by simpa [WindowRecord.wf] using h
  simp only [readWindowRecord, emitWindowRecord, readWindowFields_emit, hf]

theorem readWindowRecord_wf (j : JVal) (w : WindowRecord) (h : readWindowRecord j = .ok w) : w.wf = true := by
  unfold readWindowRecord at h
  split at h
  · split at h
    · split at h
      · exact absurd h (by simp)
      · rename_i r _ hf; simp only [Except.ok.injEq] at h; subst h; simp [WindowRecord.wf, hf]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem readWindowRecord_emitWindowRecord_iff (w : WindowRecord) :
    readWindowRecord (emitWindowRecord w) = .ok w ↔ w.wf = true :=
  ⟨readWindowRecord_wf _ w, readWindowRecord_emitWindowRecord w⟩

def cWindowRecord : Codec WindowRecord :=
  cIso (cTuple <| tCons cNat <| tCons cItemMins <| tCons cDoneIds <| tCons cInsts <| tNil)
    (fun w => (w.day, w.itemMin, w.doneIds, w.inst, ())) (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1⟩) (fun _ => rfl)

/-! ### The checkpoint -/

abbrev cOptInstant : Codec (Option Cal.Instant) := cOpt cInstant cInstant_nonnull
abbrev cWakes : Codec (List Cal.Instant) := cList maxWakes cInstant
abbrev cSlept : Codec (List (Nat × Nat)) := cList maxWakes (cPair cNat cNat)
abbrev cTagLast : Codec (List (List Char × Nat)) := cList maxTags (cPair cStr cNat)
abbrev cSettled : Codec (List Nat) := cList maxSettled cNat

def cItemAgg : Codec ItemAgg :=
  cIso (cTuple <| tCons cStr <| tCons (cOpt cItemAcc cItemAcc_nonnull) <| tCons cOptAt <| tCons cBool <| tCons cOptNat
      <| tCons cNat <| tNil)
    (fun a => (a.id, a.acc, a.lastDone, a.dropped, a.doneFirst, a.doneCount, ()))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1⟩) (fun _ => rfl)

abbrev cItems : Codec (List ItemAgg) := cList maxItems cItemAgg
abbrev cWindow : Codec (List WindowRecord) := cList maxWindow cWindowRecord
abbrev cInstOther : Codec (List ((List Char × List Char) × InstRec)) := cList maxItems (cPair (cPair cStr cStr) cInstRec)
abbrev cNamed : Codec (List ((List Char × Option Log.Id) × NamedRec)) :=
  cList maxNamed (cPair (cPair cStr cOptStr) cNamedRec)
abbrev cOpenDays : Codec (List OpenDay) := cList maxOpenDays cOpenDay
abbrev cOptLeak : Codec (Option LeakRec) := cOpt cLeakRec cLeakRec_nonnull
abbrev cRWarns : Codec (List RWarn) := cList maxList cRWarn
abbrev cWarnings : Codec (List (Nat × Log.LWarn)) := cList maxWarnings (cPair cNat cLWarn)

def idLt : List Char → List Char → Bool := Log.charsLt

/-- The key order of the instance map, `(item, inst)`. -/
def instKeyLt : (List Char × List Char) → (List Char × List Char) → Bool := lexLt idLt idLt

/-- The key order of the named map, `(name, id?)`. -/
def namedKeyLt : (List Char × Option Log.Id) → (List Char × Option Log.Id) → Bool := lexLt idLt (optLt idLt)

/-- **The first bound a checkpoint breaks**, in key order (§10.4): the version; the zone key; `sleptByDay`, `tagLast`,
`settled`, `items`, `window`, `instOther`, `named` and `openDays` within their lengths and ascending in their keys; every
open day at or after `ledgerDay` and every window date at or after its horizon; every settled line after the cut;
every string within 65,536 characters. -/
def Ckpt.fault (k : Ckpt) : Option CkField :=
  check (k.v == ckptVersion) .v <|>
  check (decide (k.tzKey.length ≤ maxTzKey)) .tzKey <|>
  check (cWakes.ok k.wakes) .wakes <|>
  check (cSlept.ok k.sleptByDay && ascending natLt (k.sleptByDay.map Prod.fst)) .sleptByDay <|>
  check (cTagLast.ok k.tagLast && k.tagLast.all (fun p => decide (p.1.length ≤ maxTagChars))
      && decide ((k.tagLast.filter (fun p => !Log.isKnownTag p.1)).length ≤ maxUnknownTags)
      && ascending idLt (k.tagLast.map Prod.fst)) .tagLast <|>
  check (cSettled.ok k.settled && k.settled.all (fun n => decide (k.cut < n)) && ascending natLt k.settled) .settled <|>
  check (cMachine.ok k.machine) .machine <|>
  check (cItems.ok k.items && ascending idLt (k.items.map ItemAgg.id)) .items <|>
  check (cWindow.ok k.window && k.window.all (fun w => decide (horizonOf k.ledgerDay ≤ w.day))
      && ascending natLt (k.window.map WindowRecord.day)) .window <|>
  check (cInstOther.ok k.instOther && ascending instKeyLt (k.instOther.map Prod.fst)) .instOther <|>
  check (cNamed.ok k.named && ascending namedKeyLt (k.named.map Prod.fst)) .named <|>
  check (cOpenDays.ok k.openDays && k.openDays.all (fun o => decide (k.ledgerDay ≤ o.day))
      && ascending natLt (k.openDays.map OpenDay.day)) .openDays <|>
  check (cOptLeak.ok k.longestLeak) .longestLeak <|>
  check (cRWarns.ok k.rwarns) .rwarns <|>
  check (cWarnings.ok k.warnings) .warnings

/-- **A checkpoint within every bound** (§9.2's `Ckpt.wf`). -/
def Ckpt.wf (k : Ckpt) : Bool := k.fault.isNone

def kV : List Char := ['v']
def kTzKey : List Char := ['t','z','K','e','y']
def kCut : List Char := ['c','u','t']
def kLedgerDay : List Char := ['l','e','d','g','e','r','D','a','y']
def kResealDay : List Char := ['r','e','s','e','a','l','D','a','y']
def kMaxT : List Char := ['m','a','x','T']
def kFutureFloor : List Char := ['f','u','t','u','r','e','F','l','o','o','r']
def kWakes : List Char := ['w','a','k','e','s']
def kSleptByDay : List Char := ['s','l','e','p','t','B','y','D','a','y']
def kTagLast : List Char := ['t','a','g','L','a','s','t']
def kTagOverflow : List Char := ['t','a','g','O','v','e','r','f','l','o','w']
def kSettled : List Char := ['s','e','t','t','l','e','d']
def kMachine : List Char := ['m','a','c','h','i','n','e']
def kItems : List Char := ['i','t','e','m','s']
def kWindow : List Char := ['w','i','n','d','o','w']
def kInstOther : List Char := ['i','n','s','t','O','t','h','e','r']
def kNamed : List Char := ['n','a','m','e','d']
def kOpenDays : List Char := ['o','p','e','n','D','a','y','s']
def kLastDay : List Char := ['l','a','s','t','D','a','y']
def kLastEff : List Char := ['l','a','s','t','E','f','f']
def kEntryCount : List Char := ['e','n','t','r','y','C','o','u','n','t']
def kUnknown : List Char := ['u','n','k','n','o','w','n']
def kLongestLeak : List Char := ['l','o','n','g','e','s','t','L','e','a','k']
def kRWarns : List Char := ['r','e','p','l','a','y','W','a','r','n','i','n','g','s']
def kWarnings : List Char := ['w','a','r','n','i','n','g','s']
def kWarnOverflow : List Char := ['w','a','r','n','O','v','e','r','f','l','o','w']

/-- The checkpoint's pairs, in build order. -/
def ckptPairs (k : Ckpt) : List (List Char × JVal) :=
  [(kV, cNat.enc k.v), (kTzKey, cStr.enc k.tzKey), (kCut, cNat.enc k.cut), (kLedgerDay, cNat.enc k.ledgerDay),
   (kResealDay, cNat.enc k.resealDay), (kMaxT, cOptInstant.enc k.maxT), (kFutureFloor, cOptInstant.enc k.futureFloor),
   (kWakes, cWakes.enc k.wakes), (kSleptByDay, cSlept.enc k.sleptByDay), (kTagLast, cTagLast.enc k.tagLast),
   (kTagOverflow, cBool.enc k.tagOverflow), (kSettled, cSettled.enc k.settled), (kMachine, cMachine.enc k.machine),
   (kItems, cItems.enc k.items), (kWindow, cWindow.enc k.window), (kInstOther, cInstOther.enc k.instOther),
   (kNamed, cNamed.enc k.named), (kOpenDays, cOpenDays.enc k.openDays), (kLastDay, cOptNat.enc k.lastDay),
   (kLastEff, cOptAt.enc k.lastEff), (kEntryCount, cNat.enc k.entryCount), (kUnknown, cNat.enc k.unknown),
   (kLongestLeak, cOptLeak.enc k.longestLeak), (kRWarns, cRWarns.enc k.rwarns), (kWarnings, cWarnings.enc k.warnings),
   (kWarnOverflow, cNat.enc k.warnOverflow)]

/-- **The checkpoint on the wire** (§9.2): an object, keys in build order; Rust stores it verbatim and never looks
inside. -/
def emitCkpt (k : Ckpt) : JVal := .obj (ckptPairs k)

def readCkptFields (kvs : List (List Char × JVal)) : Except CkErr Ckpt := do
  let (v, kvs) ← key kV cNat .v kvs
  let (tzKey, kvs) ← key kTzKey cStr .tzKey kvs
  let (cut, kvs) ← key kCut cNat .cut kvs
  let (ledgerDay, kvs) ← key kLedgerDay cNat .ledgerDay kvs
  let (resealDay, kvs) ← key kResealDay cNat .resealDay kvs
  let (maxT, kvs) ← key kMaxT cOptInstant .maxT kvs
  let (futureFloor, kvs) ← key kFutureFloor cOptInstant .futureFloor kvs
  let (wakes, kvs) ← key kWakes cWakes .wakes kvs
  let (sleptByDay, kvs) ← key kSleptByDay cSlept .sleptByDay kvs
  let (tagLast, kvs) ← key kTagLast cTagLast .tagLast kvs
  let (tagOverflow, kvs) ← key kTagOverflow cBool .tagOverflow kvs
  let (settled, kvs) ← key kSettled cSettled .settled kvs
  let (machine, kvs) ← key kMachine cMachine .machine kvs
  let (items, kvs) ← key kItems cItems .items kvs
  let (window, kvs) ← key kWindow cWindow .window kvs
  let (instOther, kvs) ← key kInstOther cInstOther .instOther kvs
  let (named, kvs) ← key kNamed cNamed .named kvs
  let (openDays, kvs) ← key kOpenDays cOpenDays .openDays kvs
  let (lastDay, kvs) ← key kLastDay cOptNat .lastDay kvs
  let (lastEff, kvs) ← key kLastEff cOptAt .lastEff kvs
  let (entryCount, kvs) ← key kEntryCount cNat .entryCount kvs
  let (unknown, kvs) ← key kUnknown cNat .unknown kvs
  let (longestLeak, kvs) ← key kLongestLeak cOptLeak .longestLeak kvs
  let (rwarns, kvs) ← key kRWarns cRWarns .rwarns kvs
  let (warnings, kvs) ← key kWarnings cWarnings .warnings kvs
  let (warnOverflow, kvs) ← key kWarnOverflow cNat .warnOverflow kvs
  match kvs with
  | [] => pure ⟨v, tzKey, cut, ledgerDay, resealDay, maxT, futureFloor, wakes, sleptByDay, tagLast, tagOverflow, settled,
      machine, items, window, instOther, named, openDays, lastDay, lastEff, entryCount, unknown, longestLeak, rwarns,
      warnings, warnOverflow⟩
  | _ => throw (.badCkpt .shape)

/-- **The smart decoder of a checkpoint** (R10): key by key, in build order, refusing `badCkpt <field>` at the first key
that is absent, out of order or of the wrong shape; then every bound (`Ckpt.fault`).  A missing field is never
defaulted. -/
def readCkpt (j : JVal) : Except CkErr Ckpt :=
  match j with
  | .obj kvs =>
    match readCkptFields kvs with
    | .ok k =>
      match k.fault with
      | some f => .error (.badCkpt f)
      | none => .ok k
    | .error e => .error e
  | _ => .error (.badCkpt .shape)

theorem readCkptFields_emit (k : Ckpt) : readCkptFields (ckptPairs k) = .ok k := by
  simp only [readCkptFields, ckptPairs, key_enc, ok_bind]
  rfl

/-- **Law 10, the checkpoint: a checkpoint the kernel emits reads back as itself**, for every checkpoint within §10.4's
bounds (the emission refuses `counterOverflow` rather than write one outside them, W3). -/
theorem readCkpt_emitCkpt (k : Ckpt) (h : k.wf = true) : readCkpt (emitCkpt k) = .ok k := by
  have hf : k.fault = none := by simpa [Ckpt.wf] using h
  simp only [readCkpt, emitCkpt, readCkptFields_emit, hf]

/-- **The decoder is smart**: whatever it returns is within every bound. -/
theorem readCkpt_wf (j : JVal) (k : Ckpt) (h : readCkpt j = .ok k) : k.wf = true := by
  unfold readCkpt at h
  split at h
  · split at h
    · split at h
      · exact absurd h (by simp)
      · rename_i r _ hf; simp only [Except.ok.injEq] at h; subst h; simp [Ckpt.wf, hf]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Both directions (§5.8). -/
theorem readCkpt_emitCkpt_iff (k : Ckpt) : readCkpt (emitCkpt k) = .ok k ↔ k.wf = true :=
  ⟨readCkpt_wf _ k, readCkpt_emitCkpt k⟩

/-- **A missing field is refused by name, never defaulted** (cheat 151's control): a checkpoint whose `ledgerDay` pair
is gone is refused `badCkpt ledgerDay`, whatever it holds. -/
theorem readCkpt_refuses_a_checkpoint_without_its_ledgerDay (k : Ckpt) :
    readCkpt (.obj ((ckptPairs k).filter (fun p => !(p.1 == kLedgerDay)))) = .error (.badCkpt .ledgerDay) := by
  have hl : (ckptPairs k).filter (fun p => !(p.1 == kLedgerDay))
      = (kV, cNat.enc k.v) :: (kTzKey, cStr.enc k.tzKey) :: (kCut, cNat.enc k.cut)
        :: (kResealDay, cNat.enc k.resealDay) :: ((ckptPairs k).drop 5) := rfl
  rw [hl]
  simp only [readCkpt, readCkptFields, key_enc, ok_bind, key_ne cNat .ledgerDay (show kResealDay ≠ kLedgerDay by decide),
    err_bind]



/-- **The query of the window laws**: `Replay.Q` (carried note 3). -/
abbrev Q := Replay.Q
abbrev DayQ := Replay.DayQ
abbrev WinQ := Replay.WinQ

/-- **The replay of lines** (carried note 3): `Replay.replayDoc` over the entries the lines read as. -/
def replayLines (z : Cal.Tz) (ls : List Log.Line) : Doc := Replay.replayDoc z (Log.lineEntries ls)

/-- A query at or above the horizons: a day's at `d ≥ L`, a window date's at `d ≥ H`, and every all-time one. -/
def Q.atOrAbove (q : Q) (L H : Nat) : Bool :=
  match q with
  | .day d _ => decide (L ≤ d)
  | .win d _ => decide (H ≤ d)
  | _ => true

/-! ### Canonical lists: every map of the checkpoint sorted by its key, one pair a key -/

/-- Insert into a list ascending in `lt`, once. -/
def insUniq {α : Type} (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else if lt y x then y :: insUniq lt x ys else y :: ys

/-- The distinct elements of a list, ascending (specification only: each insertion scans). -/
def canon {α : Type} (lt : α → α → Bool) (l : List α) : List α := l.foldl (fun acc x => insUniq lt x acc) []

/-! ### The fold of the folded lines, under the call-wide mask -/

/-- **The folded survivors**: the entries of `es` the mask over `es ++ er` keeps (an undo of `er` may cancel one). -/
def foldedSurvivors (es er : List Entry) : List Entry :=
  (es.zipIdx.filter (fun p => !Replay.cancelledAt (es ++ er) p.2)).map Prod.fst

/-- The day index of the folded survivors. -/
def foldedIndex (z : Cal.Tz) (es er : List Entry) : List Cal.Instant :=
  Replay.keptWakes z (Replay.wakeInstants (foldedSurvivors es er))

/-- **The state after the folded lines** (before `finish`): the replay's fold over the folded survivors, on their day
index and `slept_by_day`, its maps sized for `es`. -/
def foldedState (z : Cal.Tz) (es er : List Entry) : State :=
  let sv := foldedSurvivors es er
  let kw := foldedIndex z es er
  sv.foldl (Replay.step z kw (Replay.sleptByDay z kw sv)) (State.init es.length)

/-- **Every folded entry's header**: its day on the folded index, and the call-wide mask bit. -/
def foldedHeaders (z : Cal.Tz) (es er : List Entry) : List (Nat × HeaderRec) :=
  es.zipIdx.map (fun p => (Replay.dayOf z (foldedIndex z es er) p.1.t.val,
    HeaderRec.of p.1 (Replay.cancelledAt (es ++ er) p.2)))

/-! ### The readings of a state, grouped by where they live -/

/-- The days with a reading: a record, a seam, an observation, an interruption, a demotion, a close or a header. -/
def dayKeys (st : State) (hs : List (Nat × HeaderRec)) : List Nat :=
  canon natLt (st.days.pairs.map Prod.fst ++ st.seams.pairs.map Prod.fst ++ st.energy.map (·.day)
    ++ st.durations.map (·.day) ++ st.interrupts.map (·.day) ++ st.demotions.map Prod.fst ++ st.closes.map Prod.fst
    ++ hs.map Prod.fst)

/-- **One day of a state**, as the fold leaves it. -/
def openDayOf (st : State) (hs : List (Nat × HeaderRec)) (d : Nat) : OpenDay :=
  ⟨d, st.days.get d, st.seams.get d, (st.energy.filter (fun o => decide (o.day = d))).reverse,
   (st.durations.filter (fun o => decide (o.day = d))).reverse,
   (st.interrupts.filter (fun r => decide (r.day = d))).reverse,
   ((st.demotions.filter (fun p => decide (p.1 = d))).map Prod.snd).reverse,
   ((st.closes.filter (fun p => decide (p.1 = d))).map Prod.snd).reverse,
   (hs.filter (fun p => decide (p.1 = d))).map Prod.snd⟩

/-- The days of a state in `[lo, hi)`. -/
def daysIn (st : State) (hs : List (Nat × HeaderRec)) (lo hi : Nat) : List OpenDay :=
  ((dayKeys st hs).filter (fun d => decide (lo ≤ d ∧ d < hi))).map (openDayOf st hs)

/-- The days of a state at or after `lo`. -/
def daysFrom (st : State) (hs : List (Nat × HeaderRec)) (lo : Nat) : List OpenDay :=
  ((dayKeys st hs).filter (fun d => decide (lo ≤ d))).map (openDayOf st hs)

/-- The machine's pending start observation, if it is on day `d`. -/
def pendingOn (m : Machine) (d : Nat) : List EnergyObs :=
  ((m.block.bind (·.obs)).filter (fun o => decide (o.day = d))).toList

/-- **A day finished** (fork `Machine::finish` on one day): the record and seam finished, the pending start observation
emitted, and the observations by line. -/
def OpenDay.finish (m : Machine) (o : OpenDay) : DayRecord :=
  ⟨o.day, o.acc.map DayAcc.finish, o.seam.map (fun a => { a with idleMarks := a.idleMarks.reverse }),
   Replay.sortObs (o.energy ++ pendingOn m o.day), o.durations, o.interrupts, o.demotions, o.closes, o.headers⟩

/-- The dates with a window fact: an item's minutes, a done date, an instance whose `inst` names the date. -/
def winKeys (st : State) : List Nat :=
  canon natLt (st.itemDays.pairs.map (·.1.1) ++ st.doneDates.pairs.map (·.1.1)
    ++ st.instances.pairs.filterMap (fun p => Log.instDate? p.1.2))

/-- **One date's window facts** of a state, each list sorted by its key and read through `get`. -/
def windowOf (st : State) (d : Nat) : WindowRecord :=
  ⟨d, (canon idLt ((st.itemDays.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2))).filterMap
        (fun i => (st.itemDays.get (d, i)).map (fun m => (i, m))),
   canon idLt ((st.doneDates.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2)),
   (canon instKeyLt ((st.instances.pairs.filter (fun p => decide (Log.instDate? p.1.2 = some d))).map Prod.fst)).filterMap
        (fun key => (st.instances.get key).map (fun r => (key, r)))⟩

def windowsIn (st : State) (lo hi : Nat) : List WindowRecord :=
  ((winKeys st).filter (fun d => decide (lo ≤ d ∧ d < hi))).map (windowOf st)

def windowsFrom (st : State) (lo : Nat) : List WindowRecord :=
  ((winKeys st).filter (fun d => decide (lo ≤ d))).map (windowOf st)

/-- **One item's all-time facts** of a state, read as `factsView` reads them. -/
def itemAggOf (st : State) (i : Log.Id) : ItemAgg :=
  let ds := (st.doneDates.pairs.filter (fun p => decide (p.1.2 = i))).map (·.1.1)
  ⟨i, st.items.get i, st.lastDone.get i, (st.dropped.get i).isSome, Replay.minDay? ds, ds.length⟩

def itemIds (st : State) : List Log.Id :=
  canon idLt (st.items.pairs.map Prod.fst ++ st.lastDone.pairs.map Prod.fst ++ st.dropped.pairs.map Prod.fst
    ++ st.doneDates.pairs.map (·.1.2))

def instOtherOf (st : State) : List ((List Char × List Char) × InstRec) :=
  (canon instKeyLt ((st.instances.pairs.filter (fun p => (Log.instDate? p.1.2).isNone)).map Prod.fst)).filterMap
    (fun key => (st.instances.get key).map (fun r => (key, r)))

def namedOf (st : State) : List ((List Char × Option Log.Id) × NamedRec) :=
  (canon namedKeyLt (st.named.pairs.map Prod.fst)).filterMap (fun key => (st.named.get key).map (fun r => (key, r)))

/-! ### The checkpoint's bookkeeping -/

/-- **Future-dated** (§9.4): the entry's local date is more than two days after `T`. -/
def futureDated (z : Cal.Tz) (T : Nat) (e : Entry) : Bool := decide (T + 2 < Cal.localDate z e.t.val)

def maxInstant? (l : List Cal.Instant) : Option Cal.Instant :=
  l.foldl (fun acc t => some (match acc with | none => t | some a => if a < t then t else a)) none

def minInstant? (l : List Cal.Instant) : Option Cal.Instant :=
  l.foldl (fun acc t => some (match acc with | none => t | some a => if t < a then t else a)) none

/-- The kept wakes the checkpoint stores (§9.2): the last dated `< L − 2`, then every one dated `≥ L − 2`. -/
def storedWakes (z : Cal.Tz) (L : Nat) (kw : List Cal.Instant) : List Cal.Instant :=
  (kw.filter (fun w => decide (Cal.localDate z w < L - 2))).getLast?.toList
    ++ kw.filter (fun w => decide (L - 2 ≤ Cal.localDate z w))

/-- Fork `slept_by_day` for days `≥ L`, one pair a day (its first in file order, as `KMap.get` reads it). -/
def storedSlept (sl : List (Nat × Nat)) (L : Nat) : List (Nat × Nat) :=
  ((canon natLt (sl.map Prod.fst)).filter (fun d => decide (L ≤ d))).filterMap
    (fun d => (Replay.KMap.get sl d).map (fun s => (d, s)))

/-- The latest line per tag of the folded survivors, sorted by tag, with the unknown tags bounded (§7.4): kept when at
most 128 characters, the first 64 in tag order. -/
def tagLines (sv : List Entry) : List (List Char × Nat) :=
  (canon idLt (sv.map (·.ev.tag))).map (fun t => (t, (sv.filter (fun e => decide (e.ev.tag = t))).foldl (fun _ e => e.line) 0))

def keptTags (sv : List Entry) : List (List Char × Nat) :=
  let all := tagLines sv
  let unknownKept := ((all.filter (fun p => !Log.isKnownTag p.1 && decide (p.1.length ≤ maxTagChars))).take maxUnknownTags)
  all.filter (fun p => Log.isKnownTag p.1 || unknownKept.contains p)

/-- One step of the mask that also records each undo's target position (the stack's first match), or none. -/
def targetStep (acc : List (Entry × Nat) × List (Nat × Option Nat)) (p : Entry × Nat) :
    List (Entry × Nat) × List (Nat × Option Nat) :=
  match p.1.ev with
  | .undo of_ id => (acc.1.eraseP (fun q => Replay.«matches» of_ id q.1),
      (p.2, (acc.1.find? (fun q => Replay.«matches» of_ id q.1)).map Prod.snd) :: acc.2)
  | _ => (p :: acc.1, acc.2)

/-- Every undo's position and its target's, in file order. -/
def undoTargets (es : List Entry) : List (Nat × Option Nat) := (es.zipIdx.foldl targetStep ([], [])).2.reverse

/-- **The settled undos** (§7.4): the lines of the undos of `er` whose call-wide target is in `es` or absent. -/
def settledOf (es er : List Entry) : List Nat :=
  ((undoTargets (es ++ er)).filter (fun p => decide (es.length ≤ p.1) && p.2.all (fun t => decide (t < es.length)))).filterMap
    (fun p => ((es ++ er)[p.1]?).map (·.line))

/-! ### The specification checkpoint, its records and its answer -/

/-- **The checkpoint of folded entries** `es` (of lines `1..cut`, with line warnings `ws`), sealed at `T₀` with ledger
day `L`, knowing the unfolded entries `er`. -/
def ckptOfEntries (z : Cal.Tz) (T₀ L cut : Nat) (es er : List Entry) (ws : List (Nat × Log.LWarn)) : Ckpt :=
  let st := foldedState z es er
  let hs := foldedHeaders z es er
  let sv := foldedSurvivors es er
  let kw := foldedIndex z es er
  let tags := tagLines sv
  ⟨ckptVersion, z.val.key, cut, L, T₀,
   maxInstant? ((es.filter (fun e => !futureDated z T₀ e)).map (·.t.val)),
   minInstant? ((es.filter (futureDated z T₀)).map (·.t.val)),
   storedWakes z L kw, storedSlept (Replay.sleptByDay z kw sv) L, keptTags sv, decide ((keptTags sv).length < tags.length),
   settledOf es er, st.machine, (itemIds st).map (itemAggOf st), windowsFrom st (horizonOf L), instOtherOf st,
   namedOf st, daysFrom st hs L, Replay.maxDay? (st.days.pairs.map Prod.fst), st.global.lastEffective, es.length,
   st.unknown, st.longestLeak, st.rwarns.reverse, ws.take maxWarnings, ws.length - maxWarnings⟩

/-- **The checkpoint of lines** `ls`, sealed at `T₀` with ledger day `L`, knowing the unfolded lines `r` (§15).  A
specification: `resume` builds checkpoints, and `reseal_is_seal` (W2) says they are these. -/
def ckptOf (z : Cal.Tz) (T₀ L : Nat) (ls r : List Log.Line) : Ckpt :=
  ckptOfEntries z T₀ L ls.length (Log.lineEntries ls) (Log.lineEntries r) (Log.lineWarnings ls)

/-- The day records of entries in `[lo, hi)`: every day with a reading, finished. -/
def dayRecordsOfEntries (z : Cal.Tz) (lo hi : Nat) (es : List Entry) : List DayRecord :=
  (daysIn (foldedState z es []) (foldedHeaders z es []) lo hi).map (OpenDay.finish (foldedState z es []).machine)

def windowRecordsOfEntries (z : Cal.Tz) (lo hi : Nat) (es : List Entry) : List WindowRecord :=
  windowsIn (foldedState z es []) lo hi

/-- **The day records of `[lo, hi)`** of lines `ls` (§9.4): every day in the range with a reading. -/
def dayRecordsBetween (z : Cal.Tz) (_T lo hi : Nat) (ls : List Log.Line) : List DayRecord :=
  dayRecordsOfEntries z lo hi (Log.lineEntries ls)

/-- **The window records of `[lo, hi)`** of lines `ls`. -/
def windowRecordsBetween (z : Cal.Tz) (_T lo hi : Nat) (ls : List Log.Line) : List WindowRecord :=
  windowRecordsOfEntries z lo hi (Log.lineEntries ls)

/-- **The day records below the ledger day `L`**: what Rust stored. -/
def dayRecordsBelow (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) : List DayRecord := dayRecordsBetween z T₀ 0 L ls

/-- **The window records below the horizon of `L`.** -/
def windowRecordsBelow (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) : List WindowRecord :=
  windowRecordsBetween z T₀ 0 (horizonOf L) ls

/-- An item's facts, finished. -/
def ItemAgg.finish (a : ItemAgg) : ItemAgg := { a with acc := a.acc.map ItemAcc.finish }

/-- **The answer of a checkpoint** (§11.1's `Hot`): its all-time facts, window and open days, finished as the replay
finishes them. -/
def answer (k : Ckpt) : Seal.Answer :=
  ⟨k.ledgerDay, horizonOf k.ledgerDay, k.items.map ItemAgg.finish, k.window, k.instOther, k.named,
   k.openDays.map (OpenDay.finish k.machine),
   k.machine.block.map (fun b => ⟨b.id, b.started, b.workedMin, b.since, b.paused⟩),
   k.machine.interrupt.map (fun i => ⟨0, some i.1, none, i.2.1, i.2.2, 0, []⟩),
   k.lastDay, k.lastEff, k.entryCount, k.unknown, k.longestLeak, k.rwarns, k.warnings, k.warnOverflow⟩

/-- The answer's observations (law 11): each open day's, energy then durations. -/
def DayRecord.obs (r : DayRecord) : List Obs := r.energy.map Obs.energy ++ r.durations.map Obs.duration

def Answer.obs (v : Seal.Answer) : List Obs := v.days.flatMap DayRecord.obs

/-- **One day's reading** from its record, if it has one (a day without a record reads empty, as the replay does). -/
def dayRead (r : Option DayRecord) : DayQ → Replay.Answer
  | .record => .dayRecord (r.bind (·.record))
  | .seam => .seam (r.bind (·.seam))
  | .energy => .energy ((r.map (·.energy)).getD [])
  | .durations => .durations ((r.map (·.durations)).getD [])
  | .interrupts => .interrupts ((r.map (·.interrupts)).getD [])
  | .demotions => .demotions ((r.map (·.demotions)).getD [])
  | .closes => .closes ((r.map (·.closes)).getD [])
  | .headers => .headers ((r.map (·.headers)).getD [])

/-- **One date's window reading** from its record. -/
def winRead (w : Option WindowRecord) (d : Nat) : WinQ → Replay.Answer
  | .itemMin i => .minutes ((w.bind (fun w => w.itemMin.find? (fun p => decide (p.1 = i)))).map Prod.snd)
  | .done i => .bool ((w.map (fun w => w.doneIds.contains i)).getD false)
  | .inst item inst => .inst (if Log.instDate? inst = some d then
      (w.bind (fun w => w.inst.find? (fun p => decide (p.1 = (item, inst))))).map Prod.snd else none)

def findDay (rs : List DayRecord) (d : Nat) : Option DayRecord := rs.find? (fun r => decide (r.day = d))
def findWin (ws : List WindowRecord) (d : Nat) : Option WindowRecord := ws.find? (fun w => decide (w.day = d))
def findItem (is : List ItemAgg) (i : Log.Id) : Option ItemAgg := is.find? (fun a => decide (a.id = i))

/-- **A query on the answer**: `none` below its horizons, where the sealed records answer instead. -/
def askAnswer (v : Seal.Answer) : Q → Option Replay.Answer
  | .day d q => if d < v.ledgerDay then none else some (dayRead (findDay v.days d) q)
  | .win d q => if d < v.horizon then none else some (winRead (findWin v.window d) d q)
  | .item i => some (.item ((findItem v.items i).bind (·.acc)))
  | .lastDone i => some (.stamp ((findItem v.items i).bind (·.lastDone)))
  | .doneFirst i => some (.date ((findItem v.items i).bind (·.doneFirst)))
  | .doneCount i => some (.count (((findItem v.items i).map (·.doneCount)).getD 0))
  | .dropped i => some (.bool (((findItem v.items i).map (·.dropped)).getD false))
  | .instOther item inst => some (.inst (if Log.instDate? inst = none then
      (v.instOther.find? (fun p => decide (p.1 = (item, inst)))).map Prod.snd else none))
  | .named name id => some (.named ((v.named.find? (fun p => decide (p.1 = (name, id)))).map Prod.snd))
  | .openBlock => some (.openBlock v.openBlock)
  | .openInterrupt => some (.openInterrupt v.openInterrupt)
  | .lastDay => some (.date v.lastDay)
  | .lastEffective => some (.stamp v.lastEffective)
  | .unknown => some (.count v.unknown)
  | .longestLeak => some (.leak v.longestLeak)
  | .replayWarnings => some (.warnings v.rwarns)
  | .entryCount => some (.count v.entryCount)

/-- A day query on sealed day records. -/
def askDayRecords (rs : List DayRecord) (d : Nat) (q : DayQ) : Replay.Answer := dayRead (findDay rs d) q

/-- A window query on sealed window records. -/
def askWindowRecords (ws : List WindowRecord) (d : Nat) (q : WinQ) : Replay.Answer := winRead (findWin ws d) d q

/-- **The merged reading** (§11.1): the answer at or above its horizons, the sealed records below. -/
def askMerged (ds : List DayRecord) (ws : List WindowRecord) (v : Seal.Answer) (q : Q) : Replay.Answer :=
  match askAnswer v q with
  | some a => a
  | none =>
    match q with
    | .day d dq => askDayRecords ds d dq
    | .win d wq => askWindowRecords ws d wq
    | _ => .lines

/-! ### `sealable`: what every checkpoint `resume` builds satisfies (§9.5, CRIT 3) -/

/-- A key at or above the horizons: a day key at `d ≥ L`, a window key at `d ≥ H`. -/
def keyAtOrAbove (L H : Nat) : Replay.Key → Bool
  | .day d => decide (L ≤ d)
  | .itemDay _ d | .doneDate _ d | .instDate _ _ d => decide (H ≤ d)
  | _ => true

/-- The days the machine can still write (§9.4's `L'` rule): the pending observation's, the last cut's and the open
interruption's. -/
def machineDays (m : Machine) : List Nat :=
  ((m.block.bind (·.obs)).map (·.day)).toList ++ (m.lastCut.map (·.day)).toList ++ (m.interrupt.map (·.2.1)).toList

/-- The effects of the unfolded survivors, stepped after the folded ones on the call-wide index (specification). -/
def unfoldedEffects (z : Cal.Tz) (es er : List Entry) : List Replay.Effect :=
  let sv := foldedSurvivors es er
  let tv := (er.zipIdx es.length).filter (fun p => !Replay.cancelledAt (es ++ er) p.2) |>.map Prod.fst
  let kw := Replay.keptWakes z (Replay.wakeInstants (sv ++ tv))
  let sl := Replay.sleptByDay z kw (sv ++ tv)
  let st := sv.foldl (Replay.step z kw sl) (State.init (es ++ er).length)
  (tv.foldl (fun (acc : State × List (List Replay.Effect)) e =>
    let fx := Replay.effects z kw sl acc.1 e
    (Replay.applyEffects acc.1 fx, fx :: acc.2)) (st, [])).2.reverse.flatten

/-- **Sealable at `L`** over entries: (i) no survivor of the unfolded entries names a day below `L` or a window date
below `horizonOf L`, and no unfolded entry's header is below `L`; (ii) the machine's days are `≥ L`; (iii) what the
unfolded undos cancel changes no record below the horizons. -/
def sealableEntries (z : Cal.Tz) (_T₀ L : Nat) (es er : List Entry) : Bool :=
  (unfoldedEffects z es er).all (fun fx => keyAtOrAbove L (horizonOf L) fx.key)
    && ((Replay.entryHeaders z (es ++ er)).drop es.length).all (fun p => decide (L ≤ p.1))
    && (machineDays (foldedState z es er).machine).all (fun d => decide (L ≤ d))
    && (daysIn (foldedState z es er) (foldedHeaders z es er) 0 L).map (OpenDay.finish (foldedState z es er).machine)
        == dayRecordsOfEntries z 0 L es
    && windowsIn (foldedState z es er) 0 (horizonOf L) == windowRecordsOfEntries z 0 (horizonOf L) es

/-- **Sealable** (§9.5): the hypothesis of every window law on a checkpoint. -/
def sealable (z : Cal.Tz) (T₀ L : Nat) (ls r : List Log.Line) : Bool :=
  sealableEntries z T₀ L (Log.lineEntries ls) (Log.lineEntries r)

/-! ### The empty checkpoint, the meta and the policy -/

/-- **The empty checkpoint** (§9.2): nothing folded, cut 0, ledger day 0. -/
def Ckpt.empty (z : Cal.Tz) : Ckpt :=
  ⟨ckptVersion, z.val.key, 0, 0, 0, none, none, [], [], [], false, [], ⟨none, none, none⟩, [], [], [], [], [], none,
   none, 0, 0, none, [], [], 0⟩

/-- The meta the host reads beside a checkpoint. -/
def Ckpt.meta (k : Ckpt) : Meta := ⟨k.cut, k.ledgerDay, horizonOf k.ledgerDay, k.resealDay, k.maxT, k.futureFloor⟩

/-- The most days a reseal leaves unfolded (§10.4). -/
def maxKeepDays : Nat := 31

def Policy.wf (p : Policy) : Bool := decide (p.keepDays ≤ maxKeepDays) && p.maxLine.all (fun n => decide (n < 1099511627776))

/-- **The smart constructor of a policy** (R10): `keepDays ≤ 31`, `maxLine < 2^40`. -/
def mkPolicy? (keepDays : Nat) (maxLine : Option Nat) : Option { p : Policy // p.wf = true } :=
  if h : (Policy.mk keepDays maxLine).wf = true then some ⟨⟨keepDays, maxLine⟩, h⟩ else none

theorem mkPolicy?_refuses_keepDays_past_31 (k : Nat) (m : Option Nat) (h : maxKeepDays < k) : mkPolicy? k m = none := by
  have hk : decide (k ≤ maxKeepDays) = false := by simp only [decide_eq_false_iff_not]; omega
  unfold mkPolicy?
  simp [Policy.wf, hk]

theorem mkPolicy?_refuses_maxLine_past_2_40 (k n : Nat) (h : 1099511627776 ≤ n) : mkPolicy? k (some n) = none := by
  have hn : decide (n < 1099511627776) = false := by simp only [decide_eq_false_iff_not]; omega
  unfold mkPolicy?
  simp [Policy.wf, hn]

/-! ## What W1 proves of its definitions -/

/-! ### The horizon (§9.1) -/

/-- The horizon is never after its ledger day. -/
theorem horizonOf_le (L : Nat) : horizonOf L ≤ L := by
  unfold horizonOf autoCloseCatchup; omega

/-- **`L − H ≤ 30`** (§9.1): the window keeps at most a month of dates below the ledger day. -/
theorem the_horizon_is_at_most_thirty_days_back (L : Nat) : L ≤ horizonOf L + 30 := by
  have hv := Cal.ofDay_valid L
  rw [Cal.valid_iff] at hv
  obtain ⟨_, _, hm, hd1, hd⟩ := hv
  have h31 := Cal.monthLen_le_31 (Cal.isLeap (Cal.ofDay L).year) (show (Cal.ofDay L).month < 13 by omega)
  unfold horizonOf Cal.monthStart Cal.isoMonday autoCloseCatchup
  omega

/-! ### The folded state of a log with nothing unfolded is the replay's -/

/-- **The replay is the finished fold** of `foldedState` with nothing unfolded: one fold, two readings. -/
theorem replay_eq_finish_foldedState (z : Cal.Tz) (es : List Entry) :
    Replay.replay z es = Replay.finish (foldedState z es []) := by
  unfold Replay.replay foldedState foldedIndex foldedSurvivors Replay.dayIndexOf
  rw [List.append_nil, ← Replay.survivors_are_the_uncancelled_entries]

/-- **Every entry's header is the fold's**, with nothing unfolded. -/
theorem entryHeaders_eq_foldedHeaders (z : Cal.Tz) (es : List Entry) :
    Replay.entryHeaders z es = foldedHeaders z es [] := by
  unfold Replay.entryHeaders foldedHeaders foldedIndex foldedSurvivors Replay.dayIndexOf
  rw [List.append_nil, ← Replay.survivors_are_the_uncancelled_entries]

/-! ### Carried note 1: the global longest leak lives in the checkpoint, and it is the replay's -/

/-- **The global longest leak is an all-time fact kept whole** (carried note 1): a first maximum in file order over
every day, so it is kept in the checkpoint (A) rather than as per-day candidates, and the answer's reading of it is the
replay's, for every log and every ledger day. -/
theorem the_answer_reads_the_replays_longest_leak (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) :
    askAnswer (answer (ckptOf z T₀ L ls [])) .longestLeak = some (Replay.ask (replayLines z ls) .longestLeak) := by
  simp only [askAnswer, answer, ckptOf, ckptOfEntries, replayLines, Replay.ask, Replay.factsView, Replay.replayDoc,
    replay_eq_finish_foldedState, Log.lineEntries]
  rfl

/-- **Every scalar all-time reading of the answer is the replay's**, for every log and every ledger day: the open block
and interruption, the last day, the last effective stamp, the unknown count, the replay warnings and the entry count
(beside the longest leak above).  The checkpoint keeps each whole (A). -/
theorem the_answer_reads_the_replays_scalar_facts (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) :
    askAnswer (answer (ckptOf z T₀ L ls [])) .openBlock = some (Replay.ask (replayLines z ls) .openBlock) ∧
    askAnswer (answer (ckptOf z T₀ L ls [])) .openInterrupt = some (Replay.ask (replayLines z ls) .openInterrupt) ∧
    askAnswer (answer (ckptOf z T₀ L ls [])) .lastDay = some (Replay.ask (replayLines z ls) .lastDay) ∧
    askAnswer (answer (ckptOf z T₀ L ls [])) .lastEffective = some (Replay.ask (replayLines z ls) .lastEffective) ∧
    askAnswer (answer (ckptOf z T₀ L ls [])) .unknown = some (Replay.ask (replayLines z ls) .unknown) ∧
    askAnswer (answer (ckptOf z T₀ L ls [])) .replayWarnings = some (Replay.ask (replayLines z ls) .replayWarnings) ∧
    askAnswer (answer (ckptOf z T₀ L ls [])) .entryCount = some (Replay.ask (replayLines z ls) .entryCount) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (simp only [askAnswer, answer, ckptOf, ckptOfEntries, replayLines, Replay.ask, Replay.factsView, Replay.replayDoc,
    replay_eq_finish_foldedState, Log.lineEntries, Replay.finish, Replay.HMap.keys_pairs_mapVals]; try rfl)

/-! ### R10: what a read checkpoint holds -/

theorem orElse_eq_none {α : Type} (a b : Option α) : (a <|> b) = none ↔ a = none ∧ b = none := by
  cases a <;> simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem check_eq_none (b : Bool) (f : CkField) : check b f = none ↔ b = true := by
  cases b <;> simp [check]

/-- **§10.4's checkpoint rows, as a read checkpoint holds them**: a checkpoint within its bounds has at most 65,536
items and non-date instances, 4,096 window records (each at or after its horizon), 16,384 named records, 4,096 open days
(each at or after its ledger day), 4,096 wakes and slept days, 89 tags, 1,024 settled lines (each after the cut), 256
line warnings, and a zone key of at most 128 characters.  With `readCkpt_wf`, every checkpoint the decoder returns. -/
theorem Ckpt.wf_bounds (k : Ckpt) (h : k.wf = true) :
    k.v = ckptVersion ∧ k.tzKey.length ≤ maxTzKey ∧ k.wakes.length ≤ maxWakes ∧ k.sleptByDay.length ≤ maxWakes ∧
    k.tagLast.length ≤ maxTags ∧ k.settled.length ≤ maxSettled ∧ (∀ n ∈ k.settled, k.cut < n) ∧
    k.items.length ≤ maxItems ∧ k.window.length ≤ maxWindow ∧ (∀ w ∈ k.window, horizonOf k.ledgerDay ≤ w.day) ∧
    k.instOther.length ≤ maxItems ∧ k.named.length ≤ maxNamed ∧ k.openDays.length ≤ maxOpenDays ∧
    (∀ o ∈ k.openDays, k.ledgerDay ≤ o.day) ∧ k.warnings.length ≤ maxWarnings := by
  simp only [Ckpt.wf, Ckpt.fault, Option.isNone_iff_eq_none, orElse_eq_none, check_eq_none] at h
  simp only [cList, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hv, htz, hw, ⟨⟨hs, _⟩, _⟩, ⟨⟨⟨⟨ht, _⟩, _⟩, _⟩, _⟩, ⟨⟨⟨hse, _⟩, hsc⟩, _⟩, _, ⟨⟨hi, _⟩, _⟩,
    ⟨⟨⟨hwi, _⟩, hwh⟩, _⟩, ⟨⟨hio, _⟩, _⟩, ⟨⟨hn, _⟩, _⟩, ⟨⟨⟨ho, _⟩, hol⟩, _⟩, _, _, hwa, _⟩ := h
  exact ⟨hv, htz, hw.1, hs, ht, hse, hsc, hi, hwi, hwh, hio, hn, ho, hol, hwa⟩


/-- **The checkpoint of nothing is the empty checkpoint.** -/
theorem the_checkpoint_of_nothing_is_the_empty_checkpoint (z : Cal.Tz) : ckptOfEntries z 0 0 0 [] [] [] = Ckpt.empty z :=
  rfl

/-- **The empty checkpoint is within every bound**, so it reads back as itself (`readCkpt_emitCkpt`). -/
theorem the_empty_checkpoint_is_wf (z : Cal.Tz) : (Ckpt.empty z).wf = true := by
  have hz : z.val.key.length ≤ maxTzKey := by
    have := z.property; simp only [Cal.TzTable.wf, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1
  simp [Ckpt.empty, Ckpt.wf, Ckpt.fault, check, hz, cList, ascending, cOpt, cMachine, cIso, cTuple, tCons, tNil,
    ckptVersion]

/-! ## Witnesses (W1)

Each was probed in a scratch copy under `MemoryMax=8G timeout 120` (§14.0 item 4): at most 5 entries, `utcZone` (no
transition), instants as `Nat` literals, no text parsed.  2026-09-07T09:00:00Z is second 63924368400 and day 739865. -/

section Witnesses

open Replay (bE bDone bStart utcZone)

/-- `done x` at 09:00 on 2026-09-07 (line 1) and at 09:00 on the 8th (line 2). -/
def twoDoneDays : List Entry := [bE 1 63924368400 (bDone ['x'] 50 false), bE 2 63924454800 (bDone ['x'] 40 false)]

/-- The merged reading of entries sealed at `L`, queried with `q`, against the replay's (the checkpoint sealed at
2026-09-12). -/
def sealedReads (L : Nat) (es : List Entry) (q : Q) : Bool :=
  askMerged (dayRecordsOfEntries utcZone 0 L es) (windowRecordsOfEntries utcZone 0 (horizonOf L) es)
    (answer (ckptOfEntries utcZone 739870 L es.length es [] [])) q == Replay.ask (Replay.replayDoc utcZone es) q

/-- Thirteen readings of every kind: a done date's, a day's record and headers, an item's all-time facts. -/
def twoDoneQueries : List Q := [.lastDone ['x'], .day 739865 .record, .day 739866 .record, .day 739866 .headers,
  .day 739865 .durations, .win 739865 (.done ['x']), .win 739866 (.itemMin ['x']), .doneCount ['x'], .doneFirst ['x'],
  .lastDay, .entryCount, .item ['x'], .day 739867 .record]

set_option maxRecDepth 8000 in
/-- **The partition reads as the replay on its minimal witness** (law 1's, cheat 150's control): two `done` entries of
one id on two days, sealed before both days, between them, and after both (every day and window date sealed), answer
thirteen readings as the replay does, `last_done` among them. -/
theorem a_log_sealed_anywhere_answers_as_its_replay :
    twoDoneQueries.all (sealedReads 0 twoDoneDays) = true ∧
    twoDoneQueries.all (sealedReads 739866 twoDoneDays) = true ∧
    twoDoneQueries.all (sealedReads 739900 twoDoneDays) = true := by
  decide

/-- **`last_done` is all-time**: sealed after both its days, the answer still reads the later one. -/
theorem the_last_done_outlives_the_seal_of_its_days :
    askAnswer (answer (ckptOfEntries utcZone 739870 739900 2 twoDoneDays [] [])) (.lastDone ['x'])
      = some (.stamp (some (⟨63924454800, 0⟩, ⟨false, 0⟩))) := by
  decide

/-- **Carried note 2: the checkpoint carries the machine's last cut**: `start a` at 09:00 then `stop a` at 09:30 leaves
the cut of `a` (30 minutes on the 7th), which no view reads (the R-audit) and a later `done a` would take back. -/
theorem a_checkpoint_carries_the_last_cut :
    ((ckptOfEntries utcZone 739870 739865 2 [bE 1 63924368400 (bStart ['a']), bE 2 63924370200 (.stop ['a'] 0)] [] []).machine.lastCut.map
      (fun c => (c.id, c.day, c.min))) = some (['a'], 739865, 30) := by
  decide

/-- **The horizon on 2026-09-14** (Monday, day 739872): its month starts on the 1st (739859), its ISO week on the 14th,
and `auto_close` reaches back to the 29th of August (739856), which is the horizon. -/
theorem the_horizon_of_2026_09_14 :
    Cal.monthStart 739872 = 739859 ∧ Cal.isoMonday 739872 = 739872 ∧ horizonOf 739872 = 739856 := by
  decide

/-- **Settled undos** (§7.4): after a folded `done a`, the unfolded `undo done a` (its target folded) and `undo zz`
(no target) are settled; `undo note`, whose target is the unfolded note, is not. -/
theorem an_undo_is_settled_when_its_target_is_folded_or_absent :
    settledOf [bE 1 63924368400 (bDone ['a'] 50 false)]
      [bE 2 63924368460 (.undo ['d', 'o', 'n', 'e'] (some ['a'])), bE 3 63924368520 (.undo ['z', 'z'] none),
       bE 4 63924368580 (.note ['n']), bE 5 63924368640 (.undo ['n', 'o', 't', 'e'] none)] = [2, 3] := by
  decide

/-- **`sealable` bites and is satisfiable** (CRIT 3): an unfolded undo of a folded `done` on the 7th changes the 7th's
record, so the checkpoint is not sealable past the 7th; it is at the 7th. -/
theorem an_unfolded_undo_of_a_sealed_day_is_not_sealable :
    sealableEntries utcZone 739870 739866 [bE 1 63924368400 (bDone ['a'] 50 false)]
        [bE 2 63924368460 (.undo ['d', 'o', 'n', 'e'] (some ['a']))] = false ∧
    sealableEntries utcZone 739870 739865 [bE 1 63924368400 (bDone ['a'] 50 false)]
        [bE 2 63924368460 (.undo ['d', 'o', 'n', 'e'] (some ['a']))] = true := by
  decide

/-- **A future-dated line is fenced, not folded into `maxT`** (§9.4): a `note` on the 7th and one in 2028, sealed at
the 7th: `maxT` is the 7th's, `futureFloor` the 2028 one's. -/
theorem a_future_dated_line_sets_the_future_floor :
    let k := ckptOfEntries utcZone 739865 739865 2 [bE 1 63924368400 (.note ['n']), bE 2 63987526800 (.note ['f'])] [] []
    k.maxT = some ⟨63924368400, 0⟩ ∧ k.futureFloor = some ⟨63987526800, 0⟩ := by
  decide

/-- **Law 11 on a start across the seal**: `start a` on the 7th with a reported energy, `done a`, then an `energy`
report and `start b` on the 8th, sealed at the 8th.  The 7th's record holds the start's observation, the answer holds
the report and `b`'s pending one, and together, by line, they are the replay's. -/
theorem sealed_and_live_observations_on_a_start_across_the_seal :
    let es := [bE 1 63924368400 (bStart ['a']), bE 2 63924372000 (bDone ['a'] 60 false),
      bE 3 63924454800 (.energy 3 4 (.nat 2) ['h']), bE 4 63924456600 (bStart ['b'])]
    Replay.sortByLine ((dayRecordsOfEntries utcZone 0 739866 es).flatMap DayRecord.obs
      ++ (answer (ckptOfEntries utcZone 739870 739866 4 es [] [])).obs) = (Replay.replayDoc utcZone es).obs ∧
    ((dayRecordsOfEntries utcZone 0 739866 es).flatMap DayRecord.obs).length = 2 ∧
    (answer (ckptOfEntries utcZone 739870 739866 4 es [] [])).obs.length = 2 := by
  decide

set_option maxRecDepth 8000 in
/-- **The round trips are not vacuous**: the checkpoint of the two-done log sealed between its days, and its sealed day
record, are within their bounds (so `readCkpt_emitCkpt` and `readDayRecord_emitDayRecord` read them back) and are not
empty. -/
theorem the_round_trips_are_not_vacuous :
    (ckptOfEntries utcZone 739870 739866 2 twoDoneDays [] []).wf = true ∧
    (ckptOfEntries utcZone 739870 739866 2 twoDoneDays [] []) ≠ Ckpt.empty utcZone ∧
    (dayRecordsOfEntries utcZone 0 739866 twoDoneDays).all DayRecord.wf = true ∧
    (dayRecordsOfEntries utcZone 0 739866 twoDoneDays).length = 1 := by
  decide

end Witnesses

end Seal
end Tm
