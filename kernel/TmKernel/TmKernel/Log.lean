import TmKernel.Json
import TmKernel.Stamp
/-!
# Log — the typed event grammar of `.tm/log.jsonl` (stage 5, D9 track, step B3)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §5.4–§5.6 and §14.2 row B3.  One line of the
log is one JSON object, and the fork point reads it with `Log::parse_bytes`, `LogEntry::parse` and
`Event`'s hand-written `Deserialize` (`tm-core/src/log.rs`), and writes it with
`LogEntry::to_json`.  This module ports both:

* `readLine n seg : Verdict` — a line is `blank`, an `Entry`, or a warning `LWarn` **by name**;
* `renderLine e` — serde's bytes for an entry: `{"t":…,"ev":…,<fields>}`, compact, fields in
  `define_events!` order, `skip_serializing_if` as declared, an unknown event's keys sorted.

Nothing in the binary calls it yet: B4 puts `log` on the wire, C1–C6 replay its entries.

## The grammar is a table

The **26** known tags (`EVENT_NAMES`; the design says 25, and `define_events!` has 26: `wake` …
`undo`) are the constructors of `Event`, plus `unknown tag rest`.  What varies between kinds is
data, so it is a table (AGENTS §5.5): `Kind.schema` lists each kind's keys in declaration order with
serde's type (`FTy`: `u8`, `u32`, a defaulted `u32d`, the `Option`s, `str`, `strs`, `flag`, `num` for
`hsw`, `pair` for `window`).  There is **one reader** (`readF`) and **one writer** (`renderF`) per
field type, and every kind reads and writes through them (`readArgs`, `renderArgs`), so a kind cannot
read a field one way and write it another.  `Kind.build` and `Event.split` are the two directions
between a kind's decoded fields (`Args`) and the typed `Event`; `Event.tag`, `Event.strings` and
`Event.primaryId` are written out per constructor, so their meaning does not depend on the table.

## What serde does, and what the reader does (each row pinned by the B3 probe, README)

1. `none` (the host found the line not UTF-8) is `invalidUtf8`.
2. **Every** trailing `\r` goes (`trim_end_matches('\r')`; the design says one).
3. A line of Rust whitespace only (`str::trim`, `LogStamp.isRustSpace`) is `blank`.
4. More than `maxLineChars` characters is `lineTooLong`; brackets nested deeper than
   `maxLineDepth` outside strings (`depthOf`, a scan before `jparse`) is `lineTooDeep` (P14).
5. `jparse` failing is `notJson`.
6. Any numeral anywhere in the line that serde would refuse is `numberOutOfRange` (`finiteF64`,
   serde_json 1.0.151's own algorithm without `float_roundtrip`, not IEEE's rounding: see its
   section).
7. Not an object is `notAnObject`.
8. `t`: `LogEntry`'s derived reader takes the **first** `t` key; missing is `noT`, not a string is
   `tNotString`, not a stamp is `badT`, and a **second** `t` key after a good one is `duplicateT`
   (serde's `duplicate field`).  The design names neither of the last two.
9. `ev`: the **last** `ev` key (serde collects a `Map` first); missing is `noEv`, not a string is
   `evNotString`.
10. A known tag decodes strictly, and a bad payload is a warning, never `unknown`.  Every key is
    read at its **last** value; a type error anywhere beats a missing field, and among each the
    first in declaration order is named (`FR.pair`: `Known::field_error` looks for a type error
    first).  `-0`, `3.0`, `1e2` and `-1` are type errors at an integer field (serde reads them as
    floats or negatives); `hsw` keeps any numeral as written, and an absent `hsw` is `0.0`, which
    serde writes back as `0.0`.
11. Any other tag is `unknown tag rest`, `rest` being every other key, sorted by serde's `String`
    order (`charsLe`, core's stable merge sort), the last of a repeated key kept (`restOf`).

**Where the reader's order is not serde's.**  serde reports the first defect **in stream order**,
the reader the first in the order above.  They differ only on lines with two defects, or where
serde stops early: `{"t":"bad","x":1e400}` (`numberOutOfRange` here, `badT` in the fork),
`[1,2,` (`notJson` here, `notAnObject` there), and an object followed by trailing text whose event
is also bad.  Only the class of a warning differs; entry or warning never does.  Recorded as parity
residue (README, P24), decided against serde by T1 at B4.

## The goals (design §15, B3), all discharged here

`the_log_reads_what_it_renders` (every canonical entry), `a_known_event_is_never_read_as_unknown`,
`an_unknown_tag_is_never_a_warning` and `lineTooLong_bounds_every_string`; beside them
`an_out_of_range_numeral_warns_even_in_an_unknown_event`,
`finiteF64_reads_only_the_sign_past_an_i32_exponent`, `every_line_warning_is_reachable`, the
per-line theorems over the fork's `malformed.jsonl`, and the R10 refusals.

## Names

`LogStamp.parseStamp`, `LogStamp.renderStamp` and `LogStamp.StampErr` are written qualified: this
module never opens `LogStamp` (B2's note: `Field.Stamp` is the `demoted:` stamp, and
`Field.Stamp` is what `stampFromKey` returns).  No instant is compared here (carried note 1).

## Rule D9-21

Every function here that walks a line-sized list is a `foldl` or a loop, checked in the generated
C (`goto _start`, no self-call): `lastVal`, `allStrs` (`strStep`), `depthOf` (`scanStep`), `capOf`
and the exponent fold in `finiteF64`, `restOf`'s `dedupStep` fold, `charsLe`/`charsLt`,
`splitDashW.go`, `allFiniteL`/`allFiniteO` (the list recursion is the tail of `&&`), and core's
`find?`, `countP.go`, `all`, `dropWhile`, `filterTR`, `mapTR`, `lengthTR`, `reverse` and
`mergeSortTR₂`.  `allFinite` recurses per nesting level, which `lineTooDeep` bounds at 64.
`readArgs` and `renderArgs` recurse over a kind's schema (at most 8 keys).  `jstrs`, `Agrees` and
the other definitions of the laws section are specifications no wire path calls.  `digitsOf`, which
`renderLine` reaches through `JDec.render` and `jemit (.num _)`, runs as `digitsOfTR` since this step
(`Text.lean`; README gap 101, closed).
-/
namespace Tm
namespace Log

open Cal (VInstant VOffset)

/-! ## Widths and values -/

/-- serde's `u8`: the fork checks no range narrower than this (`ci.min(5)` is the machine's). -/
abbrev U8 := Fin 256
/-- serde's `u32`. -/
abbrev U32 := Fin 4294967296
/-- An item id, as the log spells it. -/
abbrev Id := List Char

/-- `hsw`, lexical: the numeral as written, never evaluated (`f64` in the fork). -/
inductive Num
  | nat (n : Nat)
  | dec (d : { d : JDec // d.plain = false })
deriving DecidableEq, Repr

/-- What an absent `hsw` is: serde's `#[serde(default)]` `0.0`, which it writes as `0.0`. -/
def Num.zero : Num := .dec ⟨⟨false, 0, [0], none⟩, rfl⟩

/-! ## Two readers of an object's pairs -/

/-- **The value serde keeps for a key**: the last one written.  `Map<String, Value>` inserts in
order, so a repeated key's last value wins.  A `foldl` (D9-21). -/
def lastVal (kvs : List (List Char × JVal)) (k : List Char) : Option JVal :=
  kvs.foldl (fun acc kv => if kv.1 == k then some kv.2 else acc) none

/-! ## Every string in a value (a specification; never run on the wire) -/

mutual
/-- Every string in a value, keys included. -/
def jstrs : JVal → List (List Char)
  | .str s => [s]
  | .arr xs => jstrsL xs
  | .obj kvs => jstrsO kvs
  | _ => []
def jstrsL : List JVal → List (List Char)
  | [] => []
  | x :: xs => jstrs x ++ jstrsL xs
def jstrsO : List (List Char × JVal) → List (List Char)
  | [] => []
  | (k, v) :: kvs => k :: (jstrs v ++ jstrsO kvs)
end

/-! ## `finiteF64`: serde_json's "number out of range", ported

The fork collects every line as a `Map<String, Value>` before it reads a field, so **every
numeral in the line**, at any depth and in a known or an unknown event, is parsed to a
`serde_json::Number` first, and one that serde refuses fails the whole line (design §5.4, G-d,
CRIT 15).  serde_json 1.0.151 is built without `float_roundtrip` here (`cargo tree -e features`),
so its refusal is `Deserializer::f64_from_parts`'s, and that is not IEEE's rounding of the written
decimal: the significand keeps the first digits that fit a `u64` (the rest are **dropped**, not
rounded), it becomes a `f64` (rounded), and it is multiplied by `POW10[e]` (a rounded `f64`), and
only that product's overflow is refused.  So `1.7976931348623157e308` is finite and the
309-digit integer spelling of the same `f64` is not (B3 probe, lines 36 and 49).  The port below
follows `parse_integer`, `parse_long_integer`, `parse_decimal`, `parse_decimal_overflow`,
`parse_exponent`, `parse_exponent_overflow` and `f64_from_parts` step for step.

**Its cost is bounded by the line, never by the numeral's value** (CRIT 14): the significand is
below 2⁶⁴, a power is computed only for an exponent of at most 308, and the exponent's digits are
folded with serde's `i32` overflow check, so a 60,000-digit exponent is a Boolean after ten
digits. -/

/-- `u64::MAX`. -/
def u64Max : Nat := 18446744073709551615
/-- `i32::MAX`. -/
def i32Max : Nat := 2147483647

/-- The number of bits of `n`.  Structural, with `n` as its own fuel (it reduces). -/
def bitLen : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n = 0 then 0 else bitLen f (n / 2) + 1

/-- **The `f64` nearest to `n`**, as an exact natural: 53 significant bits, ties to even.  Both
`significand as f64` and a `POW10` entry (a float literal) are this. -/
def roundF (n : Nat) : Nat :=
  if bitLen n n ≤ 53 then n
  else
    let s := bitLen n n - 53
    let q := n / 2 ^ s
    let r := n % 2 ^ s
    (if 2 ^ (s - 1) < r || (r == 2 ^ (s - 1) && q % 2 == 1) then q + 1 else q) * 2 ^ s

/-- The least exact product a round-to-nearest multiplication turns into infinity:
`f64::MAX = 2¹⁰²⁴ − 2⁹⁷¹` and the next value up, `2¹⁰²⁴`, tie at `2¹⁰²⁴ − 2⁹⁷⁰`, and the tie goes to
the even one, infinity. -/
def f64Overflow : Nat := 2 ^ 1024 - 2 ^ 970

/-- `f64_from_parts(positive, significand, exponent)` returns a value (not
`NumberOutOfRange`).  A negative exponent only divides; above 308 there is no `POW10` entry, and a
non-zero significand is refused. -/
def fromPartsFinite (sig : Nat) (e : Int) : Bool :=
  if e < 0 then true
  else if 308 < e then sig == 0
  else decide (roundF sig * roundF (10 ^ e.toNat) < f64Overflow)

/-- The significand serde keeps and the exponent the dropped digits add. -/
structure Cap where
  sig : Nat
  exp : Int
  full : Bool
deriving Repr

/-- An integer digit: kept while `sig * 10 + d` fits a `u64` (`parse_integer`); from the first
that does not, every integer digit adds one to the exponent (`parse_long_integer`). -/
def capInt (c : Cap) (d : Nat) : Cap :=
  if c.full then { c with exp := c.exp + 1 }
  else if u64Max < c.sig * 10 + d then { c with exp := c.exp + 1, full := true }
  else { c with sig := c.sig * 10 + d }

/-- A fraction digit: kept, taking one from the exponent, while it fits (`parse_decimal`); from
the first that does not, ignored (`parse_decimal_overflow`). -/
def capFrac (c : Cap) (d : Nat) : Cap :=
  if c.full then c
  else if u64Max < c.sig * 10 + d then { c with full := true }
  else { c with sig := c.sig * 10 + d, exp := c.exp - 1 }

/-- An exponent digit: `none` once `exp * 10 + d` passes `i32::MAX` (`parse_exponent`). -/
def capExp (acc : Option Nat) (d : Nat) : Option Nat :=
  acc.bind (fun e => if i32Max < e * 10 + d then none else some (e * 10 + d))

/-- The significand and exponent serde has after a numeral's integer and fraction digits.  The
integer digits are `digitsOf`'s (a loop since `digitsOf_eq_digitsOfTR`); both folds are `foldl`s. -/
def capOf (d : JDec) : Cap :=
  d.frac.foldl (fun c f => capFrac c f.val)
    { ((digitsOf d.int).foldl (fun c ch => capInt c ((charDigit ch).getD 0)) ⟨0, 0, false⟩) with
      full := false }

/-- **serde_json reads this numeral as a finite number.**  A numeral with no fraction and no
exponent that fits a `u64` is `parse_number`'s `U64`, `I64` or `-0.0` and never reaches
`f64_from_parts`; everything else does. -/
def finiteF64 (d : JDec) : Bool :=
  if d.frac.isEmpty && d.exp.isNone && decide (d.int ≤ u64Max) then true
  else
    match d.exp with
    | none => fromPartsFinite (capOf d).sig (capOf d).exp
    | some (negE, x, xs) =>
      match (x :: xs).foldl (fun a f => capExp a f.val) (some 0) with
      | none => negE || (capOf d).sig == 0
      | some v => fromPartsFinite (capOf d).sig (if negE then (capOf d).exp - v else (capOf d).exp + v)

/-- An `hsw` serde reads as finite. -/
def Num.finite : Num → Bool
  | .nat n => finiteF64 ⟨false, n, [], none⟩
  | .dec d => finiteF64 d.val

mutual
/-- **Every numeral in a value is finite to serde.**  Per nesting level in `allFinite`; along a
list the recursive call is the tail of `&&` (D9-21: a loop in the generated C). -/
def allFinite : JVal → Bool
  | .num n => finiteF64 ⟨false, n, [], none⟩
  | .dec d => finiteF64 d.val
  | .arr xs => allFiniteL xs
  | .obj kvs => allFiniteO kvs
  | _ => true
def allFiniteL : List JVal → Bool
  | [] => true
  | x :: xs => allFinite x && allFiniteL xs
def allFiniteO : List (List Char × JVal) → Bool
  | [] => true
  | (_, v) :: kvs => allFinite v && allFiniteO kvs
end

/-! ## The field types -/

/-- serde's field types as `define_events!` declares them.  `u32d` is a `u32` with
`#[serde(default)]`; every `Option`, `strs` (`Vec<String>`), `flag` (`bool`) and `num` (`hsw`) is
defaulted. -/
inductive FTy
  | u8 | u32 | u32d | optU8 | optU32 | str | optStr | strs | flag | num | pair
deriving DecidableEq, Repr

/-- The kernel's type for each. -/
@[reducible] def FTy.T : FTy → Type
  | .u8 => U8
  | .u32 => U32
  | .u32d => U32
  | .optU8 => Option U8
  | .optU32 => Option U32
  | .str => List Char
  | .optStr => Option (List Char)
  | .strs => List (List Char)
  | .flag => Bool
  | .num => Num
  | .pair => List Char × List Char

/-- A schema's decoded fields, one per key, in order. -/
@[reducible] def Args : List (List Char × FTy) → Type
  | [] => Unit
  | (_, t) :: s => t.T × Args s

inductive Event
  | wake (sleptMin : U32) (onsetMin : Option U32)
  | arrive (loc : List Char) (window : List Char × List Char) (budget : U32)
  | start (id : Id) (pred : U8) (rep : Option U8) (hsw : Num) (sleptMin : U32) (loc : List Char) (blocksDone : U32) (sinceBreakMin : U32)
  | done (id : Id) (estMin : U32) (actualMin : U32) (went : Option U8) (tags : List (List Char)) (ci : U8) (isPartial : Bool)
  | extend (id : Id) (byMin : U32)
  | stop (id : Id) (remainingMin : U32)
  | brk (plannedMin : U32) (actualMin : Option U32) (where_ : Option (List Char))
  | energy (pred : U8) (rep : U8) (hsw : Num) (loc : List Char)
  | interrupt (id : Option Id)
  | resume (lostMin : U32) (dropped : List Id)
  | pause (id : Id)
  | unpause (id : Id)
  | idle (attributed : List Char) (min : U32)
  | routine (item : List Char) (inst : List Char) (status : List Char) (actualMin : Option U32)
  | skip (item : List Char) (inst : List Char)
  | plan (hash : List Char) (replansToday : U32) (driftMin : U32)
  | named (name : List Char) (id : Option Id)
  | demote (id : Id) (from_ : List Char) (to : List Char) (estMin : U32)
  | readopt (id : Id)
  | move (id : Id) (from_ : List Char) (to : List Char)
  | drop (id : Id)
  | edit (id : Id) (field : List Char) (from_ : List Char) (to : List Char)
  | note (text : List Char)
  | loc (loc : List Char)
  | close (period : List Char) (key : List Char)
  | undo (of_ : List Char) (id : Option Id)
  /-- Any tag that is not one of the 26: every other key, sorted by key, the last of a repeated
  key kept (serde's `Map<String, Value>`). -/
  | unknown (tag : List Char) (rest : List (List Char × JVal))
deriving DecidableEq, Repr

/-- The 26 known kinds, in `EVENT_NAMES` order. -/
inductive Kind
  | wake | arrive | start | done | extend | stop | brk | energy | interrupt | resume | pause | unpause | idle | routine | skip | plan | named | demote | readopt | move | drop | edit | note | loc | close | undo
deriving DecidableEq, Repr

/-- `EVENT_NAMES`, in order. -/
def Kind.all : List Kind :=
  [.wake, .arrive, .start, .done, .extend, .stop, .brk, .energy, .interrupt, .resume, .pause, .unpause, .idle, .routine, .skip, .plan, .named, .demote, .readopt, .move, .drop, .edit, .note, .loc, .close, .undo]

/-- The `ev` tag of a known kind. -/
def Kind.tag : Kind → List Char
  | .wake => ['w','a','k','e']
  | .arrive => ['a','r','r','i','v','e']
  | .start => ['s','t','a','r','t']
  | .done => ['d','o','n','e']
  | .extend => ['e','x','t','e','n','d']
  | .stop => ['s','t','o','p']
  | .brk => ['b','r','e','a','k']
  | .energy => ['e','n','e','r','g','y']
  | .interrupt => ['i','n','t','e','r','r','u','p','t']
  | .resume => ['r','e','s','u','m','e']
  | .pause => ['p','a','u','s','e']
  | .unpause => ['u','n','p','a','u','s','e']
  | .idle => ['i','d','l','e']
  | .routine => ['r','o','u','t','i','n','e']
  | .skip => ['s','k','i','p']
  | .plan => ['p','l','a','n']
  | .named => ['e','v','e','n','t']
  | .demote => ['d','e','m','o','t','e']
  | .readopt => ['r','e','a','d','o','p','t']
  | .move => ['m','o','v','e']
  | .drop => ['d','r','o','p']
  | .edit => ['e','d','i','t']
  | .note => ['n','o','t','e']
  | .loc => ['l','o','c']
  | .close => ['c','l','o','s','e']
  | .undo => ['u','n','d','o']

/-- **The field table** (`define_events!`, inventory §1): each kind's keys in declaration order,
with serde's type and default.  Data, not derivation (AGENTS §5.5): the order is serde's
writing order, and nothing about it follows from anything else. -/
def Kind.schema : Kind → List (List Char × FTy)
  | .wake => [(['s','l','e','p','t','_','m','i','n'], .u32), (['o','n','s','e','t','_','m','i','n'], .optU32)]
  | .arrive => [(['l','o','c'], .str), (['w','i','n','d','o','w'], .pair), (['b','u','d','g','e','t'], .u32)]
  | .start => [(['i','d'], .str), (['p','r','e','d'], .u8), (['r','e','p'], .optU8), (['h','s','w'], .num), (['s','l','e','p','t','_','m','i','n'], .u32d), (['l','o','c'], .str), (['b','l','o','c','k','s','_','d','o','n','e'], .u32d), (['s','i','n','c','e','_','b','r','e','a','k','_','m','i','n'], .u32d)]
  | .done => [(['i','d'], .str), (['e','s','t','_','m','i','n'], .u32), (['a','c','t','u','a','l','_','m','i','n'], .u32), (['w','e','n','t'], .optU8), (['t','a','g','s'], .strs), (['c','i'], .u8), (['p','a','r','t','i','a','l'], .flag)]
  | .extend => [(['i','d'], .str), (['b','y','_','m','i','n'], .u32)]
  | .stop => [(['i','d'], .str), (['r','e','m','a','i','n','i','n','g','_','m','i','n'], .u32)]
  | .brk => [(['p','l','a','n','n','e','d','_','m','i','n'], .u32), (['a','c','t','u','a','l','_','m','i','n'], .optU32), (['w','h','e','r','e'], .optStr)]
  | .energy => [(['p','r','e','d'], .u8), (['r','e','p'], .u8), (['h','s','w'], .num), (['l','o','c'], .str)]
  | .interrupt => [(['i','d'], .optStr)]
  | .resume => [(['l','o','s','t','_','m','i','n'], .u32), (['d','r','o','p','p','e','d'], .strs)]
  | .pause => [(['i','d'], .str)]
  | .unpause => [(['i','d'], .str)]
  | .idle => [(['a','t','t','r','i','b','u','t','e','d'], .str), (['m','i','n'], .u32)]
  | .routine => [(['i','t','e','m'], .str), (['i','n','s','t'], .str), (['s','t','a','t','u','s'], .str), (['a','c','t','u','a','l','_','m','i','n'], .optU32)]
  | .skip => [(['i','t','e','m'], .str), (['i','n','s','t'], .str)]
  | .plan => [(['h','a','s','h'], .str), (['r','e','p','l','a','n','s','_','t','o','d','a','y'], .u32), (['d','r','i','f','t','_','m','i','n'], .u32)]
  | .named => [(['n','a','m','e'], .str), (['i','d'], .optStr)]
  | .demote => [(['i','d'], .str), (['f','r','o','m'], .str), (['t','o'], .str), (['e','s','t','_','m','i','n'], .u32)]
  | .readopt => [(['i','d'], .str)]
  | .move => [(['i','d'], .str), (['f','r','o','m'], .str), (['t','o'], .str)]
  | .drop => [(['i','d'], .str)]
  | .edit => [(['i','d'], .str), (['f','i','e','l','d'], .str), (['f','r','o','m'], .str), (['t','o'], .str)]
  | .note => [(['t','e','x','t'], .str)]
  | .loc => [(['l','o','c'], .str)]
  | .close => [(['p','e','r','i','o','d'], .str), (['k','e','y'], .str)]
  | .undo => [(['o','f'], .str), (['i','d'], .optStr)]

/-- A kind and its decoded fields, as the event. -/
def Kind.build : (k : Kind) → Args k.schema → Event
  | .wake, (x0, x1, ()) => .wake x0 x1
  | .arrive, (x0, x1, x2, ()) => .arrive x0 x1 x2
  | .start, (x0, x1, x2, x3, x4, x5, x6, x7, ()) => .start x0 x1 x2 x3 x4 x5 x6 x7
  | .done, (x0, x1, x2, x3, x4, x5, x6, ()) => .done x0 x1 x2 x3 x4 x5 x6
  | .extend, (x0, x1, ()) => .extend x0 x1
  | .stop, (x0, x1, ()) => .stop x0 x1
  | .brk, (x0, x1, x2, ()) => .brk x0 x1 x2
  | .energy, (x0, x1, x2, x3, ()) => .energy x0 x1 x2 x3
  | .interrupt, (x0, ()) => .interrupt x0
  | .resume, (x0, x1, ()) => .resume x0 x1
  | .pause, (x0, ()) => .pause x0
  | .unpause, (x0, ()) => .unpause x0
  | .idle, (x0, x1, ()) => .idle x0 x1
  | .routine, (x0, x1, x2, x3, ()) => .routine x0 x1 x2 x3
  | .skip, (x0, x1, ()) => .skip x0 x1
  | .plan, (x0, x1, x2, ()) => .plan x0 x1 x2
  | .named, (x0, x1, ()) => .named x0 x1
  | .demote, (x0, x1, x2, x3, ()) => .demote x0 x1 x2 x3
  | .readopt, (x0, ()) => .readopt x0
  | .move, (x0, x1, x2, ()) => .move x0 x1 x2
  | .drop, (x0, ()) => .drop x0
  | .edit, (x0, x1, x2, x3, ()) => .edit x0 x1 x2 x3
  | .note, (x0, ()) => .note x0
  | .loc, (x0, ()) => .loc x0
  | .close, (x0, x1, ()) => .close x0 x1
  | .undo, (x0, x1, ()) => .undo x0 x1

/-- A known event as its kind and fields; `none` for `unknown`. -/
def Event.split : Event → Option (Σ k : Kind, Args k.schema)
  | .wake x0 x1 => some ⟨.wake, (x0, x1, ())⟩
  | .arrive x0 x1 x2 => some ⟨.arrive, (x0, x1, x2, ())⟩
  | .start x0 x1 x2 x3 x4 x5 x6 x7 => some ⟨.start, (x0, x1, x2, x3, x4, x5, x6, x7, ())⟩
  | .done x0 x1 x2 x3 x4 x5 x6 => some ⟨.done, (x0, x1, x2, x3, x4, x5, x6, ())⟩
  | .extend x0 x1 => some ⟨.extend, (x0, x1, ())⟩
  | .stop x0 x1 => some ⟨.stop, (x0, x1, ())⟩
  | .brk x0 x1 x2 => some ⟨.brk, (x0, x1, x2, ())⟩
  | .energy x0 x1 x2 x3 => some ⟨.energy, (x0, x1, x2, x3, ())⟩
  | .interrupt x0 => some ⟨.interrupt, (x0, ())⟩
  | .resume x0 x1 => some ⟨.resume, (x0, x1, ())⟩
  | .pause x0 => some ⟨.pause, (x0, ())⟩
  | .unpause x0 => some ⟨.unpause, (x0, ())⟩
  | .idle x0 x1 => some ⟨.idle, (x0, x1, ())⟩
  | .routine x0 x1 x2 x3 => some ⟨.routine, (x0, x1, x2, x3, ())⟩
  | .skip x0 x1 => some ⟨.skip, (x0, x1, ())⟩
  | .plan x0 x1 x2 => some ⟨.plan, (x0, x1, x2, ())⟩
  | .named x0 x1 => some ⟨.named, (x0, x1, ())⟩
  | .demote x0 x1 x2 x3 => some ⟨.demote, (x0, x1, x2, x3, ())⟩
  | .readopt x0 => some ⟨.readopt, (x0, ())⟩
  | .move x0 x1 x2 => some ⟨.move, (x0, x1, x2, ())⟩
  | .drop x0 => some ⟨.drop, (x0, ())⟩
  | .edit x0 x1 x2 x3 => some ⟨.edit, (x0, x1, x2, x3, ())⟩
  | .note x0 => some ⟨.note, (x0, ())⟩
  | .loc x0 => some ⟨.loc, (x0, ())⟩
  | .close x0 x1 => some ⟨.close, (x0, x1, ())⟩
  | .undo x0 x1 => some ⟨.undo, (x0, x1, ())⟩
  | .unknown _ _ => none

/-- `Event::name`: the `ev` tag. -/
def Event.tag : Event → List Char
  | .wake _ _ => Kind.wake.tag
  | .arrive _ _ _ => Kind.arrive.tag
  | .start _ _ _ _ _ _ _ _ => Kind.start.tag
  | .done _ _ _ _ _ _ _ => Kind.done.tag
  | .extend _ _ => Kind.extend.tag
  | .stop _ _ => Kind.stop.tag
  | .brk _ _ _ => Kind.brk.tag
  | .energy _ _ _ _ => Kind.energy.tag
  | .interrupt _ => Kind.interrupt.tag
  | .resume _ _ => Kind.resume.tag
  | .pause _ => Kind.pause.tag
  | .unpause _ => Kind.unpause.tag
  | .idle _ _ => Kind.idle.tag
  | .routine _ _ _ _ => Kind.routine.tag
  | .skip _ _ => Kind.skip.tag
  | .plan _ _ _ => Kind.plan.tag
  | .named _ _ => Kind.named.tag
  | .demote _ _ _ _ => Kind.demote.tag
  | .readopt _ => Kind.readopt.tag
  | .move _ _ _ => Kind.move.tag
  | .drop _ => Kind.drop.tag
  | .edit _ _ _ _ => Kind.edit.tag
  | .note _ => Kind.note.tag
  | .loc _ => Kind.loc.tag
  | .close _ _ => Kind.close.tag
  | .undo _ _ => Kind.undo.tag
  | .unknown t _ => t

/-- **Every string an event holds**, field by field (`lineTooLong_bounds_every_string`).  For
`unknown`, the tag, every key and every string at any depth of `rest`. -/
def Event.strings : Event → List (List Char)
  | .wake _ _ => []
  | .arrive x0 x1 _ => [x0] ++ [x1.1, x1.2]
  | .start x0 _ _ _ _ x5 _ _ => [x0] ++ [x5]
  | .done x0 _ _ _ x4 _ _ => [x0] ++ x4
  | .extend x0 _ => [x0]
  | .stop x0 _ => [x0]
  | .brk _ _ x2 => x2.toList
  | .energy _ _ _ x3 => [x3]
  | .interrupt x0 => x0.toList
  | .resume _ x1 => x1
  | .pause x0 => [x0]
  | .unpause x0 => [x0]
  | .idle x0 _ => [x0]
  | .routine x0 x1 x2 _ => [x0] ++ [x1] ++ [x2]
  | .skip x0 x1 => [x0] ++ [x1]
  | .plan x0 _ _ => [x0]
  | .named x0 x1 => [x0] ++ x1.toList
  | .demote x0 x1 x2 _ => [x0] ++ [x1] ++ [x2]
  | .readopt x0 => [x0]
  | .move x0 x1 x2 => [x0] ++ [x1] ++ [x2]
  | .drop x0 => [x0]
  | .edit x0 x1 x2 x3 => [x0] ++ [x1] ++ [x2] ++ [x3]
  | .note x0 => [x0]
  | .loc x0 => [x0]
  | .close x0 x1 => [x0] ++ [x1]
  | .undo x0 x1 => [x0] ++ x1.toList
  | .unknown t rest => t :: jstrsO rest

/-- `Event::primary_id`: what `undo{id}` matches. -/
def Event.primaryId : Event → Option Id
  | .start i _ _ _ _ _ _ _ => some i
  | .done i _ _ _ _ _ _ => some i
  | .extend i _ => some i
  | .stop i _ => some i
  | .interrupt i => i
  | .pause i => some i
  | .unpause i => some i
  | .routine item _ _ _ => some item
  | .skip item _ => some item
  | .named _ i => i
  | .demote i _ _ _ => some i
  | .readopt i => some i
  | .move i _ _ => some i
  | .drop i => some i
  | .edit i _ _ _ => some i
  | .undo _ i => i
  | .unknown _ rest =>
    match lastVal rest ['i','d'] with
    | some (.str s) => some s
    | _ => none
  | _ => none

/-! ## Reading a field -/

/-- A field's verdict: its value, or the key serde names in a `missing field` or a type error. -/
inductive FR (α : Type)
  | ok (a : α)
  | missing (k : List Char)
  | bad (k : List Char)

/-- **Two fields' verdicts, the earlier first.**  The fork reports a mistyped field before a
missing one, whatever their order (`Known::field_error` looks for a type error first, in
declaration order, and serde's own error, which names the first missing field, is used only
when there is none).  So a `bad` anywhere beats a `missing`, and among each the earlier wins. -/
def FR.pair {α β : Type} : FR α → FR β → FR (α × β)
  | .ok a, .ok b => .ok (a, b)
  | .bad k, _ => .bad k
  | .missing _, .bad k => .bad k
  | .missing k, _ => .missing k
  | .ok _, .bad k => .bad k
  | .ok _, .missing k => .missing k

/-- One element of a string array, onto the reversed strings so far. -/
def strStep : Option (List (List Char)) → JVal → Option (List (List Char))
  | some l, .str s => some (s :: l)
  | _, _ => none

/-- Every element a string, in order.  A `foldl` (D9-21): `tags` can be as long as a line. -/
def allStrs (xs : List JVal) : Option (List (List Char)) :=
  (xs.foldl strStep (some [])).map List.reverse

/-- **One field, as serde reads it** (design §5.4's table, pinned by the B3 probe): absent is the
default or `missing`; `null` is `none` for an `Option` and a type error otherwise; a numeral is an
integer in the field's width or a type error (`-0`, `3.0` and `1e2` are floats to serde, so they
are type errors at an integer field); `hsw` takes any numeral as written. -/
def readF (k : List Char) : (t : FTy) → Option JVal → FR t.T
  | .u8, none => .missing k
  | .u8, some (.num n) => if h : n < 256 then .ok ⟨n, h⟩ else .bad k
  | .u8, some _ => .bad k
  | .u32, none => .missing k
  | .u32, some (.num n) => if h : n < 4294967296 then .ok ⟨n, h⟩ else .bad k
  | .u32, some _ => .bad k
  | .u32d, none => .ok ⟨0, by decide⟩
  | .u32d, some (.num n) => if h : n < 4294967296 then .ok ⟨n, h⟩ else .bad k
  | .u32d, some _ => .bad k
  | .optU8, none => .ok none
  | .optU8, some .null => .ok none
  | .optU8, some (.num n) => if h : n < 256 then .ok (some ⟨n, h⟩) else .bad k
  | .optU8, some _ => .bad k
  | .optU32, none => .ok none
  | .optU32, some .null => .ok none
  | .optU32, some (.num n) => if h : n < 4294967296 then .ok (some ⟨n, h⟩) else .bad k
  | .optU32, some _ => .bad k
  | .str, none => .missing k
  | .str, some (.str s) => .ok s
  | .str, some _ => .bad k
  | .optStr, none => .ok none
  | .optStr, some .null => .ok none
  | .optStr, some (.str s) => .ok (some s)
  | .optStr, some _ => .bad k
  | .strs, none => .ok []
  | .strs, some (.arr xs) =>
    match allStrs xs with
    | some ss => .ok ss
    | none => .bad k
  | .strs, some _ => .bad k
  | .flag, none => .ok false
  | .flag, some (.bool b) => .ok b
  | .flag, some _ => .bad k
  | .num, none => .ok Num.zero
  | .num, some (.num n) => .ok (.nat n)
  | .num, some (.dec d) => .ok (.dec d)
  | .num, some _ => .bad k
  | .pair, none => .missing k
  | .pair, some (.arr [.str a, .str b]) => .ok (a, b)
  | .pair, some _ => .bad k

/-- A schema's fields, each read from the pairs' last value for its key. -/
def readArgs (kvs : List (List Char × JVal)) : (s : List (List Char × FTy)) → FR (Args s)
  | [] => .ok ()
  | (k, t) :: s => FR.pair (readF k t (lastVal kvs k)) (readArgs kvs s)

/-! ## Writing a field -/

/-- **One field, as serde writes it**: `none` is skipped (`skip_serializing_if = "Option::is_none"`),
as is `partial: false` (`is_false`); `tags` and `dropped` are always written, and so is `hsw`. -/
def renderF : (t : FTy) → t.T → Option JVal
  | .u8, x => some (.num x.val)
  | .u32, x => some (.num x.val)
  | .u32d, x => some (.num x.val)
  | .optU8, none => none
  | .optU8, some x => some (.num x.val)
  | .optU32, none => none
  | .optU32, some x => some (.num x.val)
  | .str, s => some (.str s)
  | .optStr, none => none
  | .optStr, some s => some (.str s)
  | .strs, ss => some (.arr (ss.map JVal.str))
  | .flag, false => none
  | .flag, true => some (.bool true)
  | .num, .nat n => some (.num n)
  | .num, .dec d => some (.dec d)
  | .pair, (a, b) => some (.arr [.str a, .str b])

/-- A schema's fields as pairs, in declaration order, skipped ones left out. -/
def renderArgs : (s : List (List Char × FTy)) → Args s → List (List Char × JVal)
  | [], () => []
  | (k, t) :: s, (x, xs) =>
    (match renderF t x with
     | some v => [(k, v)]
     | none => []) ++ renderArgs s xs

/-- The strings a field holds. -/
def strsOfF : (t : FTy) → t.T → List (List Char)
  | .str, s => [s]
  | .optStr, o => o.toList
  | .strs, ss => ss
  | .pair, p => [p.1, p.2]
  | .u8, _ | .u32, _ | .u32d, _ | .optU8, _ | .optU32, _ | .flag, _ | .num, _ => []

/-- The strings a schema's fields hold, in order. -/
def argStrs : (s : List (List Char × FTy)) → Args s → List (List Char)
  | [], () => []
  | (_, t) :: s, (x, xs) => strsOfF t x ++ argStrs s xs

/-- A field serde reads as finite: only `hsw` can fail. -/
def fieldFinite : (t : FTy) → t.T → Bool
  | .num, h => h.finite
  | .u8, _ | .u32, _ | .u32d, _ | .optU8, _ | .optU32, _ | .str, _ | .optStr, _ | .strs, _
  | .flag, _ | .pair, _ => true

def argsFinite : (s : List (List Char × FTy)) → Args s → Bool
  | [], () => true
  | (_, t) :: s, (x, xs) => fieldFinite t x && argsFinite s xs

/-! ## The known tags -/

/-- The known kind of a tag, if any.  A scan of `EVENT_NAMES` (26 entries; each comparison stops at
the first differing character, so a long unknown tag costs at most a few characters each). -/
def kindOf (tag : List Char) : Option Kind := Kind.all.find? (fun k => k.tag == tag)

/-- `EVENT_NAMES.contains(tag)`. -/
def isKnownTag (tag : List Char) : Bool := (kindOf tag).isSome

/-- `matches!(self, Event::Unknown { .. })`. -/
def Event.isUnknown : Event → Bool
  | .unknown _ _ => true
  | _ => false

/-- `matches!(self, Event::Undo { .. })`. -/
def Event.isUndo : Event → Bool
  | .undo _ _ => true
  | _ => false

/-- `Event::is_state_change`: everything but `plan`, `note`, `undo` and unknown events.  Ported for
the grammar's completeness; the undo mask (C1) does not read it. -/
def Event.isStateChange : Event → Bool
  | .plan _ _ _ | .note _ | .undo _ _ | .unknown _ _ => false
  | _ => true

/-- An event's pairs after `t` and `ev`, as serde writes them: a known event's fields in
declaration order; an unknown event's `rest`. -/
def Event.fields (ev : Event) : List (List Char × JVal) :=
  match ev with
  | .unknown _ rest => rest
  | _ =>
    match ev.split with
    | some ⟨k, a⟩ => renderArgs k.schema a
    | none => []


/-! ## Lines, warnings and verdicts (design §5.5) -/

/-- **Why a line is not an entry.**  Every warning is named (AGENTS §5.7); the fork's text for
each is serde's or its own, and parity entry P15 records that the kernel names them instead. -/
inductive LWarn
  /-- the line is not UTF-8 (the host hands the kernel `null` for it) -/
  | invalidUtf8
  /-- more than `maxLineChars` characters (P14) -/
  | lineTooLong
  /-- brackets nested deeper than `maxLineDepth` (P14) -/
  | lineTooDeep
  /-- not JSON -/
  | notJson (e : JErr)
  /-- a numeral serde refuses as out of range, anywhere in the line -/
  | numberOutOfRange
  /-- JSON, but not an object -/
  | notAnObject
  /-- no `t` key -/
  | noT
  /-- the first `t` is not a string -/
  | tNotString
  /-- the first `t` is not a stamp -/
  | badT (e : LogStamp.StampErr)
  /-- a second `t` key (serde's `duplicate field `t``, B3 probe) -/
  | duplicateT
  /-- no `ev` key -/
  | noEv
  /-- the last `ev` is not a string -/
  | evNotString
  /-- a known event without a field that has no default -/
  | missingField (k : List Char)
  /-- a known event's field of the wrong type or out of its width -/
  | badField (k : List Char)
deriving DecidableEq, Repr

/-- One line: an entry, a warning, or nothing (a blank line). -/
structure Entry where
  line : Nat
  t : VInstant
  off : VOffset
  ev : Event
deriving DecidableEq, Repr

inductive Verdict
  | blank
  | entry (e : Entry)
  | warn (line : Nat) (w : LWarn)
deriving DecidableEq, Repr

/-- The line bound (R10; P14). -/
def maxLineChars : Nat := 65536
/-- The nesting bound (P14): `jparse` recurses per nesting level, so this is what keeps it on the
stack. serde_json's own limit is 128. -/
def maxLineDepth : Nat := 64

/-- `trim_end_matches('\r')`: **every** trailing carriage return. -/
def trimCR (l : List Char) : List Char := (l.reverse.dropWhile (· == '\r')).reverse

/-- The bracket scanner's state: inside a string, just after a backslash in one, the open
brackets, and the most there have been. -/
structure Scan where
  inStr : Bool
  esc : Bool
  depth : Nat
  peak : Nat
deriving Repr

def scanStep (s : Scan) (c : Char) : Scan :=
  if s.inStr then
    if s.esc then { s with esc := false }
    else if c = '\\' then { s with esc := true }
    else if c = '"' then { s with inStr := false }
    else s
  else if c = '"' then { s with inStr := true }
  else if c = '[' || c = '{' then { s with depth := s.depth + 1, peak := max s.peak (s.depth + 1) }
  else if c = ']' || c = '}' then { s with depth := s.depth - 1 }
  else s

/-- **The deepest bracket nesting outside strings**, found before `jparse` runs.  A `foldl`. -/
def depthOf (l : List Char) : Nat := (l.foldl scanStep ⟨false, false, 0, 0⟩).peak

def kT : List Char := ['t']
def kEv : List Char := ['e','v']

/-- **`t`, as `LogEntry`'s derived reader takes it**: the first `t` key decides (`badT`,
`tNotString`), and a second `t` key after a good one is `duplicateT` (serde's derived visitor
refuses a repeated field; B3 probe). -/
def readT (kvs : List (List Char × JVal)) : Except LWarn (VInstant × VOffset) :=
  match kvs.find? (fun kv => kv.1 == kT) with
  | none => .error .noT
  | some (_, .str s) =>
    match LogStamp.parseStamp s with
    | .error e => .error (.badT e)
    | .ok p => if kvs.countP (fun kv => kv.1 == kT) = 1 then .ok p else .error .duplicateT
  | some _ => .error .tNotString

/-- serde's `String` order: bytewise, which on UTF-8 is the code points' order.  Tail recursive. -/
def charsLe : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a.val < b.val then true else if a = b then charsLe as bs else false

/-- Strictly before, in the same order. -/
def charsLt : List Char → List Char → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a.val < b.val then true else if a = b then charsLt as bs else false

/-- One step of keeping a sorted run's last pair per key; the accumulator is reversed. -/
def dedupStep (acc : List (List Char × JVal)) (kv : List Char × JVal) : List (List Char × JVal) :=
  match acc with
  | p :: ps => if p.1 == kv.1 then kv :: ps else kv :: p :: ps
  | [] => [kv]

/-- **An unknown event's `rest`**: every pair but `t` and `ev`, sorted by key (core's stable merge
sort, `mergeSortTR₂` at run time), the last of a repeated key kept — serde's `Map`. -/
def restOf (kvs : List (List Char × JVal)) : List (List Char × JVal) :=
  ((((kvs.filter (fun kv => !(kv.1 == kT) && !(kv.1 == kEv))).mergeSort
    (fun a b => charsLe a.1 b.1)).foldl dedupStep []).reverse)

/-- After `t`: the tag, then a known kind's fields or an unknown event's `rest`. -/
def readObject (n : Nat) (kvs : List (List Char × JVal)) : Verdict :=
  match readT kvs with
  | .error w => .warn n w
  | .ok (t, off) =>
    match lastVal kvs kEv with
    | none => .warn n .noEv
    | some (.str tag) =>
      match kindOf tag with
      | some k =>
        match readArgs kvs k.schema with
        | .ok a => .entry ⟨n, t, off, k.build a⟩
        | .missing key => .warn n (.missingField key)
        | .bad key => .warn n (.badField key)
      | none => .entry ⟨n, t, off, .unknown tag (restOf kvs)⟩
    | some _ => .warn n .evNotString

/-- After `jparse`: the numerals, then the shape. -/
def readValue (n : Nat) (v : JVal) : Verdict :=
  if allFinite v then
    match v with
    | .obj kvs => readObject n kvs
    | _ => .warn n .notAnObject
  else .warn n .numberOutOfRange

/-- **One log line** (a port of `Log::parse_bytes`' loop body and `LogEntry::parse`).  `n` is the
physical line number; `none` is a line the host found not to be UTF-8.  In order: invalid UTF-8,
trailing carriage returns, blank (Rust's `str::trim`, `LogStamp.isRustSpace`), the length and
nesting bounds, `jparse`, every numeral, the object, `t`, `ev`, and the fields. -/
def readLine (n : Nat) : Option (List Char) → Verdict
  | none => .warn n .invalidUtf8
  | some raw =>
    if (trimCR raw).all LogStamp.isRustSpace then .blank
    else if maxLineChars < (trimCR raw).length then .warn n .lineTooLong
    else if maxLineDepth < depthOf (trimCR raw) then .warn n .lineTooDeep
    else
      match jparse (trimCR raw) with
      | .error e => .warn n (.notJson e)
      | .ok v => readValue n v

/-! ## Small grammars (design §5.6): what the replay reads out of an event's strings

Nothing in B3 calls these; C4 (`routine`, `skip`) and C5 (`demote`) do.  They are here because
they are grammar, not replay. -/

/-- `InstanceStatus`, as `routine.status` names it. -/
inductive InstanceStatus
  | done | pending | missed | expired | skipped
deriving DecidableEq, Repr

/-- **`parse_instance_status`**: `done`, `pending`, `missed`, `expired`, and `skipped` or `skip`;
anything else is `none` (the replay warning `unknownInstanceStatus`, §8.3). -/
def parseInstanceStatus (s : List Char) : Option InstanceStatus :=
  if s == ['d','o','n','e'] then some .done
  else if s == ['p','e','n','d','i','n','g'] then some .pending
  else if s == ['m','i','s','s','e','d'] then some .missed
  else if s == ['e','x','p','i','r','e','d'] then some .expired
  else if s == ['s','k','i','p','p','e','d'] || s == ['s','k','i','p'] then some .skipped
  else none

/-- chrono's generic `%Y-%m-%d` (`NaiveDate::parse_from_str`), through B2's readers of its fallback
(`yearOf`, `lit`, `numIn`: whitespace before each number, one or two digits for month and day, a
signed year), then the end.  The year, month and day as written; validity is the caller's. -/
def chronoDateParts (s : List Char) : Option (Nat × Nat × Nat) :=
  match LogStamp.yearOf s with
  | .error _ => none
  | .ok (y, s) =>
    match LogStamp.lit '-' .badDate s with
    | .error _ => none
    | .ok s =>
      match LogStamp.numIn 2 1 12 .badDate s with
      | .error _ => none
      | .ok (m, s) =>
        match LogStamp.lit '-' .badDate s with
        | .error _ => none
        | .ok s =>
          match LogStamp.numIn 2 1 31 .badDate s with
          | .error _ => none
          | .ok (d, rest) => if rest.isEmpty then some (y, m, d) else none

/-- **`parse_date`** (`model.rs`): exactly 10 characters, then chrono's `%Y-%m-%d`, as a `Day`.
Year 0 is a date to chrono and not a `Cal.Day`, so it is `none` here (P23's residue). -/
def instDate? (s : List Char) : Option Nat :=
  if s.length = 10 then
    (chronoDateParts s).bind (fun (y, m, d) =>
      if Cal.Date.valid ⟨y, m, d⟩ then some (Cal.toDay ⟨y, m, d⟩) else none)
  else none

/-- `str::split_once("-W")`, as a loop. -/
def splitDashW.go : List Char → List Char → Option (List Char × List Char)
  | '-' :: 'W' :: rest, acc => some (acc.reverse, rest)
  | c :: rest, acc => splitDashW.go rest (c :: acc)
  | [], _ => none

def splitDashW (s : List Char) : Option (List Char × List Char) := splitDashW.go s []

/-- Rust's `str::parse::<i32>` on a short string: an optional `+` or `-`, then at least one ASCII
digit and nothing else. -/
def rustInt (s : List Char) : Option Int :=
  match s with
  | '-' :: t => (if t.all Field.isDigitC then readNat t else none).map (fun n => -(n : Int))
  | '+' :: t => (if t.all Field.isDigitC then readNat t else none).map (fun n => (n : Int))
  | t => (if t.all Field.isDigitC then readNat t else none).map (fun n => (n : Int))

/-- **`IsoWeek::parse`**, the week: `YYYY-Www` split at the first `-W`, four characters and two,
Rust's integer readers (so `+202` and `-999` are years and `+5` is a week), a week from 1 to 53 that
the ISO year has (`Cal.isoWeeksIn`, which the 400-year Gregorian cycle carries to every year). -/
def isoWeekOfKey (s : List Char) : Option Nat :=
  match splitDashW s with
  | none => none
  | some (y, w) =>
    if y.length = 4 && w.length = 2 then
      match rustInt y, rustInt w with
      | some yr, some (.ofNat wk) =>
        if w.head? != some '-' && 1 ≤ wk && wk ≤ 53 &&
            wk ≤ Cal.isoWeeksIn ((yr % 400 + 400) % 400 + 400).toNat then some wk else none
      | _, _ => none
    else none

/-- **`stamp_from_key`**: an ISO week key is a week stamp, a date key is its day of the month,
anything else (a month key) is `none`.  The week number is read by `isoWeekOfKey`; there is no other
reader of a `YYYY-Www` key in the kernel (`Field.parseStamp` reads the `W37` of a `demoted:` field,
not a key). -/
def stampFromKey (s : List Char) : Option Field.Stamp :=
  match isoWeekOfKey s with
  | some w => some (.week w)
  | none =>
    if s.length = 10 then
      match chronoDateParts s with
      | some (y, m, d) => if Cal.Date.valid ⟨y + 400, m, d⟩ then some (.day d) else none
      | none => none
    else none

/-! ## What the goals speak of -/

/-- The tag a line carries: its last `ev`, when the line is an object and that is a string;
otherwise empty (no known tag is empty). -/
def tagIn (l : List Char) : List Char :=
  match jparse (trimCR l) with
  | .ok (.obj kvs) =>
    match lastVal kvs kEv with
    | some (.str s) => s
    | _ => []
  | _ => []

/-- The line is an object whose `t` is one good stamp and whose `ev` is a string. -/
def isObjectWithStampAndTag (l : List Char) : Bool :=
  match jparse (trimCR l) with
  | .ok (.obj kvs) =>
    (match readT kvs with
     | .ok _ => true
     | .error _ => false) &&
    (match lastVal kvs kEv with
     | some (.str _) => true
     | _ => false)
  | _ => false

/-- Every numeral in the line is finite to serde (vacuously, when it is not JSON). -/
def allNumeralsFinite (l : List Char) : Bool :=
  match jparse (trimCR l) with
  | .ok v => allFinite v
  | .error _ => true

/-! ## Writing a line -/

/-- The line as a value: `t`, `ev`, then the fields, in serde's order. -/
def lineVal (e : Entry) : JVal :=
  .obj ((kT, .str (LogStamp.renderStamp e.t e.off)) :: (kEv, .str e.ev.tag) :: e.ev.fields)

/-- **`LogEntry::to_json`**: `{"t":…,"ev":…,<fields>}`, compact, fields in declaration order,
`skip_serializing_if` as `define_events!` has it, an unknown event's keys sorted. -/
def renderLine (e : Entry) : List Char := jemit (lineVal e)

/-- A stamp `renderStamp` writes and `parseStamp` reads back (B2's `parseStamp_renderStamp`). -/
def stampCanonical (t : VInstant) (o : VOffset) : Bool :=
  (t.val.ns == 0 || t.val.ns == 1000000000) && o.val.sec % 60 == 0 &&
    (o.val.sec != 0 || !o.val.west) && (o.val.west || decide (t.val.sec + o.val.sec < LogStamp.yearEnd))

/-- An unknown event's `rest` as serde's `Map` holds it: keys strictly increasing, none `t` or
`ev`. -/
def restCanonical (rest : List (List Char × JVal)) : Bool :=
  decide (rest.Pairwise (fun a b => charsLt a.1 b.1 = true)) &&
    rest.all (fun kv => !(kv.1 == kT) && !(kv.1 == kEv))

/-- An event a reader can return: `hsw` finite; an unknown event's tag not a known one, its
numerals finite, its `rest` a `Map`. -/
def Event.canonical : Event → Bool
  | .start _ _ _ h _ _ _ _ => h.finite
  | .energy _ _ h _ => h.finite
  | .unknown tag rest => !isKnownTag tag && allFiniteO rest && restCanonical rest
  | _ => true

/-- **An entry `readLine` can return**: its stamp round-trips (whole seconds or a leap second, a
whole-minute offset, UTC written `+00:00`, before year 10000), its event is canonical, and its
line is within the reader's two bounds. -/
def Entry.canonical (e : Entry) : Bool :=
  stampCanonical e.t e.off && e.ev.canonical &&
    decide ((renderLine e).length ≤ maxLineChars) && decide (depthOf (renderLine e) ≤ maxLineDepth)


/-! ## Laws: the pairs' last value -/

theorem lastVal_go (xs : List (List Char × JVal)) (k : List Char) (acc : Option JVal) :
    xs.foldl (fun acc kv => if kv.1 == k then some kv.2 else acc) acc = (lastVal xs k).or acc := by
  induction xs generalizing acc with
  | nil => simp [lastVal]
  | cons kv xs ih =>
    simp only [List.foldl_cons, lastVal]
    rw [ih, ih (if kv.1 == k then some kv.2 else none)]
    by_cases h : kv.1 == k <;> simp [h]

theorem lastVal_cons (kv : List Char × JVal) (xs : List (List Char × JVal)) (k : List Char) :
    lastVal (kv :: xs) k = (lastVal xs k).or (if kv.1 == k then some kv.2 else none) := by
  conv => lhs; unfold lastVal
  simp only [List.foldl_cons]
  exact lastVal_go xs k _

theorem lastVal_append (xs ys : List (List Char × JVal)) (k : List Char) :
    lastVal (xs ++ ys) k = (lastVal ys k).or (lastVal xs k) := by
  induction xs with
  | nil => simp [lastVal]
  | cons kv xs ih =>
    rw [List.cons_append, lastVal_cons, ih, lastVal_cons, Option.or_assoc]

theorem lastVal_nil (k : List Char) : lastVal [] k = none := rfl

theorem lastVal_of_not_mem (xs : List (List Char × JVal)) (k : List Char)
    (h : k ∉ xs.map Prod.fst) : lastVal xs k = none := by
  induction xs with
  | nil => rfl
  | cons kv xs ih =>
    rw [lastVal_cons]
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [ih h.2]
    have : (kv.1 == k) = false := by simpa using (Ne.symm h.1)
    simp [this]

theorem lastVal_mem (xs : List (List Char × JVal)) (k : List Char) (v : JVal)
    (h : lastVal xs k = some v) : (k, v) ∈ xs := by
  induction xs with
  | nil => cases h
  | cons kv xs ih =>
    rw [lastVal_cons] at h
    cases hl : lastVal xs k with
    | some w => rw [hl] at h; cases h; exact List.mem_cons_of_mem _ (ih hl)
    | none =>
      rw [hl] at h
      by_cases hk : kv.1 == k
      · simp [hk] at h; subst h
        have := beq_iff_eq.mp hk
        exact List.mem_cons.mpr (Or.inl (by rw [← this]))
      · simp [hk] at h

/-! ## Laws: one field -/

theorem allStrs_map (ss : List (List Char)) : allStrs (ss.map JVal.str) = some ss := by
  unfold allStrs
  suffices h : ∀ acc, (ss.map JVal.str).foldl strStep (some acc) = some (ss.reverse ++ acc) by
    rw [h []]; simp
  induction ss with
  | nil => intro acc; rfl
  | cons s ss ih => intro acc; simp only [List.map_cons, List.foldl_cons, strStep]; rw [ih]; simp

theorem readF_renderF (k : List Char) : ∀ (t : FTy) (x : t.T), readF k t (renderF t x) = .ok x
  | .u8, x => by simp [renderF, readF, x.isLt]
  | .u32, x => by simp [renderF, readF, x.isLt]
  | .u32d, x => by simp [renderF, readF, x.isLt]
  | .optU8, none => rfl
  | .optU8, some x => by simp [renderF, readF, x.isLt]
  | .optU32, none => rfl
  | .optU32, some x => by simp [renderF, readF, x.isLt]
  | .str, _ => rfl
  | .optStr, none => rfl
  | .optStr, some _ => rfl
  | .strs, ss => by simp [renderF, readF, allStrs_map]
  | .flag, false => rfl
  | .flag, true => rfl
  | .num, .nat _ => rfl
  | .num, .dec _ => rfl
  | .pair, (_, _) => rfl

/-- The pairs agree with a schema's fields: each key's last value is what the field writes. -/
def Agrees (kvs : List (List Char × JVal)) : (s : List (List Char × FTy)) → Args s → Prop
  | [], () => True
  | (k, t) :: s, (x, xs) => lastVal kvs k = renderF t x ∧ Agrees kvs s xs

theorem readArgs_of_agrees (kvs : List (List Char × JVal)) :
    ∀ (s : List (List Char × FTy)) (a : Args s), Agrees kvs s a → readArgs kvs s = .ok a
  | [], (), _ => rfl
  | (k, t) :: s, (x, xs), ⟨h1, h2⟩ => by
    simp only [readArgs, h1, readF_renderF, readArgs_of_agrees kvs s xs h2, FR.pair]

theorem renderArgs_keys : ∀ (s : List (List Char × FTy)) (a : Args s),
    ∀ kv ∈ renderArgs s a, kv.1 ∈ s.map Prod.fst
  | [], (), kv, h => by simp [renderArgs] at h
  | (k, t) :: s, (x, xs), kv, h => by
    simp only [renderArgs, List.mem_append] at h
    rcases h with h | h
    · split at h <;> simp at h; subst h; simp
    · simp only [List.map_cons, List.mem_cons]; exact Or.inr (renderArgs_keys s xs kv h)

theorem agrees_renderArgs : ∀ (s : List (List Char × FTy)) (a : Args s)
    (pre : List (List Char × JVal)), (s.map Prod.fst).Nodup →
    (∀ kv ∈ pre, kv.1 ∉ s.map Prod.fst) → Agrees (pre ++ renderArgs s a) s a
  | [], (), _, _, _ => trivial
  | (k, t) :: s, (x, xs), pre, hnd, hpre => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hrest : k ∉ (renderArgs s xs).map Prod.fst := by
      intro hm
      obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp hm
      exact hnd.1 (renderArgs_keys s xs kv hkv)
    have hpk : k ∉ pre.map Prod.fst := by
      intro hm
      obtain ⟨kv, hkv, hk⟩ := List.mem_map.mp hm
      exact hpre kv hkv (by simp [hk])
    refine ⟨?_, ?_⟩
    · simp only [renderArgs]
      rw [← List.append_assoc, lastVal_append, lastVal_of_not_mem _ _ hrest, lastVal_append,
        lastVal_of_not_mem _ _ hpk]
      split <;> simp_all [lastVal_cons, lastVal_nil]
    · simp only [renderArgs]
      rw [← List.append_assoc]
      apply agrees_renderArgs s xs _ hnd.2
      intro kv hkv
      simp only [List.mem_append] at hkv
      rcases hkv with hkv | hkv
      · intro hm; exact hpre kv hkv (by simp [hm])
      · split at hkv <;> simp at hkv
        subst hkv; exact hnd.1

/-! ## Laws: each kind -/

theorem Kind.build_of_split (ev : Event) (k : Kind) (a : Args k.schema)
    (h : ev.split = some ⟨k, a⟩) : k.build a = ev := by
  cases ev <;> cases h <;> rfl

theorem Event.tag_of_split (ev : Event) (k : Kind) (a : Args k.schema)
    (h : ev.split = some ⟨k, a⟩) : ev.tag = k.tag := by
  cases ev <;> cases h <;> rfl

theorem Event.fields_of_split (ev : Event) (k : Kind) (a : Args k.schema)
    (h : ev.split = some ⟨k, a⟩) : ev.fields = renderArgs k.schema a := by
  cases ev <;> cases h <;> rfl

theorem Event.strings_of_split (ev : Event) (k : Kind) (a : Args k.schema)
    (h : ev.split = some ⟨k, a⟩) : ev.strings = argStrs k.schema a := by
  cases ev <;> cases h <;> simp [Event.strings, argStrs, strsOfF, Kind.schema]

theorem Event.canonical_of_split (ev : Event) (k : Kind) (a : Args k.schema)
    (h : ev.split = some ⟨k, a⟩) : ev.canonical = argsFinite k.schema a := by
  cases ev <;> cases h <;> simp [Event.canonical, argsFinite, fieldFinite, Kind.schema]

theorem Event.split_build (k : Kind) (a : Args k.schema) : (k.build a).split = some ⟨k, a⟩ := by
  cases k <;> rfl

theorem Event.split_of_not_unknown (ev : Event) (h : ev.isUnknown = false) :
    ∃ k a, ev.split = some ⟨k, a⟩ := by
  cases ev <;> first | exact ⟨_, _, rfl⟩ | cases h

theorem kindOf_tag (k : Kind) : kindOf k.tag = some k := by
  cases k <;> decide

theorem Kind.keys_nodup (k : Kind) : (k.schema.map Prod.fst).Nodup := by
  cases k <;> decide

theorem Kind.no_t_key (k : Kind) : kT ∉ k.schema.map Prod.fst := by
  cases k <;> decide

theorem Kind.no_ev_key (k : Kind) : kEv ∉ k.schema.map Prod.fst := by
  cases k <;> decide

/-! ## Laws: finiteness of what is written -/

theorem finiteF64_of_nat (n : Nat) (h : n ≤ u64Max) : finiteF64 ⟨false, n, [], none⟩ = true := by
  simp [finiteF64, h]

theorem allFiniteL_map_str (ss : List (List Char)) : allFiniteL (ss.map JVal.str) = true := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [allFiniteL, allFinite, ih]

theorem allFiniteO_append (xs ys : List (List Char × JVal)) :
    allFiniteO (xs ++ ys) = (allFiniteO xs && allFiniteO ys) := by
  induction xs with
  | nil => simp [allFiniteO]
  | cons kv xs ih => obtain ⟨k, v⟩ := kv; simp [allFiniteO, ih, Bool.and_assoc]

theorem u32_le_u64Max (x : U32) : x.val ≤ u64Max := by
  have := x.isLt; unfold u64Max; omega

theorem u8_le_u64Max (x : U8) : x.val ≤ u64Max := by
  have := x.isLt; unfold u64Max; omega

theorem allFiniteO_renderArgs : ∀ (s : List (List Char × FTy)) (a : Args s),
    argsFinite s a = true → allFiniteO (renderArgs s a) = true
  | [], (), _ => rfl
  | (k, t) :: s, (x, xs), h => by
    simp only [argsFinite, Bool.and_eq_true] at h
    simp only [renderArgs, allFiniteO_append, allFiniteO_renderArgs s xs h.2, Bool.and_true]
    cases t with
    | u8 => simp [renderF, allFiniteO, allFinite, finiteF64_of_nat _ (u8_le_u64Max x)]
    | u32 => simp [renderF, allFiniteO, allFinite, finiteF64_of_nat _ (u32_le_u64Max x)]
    | u32d => simp [renderF, allFiniteO, allFinite, finiteF64_of_nat _ (u32_le_u64Max x)]
    | optU8 => cases x <;> simp [renderF, allFiniteO, allFinite, finiteF64_of_nat _ (u8_le_u64Max _)]
    | optU32 => cases x <;> simp [renderF, allFiniteO, allFinite, finiteF64_of_nat _ (u32_le_u64Max _)]
    | str => simp [renderF, allFiniteO, allFinite]
    | optStr => cases x <;> simp [renderF, allFiniteO, allFinite]
    | strs => simp [renderF, allFiniteO, allFinite, allFiniteL_map_str]
    | flag => cases x <;> simp [renderF, allFiniteO, allFinite]
    | num => cases x <;> simp_all [renderF, allFiniteO, allFinite, fieldFinite, Num.finite]
    | pair => simp [renderF, allFiniteO, allFinite, allFiniteL]

/-! ## Laws: the written line's shape -/

theorem jemitOTail_ends (kvs : List (List Char × JVal)) : ∃ p, jemitOTail kvs = p ++ ['}'] := by
  induction kvs with
  | nil => exact ⟨[], rfl⟩
  | cons kv kvs ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨',' :: (jemitPair kv ++ p), by simp [jemitOTail, hp]⟩

theorem jemit_obj_ends (kvs : List (List Char × JVal)) : ∃ p, jemit (.obj kvs) = '{' :: (p ++ ['}']) := by
  cases kvs with
  | nil => exact ⟨[], rfl⟩
  | cons kv kvs =>
    obtain ⟨p, hp⟩ := jemitOTail_ends kvs
    exact ⟨jemitPair kv ++ p, by simp [jemit, jemitObj, hp]⟩

theorem trimCR_of_last (l : List Char) (c : Char) (h : c ≠ '\r') : trimCR (l ++ [c]) = l ++ [c] := by
  have : (c == '\r') = false := by simpa using h
  simp [trimCR, this]

theorem trimCR_jemit_obj (kvs : List (List Char × JVal)) : trimCR (jemit (.obj kvs)) = jemit (.obj kvs) := by
  obtain ⟨p, hp⟩ := jemit_obj_ends kvs
  rw [hp, ← List.cons_append, trimCR_of_last _ _ (by decide)]

theorem not_blank_jemit_obj (kvs : List (List Char × JVal)) :
    (jemit (.obj kvs)).all LogStamp.isRustSpace = false := by
  obtain ⟨p, hp⟩ := jemit_obj_ends kvs
  rw [hp]
  have h : LogStamp.isRustSpace '{' = false := by decide
  simp [List.all_cons, h]

/-! ## Laws: an unknown event's `rest` -/

theorem charsLt_irrefl : ∀ a : List Char, charsLt a a = false
  | [] => rfl
  | c :: as => by simp [charsLt, charsLt_irrefl as]

theorem charsLe_of_lt : ∀ a b : List Char, charsLt a b = true → charsLe a b = true
  | [], _, _ => rfl
  | _ :: _, [], h => by simp [charsLt] at h
  | x :: as, y :: bs, h => by
    simp only [charsLt] at h
    simp only [charsLe]
    split
    · rfl
    · split at h
      · contradiction
      · split
        · next hxy => simp only [hxy, if_true] at h; exact charsLe_of_lt as bs h
        · next hxy => simp [hxy] at h

theorem ne_of_charsLt (a b : List Char) (h : charsLt a b = true) : a ≠ b := by
  rintro rfl; rw [charsLt_irrefl] at h; cases h

theorem dedup_of_pairwise : ∀ (rest acc : List (List Char × JVal)),
    (acc.reverse ++ rest).Pairwise (fun a b => charsLt a.1 b.1 = true) →
    (rest.foldl dedupStep acc).reverse = acc.reverse ++ rest
  | [], acc, _ => by simp
  | kv :: rest, acc, h => by
    simp only [List.foldl_cons]
    have step : dedupStep acc kv = kv :: acc := by
      cases acc with
      | nil => rfl
      | cons p ps =>
        have hp : charsLt p.1 kv.1 = true := by
          have := List.pairwise_append.mp h
          exact this.2.2 p (by simp) kv (by simp)
        have : (p.1 == kv.1) = false := by simpa using ne_of_charsLt _ _ hp
        simp [dedupStep, this]
    rw [step, dedup_of_pairwise rest (kv :: acc) (by simpa using h)]
    simp

theorem restOf_canonical (a b : JVal) (rest : List (List Char × JVal)) (h : restCanonical rest = true) :
    restOf ((kT, a) :: (kEv, b) :: rest) = rest := by
  simp only [restCanonical, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hp, hk⟩ := h
  have hf : ((kT, a) :: (kEv, b) :: rest).filter (fun kv => !(kv.1 == kT) && !(kv.1 == kEv)) = rest := by
    simp only [List.filter_cons]
    have h1 : (!(kT == kT) && !(kT == kEv)) = false := by decide
    have h2 : (!(kEv == kT) && !(kEv == kEv)) = false := by decide
    simp only [h1, h2, Bool.false_eq_true, if_false]
    exact List.filter_eq_self.mpr (fun x hx => by simpa using hk x hx)
  unfold restOf
  rw [hf, List.mergeSort_of_pairwise (hp.imp (fun {x y} hxy => charsLe_of_lt _ _ hxy))]
  have := dedup_of_pairwise rest [] (by simpa using hp)
  simpa using this

/-! ## Laws: `t` and `ev` in a written line -/

theorem countP_of_not_mem (fields : List (List Char × JVal)) (k : List Char)
    (h : k ∉ fields.map Prod.fst) : fields.countP (fun kv => kv.1 == k) = 0 := by
  rw [List.countP_eq_zero]
  intro kv hkv hk
  exact h (List.mem_map.mpr ⟨kv, hkv, by simpa using hk⟩)

theorem stamp_hyps (t : VInstant) (o : VOffset) (h : stampCanonical t o = true) :
    (t.val.ns = 0 ∨ t.val.ns = 1000000000) ∧ o.val.sec % 60 = 0 ∧ (o.val.sec = 0 → o.val.west = false)
      ∧ (o.val.west = true ∨ t.val.sec + o.val.sec < LogStamp.yearEnd) := by
  simp only [stampCanonical, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun hz => ?_, h4⟩
  rcases h3 with h3 | h3
  · exact absurd hz h3
  · exact h3

theorem readT_line (t : VInstant) (o : VOffset) (tag : List Char) (fields : List (List Char × JVal))
    (hs : stampCanonical t o = true) (hf : kT ∉ fields.map Prod.fst) :
    readT ((kT, .str (LogStamp.renderStamp t o)) :: (kEv, .str tag) :: fields) = .ok (t, o) := by
  obtain ⟨h1, h2, h3, h4⟩ := stamp_hyps t o hs
  have hte : (kT == kT) = true := by decide
  have hne : (kEv == kT) = false := by decide
  simp only [readT, List.find?_cons, hte, LogStamp.parseStamp_renderStamp t o h1 h2 h3 h4,
    List.countP_cons, hne, countP_of_not_mem fields kT hf]
  rfl

theorem lastVal_ev_line (a : JVal) (tag : List Char) (fields : List (List Char × JVal))
    (hf : kEv ∉ fields.map Prod.fst) :
    lastVal ((kT, a) :: (kEv, .str tag) :: fields) kEv = some (.str tag) := by
  have hte : (kT == kEv) = false := by decide
  have hee : (kEv == kEv) = true := by decide
  rw [lastVal_cons, lastVal_cons, lastVal_of_not_mem _ _ hf]
  simp [hte]

/-! ## Laws: the grammar's goals -/

theorem readLine_of_parse (n : Nat) (raw : List Char) (v : JVal)
    (hb : (trimCR raw).all LogStamp.isRustSpace = false)
    (hl : (trimCR raw).length ≤ maxLineChars) (hd : depthOf (trimCR raw) ≤ maxLineDepth)
    (hp : jparse (trimCR raw) = .ok v) : readLine n (some raw) = readValue n v := by
  simp only [readLine, hb, Bool.false_eq_true, if_false, Nat.not_lt.mpr hl, Nat.not_lt.mpr hd, hp]

theorem keys_of_fields_known (ev : Event) (k : Kind) (a : Args k.schema) (h : ev.split = some ⟨k, a⟩)
    (key : List Char) (hk : key ∉ k.schema.map Prod.fst) : key ∉ ev.fields.map Prod.fst := by
  rw [Event.fields_of_split ev k a h]
  intro hm
  obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp hm
  exact hk (renderArgs_keys _ _ kv hkv)

theorem keys_of_rest (rest : List (List Char × JVal)) (h : restCanonical rest = true) :
    kT ∉ rest.map Prod.fst ∧ kEv ∉ rest.map Prod.fst := by
  simp only [restCanonical, Bool.and_eq_true, List.all_eq_true] at h
  constructor <;> intro hm <;> obtain ⟨kv, hkv, hk⟩ := List.mem_map.mp hm <;>
    have := h.2 kv hkv <;> simp_all

/-- **The log reads what it renders** (design §15, B3; added and discharged in B3). -/
theorem the_log_reads_what_it_renders (e : Entry) (h : e.canonical = true) :
    readLine e.line (some (renderLine e)) = .entry e := by
  simp only [Entry.canonical, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hs, hc⟩, hl⟩, hd⟩ := h
  have ht : trimCR (renderLine e) = renderLine e := trimCR_jemit_obj _
  rw [readLine_of_parse e.line (renderLine e) (lineVal e) (by rw [ht]; exact not_blank_jemit_obj _)
    (by rw [ht]; exact hl) (by rw [ht]; exact hd) (by rw [ht]; exact jparse_jemit _)]
  obtain ⟨line, t, o, ev⟩ := e
  cases hu : ev.isUnknown with
  | false =>
    obtain ⟨k, a, hsp⟩ := Event.split_of_not_unknown ev hu
    have hfin : allFinite (lineVal ⟨line, t, o, ev⟩) = true := by
      simp only [lineVal, allFinite, allFiniteO, Bool.true_and]
      rw [Event.fields_of_split ev k a hsp]
      exact allFiniteO_renderArgs _ _ (by rw [← Event.canonical_of_split ev k a hsp]; exact hc)
    simp only [readValue]
    rw [if_pos hfin]
    simp only [lineVal, readObject]
    rw [readT_line t o ev.tag ev.fields hs (keys_of_fields_known ev k a hsp kT (Kind.no_t_key k)),
      lastVal_ev_line _ ev.tag ev.fields (keys_of_fields_known ev k a hsp kEv (Kind.no_ev_key k))]
    simp only
    rw [Event.tag_of_split ev k a hsp, kindOf_tag]
    simp only
    have hag := agrees_renderArgs k.schema a [(kT, .str (LogStamp.renderStamp t o)), (kEv, .str k.tag)]
      (Kind.keys_nodup k) (by
        intro kv hkv
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hkv
        rcases hkv with rfl | rfl
        · exact Kind.no_t_key k
        · exact Kind.no_ev_key k)
    rw [← Event.fields_of_split ev k a hsp] at hag
    have hr := readArgs_of_agrees _ k.schema a hag
    simp only [List.cons_append, List.nil_append] at hr
    rw [hr]
    simp only [Kind.build_of_split ev k a hsp]
  | true =>
    cases ev with
    | unknown tag rest =>
      simp only [Event.canonical, Bool.and_eq_true, Bool.not_eq_true'] at hc
      obtain ⟨⟨hkn, hfr⟩, hrc⟩ := hc
      have hfin : allFinite (lineVal ⟨line, t, o, .unknown tag rest⟩) = true := by
        simp [lineVal, allFinite, allFiniteO, Event.fields, hfr]
      simp only [readValue]
      rw [if_pos hfin]
      simp only [lineVal, readObject, Event.fields, Event.tag]
      rw [readT_line t o tag rest hs (keys_of_rest rest hrc).1,
        lastVal_ev_line _ tag rest (keys_of_rest rest hrc).2]
      simp only
      have hk : kindOf tag = none := by
        simp only [isKnownTag, Option.isSome_eq_false_iff] at hkn; simpa using hkn
      rw [hk]
      simp only
      rw [restOf_canonical _ _ rest hrc]
    | _ => cases hu

/-- **A known event is never read as `unknown`** (design §15, B3; added and discharged in B3):
a line whose tag is one of the 26 is that kind's event or a warning (cheat 94's claim is false). -/
theorem a_known_event_is_never_read_as_unknown (n : Nat) (l : List Char) (e : Entry)
    (h : readLine n (some l) = .entry e) (hk : isKnownTag (tagIn l) = true) :
    e.ev.isUnknown = false := by
  simp only [readLine] at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h
  · cases h
  next v hp =>
    simp only [readValue] at h
    split at h
    · split at h
      next kvs =>
        simp only [readObject] at h
        split at h
        · cases h
        · split at h
          · cases h
          next tag hev =>
            split at h
            next k hkind =>
              split at h
              next a _ => cases h; cases k <;> rfl
              · cases h
              · cases h
            next hkind =>
              simp only [tagIn, hp, hev] at hk
              simp [isKnownTag, hkind] at hk
          · cases h
      · cases h
    · cases h

theorem trimCR_prefix (l : List Char) : ∃ s, l = trimCR l ++ s := by
  refine ⟨(l.reverse.takeWhile (· == '\r')).reverse, ?_⟩
  unfold trimCR
  rw [← List.reverse_append, List.takeWhile_append_dropWhile, List.reverse_reverse]

theorem scan_peak_mono (xs : List Char) (s : Scan) : s.peak ≤ (xs.foldl scanStep s).peak := by
  induction xs generalizing s with
  | nil => exact Nat.le_refl _
  | cons c xs ih =>
    simp only [List.foldl_cons]
    refine Nat.le_trans ?_ (ih _)
    unfold scanStep
    split <;> (try split) <;> (try split) <;> (try split) <;> simp <;> omega

theorem depthOf_prefix (a b : List Char) : depthOf a ≤ depthOf (a ++ b) := by
  unfold depthOf; rw [List.foldl_append]; exact scan_peak_mono _ _

theorem skipWs_suffix : ∀ l : List Char, ∃ p, l = p ++ skipWs l
  | [] => ⟨[], rfl⟩
  | c :: cs => by
    rw [skipWs.eq_2]
    split
    · obtain ⟨p, hp⟩ := skipWs_suffix cs; exact ⟨c :: p, by rw [List.cons_append, ← hp]⟩
    · exact ⟨[], rfl⟩

theorem isRustSpace_digit (c : Char) (h : (charDigit c).isSome = true) : LogStamp.isRustSpace c = false := by
  rcases charDigit_cases c h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem jparse_not_blank (m : List Char) (v : JVal) (h : jparse m = .ok v) :
    m.all LogStamp.isRustSpace = false := by
  cases hall : m.all LogStamp.isRustSpace with
  | false => rfl
  | true =>
    exfalso
    have hsp : ∀ c ∈ m, LogStamp.isRustSpace c = true := by simpa using hall
    unfold jparse jparseWith at h
    rw [show 2 * m.length + 2 = (2 * m.length + 1) + 1 by omega, jval.eq_2] at h
    obtain ⟨p, hp⟩ := skipWs_suffix m
    cases hs : skipWs m with
    | nil => rw [hs] at h; cases h
    | cons c r =>
      rw [hs] at h hp
      have hc : LogStamp.isRustSpace c = true := hsp c (by rw [hp]; simp)
      simp only at h
      have hd : (charDigit c).isSome = false := by
        cases hx : (charDigit c).isSome
        · rfl
        · rw [isRustSpace_digit c hx] at hc; cases hc
      have hne : ∀ x : Char, LogStamp.isRustSpace x = false → c ≠ x := by
        intro x hx hcx; subst hcx; rw [hc] at hx; cases hx
      rw [if_neg (by simp [hd]), if_neg (hne '-' (by decide)), if_neg (hne '"' (by decide)),
        if_neg (hne '[' (by decide)), if_neg (hne '{' (by decide))] at h
      have hn := hne 'n' (by decide)
      have ht := hne 't' (by decide)
      have hf := hne 'f' (by decide)
      split at h <;> simp_all

/-- **An unknown tag is never a warning** (design §15, B3; added and discharged in B3): a line that
is an object with one good `t` and a string `ev` that no kind has, within the two bounds and with
every numeral finite, is an entry (cheat 93's claim is false). -/
theorem an_unknown_tag_is_never_a_warning (n : Nat) (l : List Char) (w : LWarn)
    (hshape : isObjectWithStampAndTag l = true) (hu : isKnownTag (tagIn l) = false)
    (hlen : l.length ≤ maxLineChars) (hdepth : depthOf l ≤ maxLineDepth)
    (hfin : allNumeralsFinite l = true) :
    readLine n (some l) ≠ .warn n w := by
  obtain ⟨sfx, hsfx⟩ := trimCR_prefix l
  unfold isObjectWithStampAndTag at hshape
  split at hshape
  next kvs hp =>
    simp only [Bool.and_eq_true] at hshape
    obtain ⟨ht, hev⟩ := hshape
    have hl' : (trimCR l).length ≤ maxLineChars := by
      have := congrArg List.length hsfx; simp at this; omega
    have hd' : depthOf (trimCR l) ≤ maxLineDepth := by
      have := depthOf_prefix (trimCR l) sfx; rw [← hsfx] at this; omega
    rw [readLine_of_parse n l _ (jparse_not_blank _ _ hp) hl' hd' hp]
    simp only [allNumeralsFinite, hp] at hfin
    simp only [readValue, hfin, if_true, readObject]
    split at ht
    next p hrt =>
      rw [hrt]
      split at hev
      next tag htag =>
        simp only [htag]
        have hk : kindOf tag = none := by
          simp only [tagIn, hp, htag, isKnownTag, Option.isSome_eq_false_iff] at hu
          simpa using hu
        simp only [hk]
        intro h; cases h
      · cases hev
    · cases ht
  · cases hshape

/-! ## Laws: every string a parse returns is shorter than its input -/

theorem map_cons_ok {c : Char} {e : Except JEsc (List Char)} {s : List Char}
    (h : e.map (fun t => c :: t) = .ok s) : ∃ t, e = .ok t ∧ s = c :: t := by
  cases e with
  | error x => simp [Except.map] at h
  | ok t => simp [Except.map] at h; exact ⟨t, rfl, h.symm⟩

theorem junescape_length (n : Nat) : ∀ (l s : List Char), l.length ≤ n →
    junescape l = .ok s → s.length ≤ l.length := by
  induction n with
  | zero =>
    intro l s hl h
    cases l with
    | nil => simp [junescape] at h; subst h; simp
    | cons _ _ => simp at hl
  | succ n ih =>
    intro l s hl h
    rw [junescape.eq_def] at h
    repeat' split at h
    all_goals first
      | (simp at h; subst h; simp)
      | cases h
      | (obtain ⟨t, ht, rfl⟩ := map_cons_ok h
         have := ih _ t (by simp at hl ⊢; omega) ht
         simp; omega)

theorem jscan_strlen (n : Nat) : ∀ (l s r : List Char), l.length ≤ n →
    jscan l = some (s, r) → s.length + r.length < l.length := by
  induction n with
  | zero =>
    intro l s r hl h
    cases l with
    | nil => simp [jscan] at h
    | cons _ _ => simp at hl
  | succ n ih =>
    intro l s r hl h
    match l with
    | [] => simp [jscan] at h
    | c :: rest =>
      rw [jscan.eq_def] at h
      simp only at h
      by_cases hq : c = '"'
      · rw [if_pos hq] at h
        cases h
        simp
      · rw [if_neg hq] at h
        by_cases hb : c = '\\'
        · rw [if_pos hb] at h
          match rest with
          | [] => simp at h
          | e :: rest' =>
            simp only at h
            cases hj : jscan rest' with
            | none => rw [hj] at h; simp at h
            | some p =>
              obtain ⟨s', r'⟩ := p
              rw [hj] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have := ih rest' s' r' (by simp at hl; omega) hj
              simp; omega
        · rw [if_neg hb] at h
          cases hj : jscan rest with
          | none => rw [hj] at h; simp at h
          | some p =>
            obtain ⟨s', r'⟩ := p
            rw [hj] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have := ih rest s' r' (by simp at hl; omega) hj
            simp; omega

theorem jstring_strlen (l s r : List Char) (h : jstring l = .ok (s, r)) :
    s.length + r.length < l.length := by
  unfold jstring at h
  cases hj : jscan l with
  | none => rw [hj] at h; cases h
  | some p =>
    obtain ⟨raw, r'⟩ := p
    rw [hj] at h
    simp only at h
    cases hu : junescape raw with
    | error e => rw [hu] at h; cases h
    | ok cs =>
      rw [hu] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h1 := jscan_strlen l.length l raw r' (Nat.le_refl _) hj
      have h2 := junescape_length raw.length raw cs (Nat.le_refl _) hu
      omega

theorem jstrs_ofDec (d : JDec) : jstrs (JVal.ofDec d) = [] := by
  unfold JVal.ofDec; split <;> rfl

theorem jstrsO_cons (kv : List Char × JVal) (kvs : List (List Char × JVal)) :
    jstrsO (kv :: kvs) = kv.1 :: (jstrs kv.2 ++ jstrsO kvs) := by
  obtain ⟨k, v⟩ := kv; rfl

theorem jval_strs_step (f : Nat)
    (harr : ∀ l xs r, jarr f l = .ok (xs, r) → ∀ s ∈ jstrsL xs, s.length + r.length < l.length)
    (hobj : ∀ l kvs r, jobj f l = .ok (kvs, r) → ∀ s ∈ jstrsO kvs, s.length + r.length < l.length) :
    ∀ l v r, jval (f + 1) l = .ok (v, r) → ∀ s ∈ jstrs v, s.length + r.length < l.length := by
  intro l v r h s hs
  rw [jval.eq_2] at h
  have hl := skipWs_length_le l
  cases hsk : skipWs l with
  | nil => rw [hsk] at h; cases h
  | cons c t =>
    rw [hsk] at h hl
    simp only at h
    by_cases hd : (charDigit c).isSome = true
    · rw [if_pos hd] at h
      unfold jnumber at h
      split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [jstrs_ofDec] at hs
    · rw [if_neg hd] at h
      by_cases hm : c = '-'
      · rw [if_pos hm] at h
        unfold jnumber at h
        split at h
        · cases h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [jstrs_ofDec] at hs
      rw [if_neg hm] at h
      by_cases hq : c = '"'
      · rw [if_pos hq] at h
        cases hj : jstring t with
        | error e => rw [hj] at h; cases h
        | ok p =>
          obtain ⟨s', r'⟩ := p
          rw [hj] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [jstrs, List.mem_singleton] at hs
          subst hs
          have := jstring_strlen t _ _ hj
          simp only [List.length_cons] at hl; omega
      · rw [if_neg hq] at h
        by_cases hb : c = '['
        · rw [if_pos hb] at h
          cases hj : jarr f t with
          | error e => rw [hj] at h; cases h
          | ok p =>
            obtain ⟨xs, r'⟩ := p
            rw [hj] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have := harr t _ _ hj s hs
            simp only [List.length_cons] at hl; omega
        · rw [if_neg hb] at h
          by_cases hc : c = '{'
          · rw [if_pos hc] at h
            cases hj : jobj f t with
            | error e => rw [hj] at h; cases h
            | ok p =>
              obtain ⟨kvs, r'⟩ := p
              rw [hj] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have := hobj t _ _ hj s hs
              simp only [List.length_cons] at hl; omega
          · rw [if_neg hc] at h
            split at h <;> first
              | (cases h; done)
              | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
                 obtain ⟨rfl, rfl⟩ := h
                 simp [jstrs] at hs)

theorem jarr_strs_step (f : Nat)
    (hval : ∀ l v r, jval f l = .ok (v, r) → ∀ s ∈ jstrs v, s.length + r.length < l.length)
    (htail : ∀ l xs r, jtail f l = .ok (xs, r) → ∀ s ∈ jstrsL xs, s.length + r.length < l.length) :
    ∀ l xs r, jarr (f + 1) l = .ok (xs, r) → ∀ s ∈ jstrsL xs, s.length + r.length < l.length := by
  intro l xs r h s hs
  rw [jarr.eq_2] at h
  have hl := skipWs_length_le l
  cases hsk : skipWs l with
  | nil => rw [hsk] at h; cases h
  | cons c t =>
    rw [hsk] at h hl
    simp only at h
    by_cases hb : c = ']'
    · rw [if_pos hb] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [jstrsL] at hs
    · rw [if_neg hb] at h
      cases hv : jval f (c :: t) with
      | error e => rw [hv] at h; cases h
      | ok p =>
        obtain ⟨x, r1⟩ := p
        rw [hv] at h
        simp only at h
        cases ht : jtail f r1 with
        | error e => rw [ht] at h; cases h
        | ok q =>
          obtain ⟨ys, r2⟩ := q
          rw [ht] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [jstrsL, List.mem_append] at hs
          have hc2 := (jparser_consumes f).2.2.1 _ _ _ ht
          rcases hs with hs | hs
          · have := hval _ _ _ hv s hs; omega
          · have := htail _ _ _ ht s hs
            have hc1 := (jparser_consumes f).1 _ _ _ hv
            omega

theorem jtail_strs_step (f : Nat)
    (hval : ∀ l v r, jval f l = .ok (v, r) → ∀ s ∈ jstrs v, s.length + r.length < l.length)
    (htail : ∀ l xs r, jtail f l = .ok (xs, r) → ∀ s ∈ jstrsL xs, s.length + r.length < l.length) :
    ∀ l xs r, jtail (f + 1) l = .ok (xs, r) → ∀ s ∈ jstrsL xs, s.length + r.length < l.length := by
  intro l xs r h s hs
  rw [jtail.eq_2] at h
  have hl := skipWs_length_le l
  cases hsk : skipWs l with
  | nil => rw [hsk] at h; cases h
  | cons c t =>
    rw [hsk] at h hl
    simp only at h
    by_cases hb : c = ']'
    · rw [if_pos hb] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [jstrsL] at hs
    · rw [if_neg hb] at h
      by_cases hc : c = ','
      · rw [if_pos hc] at h
        cases hv : jval f t with
        | error e => rw [hv] at h; cases h
        | ok p =>
          obtain ⟨x, r1⟩ := p
          rw [hv] at h
          simp only at h
          cases ht : jtail f r1 with
          | error e => rw [ht] at h; cases h
          | ok q =>
            obtain ⟨ys, r2⟩ := q
            rw [ht] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [jstrsL, List.mem_append] at hs
            have hc2 := (jparser_consumes f).2.2.1 _ _ _ ht
            simp only [List.length_cons] at hl
            rcases hs with hs | hs
            · have := hval _ _ _ hv s hs; omega
            · have := htail _ _ _ ht s hs
              have hc1 := (jparser_consumes f).1 _ _ _ hv
              omega
      · rw [if_neg hc] at h; cases h

theorem jobj_strs_step (f : Nat)
    (hpair : ∀ l kv r, jpair f l = .ok (kv, r) → ∀ s ∈ jstrsO [kv], s.length + r.length < l.length)
    (hotail : ∀ l kvs r, jotail f l = .ok (kvs, r) → ∀ s ∈ jstrsO kvs, s.length + r.length < l.length) :
    ∀ l kvs r, jobj (f + 1) l = .ok (kvs, r) → ∀ s ∈ jstrsO kvs, s.length + r.length < l.length := by
  intro l kvs r h s hs
  rw [jobj.eq_2] at h
  have hl := skipWs_length_le l
  cases hsk : skipWs l with
  | nil => rw [hsk] at h; cases h
  | cons c t =>
    rw [hsk] at h hl
    simp only at h
    by_cases hb : c = '}'
    · rw [if_pos hb] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [jstrsO] at hs
    · rw [if_neg hb] at h
      cases hv : jpair f (c :: t) with
      | error e => rw [hv] at h; cases h
      | ok p =>
        obtain ⟨kv, r1⟩ := p
        rw [hv] at h
        simp only at h
        cases ht : jotail f r1 with
        | error e => rw [ht] at h; cases h
        | ok q =>
          obtain ⟨ys, r2⟩ := q
          rw [ht] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hc2 := (jparser_consumes f).2.2.2.2.2 _ _ _ ht
          rw [jstrsO_cons] at hs
          simp only [List.mem_cons, List.mem_append] at hs
          have hp := hpair _ _ _ hv
          simp only [jstrsO, List.append_nil, List.mem_cons] at hp
          rcases hs with hs | hs | hs
          · have := hp s (Or.inl hs); omega
          · have := hp s (Or.inr hs); omega
          · have := hotail _ _ _ ht s hs
            have hc1 := (jparser_consumes f).2.2.2.2.1 _ _ _ hv
            omega

theorem jpair_strs_step (f : Nat)
    (hval : ∀ l v r, jval f l = .ok (v, r) → ∀ s ∈ jstrs v, s.length + r.length < l.length) :
    ∀ l kv r, jpair (f + 1) l = .ok (kv, r) → ∀ s ∈ jstrsO [kv], s.length + r.length < l.length := by
  intro l kv r h s hs
  rw [jpair.eq_2] at h
  have hl := skipWs_length_le l
  cases hsk : skipWs l with
  | nil => rw [hsk] at h; cases h
  | cons c t =>
    rw [hsk] at h hl
    simp only at h
    by_cases hq : c = '"'
    · rw [if_pos hq] at h
      cases hj : jstring t with
      | error e => rw [hj] at h; cases h
      | ok p =>
        obtain ⟨k, r1⟩ := p
        rw [hj] at h
        simp only at h
        have h1 := jstring_strlen t k r1 hj
        have hl1 := skipWs_length_le r1
        cases hs1 : skipWs r1 with
        | nil => rw [hs1] at h; cases h
        | cons c' r2 =>
          rw [hs1] at h hl1
          simp only at h
          by_cases hc : c' = ':'
          · rw [if_pos hc] at h
            cases hv : jval f r2 with
            | error e => rw [hv] at h; cases h
            | ok q =>
              obtain ⟨v, r3⟩ := q
              rw [hv] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hc3 := (jparser_consumes f).1 _ _ _ hv
              simp only [jstrsO, List.append_nil, List.mem_cons] at hs
              simp only [List.length_cons] at hl hl1
              rcases hs with rfl | hs
              · omega
              · have := hval _ _ _ hv s hs; omega
          · rw [if_neg hc] at h; cases h
    · rw [if_neg hq] at h; cases h

theorem jotail_strs_step (f : Nat)
    (hpair : ∀ l kv r, jpair f l = .ok (kv, r) → ∀ s ∈ jstrsO [kv], s.length + r.length < l.length)
    (hotail : ∀ l kvs r, jotail f l = .ok (kvs, r) → ∀ s ∈ jstrsO kvs, s.length + r.length < l.length) :
    ∀ l kvs r, jotail (f + 1) l = .ok (kvs, r) → ∀ s ∈ jstrsO kvs, s.length + r.length < l.length := by
  intro l kvs r h s hs
  rw [jotail.eq_2] at h
  have hl := skipWs_length_le l
  cases hsk : skipWs l with
  | nil => rw [hsk] at h; cases h
  | cons c t =>
    rw [hsk] at h hl
    simp only at h
    by_cases hb : c = '}'
    · rw [if_pos hb] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [jstrsO] at hs
    · rw [if_neg hb] at h
      by_cases hc : c = ','
      · rw [if_pos hc] at h
        cases hv : jpair f t with
        | error e => rw [hv] at h; cases h
        | ok p =>
          obtain ⟨kv, r1⟩ := p
          rw [hv] at h
          simp only at h
          cases ht : jotail f r1 with
          | error e => rw [ht] at h; cases h
          | ok q =>
            obtain ⟨ys, r2⟩ := q
            rw [ht] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hc2 := (jparser_consumes f).2.2.2.2.2 _ _ _ ht
            simp only [List.length_cons] at hl
            rw [jstrsO_cons] at hs
            simp only [List.mem_cons, List.mem_append] at hs
            have hp := hpair _ _ _ hv
            simp only [jstrsO, List.append_nil, List.mem_cons] at hp
            rcases hs with hs | hs | hs
            · have := hp s (Or.inl hs); omega
            · have := hp s (Or.inr hs); omega
            · have := hotail _ _ _ ht s hs
              have hc1 := (jparser_consumes f).2.2.2.2.1 _ _ _ hv
              omega
      · rw [if_neg hc] at h; cases h

theorem jparser_strs (f : Nat) :
    (∀ l v r, jval f l = .ok (v, r) → ∀ s ∈ jstrs v, s.length + r.length < l.length) ∧
    (∀ l xs r, jarr f l = .ok (xs, r) → ∀ s ∈ jstrsL xs, s.length + r.length < l.length) ∧
    (∀ l xs r, jtail f l = .ok (xs, r) → ∀ s ∈ jstrsL xs, s.length + r.length < l.length) ∧
    (∀ l kvs r, jobj f l = .ok (kvs, r) → ∀ s ∈ jstrsO kvs, s.length + r.length < l.length) ∧
    (∀ l kv r, jpair f l = .ok (kv, r) → ∀ s ∈ jstrsO [kv], s.length + r.length < l.length) ∧
    (∀ l kvs r, jotail f l = .ok (kvs, r) → ∀ s ∈ jstrsO kvs, s.length + r.length < l.length) := by
  induction f with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro l x r h <;> cases h
  | succ f ih =>
    obtain ⟨hv, ha, ht, ho, hp, hot⟩ := ih
    exact ⟨jval_strs_step f ha ho, jarr_strs_step f hv ht, jtail_strs_step f hv ht,
           jobj_strs_step f hp hot, jpair_strs_step f hv, jotail_strs_step f hp hot⟩

/-- **Every string `jparse` returns is shorter than the input.** -/
theorem jparse_strs (l : List Char) (v : JVal) (h : jparse l = .ok v) :
    ∀ s ∈ jstrs v, s.length < l.length := by
  intro s hs
  unfold jparse jparseWith at h
  split at h
  · cases h
  next v' rest hv =>
    split at h
    · cases h
      have := (jparser_strs _).1 _ _ _ hv s hs; omega
    · cases h

/-! ## Laws: every string an entry holds came from its line -/

theorem FR.pair_ok {α β : Type} {x : FR α} {y : FR β} {p : α × β} (h : FR.pair x y = .ok p) :
    x = .ok p.1 ∧ y = .ok p.2 := by
  cases x <;> cases y <;> simp [FR.pair] at h ⊢ <;> subst h <;> simp

theorem mem_jstrsO_of_mem (kvs : List (List Char × JVal)) (kv : List Char × JVal) (h : kv ∈ kvs) :
    kv.1 ∈ jstrsO kvs ∧ ∀ s ∈ jstrs kv.2, s ∈ jstrsO kvs := by
  induction kvs with
  | nil => cases h
  | cons p ps ih =>
    rw [jstrsO_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨List.mem_cons_self, fun s hs => List.mem_cons_of_mem _ (List.mem_append_left _ hs)⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ (List.mem_append_right _ h1),
        fun s hs => List.mem_cons_of_mem _ (List.mem_append_right _ (h2 s hs))⟩

theorem jstrsO_sub (xs ys : List (List Char × JVal)) (h : ∀ kv ∈ xs, kv ∈ ys) :
    ∀ s ∈ jstrsO xs, s ∈ jstrsO ys := by
  induction xs with
  | nil => intro s hs; cases hs
  | cons p ps ih =>
    intro s hs
    rw [jstrsO_cons] at hs
    have hp := mem_jstrsO_of_mem ys p (h p List.mem_cons_self)
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hp.1
    · rcases List.mem_append.mp hs with hs | hs
      · exact hp.2 s hs
      · exact ih (fun kv hkv => h kv (List.mem_cons_of_mem _ hkv)) s hs

theorem allStrs_mem (xs : List JVal) (ss : List (List Char)) (h : allStrs xs = some ss) :
    ∀ s ∈ ss, JVal.str s ∈ xs := by
  unfold allStrs at h
  suffices H : ∀ (ys : List JVal) (acc out : List (List Char)), ys.foldl strStep (some acc) = some out →
      ∀ s ∈ out, s ∈ acc ∨ JVal.str s ∈ ys by
    cases hf : xs.foldl strStep (some []) with
    | none => rw [hf] at h; cases h
    | some out =>
      rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      intro s hs
      rcases H xs [] out hf s (List.mem_reverse.mp hs) with h | h
      · cases h
      · exact h
  intro ys
  induction ys with
  | nil => intro acc out h s hs; simp at h; subst h; exact Or.inl hs
  | cons y ys ih =>
    intro acc out h s hs
    simp only [List.foldl_cons] at h
    cases y with
    | str t =>
      simp only [strStep] at h
      rcases ih (t :: acc) out h s hs with h1 | h1
      · rcases List.mem_cons.mp h1 with rfl | h1
        · exact Or.inr List.mem_cons_self
        · exact Or.inl h1
      · exact Or.inr (List.mem_cons_of_mem _ h1)
    | _ =>
      simp only [strStep] at h
      have : ∀ zs : List JVal, zs.foldl strStep none = none := by
        intro zs; induction zs with
        | nil => rfl
        | cons z zs ihz => simp only [List.foldl_cons, strStep]; exact ihz
      rw [this] at h; cases h

theorem readF_strs (k : List Char) : ∀ (t : FTy) (ov : Option JVal) (x : t.T), readF k t ov = .ok x →
    ∀ s ∈ strsOfF t x, ∃ v, ov = some v ∧ s ∈ jstrs v
  | .str, none, x, h => by simp [readF] at h
  | .str, some v, x, h => by
    cases v <;> simp [readF] at h
    subst h; intro s hs; simp [strsOfF] at hs; subst hs; exact ⟨_, rfl, by simp [jstrs]⟩
  | .optStr, none, x, h => by simp [readF] at h; subst h; simp [strsOfF]
  | .optStr, some v, x, h => by
    cases v <;> simp [readF] at h
    · subst h; simp [strsOfF]
    · subst h; intro s hs; simp [strsOfF] at hs; subst hs; exact ⟨_, rfl, by simp [jstrs]⟩
  | .strs, none, x, h => by simp [readF] at h; subst h; simp [strsOfF]
  | .strs, some v, x, h => by
    cases v with
    | arr xs =>
      simp only [readF] at h
      split at h
      · next ss hss =>
        cases h
        intro s hs
        refine ⟨_, rfl, ?_⟩
        show s ∈ jstrsL xs
        have hm := allStrs_mem xs _ hss s hs
        clear hss hs
        induction xs with
        | nil => cases hm
        | cons y ys ih =>
          simp only [jstrsL, List.mem_append]
          rcases List.mem_cons.mp hm with rfl | hm
          · exact Or.inl (by simp [jstrs])
          · exact Or.inr (ih hm)
      · cases h
    | _ => simp [readF] at h
  | .pair, none, x, h => by simp [readF] at h
  | .pair, some v, x, h => by
    cases v with
    | arr xs =>
      match xs, h with
      | [.str a, .str b], h =>
        simp [readF] at h; subst h
        intro s hs; refine ⟨_, rfl, ?_⟩
        simp [strsOfF] at hs; simp [jstrs, jstrsL]; exact hs
      | [], h => simp [readF] at h
      | [_], h => simp [readF] at h
      | _ :: _ :: _ :: _, h => simp [readF] at h
      | [.null, _], h | [.bool _, _], h | [.num _, _], h | [.dec _, _], h | [.arr _, _], h
      | [.obj _, _], h => simp [readF] at h
      | [.str _, .null], h | [.str _, .bool _], h | [.str _, .num _], h | [.str _, .dec _], h
      | [.str _, .arr _], h | [.str _, .obj _], h => simp [readF] at h
    | _ => simp [readF] at h
  | .u8, ov, x, _ => by simp [strsOfF]
  | .u32, ov, x, _ => by simp [strsOfF]
  | .u32d, ov, x, _ => by simp [strsOfF]
  | .optU8, ov, x, _ => by simp [strsOfF]
  | .optU32, ov, x, _ => by simp [strsOfF]
  | .flag, ov, x, _ => by simp [strsOfF]
  | .num, ov, x, _ => by simp [strsOfF]

theorem readArgs_strs (kvs : List (List Char × JVal)) :
    ∀ (s : List (List Char × FTy)) (a : Args s), readArgs kvs s = .ok a →
      ∀ str ∈ argStrs s a, str ∈ jstrsO kvs
  | [], (), _ => by simp [argStrs]
  | (k, t) :: s, (x, xs), h => by
    simp only [readArgs] at h
    obtain ⟨h1, h2⟩ := FR.pair_ok h
    intro str hstr
    simp only [argStrs, List.mem_append] at hstr
    rcases hstr with hstr | hstr
    · obtain ⟨v, hv, hsv⟩ := readF_strs k t _ x h1 str hstr
      exact (mem_jstrsO_of_mem kvs (k, v) (lastVal_mem kvs k v hv)).2 str hsv
    · exact readArgs_strs kvs s xs h2 str hstr

theorem dedupStep_sub : ∀ (xs acc : List (List Char × JVal)) (kv : List Char × JVal),
    kv ∈ xs.foldl dedupStep acc → kv ∈ acc ∨ kv ∈ xs
  | [], acc, kv, h => Or.inl h
  | x :: xs, acc, kv, h => by
    simp only [List.foldl_cons] at h
    rcases dedupStep_sub xs _ kv h with h | h
    · unfold dedupStep at h
      split at h
      · split at h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inr List.mem_cons_self
          · exact Or.inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inr List.mem_cons_self
          · exact Or.inl h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr List.mem_cons_self
        · cases h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem restOf_sub (kvs : List (List Char × JVal)) : ∀ kv ∈ restOf kvs, kv ∈ kvs := by
  intro kv h
  unfold restOf at h
  rcases dedupStep_sub _ [] kv (List.mem_reverse.mp h) with h | h
  · cases h
  · exact (List.mem_filter.mp (List.mem_mergeSort.mp h)).1

/-- What an entry verdict says about its line: the trimmed line is within the bound, parses to an
object, and that object reads as the entry. -/
theorem readLine_entry_inv (n : Nat) (l : List Char) (e : Entry) (h : readLine n (some l) = .entry e) :
    ∃ kvs, (trimCR l).length ≤ maxLineChars ∧ jparse (trimCR l) = .ok (.obj kvs) ∧
      readObject n kvs = .entry e := by
  simp only [readLine] at h
  by_cases hb : (trimCR l).all LogStamp.isRustSpace = true
  · rw [if_pos hb] at h; cases h
  rw [if_neg hb] at h
  by_cases hl : maxLineChars < (trimCR l).length
  · rw [if_pos hl] at h; cases h
  rw [if_neg hl] at h
  by_cases hd : maxLineDepth < depthOf (trimCR l)
  · rw [if_pos hd] at h; cases h
  rw [if_neg hd] at h
  cases hp : jparse (trimCR l) with
  | error x => rw [hp] at h; cases h
  | ok v =>
    rw [hp] at h
    simp only [readValue] at h
    by_cases hf : allFinite v = true
    · rw [if_pos hf] at h
      cases v with
      | obj kvs => exact ⟨kvs, Nat.not_lt.mp hl, rfl, h⟩
      | _ => cases h
    · rw [if_neg hf] at h; cases h

/-- **`lineTooLong` bounds every string** (design §15, B3; R10; added and discharged in B3): every
string an entry holds is no longer than the line bound. -/
theorem lineTooLong_bounds_every_string (n : Nat) (l : List Char) (e : Entry)
    (h : readLine n (some l) = .entry e) : ∀ s ∈ e.ev.strings, s.length ≤ maxLineChars := by
  intro s hs
  obtain ⟨kvs, hlen, hp, ho⟩ := readLine_entry_inv n l e h
  have hbound := jparse_strs _ _ hp
  suffices hin : s ∈ jstrsO kvs by have := hbound s hin; omega
  simp only [readObject] at ho
  cases ht : readT kvs with
  | error w => rw [ht] at ho; cases ho
  | ok p =>
    rw [ht] at ho
    obtain ⟨t, o⟩ := p
    simp only at ho
    cases hev : lastVal kvs kEv with
    | none => rw [hev] at ho; cases ho
    | some v =>
      rw [hev] at ho
      cases v with
      | str tag =>
        simp only at ho
        cases hk : kindOf tag with
        | some k =>
          rw [hk] at ho
          simp only at ho
          cases ha : readArgs kvs k.schema with
          | ok a =>
            rw [ha] at ho
            simp only [Verdict.entry.injEq] at ho
            subst ho
            rw [Event.strings_of_split _ k a (Event.split_build k a)] at hs
            exact readArgs_strs kvs k.schema a ha s hs
          | missing key => rw [ha] at ho; cases ho
          | bad key => rw [ha] at ho; cases ho
        | none =>
          rw [hk] at ho
          simp only [Verdict.entry.injEq] at ho
          subst ho
          simp only [Event.strings, List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact (mem_jstrsO_of_mem kvs _ (lastVal_mem kvs kEv _ hev)).2 s (by simp [jstrs])
          · exact jstrsO_sub _ _ (restOf_sub kvs) s hs
      | _ => cases ho

/-! ## Laws: `finiteF64`'s cost -/

/-- The value of a digit run, as a number. -/
def digitsValue (a : Nat) (l : List (Fin 10)) : Nat := l.foldl (fun a f => a * 10 + f.val) a

theorem digitsValue_ge (a : Nat) (l : List (Fin 10)) : a ≤ digitsValue a l := by
  induction l generalizing a with
  | nil => exact Nat.le_refl _
  | cons f l ih =>
    simp only [digitsValue, List.foldl_cons]
    exact Nat.le_trans (by omega) (ih (a * 10 + f.val))

theorem capExp_none (l : List (Fin 10)) : l.foldl (fun a f => capExp a f.val) none = none := by
  induction l with
  | nil => rfl
  | cons f l ih => simpa [capExp] using ih

theorem capExp_fold (l : List (Fin 10)) (a : Nat) (ha : a ≤ i32Max) :
    l.foldl (fun acc f => capExp acc f.val) (some a) =
      if i32Max < digitsValue a l then none else some (digitsValue a l) := by
  induction l generalizing a with
  | nil => simp [digitsValue, Nat.not_lt.mpr ha]
  | cons f l ih =>
    rw [List.foldl_cons]
    have hstep : capExp (some a) f.val =
        if i32Max < a * 10 + f.val then none else some (a * 10 + f.val) := rfl
    have hv : digitsValue a (f :: l) = digitsValue (a * 10 + f.val) l := rfl
    rw [hstep, hv]
    by_cases h : i32Max < a * 10 + f.val
    · rw [if_pos h, capExp_none, if_pos (Nat.lt_of_lt_of_le h (digitsValue_ge _ _))]
    · rw [if_neg h, ih _ (by omega)]

/-- **Past `i32::MAX`, an exponent's digits decide nothing but its sign** (design §5.4's cost
bound, CRIT 14; the design's `finiteF64_reads_only_the_digit_counts_beyond_seven_exponent_digits`,
restated for serde's algorithm, whose cut is `i32::MAX` and not seven digits): a numeral whose
exponent is written with a value above 2,147,483,647 is finite exactly when the exponent is
negative or the kept significand is zero.  No power of ten is computed and the exponent's value is
never formed. -/
theorem finiteF64_reads_only_the_sign_past_an_i32_exponent (d : JDec) (neg : Bool) (x : Fin 10)
    (xs : List (Fin 10)) (hexp : d.exp = some (neg, x, xs)) (hbig : i32Max < digitsValue 0 (x :: xs)) :
    finiteF64 d = (neg || (capOf d).sig == 0) := by
  have hc := capExp_fold (x :: xs) 0 (by decide)
  rw [if_pos hbig] at hc
  unfold finiteF64
  simp only [hexp, Option.isNone_some, Bool.and_false, Bool.false_and, Bool.false_eq_true, if_false]
  rw [hc]

/-! ## Laws: R10, the widths and the bounds refuse by name -/

theorem readF_refuses_a_u8_past_255 (k : List Char) (n : Nat) (h : 256 ≤ n) :
    readF k .u8 (some (.num n)) = .bad k ∧ readF k .optU8 (some (.num n)) = .bad k := by
  simp [readF, Nat.not_lt.mpr h]

theorem readF_refuses_a_u32_past_its_width (k : List Char) (n : Nat) (h : 4294967296 ≤ n) :
    readF k .u32 (some (.num n)) = .bad k ∧ readF k .u32d (some (.num n)) = .bad k ∧
      readF k .optU32 (some (.num n)) = .bad k := by
  simp [readF, Nat.not_lt.mpr h]

/-- A numeral that is not a bare natural (`-0`, `3.0`, `1e2`, `-1`) is a type error at an integer
field, as serde's float/negative-integer visitors make it (B3 probe, lines 1, 2, 5, 6). -/
theorem readF_refuses_a_decimal_at_an_integer_field (k : List Char)
    (d : { d : JDec // d.plain = false }) :
    readF k .u8 (some (.dec d)) = .bad k ∧ readF k .u32 (some (.dec d)) = .bad k ∧
      readF k .u32d (some (.dec d)) = .bad k ∧ readF k .optU8 (some (.dec d)) = .bad k ∧
      readF k .optU32 (some (.dec d)) = .bad k := by
  simp [readF]

/-- ...and it is accepted, as written, at `hsw`. -/
theorem readF_reads_hsw_as_written (k : List Char) (d : { d : JDec // d.plain = false }) (n : Nat) :
    readF k .num (some (.dec d)) = .ok (.dec d) ∧ readF k .num (some (.num n)) = .ok (.nat n) ∧
      readF k .num none = .ok Num.zero := by
  simp [readF]

theorem readLine_refuses_a_line_past_the_bound (n : Nat) (l : List Char)
    (hb : (trimCR l).all LogStamp.isRustSpace = false) (hl : maxLineChars < (trimCR l).length) :
    readLine n (some l) = .warn n .lineTooLong := by
  simp [readLine, hb, hl]

theorem readLine_refuses_a_line_nested_past_the_bound (n : Nat) (l : List Char)
    (hb : (trimCR l).all LogStamp.isRustSpace = false) (hl : (trimCR l).length ≤ maxLineChars)
    (hd : maxLineDepth < depthOf (trimCR l)) :
    readLine n (some l) = .warn n .lineTooDeep := by
  simp [readLine, hb, Nat.not_lt.mpr hl, hd]

theorem readLine_refuses_a_line_that_is_not_utf8 (n : Nat) : readLine n none = .warn n .invalidUtf8 := rfl

section Witnesses
/- The decided witnesses below unfold the reader a few thousand levels deep in the elaborator: the
recursion budget, not a heartbeat or memory budget, is raised for this section only (as `Json.lean`
does file-wide), and every witness was probed under `MemoryMax=8G timeout 120` (§14.0 item 4). -/
set_option maxRecDepth 8000

/-! ## Witnesses: `tests/fixtures/logs/malformed.jsonl`, line by line

`kernel/corpus/logs/malformed.jsonl` (the fork's fixture, 11 lines and a final newline).  Every
warning line is decided on its bytes, spelled as a `List Char` (§5.10a); the good lines are
instances of `the_log_reads_what_it_renders`, so the reader is never run on them under `decide`:
only `renderLine` and `Entry.canonical` are.  Line 5 is 96 characters, over §14.0 item 4's 90, so it
is not parsed either: it is `jemit` of its value (`jparse_jemit` is the rewrite), and only the reading
of that value is decided. -/

def malformedLine1 : List Char :=
  ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','7','T','0','6',':','0','5',':','0','0','-','0','5',':','0','0','"',',','"','e','v','"',':','"','w','a','k','e','"',',','"','s','l','e','p','t','_','m','i','n','"',':','4','9','0','}']

def malformedLine2 : List Char :=
  ['t','h','i','s',' ','i','s',' ','n','o','t',' ','j','s','o','n']

def malformedLine3 : List Char :=
  ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','7','T','0','7',':','0','0',':','0','0','-','0','5',':','0','0','"',',','"','e','v','"',':','"','w','a','k','e','"','}']

def malformedLine4 : List Char :=
  ['{','"','e','v','"',':','"','n','o','t','e','"',',','"','t','e','x','t','"',':','"','n','o',' ','t','i','m','e','s','t','a','m','p','"','}']

def malformedLine5 : List Char :=
  ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','7','T','0','7',':','3','0',':','0','0','-','0','5',':','0','0','"',',','"','e','v','"',':','"','d','o','n','e','"',',','"','i','d','"',':','"','t','1','"',',','"','e','s','t','_','m','i','n','"',':','"','s','i','x','t','y','"',',','"','a','c','t','u','a','l','_','m','i','n','"',':','6','7',',','"','c','i','"',':','5','}']

def malformedLine6 : List Char :=
  ['{','"','t','"',':','"','n','o','t',' ','a',' ','t','i','m','e','"',',','"','e','v','"',':','"','n','o','t','e','"',',','"','t','e','x','t','"',':','"','b','a','d',' ','t','i','m','e','"','}']

def malformedLine7 : List Char :=
  ['[','1',',','2',',','3',']']

def malformedLine8 : List Char :=
  []

def malformedLine9 : List Char :=
  ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','7','T','0','8',':','0','0',':','0','0','-','0','5',':','0','0','"',',','"','e','v','"',':','"','m','o','o','d','"',',','"','l','e','v','e','l','"',':','3','}']

def malformedLine10 : List Char :=
  ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','7','T','0','8',':','3','0',':','0','0','-','0','5',':','0','0','"',',','"','e','v','"',':','7','}']

def malformedLine11 : List Char :=
  ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','7','T','0','9',':','0','0',':','0','0','-','0','5',':','0','0','"',',','"','e','v','"',':','"','n','o','t','e','"',',','"','t','e','x','t','"',':','"','l','a','s','t',' ','g','o','o','d',' ','l','i','n','e','"','}']

/-- 2026-09-07T06:05:00-05:00, 07:30, 08:00 and 09:00 in `Cal.Instant` seconds (B2's
`renderStamp_is_fmt_timestamp` fixes the first), and `-05:00`. -/
def at0605 : VInstant := ⟨⟨63924375900, 0⟩, by decide⟩
def at0800 : VInstant := ⟨⟨63924382800, 0⟩, by decide⟩
def at0900 : VInstant := ⟨⟨63924386400, 0⟩, by decide⟩
def cdt : VOffset := ⟨⟨true, 18000⟩, by decide⟩

def malformedEntry1 : Entry := ⟨1, at0605, cdt, .wake ⟨490, by decide⟩ none⟩
def malformedEntry9 : Entry := ⟨9, at0800, cdt, .unknown ['m','o','o','d'] [(['l','e','v','e','l'], .num 3)]⟩
def malformedEntry11 : Entry := ⟨11, at0900, cdt, .note ['l','a','s','t',' ','g','o','o','d',' ','l','i','n','e']⟩

theorem malformed_line_1_is_a_wake : readLine 1 (some malformedLine1) = .entry malformedEntry1 := by
  have h : malformedLine1 = renderLine malformedEntry1 := by decide
  rw [h]; exact the_log_reads_what_it_renders _ (by decide)

theorem malformed_line_2_is_not_json :
    readLine 2 (some malformedLine2) = .warn 2 (.notJson (.notAValue 't')) := by decide

theorem malformed_line_3_is_a_wake_without_slept_min :
    readLine 3 (some malformedLine3) = .warn 3 (.missingField ['s','l','e','p','t','_','m','i','n']) := by
  decide

theorem malformed_line_4_has_no_t : readLine 4 (some malformedLine4) = .warn 4 .noT := by decide

/-- Line 5's value: `{"t":…,"ev":"done","id":"t1","est_min":"sixty","actual_min":67,"ci":5}`. -/
def malformedValue5 : JVal :=
  .obj [(kT, .str ['2','0','2','6','-','0','9','-','0','7','T','0','7',':','3','0',':','0','0','-','0','5',':','0','0']),
    (kEv, .str ['d','o','n','e']), (['i','d'], .str ['t','1']),
    (['e','s','t','_','m','i','n'], .str ['s','i','x','t','y']),
    (['a','c','t','u','a','l','_','m','i','n'], .num 67), (['c','i'], .num 5)]

theorem malformed_line_5_is_a_done_with_est_min_sixty :
    readLine 5 (some malformedLine5) = .warn 5 (.badField ['e','s','t','_','m','i','n']) := by
  have h : malformedLine5 = jemit malformedValue5 := by decide
  have ht : trimCR malformedLine5 = malformedLine5 := by rw [h]; exact trimCR_jemit_obj _
  rw [readLine_of_parse 5 _ malformedValue5 (by rw [ht, h]; exact not_blank_jemit_obj _)
    (by rw [ht, h]; decide) (by rw [ht, h]; decide) (by rw [ht, h]; exact jparse_jemit _)]
  decide

theorem malformed_line_6_has_a_t_that_is_not_a_stamp :
    readLine 6 (some malformedLine6) = .warn 6 (.badT .tooShort) := by decide

theorem malformed_line_7_is_an_array : readLine 7 (some malformedLine7) = .warn 7 .notAnObject := by
  decide

theorem malformed_line_8_is_blank : readLine 8 (some malformedLine8) = .blank := by decide

/-- Line 9, `{"t":…,"ev":"mood","level":3}`, is an entry, and it meets every hypothesis of
`an_unknown_tag_is_never_a_warning` (which is therefore not vacuous). -/
theorem malformed_line_9_is_an_unknown_mood :
    readLine 9 (some malformedLine9) = .entry malformedEntry9 ∧
      isObjectWithStampAndTag malformedLine9 = true ∧ isKnownTag (tagIn malformedLine9) = false ∧
      malformedLine9.length ≤ maxLineChars ∧ depthOf malformedLine9 ≤ maxLineDepth ∧
      allNumeralsFinite malformedLine9 = true := by
  have h : malformedLine9 = renderLine malformedEntry9 := by decide
  refine ⟨?_, ?_, ?_, by decide, by decide, ?_⟩
  · rw [h]; exact the_log_reads_what_it_renders _ (by decide)
  · rw [h]; unfold renderLine lineVal isObjectWithStampAndTag; rw [trimCR_jemit_obj, jparse_jemit]; decide
  · rw [h]; unfold renderLine lineVal tagIn; rw [trimCR_jemit_obj, jparse_jemit]; decide
  · rw [h]; unfold renderLine lineVal allNumeralsFinite; rw [trimCR_jemit_obj, jparse_jemit]; decide

theorem malformed_line_10_has_an_ev_that_is_not_a_string :
    readLine 10 (some malformedLine10) = .warn 10 .evNotString := by decide

theorem malformed_line_11_is_a_note : readLine 11 (some malformedLine11) = .entry malformedEntry11 := by
  have h : malformedLine11 = renderLine malformedEntry11 := by decide
  rw [h]; exact the_log_reads_what_it_renders _ (by decide)

/-- **The malformed corpus reads as the fork point did**: 3 entries (`wake`, the unknown `mood`,
`note`), 7 warnings of 7 classes, and the blank line (fork `Log::parse_bytes`, inventory §0.1; B3
probe: every class agrees with serde's error on these lines). -/
theorem the_malformed_corpus_reads_as_the_fork_point_did :
    [readLine 1 (some malformedLine1), readLine 2 (some malformedLine2), readLine 3 (some malformedLine3),
     readLine 4 (some malformedLine4), readLine 5 (some malformedLine5), readLine 6 (some malformedLine6),
     readLine 7 (some malformedLine7), readLine 8 (some malformedLine8), readLine 9 (some malformedLine9),
     readLine 10 (some malformedLine10), readLine 11 (some malformedLine11)] =
    [.entry malformedEntry1, .warn 2 (.notJson (.notAValue 't')),
     .warn 3 (.missingField ['s','l','e','p','t','_','m','i','n']), .warn 4 .noT,
     .warn 5 (.badField ['e','s','t','_','m','i','n']), .warn 6 (.badT .tooShort), .warn 7 .notAnObject,
     .blank, .entry malformedEntry9, .warn 10 .evNotString, .entry malformedEntry11] := by
  rw [malformed_line_1_is_a_wake, malformed_line_2_is_not_json,
    malformed_line_3_is_a_wake_without_slept_min, malformed_line_4_has_no_t,
    malformed_line_5_is_a_done_with_est_min_sixty, malformed_line_6_has_a_t_that_is_not_a_stamp,
    malformed_line_7_is_an_array, malformed_line_8_is_blank, malformed_line_9_is_an_unknown_mood.1,
    malformed_line_10_has_an_ev_that_is_not_a_string, malformed_line_11_is_a_note]

/-! ## Witnesses: the other warnings, and the numeral an unknown event cannot hide -/

/-- `{"t":"2026-09-07T08:00:00-05:00","ev":"mood","x":1e400}`. -/
def moodOutOfRange : List Char :=
  ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','7','T','0','8',':','0','0',':','0','0','-','0','5',':','0','0','"',',','"','e','v','"',':','"','m','o','o','d','"',',','"','x','"',':','1','e','4','0','0','}']

/-- **An out-of-range numeral warns even in an unknown event** (design §5.4, G-d, CRIT 15; cheat 130):
the line meets every other hypothesis of `an_unknown_tag_is_never_a_warning`, and is still a
warning, because the fork collects the whole line as a `Map<String, Value>` first. -/
theorem an_out_of_range_numeral_warns_even_in_an_unknown_event :
    readLine 1 (some moodOutOfRange) = .warn 1 .numberOutOfRange ∧
      isObjectWithStampAndTag moodOutOfRange = true ∧ isKnownTag (tagIn moodOutOfRange) = false ∧
      allNumeralsFinite moodOutOfRange = false :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **Every line warning is reachable**, each by a line of its own (the corpus lines above, and four
short ones); `lineTooLong` by a 65,537-character line through `readLine_refuses_a_line_past_the_bound`,
whose length is rewritten, never evaluated. -/
theorem every_line_warning_is_reachable :
    (∃ n, readLine n none = .warn n .invalidUtf8) ∧
    (∃ n l, readLine n (some l) = .warn n .lineTooLong) ∧
    (∃ n l, readLine n (some l) = .warn n .lineTooDeep) ∧
    (∃ n l e, readLine n (some l) = .warn n (.notJson e)) ∧
    (∃ n l, readLine n (some l) = .warn n .numberOutOfRange) ∧
    (∃ n l, readLine n (some l) = .warn n .notAnObject) ∧
    (∃ n l, readLine n (some l) = .warn n .noT) ∧
    (∃ n l, readLine n (some l) = .warn n .tNotString) ∧
    (∃ n l e, readLine n (some l) = .warn n (.badT e)) ∧
    (∃ n l, readLine n (some l) = .warn n .duplicateT) ∧
    (∃ n l, readLine n (some l) = .warn n .noEv) ∧
    (∃ n l, readLine n (some l) = .warn n .evNotString) ∧
    (∃ n l k, readLine n (some l) = .warn n (.missingField k)) ∧
    (∃ n l k, readLine n (some l) = .warn n (.badField k)) := by
  refine ⟨⟨0, rfl⟩, ⟨0, List.replicate 65536 'x' ++ ['x'], ?_⟩, ⟨0, List.replicate 65 '[', by decide⟩,
    ⟨2, _, _, malformed_line_2_is_not_json⟩, ⟨1, _, an_out_of_range_numeral_warns_even_in_an_unknown_event.1⟩,
    ⟨7, _, malformed_line_7_is_an_array⟩, ⟨4, _, malformed_line_4_has_no_t⟩,
    ⟨0, ['{','"','t','"',':','5','}'], by decide⟩, ⟨6, _, _, malformed_line_6_has_a_t_that_is_not_a_stamp⟩,
    ⟨0, ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','7','T','0','6',':','0','5',':','0','0','-','0','5',':','0','0','"',',','"','t','"',':','"','2','0','2','6','-','0','9','-','0','7','T','0','6',':','0','5',':','0','0','-','0','5',':','0','0','"','}'], by decide⟩,
    ⟨0, ['{','"','t','"',':','"','2','0','2','6','-','0','9','-','0','7','T','0','6',':','0','5',':','0','0','-','0','5',':','0','0','"','}'], by decide⟩,
    ⟨10, _, malformed_line_10_has_an_ev_that_is_not_a_string⟩,
    ⟨3, _, _, malformed_line_3_is_a_wake_without_slept_min⟩,
    ⟨5, _, _, malformed_line_5_is_a_done_with_est_min_sixty⟩⟩
  apply readLine_refuses_a_line_past_the_bound
  · rw [trimCR_of_last _ _ (by decide), List.all_append]
    have hx : ['x'].all LogStamp.isRustSpace = false := by decide
    rw [hx, Bool.and_false]
  · rw [trimCR_of_last _ _ (by decide), List.length_append, List.length_replicate]; decide

/-! ## Witnesses: serde's float band (B3 probe, lines 36, 37, 39 and 49) -/

set_option exponentiation.threshold 1100 in
set_option maxRecDepth 20000 in
/-- `1.7976931348623157e308` is finite and `1.7976931348623158e308` is not; `1e309` is not; the
309-digit integer spelling of `f64::MAX` itself is **not** finite to serde, whose significand keeps
20 of its digits (IEEE's reading of the same decimal is finite; this is why the band is ported, not
derived); and `1e9999999999` and `1e-9999999999` meet
`finiteF64_reads_only_the_sign_past_an_i32_exponent`'s hypothesis and read by the sign alone.  The
power `10 ^ 292` is past the elaborator's default `exponentiation.threshold` (256),
which is raised for this one theorem; it bounds the size of a literal power, not memory. -/
theorem finiteF64_is_serdes_band :
    finiteF64 ⟨false, 1, [7,9,7,6,9,3,1,3,4,8,6,2,3,1,5,7], some (false, 3, [0,8])⟩ = true ∧
    finiteF64 ⟨false, 1, [7,9,7,6,9,3,1,3,4,8,6,2,3,1,5,8], some (false, 3, [0,8])⟩ = false ∧
    finiteF64 ⟨false, 1, [], some (false, 3, [0,9])⟩ = false ∧
    finiteF64 ⟨false, (2 ^ 53 - 1) * 2 ^ 971, [], none⟩ = false ∧
    (i32Max < digitsValue 0 [9,9,9,9,9,9,9,9,9,9] ∧
      finiteF64 ⟨false, 1, [], some (false, 9, [9,9,9,9,9,9,9,9,9])⟩ = false ∧
      finiteF64 ⟨false, 1, [], some (true, 9, [9,9,9,9,9,9,9,9,9])⟩ = true) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## Witnesses: the small grammars (B3 differential against `stamp_from_key`, `parse_date`,
`parse_instance_status`) -/

theorem the_small_grammars_read_as_the_fork_does :
    stampFromKey ['2','0','2','6','-','W','3','7'] = some (.week 37) ∧
    stampFromKey ['2','0','2','6','-','W','+','5'] = some (.week 5) ∧
    stampFromKey ['2','0','2','6','-','W','0','0'] = none ∧
    stampFromKey ['2','0','2','0','-','W','5','3'] = some (.week 53) ∧
    stampFromKey [' ','2','0','2','6','-','9','-','0','7'] = some (.day 7) ∧
    stampFromKey ['2','0','2','6','-','0','9'] = none ∧
    instDate? ['2','0','2','6','-','0','9','-','0','7'] = some (Cal.toDay ⟨2026, 9, 7⟩) ∧
    instDate? ['2','0','2','6','-','0','2','-','2','9'] = none ∧
    parseInstanceStatus ['s','k','i','p'] = some .skipped ∧
    parseInstanceStatus ['D','o','n','e'] = none :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

end Witnesses

end Log
end Tm
