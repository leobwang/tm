# Stage 5, D9: the kernel replays the log. A proof-first design

A read-only design pass, written 2026-09-14 against `rebuild-on-lean` at `c2cf4dc`, while stage 5
step 1 (`Tree.lean`, untracked) is in flight. It is built on the fact base
`design/inventory.md`, which it cites as "inv §n". Every Rust function is cited by **name**. Lean
names marked *(new)* do not exist yet. Where this document estimates something it says
**ESTIMATE**. Where it needs a human decision it says **OWNER** and does not take the decision
(§14 lists them).

**The lens.** Maximise what is proved, and keep the proofs tractable. Every trade-off below was
settled by one question: which choice makes the window law a short composition of small lemmas,
not a single large simulation proof?

---

## 0. The design on one page

1. **The log crosses the wire as one JSON string.** It is the raw JSONL text of the tail that is
   being replayed, not an array. Rust does no parsing. It splits nothing but bytes, and it
   reports only which line numbers were not UTF-8 (G9 stays in Rust). One string sidesteps
   gap 44's per-element recursion, because `jscanTR`/`junescapeTR` already carry 1,000,000
   characters on a 2 MiB stack. The kernel splits the lines with a tail-recursive splitter and
   parses each line on its own.
2. **One JSON grammar, widened once.** `JVal` gains one exact-decimal constructor, `dnum`, and
   `jparse_jemit` is re-proved unconditionally. `hsw` becomes an exact signed decimal. No
   `Float` exists, and no second JSON reader.
3. **Instants are UTC `(sec, nano)` pairs from 0001-01-01.** An offset is a sign and a
   magnitude. The timestamp grammar is chrono's `parse_rfc3339` plus the `%Y-%m-%dT%H:%M%:z`
   fallback, ported by name.
4. **The zone is data: a host-supplied offset table for `cfg.tz`.** Rust probes chrono-tz for
   the UTC offset spans. The kernel owns all the arithmetic: local date, local midnight, the
   24-hour rule. Fork-point behaviour is kept exactly (no parity exception beyond clamping
   outside the table), and stage 6 needs the same table for walls and `at:`.
5. **Replay is a left fold over the survivors of a left-fold mask.** Here `survivors =
   reverse (foldl maskStep [] lines)`, and replay is `foldl (step W S) init survivors`. `W` is
   the kept-wake index and `S` the slept-by-day index, both built from the survivors in a
   pre-pass, as `replay_refs` does.
6. **Windowing is a checkpoint, and its correctness is a theorem.** The kernel emits
   `Ckpt = (frame, aggregates, detail for open days, pre-pass frontier)` at a split instant
   `H`. `H` is a local midnight, and every line before the split precedes `H` in time. The
   kernel also emits the observations of the sealed days once, as an **archive** that Rust
   stores and never sends back. The law:
   > if the checkpoint is `checkpoint H D a`, and the decidable guard `resumeGuard ck b` holds,
   > then for every query `q` whose detail range starts at or after `D`:
   > `view q (replayFull (a ++ b)) = view q (resume ck b)`, and
   > `obs (replayFull (a ++ b)) = archive ++ obs (resume ck b)`.

   It composes four lemmas:
   - `foldl_append`, which is free;
   - mask decomposition under a no-reach guard;
   - wake-index locality under an instant partition;
   - a frame lemma saying a step touches only the days its event names.

   A failed guard is a named refusal. Rust then resends the whole log, which is always
   correct, and gets a fresh checkpoint.
7. **Rust keeps file I/O, G9, the checkpoint cache and the observation archive**, both stored
   as opaque kernel JSON, **and the fit.** `Machine`, `replay`, `undo_mask`, `DayIndex`, `Event`'s
   `Deserialize` and every raw-entry walk are deleted from the decision path. The one residual
   trust is that Rust hands back the checkpoint of the exact prefix. It is enforced by a
   content hash in Rust, not by a proof (**OWNER** Q2).

What the per-call wire costs after windowing, from `split_probe.py` on the synthetic 3-year
logs: a 3-day tail of about 180–280 lines, plus a checkpoint whose all-time part is **ESTIMATE**
0.3–0.45 MiB at 3 years. That part is about 900 item totals, 5,800 done-dates, 3,000 instance
records and 1,550 demotions, together with a month of open-day detail. The checkpoint grows at
about **ESTIMATE** 100–150 KiB a year, against 1.5–2.3 MiB a year for the log. This is not
constant. §6.6 names what would be needed to make it so, and why that is not proposed.

---

## 1. The algebra, and why it makes windowing a theorem

The Rust replay (`replay`, then `replay_refs`, inv §2.1) has three non-local dependencies. A
naive "replay the tail from a summary" gets each one wrong:

| non-locality | Rust site | what it means for a tail |
|---|---|---|
| **N1: undo reaches back.** An undo cancels the greatest earlier surviving match, however old | `undo_mask` | a tail undo can cancel a prefix event whose effects are already summarised |
| **N2: the day index is global.** A wake appended later in the file, with an earlier instant, re-attributes earlier events; `slept_by_day` is a pre-pass over every wake | `DayIndex::new`, `slept_by_day` in `replay_refs` | a tail wake can move prefix events to another day |
| **N3: the machine carries state across events.** Open block, last cut, open interruption, the energy observation a later `done` writes `went` onto | `Machine`'s `block`, `last_cut`, `interrupt`, `Block.obs` | the tail's first events read state the prefix built |

The design gives each one a structural answer, so that the window law is a composition:

- **N3 becomes the fold state.** Replay is `List.foldl step st survivors`, so
  `foldl step st (xs ++ ys) = foldl step (foldl step st xs) ys` is `List.foldl_append`. It
  costs nothing to prove. The checkpoint's frame is the fold state, minus the day detail that
  sealing drops (§6.3).
- **N1 becomes a stack fold with a guard.** The mask is `foldl maskStep []` over indexed lines,
  and its state is the reversed survivor list. On a tail `b` over a prefix `a`, masking `b` on
  top of `a`'s stack equals `a`'s survivors followed by `b` masked alone. This holds exactly
  when every undo that dangles in `b` alone also finds no match in `a`'s survivors. The
  checkpoint carries the set of event tags among `a`'s survivors (bounded by 25 known tags plus
  a capped set of unknown ones). The guard is decidable from that set. It is conservative for
  id-carrying undos: a locally dangling undo whose tag occurs in `a` refuses the window.
- **N2 becomes an instant partition at a local midnight.** Suppose every prefix line precedes
  `H` and every tail line is at or after `H`. Then the sorted wake list of `a ++ b` is
  `sorted a ++ sorted b`, and consecutive dedup continues from the last kept wake of `a`, which
  is the one value carried. The last wake at or before `t` is unchanged for `t < H`, and for
  `t ≥ H` it is determined by that value plus `b`'s wakes. These are list lemmas: no DST
  reasoning and no zone monotonicity. What sealing needs, "the tail never touches a sealed
  day", is **checked, not derived**. `resume` computes the days every tail step touches, and
  the guard requires them all to be `≥ ck.openFrom`. That keeps DST out of the proofs entirely.

The one thing no proof in the kernel can cover is that the `Ckpt` Rust sends is the one the
kernel emitted for the bytes that still precede the tail. That is a cache-validity property of
the file system. It is enforced in Rust (§8.3), tested, and named as a trust assumption beside
G9.

**Two consequences worth stating.** First, **a full replay is `resume ckEmpty wholeLog`**, so
there is one code path. The empty checkpoint's guard holds trivially (no survivors, no tags,
`openFrom = 0`, `H = 0`), so `resume_ckEmpty : resume ckEmpty l = replayFull l` restricted to
views is a corollary of the law with `a = []`. Second, **a checkpoint rolls forward without a
full replay.** `resume` can itself seal at a later split, and `seal_seal` (§6.4) says sealing
twice is sealing at the later horizon.

---

## 2. The typed event grammar

### 2.1 JSON: widen `JVal` once, visibly (`Json.lean`)

Log lines contain `"hsw":0.95` and possibly `"hsw":-0.5`, and `Unknown` payloads may hold any
RFC 8259 number (inv §1). Today `jparse` refuses all of these at parse
(`jparse_refuses_what_the_fragment_has_no_type_for`). A second JSON reader for log lines would
be AGENTS §5.3's bug, so the one reader widens. That is the route AGENTS §8.3 names ("widening
`JVal` **visibly**, with the round trip extended").

```lean
/-- A number literal that is not a bare digit string, kept exactly.  The shape makes the
    round trip unconditional: `pos` requires a fraction or an exponent, so a plain
    non-negative integer is always `JVal.num`, never `dnum`. -/
inductive JExp  | mk (neg : Bool) (digits : Nat)                        -- e/E [+-] digits
inductive JFrac | mk (d : Fin 10) (ds : List (Fin 10))                  -- "." 1*DIGIT, kept verbatim
inductive JDec                                                           -- (new)
  | neg (int : Nat) (frac : Option JFrac) (exp : Option JExp)           -- "-" int [frac] [exp]
  | fracPos (int : Nat) (frac : JFrac) (exp : Option JExp)              -- int frac [exp]
  | expPos (int : Nat) (exp : JExp)                                      -- int exp
inductive JVal | null | bool (b : Bool) | num (n : Nat) | dnum (d : JDec)   -- (widened)
               | str (s : List Char) | arr (xs : List JVal) | obj (kvs : List (List Char × JVal))
```

- `jemit (dnum d)` writes the canonical lexeme: no leading zeros in `int`, the fraction digits
  verbatim, and `e`/`-` for the exponent with no `+`. `jparse` accepts RFC 8259 numbers. Leading
  zeros stay accepted, as for `num` (gap 43). An exponent written `E` or `e+05` is read to the
  same `JExp`. **`jparse_jemit` stays unconditional** over the widened type.
- **The refutation, renamed (D5, and AGENTS §3.2's pattern).**
  `jparse_refuses_what_the_fragment_has_no_type_for` is false after widening. It becomes
  `jparse_reads_a_decimal_as_dnum` (`-3`, `1.5` and `1e3` parse to `dnum`). Beside it goes the
  law that keeps the wire honest, `jgetNat_refuses_a_dnum`: every request field read as a
  `Nat` still refuses a decimal.
- **Observable wire change (a behaviour row):** `{"blockMin":1.5}` was refused as
  `bad json: trailingGarbage` and is now refused as `badBlockMin`. It is still refused.
- **Denotation**, used only where a value is needed:
  `JDec.toSDec : JDec → SDec` with `structure SDec where neg : Bool; mant : Nat; exp10 : Int`.
  Nothing expands `10^exp10` except `SDec.finiteF64?` (§2.4), whose exponent work is capped.
- **Surrogate escapes (gap 42) stay refused.** A hand-appended line carrying `😀`
  becomes a line warning where serde accepts it. That is parity exception **P7** (§15). Fixing
  gap 42 is an independent step, and nothing here depends on it.

### 2.2 Instants and offsets (`Time.lean`, new; imports `Cal`)

```lean
structure Instant where  sec : Nat; nano : Fin 1000000000     -- UTC, seconds since 0001-01-01T00:00:00Z
deriving DecidableEq, Repr
def Instant.ns (i : Instant) : Nat := i.sec * 1000000000 + i.nano   -- proofs only
instance : LT Instant   -- lexicographic; `Instant.lt_iff_ns : a < b ↔ a.ns < b.ns`
structure Offset where  west : Bool; min : Fin 1440            -- ±HH:MM, |off| ≤ 23:59 (chrono's check)
def minutesBetween (a b : Instant) : Nat                        -- ⌊(b.ns − a.ns)/60e9⌋, 0 if b ≤ a
```

- **Why `(sec, nano)` and not `Int` or bare nanoseconds.** Chrono keeps nanoseconds, and
  `close_sub` truncates `num_minutes` on the nanosecond difference, so any coarser type is
  wrong on a hand-written fractional second. `sec` since year 1 is about 6.4e10, a small
  `Nat`, while total nanoseconds is about 6.4e19, a big `Nat` on every comparison. The origin
  matches `Cal.Day`'s, and `Instant.day0 i = i.sec / 86400` is a `Day` with no epoch constant.
- **`minutesBetween` is the only duration primitive**, and it saturates at 0. That is exactly
  `num_minutes().max(0)` in `close_sub`. A proved lemma: truncation is toward zero, and for
  `b > a` it equals floor, so the `max(0)` and chrono's truncation agree.
- **Signed values inside the kernel** (an offset, `hsw`) are `sign × magnitude`. `Int` is
  allowed in core but never reaches the wire.

### 2.3 The timestamp grammar (`Time.lean`)

`parseTs : List Char → Except TsErr (Instant × Offset)` is ported from chrono 0.4.45
`format::parse::parse_rfc3339` (read for this pass). It returns the offset only so that tests
can echo it. Nothing downstream reads it: inv §0.2 notes that "instants compare by absolute
time, whatever the offset".

1. At least 19 bytes. `YYYY-MM-DD`, with the date checked by `Cal.Date.valid`
   (`OUT_OF_RANGE` → `TsErr.badDate`).
2. Byte 10 is `T`, `t` or a space.
3. `HH:MM:SS` with hour ≤ 23 and minute ≤ 59. **Second 60 is accepted as 59 plus 10^9
   nanoseconds**, following chrono's leap-second rule. `NaiveTime::from_hms_nano_opt` accepts
   a nanosecond value of up to 1,999,999,999 only when the second is 59.
4. An optional `.` followed by 1 or more digits. The first 9 digits count; the rest are skipped
   (`scan::nanosecond`).
5. The offset: `Z`, `z`, or `±HH:MM` (colon required, HH ≤ 23, MM ≤ 59). Then end of input.
6. **Fallback**, taken only if 1–5 fail: `%Y-%m-%dT%H:%M%:z` (`parse_timestamp`). **The exact
   acceptance of chrono's `parse_from_str` is a porting risk.** It is padding-agnostic and
   allows spaces around numeric items (the `parse` doc comment). So step S2 pins it with a Rust
   differential test (§11, A2) rather than trusting this sentence.

Laws: `parseTs_renderTs` (canonical `YYYY-MM-DDTHH:MM:SS[.fffffffff]±HH:MM` round-trips) and
`parseTs_instant_offset_invariant` (the same instant under two offsets compares equal). Rust's
`hsw_matches_spec` (`+01:00` against `-05:00`) is ported as a `decide` witness on two short
literals.

### 2.4 The events (`LogEvent.lean`, new; imports `Json`, `Time`)

One constructor per `define_events!` tag, in `EVENT_NAMES` order, with Rust's field names and
types. Widths follow R10: `U8 := Fin 256` (serde's `u8`) and `U32 := {n : Nat // n < 2^32}`.
Both are built by smart constructors that the decoder actually uses, with rejection theorems.

```lean
abbrev Id := List Char
structure Hsw where v : SDec            -- `f64` in Rust; exact here; `finiteF64? v = true` enforced by decode
inductive Event                                                           -- (new)
  | wake (sleptMin : U32) (onsetMin : Option U32)
  | arrive (loc : List Char) (window : List Char × List Char) (budget : U32)
  | start (id : Id) (pred : U8) (rep : Option U8) (hsw : Hsw) (sleptMin : U32) (loc : List Char)
          (blocksDone : U32) (sinceBreakMin : U32)                       -- last two decoded, never read (inv §1)
  | done (id : Id) (estMin actualMin : U32) (went : Option U8) (tags : List (List Char)) (ci : U8) (partial : Bool)
  | extend (id : Id) (byMin : U32)          | stop (id : Id) (remainingMin : U32)
  | brk (plannedMin : U32) (actualMin : Option U32) (where_ : Option (List Char))
  | energy (pred rep : U8) (hsw : Hsw) (loc : List Char)
  | interrupt (id : Option Id)              | resume (lostMin : U32) (dropped : List Id)
  | pause (id : Id) | unpause (id : Id)
  | idle (attributed : List Char) (min : U32)
  | routine (item inst status : List Char) (actualMin : Option U32)
  | skip (item inst : List Char)
  | plan (hash : List Char) (replansToday driftMin : U32)
  | named (name : List Char) (id : Option Id)                              -- tag "event"
  | demote (id : Id) (from_ to : List Char) (estMin : U32)
  | readopt (id : Id) | move (id : Id) (from_ to : List Char) | drop (id : Id)
  | edit (id : Id) (field from_ to : List Char) | note (text : List Char)
  | loc (loc : List Char) | close (period key : List Char)
  | undo (of_ : List Char) (id : Option Id)
  | unknown (tag : List Char) (primary : Option Id)        -- `rest` is not kept: nothing reads it but `rest["id"]`
structure Entry where t : Instant; ev : Event
def Event.tag : Event → List Char            -- `Event::name`
def Event.primaryId : Event → Option Id      -- `Event::primary_id`, incl. `unknown`'s rest["id"] when a string
```

**`unknown` keeps only its tag and primary id.** `rest` is serialised back by nobody the grep
found (inv §3), and `Replay.unknown` is a count. This is a deliberate narrowing, recorded as a
difference in the README block. If `tm log` must print an unknown line's payload, it prints
the raw line, which Rust already holds.

**Decoding is strict per kind, and faithful to `Event`'s hand-written `Deserialize`**
(inv §0.2):
- `ev` is read first.
  - A tag in `EVENT_NAMES` decodes strictly: a bad payload is a warning, never `unknown`.
  - Any other string becomes `unknown`.
  - A non-string `ev` is the warning `evNotString`.
  - An absent `ev` is the warning `evAbsent`.
- Extra keys on a known event are ignored.
- `null` in an `Option` field is `none`.
- A `#[serde(default)]` field may be absent: 0, `[]` or `false`.
- An integer must be `JVal.num` within its width. Otherwise the warning is `badField <name>`,
  which is `Known::field_error`'s field.
- `hsw` accepts `num` or `dnum`, and must satisfy `SDec.finiteF64?`: its magnitude must not
  round to infinity in binary64, which is when serde_json fails. That check is decidable, with
  exponent work capped: a decimal exponent above 310 is out, below 300 is in, and between them
  a bignum comparison against `2^1024 − 2^970`.
- `window` must be an array of exactly two strings.
- **Duplicate keys.** serde rejects a duplicate field on a known struct. The kernel refuses
  with `duplicateKey <k>` for any key the decoder reads. The exact serde behaviour under
  `#[serde(flatten)]` is pinned by differential test A3. Any residual difference is parity
  exception P8.

### 2.5 Lines, warnings and tolerance (`LogEvent.lean`)

```lean
inductive LWarn                                          -- (new) every one named, AGENTS §5.7
  | invalidUtf8 | notJson (e : JErr) | notAnObject | tAbsent | badT (e : TsErr)
  | evAbsent | evNotString | badField (k : List Char) | duplicateKey (k : List Char)
  | lineTooLong
inductive LineResult | blank | entry (e : Entry) | warn (w : LWarn)
def parseLine (l : List Char) : LineResult
def splitLog (text : List Char) : List (List Char)       -- on '\n', trailing '\r' trimmed per line; TR (csimp twin)
```

This is a faithful port of `Log::parse_bytes` (inv §0.1):
- Lines are numbered from `firstLine` (1-based).
- A line that is blank after trimming is `blank`, silently.
- A torn last line is just a line.
- A line numbered in the request's `badUtf8` list is `warn invalidUtf8`. Rust has replaced that
  line's bytes with nothing, so no invalid bytes reach a `String` (R9).
- **Line cap.** A line longer than 16 KiB is `warn lineTooLong` before `jparse` sees it. This
  is a deliberate difference: it keeps a pathological `[[[[…` line out of gap 44's
  recursion-depth band. Parity exception P9.

Laws:
- `parseLine_emitLine : parseLine (emitLine e) = .entry e`. `emitLine` is canonical, and is
  used only by proofs and tests. **Rust stays the writer** (§8.1).
- `the_malformed_corpus_reads_as_rust_reads_it`. A `decide` on `kernel/corpus/logs/malformed.jsonl`
  is **not** proposed: 11 lines of `List Char` through `jparse` exceed §5.10a's
  small-witness rule. Instead, one small witness per warning constructor (each line ≤ 60
  characters), and the whole file compared through the FFI in a cargo test (§11, A3).
- `parseLine_total`, which is free (a function), and `every_warning_is_reachable`: one witness
  per `LWarn` (§5.8).

### 2.6 Instance keys and small grammars (`LogEvent.lean`)

- `parseInstanceStatus`: `done | pending | missed | expired | skipped | skip`, anything else
  `none`, faithful to `parse_instance_status`. An unknown status is a **named replay warning**
  `unknownRoutineStatus (line : Nat)`, not Rust's formatted string. Parity exception P10 is
  about message text only.
- `instDate? : List Char → Option Day`: exactly 10 characters, `%Y-%m-%d`, via `Cal`
  (`parse_date`).
- `stampFromKey`: ISO week, then date, then `none` (`stamp_from_key`). It reuses the week
  reader the kernel already has for `W37`-style keys, and **must not add a second one** (§5.3).
  If `IsoWeek::parse`'s accepted forms differ from the kernel's week reader, that is a finding
  for S4, not something to paper over.

---

## 3. Time zone and day attribution

### 3.1 The choice: a host-supplied offset table, the zone's arithmetic in the kernel

| option | one reader of `t`? | fork-point behaviour | proof cost | serves stage 6? |
|---|---|---|---|---|
| (a) Rust sends each event's local date | **no**: Rust must parse every line's `t` | kept | low | no |
| (b) each event's own written offset | yes | **changed**: offsets are the writer's `Local::now()`, not `cfg.tz`'s (inv §0); `day_index_wake_to_wake`'s "UTC-written entries are attributed in the configured zone" fails; a day with no events has no offset at all | lowest | no (walls, `at:` need the zone) |
| (c) a tz rule table in Lean (tzdb port) | yes | kept | a second tzdb, **data a human does not maintain** | yes |
| **(d) Rust probes chrono-tz for `cfg.tz`'s offset spans; kernel does the arithmetic** | **yes** | **kept** (clamped outside the table, P11) | small: one lookup function, a `wf` check | **yes** |

**(d) is chosen.** The zone is a fact about the world, not a definition of a tm concept. That is
§5.5's "the phase of the seven-day cycle" and plan §3.6's "the kernel consumes … as data". The
kernel keeps one reader of `t` and one definition of local date, local midnight and the 24-hour
rule. No **OWNER** question arises, because behaviour is unchanged.

```lean
structure TzTable where                                   -- (new, Time.lean)
  key   : List Char                 -- e.g. "America/Chicago|chrono-tz 0.10.4"; enters the checkpoint
  first : Offset                    -- in force before the first transition (−∞)
  spans : List (Instant × Offset)   -- strictly increasing instants; each offset in force from its instant
def TzTable.wf (z : TzTable) : Bool   -- strictly sorted; ≤ 4096 spans (R10); `Offset` already bounded
abbrev Tz := { z : TzTable // z.wf = true }
def offsetAt (z : Tz) (t : Instant) : Offset              -- last span with instant ≤ t, else `first`
def localSec (z : Tz) (t : Instant) : Nat                  -- t.sec ± offset; a line before 0001-01-02 is `badT tooEarly`
def localDate (z : Tz) (t : Instant) : Day := localSec z t / 86400
def localMidnight (z : Tz) (d : Day) : Instant             -- port of `local_midnight` (below)
```

- **`localMidnight`** is `local_midnight` ported literally. Try the naive local times `d
  00:00`, then `01:00`, `02:00` and `03:00`. For each, the candidate instants are
  `naive − o` for every offset `o` in force within ±1 day. A candidate is valid if
  `offsetAt (naive − o) = o`. Take the earliest valid candidate (`.earliest()`). If none is
  valid, fall back to `naive − offsetAt naive` (`from_utc_datetime`). Law:
  `localMidnight_is_the_first_instant_of_the_day` holds under a decidable `noGapAtMidnight z d`
  and is refuted without it, with a DST-gap witness, per §3.1's item 4.
- **Rust side** (`tm/src/cli/tz_table.rs`, new, about 60 lines): for `cfg.tz`, walk from
  1970-01-01 to `now + 5 y` in 1-day steps with `offset_from_utc_datetime`. On a change, bisect
  to the second. Memoise per process. **ESTIMATE**: about 20,000 probes, a few milliseconds at
  `opt-level = 1`, about 120 spans for Chicago, and a table of about 5 KiB on the wire.
  chrono-tz's `TimeSpans` trait is not needed.
- **P11 (clamping):** outside `[1970, now + 5 y]` the kernel uses the nearest span's offset.
  The fork point would consult tzdb. This is a recorded exception and only matters for
  timestamps outside that range.
- **Validation of the table itself** is Rust test A4 (§11): for every hour from 2000 to 2035
  and a list of zones (Chicago, London, Kolkata, Lord Howe's 30-minute DST, Sao Paulo's
  historical midnight transitions), the kernel's `localDate` through the FFI equals chrono's
  `with_timezone(&tz).date_naive()`.

### 3.2 The wake index (`DayIx.lean`, new; imports `Time`)

```lean
def keptWakes (z : Tz) (ws : List Instant) : List Instant :=     -- `DayIndex::new`
  dedupConsecBy (fun later kept => localDate z later = localDate z kept) (ws.mergeSort (· ≤ ·))
def lastLe (kept : List Instant) (t : Instant) : Option Instant   -- `last_wake_before` (partition_point ≤)
def dayOfK (z : Tz) (kept : List Instant) (t : Instant) : Day :=  -- `day_of`
  match lastLe kept t with
  | some w => if t.ns < w.ns + 86400 * 1000000000 then localDate z w else localDate z t
  | none   => localDate z t
def wakeOf (z : Tz) (kept : List Instant) (d : Day) : Option Instant  -- `wake_of`
def sleptByDay (z : Tz) (kept) (survivors : List Entry) : List (Day × Nat) -- first wake in FILE order per `dayOfK`
```

- **`dedup_by` is consecutive**, so `dedupConsecBy` is too. It is not "unique per date": the
  two differ when local dates are non-monotone in instant. This is a porting trap worth naming
  in the module header.
- **Both "first wake" rules are ported and both are named** (inv §7 FLAG 3):
  `keptWakes_is_earliest_by_instant_per_run_of_one_date`, and
  `dayWake_is_first_in_file_order_per_attributed_day`. Beside them is
  `the_two_first_wake_rules_disagree_on_an_out_of_order_append`, a witness. Unifying them would
  change behaviour, so it is **OWNER** Q6.

Goals for day attribution (full signatures are in §9):
- the four cases of `day_index_wake_to_wake`, each as a `decide` witness on one or two wakes
  with small instants. Instants are about 6.4e10 as `Nat` literals; `Nat.decEq` is
  GMP-accelerated in the kernel, and the witness involves no `List Char` parsing, so the §5.10a
  budget holds. Probe it under the 8 GB cap first anyway;
- `dayOfK_within_24h_is_the_wake_date`, `dayOfK_without_a_recent_wake_is_the_calendar_date`;
- `a_day_is_never_longer_than_24h`: `dayOfK z kept t = localDate z w` where `lastLe kept t = some w`
  implies `t.ns < w.ns + 24h`, unless `localDate z t = localDate z w`;
- **the locality lemmas the window law uses:**
  `keptWakes_append_of_partition`, `lastLe_append_of_later`, `dayOfK_prefix_of_partition`, and
  `dayOfK_resume_of_partition` (§9).

---

## 4. Undo

### 4.1 Definition (`Undo.lean`, new; imports `LogEvent`)

```lean
abbrev Ix := Nat                                            -- the line number, kept for warnings and `tm log`
def matches (of_ : List Char) (id : Option Id) (e : Entry) : Bool :=
  e.ev.tag == of_ && (id.all fun x => e.ev.primaryId == some x)     -- undos are never on the stack
/-- Stack of survivors, most recent first. -/
def maskStep (st : List (Ix × Entry)) : Ix × Entry → List (Ix × Entry)
  | (_, ⟨_, .undo of_ id⟩) => eraseFirst (fun p => matches of_ id p.2) st   -- cancels itself always
  | p                      => p :: st
def survivors (es : List (Ix × Entry)) : List (Ix × Entry) := (es.foldl maskStep []).reverse
def dangling (es : List (Ix × Entry)) : List Ix             -- undos whose `eraseFirst` found nothing
```

This equals `undo_mask`. At step `i` the stack holds exactly the entries `j < i` that are not
cancelled and not undos, most recent first. So "the greatest `j < i` with `!cancelled[j]`, not
an undo, name and id matching" is the first stack element that matches. `eraseFirst` is
`List.eraseP`, from core.

### 4.2 Laws (Goals, §9)

- `survivors_snoc_event`: for a non-undo `e`, `survivors (es ++ [e]) = survivors es ++ [e]`.
- `survivors_snoc_undo`: `survivors (es ++ [u]) = eraseLast (matches …) (survivors es)`. This
  is the independent characterisation: the target is **the last** surviving match, and the
  undo itself never survives.
- `an_undo_never_survives`, `survivors_sublist` (order is kept).
- `a_cancelled_event_is_never_revived`: once an index is not a survivor of `es`, it is not a
  survivor of `es ++ fs`.
- `an_undo_of_an_undo_cancels_nothing`: this is "there is no redo".
- `the_mask_ignores_is_state_change`: witness, `undo{of:"note"}` cancels a note.
- `undo_mask_pairs_and_dangling_ported`: Rust's test, seven entries,
  `cancelled = [T,T,T,T,T,F,T]`, `dangling = [4,6]`. The events are built as `Entry` values,
  not parsed text, so the decide stays small.
- **The window half:**
  `survivors_append_of_no_reach : noReach (tagsOf (survivors a)) b = true → survivors (a ++ b) = survivors a ++ survivors b`,
  and its refutation without the guard, `survivors_append_fails_when_an_undo_reaches_back`
  (witness: `a = [done x]`, `b = [undo done x]`).

```lean
def tagsOf (st : List (Ix × Entry)) : List (List Char)       -- deduplicated; capped (§6.2)
def noReach (tagsA : List (List Char)) (b : List (Ix × Entry)) : Bool :=
  (dangling b).all fun i => match lookup i b with
    | some ⟨_, .undo of_ _⟩ => !(tagsA.contains of_)                    -- conservative for an id undo
    | _ => true
```

### 4.3 What `tm undo` needs from the kernel

`undo.rs` `new_events` re-parses the log to learn each appended event's tag and primary id.
Under D9 that is a second reader. The response's `lines` view (§7.2) returns `(line, tag,
primaryId, survives)` for each tail line, so `Recorder::finish` reads that instead.
`log_len`'s non-blank line count and the kernel's entry count stop disagreeing on a malformed
line (inv §0), because both come from one `splitLog`. `undo_target` and `compensating_undo`
have no callers outside `log.rs` (grep, this pass), so they are deleted, not ported.
`move_has_no_inverse_command` stays the reason undo is replay.

---

## 5. The fold: frame, facts, observations (`Replay.lean`, new; imports `DayIx`, `Undo`, `Arith`)

### 5.1 Types (every one bounded or `Nat`; no saturation, a deliberate difference P12)

```lean
structure Block where id : Id; started : Instant; since : Option Instant; paused : Bool
                      pausedAt : Option Instant; worked : Nat; pendingObs : Option EnergyObs
structure Cut where id : Id; day : Day; min : Nat          -- day stored at cut time (see below)
structure Frame where                                       -- `Machine` minus `out`
  block     : Option Block
  lastCut   : Option Cut
  interrupt : Option (Instant × Day × Option Id)            -- day of the start, stored at open
inductive SegKind | block (id : Id) | pause (id : Id) | interrupt (id : Option Id)
                  | brk (where_ : Option (List Char)) | routine (item inst : List Char) | idle (attr : List Char)
structure Seg where start stop : Instant; kind : SegKind
structure DayDetail where                                    -- `DayReplay`, exact
  wake : Option Instant; sleptMin : Option Nat; onsetMin : Option Nat
  arrival : Option Instant; loc : Option (List Char); window : Option (List Char × List Char); budget : Option Nat
  locChanges : List (Instant × List Char); firstStart : Option Instant; starts : List StartRec
  blockMin blocksDone : Nat; load5 : Nat                    -- `load` = load5 / 5, exact (inv §7 FLAG 6)
  minutesByCi : Fin 6 → Nat; ciUnknown : List (Id × Nat)
  done : List Id; lostMin : Nat; dropped : List Id; leakMin longestLeak : Nat
  idle : List IdleRec; breaks : List BreakRec; routineMin plans replansToday driftMin : Nat
  lastPlanHash : Option (List Char); segments : List Seg     -- stable-sorted by start at `finish`
  itemMin : List (Id × Nat)                                  -- `ItemReplay.minutes_by_day` for this day
structure EnergyObs where t : Instant; day : Day; pred rep : U8; hsw : Hsw; loc : List Char
                          sleptMin : Option Nat; went : Option U8; id : Option Id; fromStart : Bool
structure DurationObs where t : Instant; day : Day; id : Id; ci : U8; tags : List (List Char)
                            estMin actualMin : Nat; went : Option U8; partial : Bool
structure DayObs where day : Day; wake arrival : Option Instant; loc : Option (List Char)  -- fit & lounge_rate
structure Agg where                                          -- all-time; never day-keyed
  itemMinutes : List (Id × Nat); itemBlocks : List (Id × Nat); stops extended : List (Id × Nat)
  doneAt partialDoneAt : List (Id × List Instant)
  instances : List ((List Char × List Char) × InstRec)       -- last in FILE order wins
  doneItems : List Id; lastDone : List (Id × Instant)        -- max by INSTANT
  doneDates : List (Id × List Day)                           -- sorted, deduplicated
  events : List (List Char × List NamedRec); demotions : List (Id × List DemRec)
  closes : List CloseRec; droppedItems : List Id; interrupts : List IntRec
  longestLeak : Option LeakRec; unknown : Nat; warnings : List RWarn
structure Full where frame : Frame; agg : Agg; days : List (Day × DayDetail)
                     energy : List EnergyObs; durations : List DurationObs
```

**Association lists, not maps.** `Store` taught this: `Std.HashMap` is opaque to `decide`.
The facts are association lists with a `Nodup`-keys `wf` and a `@[csimp]`-proven fast twin
where profiling demands one. A tree map is not proposed, because no core `RBMap` theorems are
needed and the lists are small per call after windowing.

**Every fact the fork point derives is ported** (D9: "every replay fact"), including those the
grep found no consumer for (inv §3's list). They are cheap accumulations. The response
**emits** only what a consumer reads, and a `view` query can ask for the rest.

### 5.2 `step`, by name

`step (z : Tz) (kept : List Instant) (slept : List (Day × Nat)) : Full → Ix × Entry → Full` is
`Machine::step`, one arm per constructor, with the helpers `closeSub`, `closePause`, `credit`,
`uncreditCut`, `cut`, `markDone` and `segment` ported **by name**. Inv §2.4's table is the
specification. Three changes are forced by the fold, and none is observable:

1. **`Cut.day` and the interrupt's day are computed when stored**, not when used.
   `uncredit_cut` recomputes `day_of(cut.t)`, and `resume` recomputes `day_of(s)`. In one full
   replay the index is global, so both give the same answer: `cut_day_stored_eq_recomputed`.
   Storing the day is what lets the checkpoint drop older wakes.
2. **`Block.obs` is the observation itself (`pendingObs`), not an index into `energy`.**
   A start with `rep` holds its observation in the block. It is appended to `energy` when the
   block closes by `done` (with `went` written), by `cut`, or at `finish` (still open, `went =
   none`). **This changes observation order**: an open block's start observation moves from its
   start position to its close position. The fix that keeps parity is a **stable sort of
   `energy` by `(day, line)` at emission**. That is the canonical order of §6.5, and it is
   parity exception P13 with an order-independence test on the fit (A8).
3. **`range` is gone.** The CLI only ever passes `None` (inv §4.3), so `in_range` is `true`.

Replay facts whose truth is a law (Goals, §9):
- `the_minutes_by_ci_and_the_unknown_sum_to_block_min`: this is the invariant in `credit`'s
  doc, as a theorem over every `step`;
- `an_instance_is_the_last_record_in_file_order`: over `routine`/`skip` survivors;
- `last_done_is_the_latest_by_instant`: with the disagreement witness
  `instances_and_last_done_order_differently` (a retro append);
- `a_stop_then_done_replaces_the_cut_credit`, and
  `a_block_cut_by_start_is_never_replaced_by_done`, the `last_cut = None` rule (witness);
- `a_retro_done_marks_done_and_credits_nothing` (`actual_min = 0`);
- `done_sets_grow_without_undo` (a two-run law under D5): `(∀ e ∈ b, ¬ e.isUndo) →
  doneItems (replayFull a) ⊆ doneItems (replayFull (a ++ b))`. This is a corollary of
  `survivors_snoc_event` and `foldl_append`;
- `load_is_minutes_times_ci_over_five`: `load5 = Σ min × min(ci, 5)`, exact.

### 5.3 The raw-entry consumers become facts

`day.rs` `since_break_min`, `idle_min_since` and `idle`, and `app.rs` `idle_since`, each walk
`iter_day(today)` or `effective().last()`. Those are replay facts outside the replay, two
readers. The kernel adds them to `DayDetail`, ported by name, as functions of the day's
survivors in file order:
- `sinceBreakAnchor : Option Instant`: the last `break`'s `t + actual_min`, else the first
  `start`'s `t`, as in `since_break_min`;
- `idleSpans : List (Instant × Option Instant)`: `pause`/`interrupt` opens and
  `unpause`/`resume` closes, with `break{actual_min}` spans, as in `idle_min_since`;
- `lastEventAt`, global, in `Agg`: the last survivor's `t`.

Clamping to `now` and to `state.break_` stays in Rust, because it reads `.tm/state.json` and
the wall clock, neither of which is replay. That is presentation arithmetic over kernel facts.
It is recorded, not hidden: when stage 6 brings `now` with a time of day onto the wire, it
moves in.

### 5.4 Proof tractability notes

- `step` is one `match` with 26 arms. Frame and aggregate lemmas go **per arm**, by
  `cases e.ev <;> simp [step, …]`. The frame lemma of §6.3 is the only lemma that quantifies
  over every arm, and it is stated through `touched` (below) so that each arm's proof is
  `rfl`/`simp`.
- No lemma unfolds `replayFull` over a concrete log bigger than about 8 entries. Corpus-sized
  agreement is an FFI test (§11), never a `decide` (§5.10a).

---

## 6. Windowing: checkpoint, seal, resume, and the law (`Window.lean`, new)

### 6.1 The specification replay

```lean
def replayFull (z : Tz) (lines : List (Ix × Entry)) : Full :=
  let sv    := survivors lines
  let kept  := keptWakes z (wakeInstants sv)
  let slept := sleptByDay z kept sv
  finish z kept (sv.foldl (step z kept slept) Full.init)
```

This is the proof-level meaning. Its runtime is never used on its own: the kernel always runs
`resume` (§1, "two consequences").

### 6.2 The checkpoint

```lean
structure Ckpt where                                   -- (new) everything crosses the wire as kernel JSON
  version  : Nat                    -- `replayVersion`, a kernel constant bumped when any step changes
  tzKey    : List Char              -- `Tz.key` the prefix was attributed under
  splitAt  : Instant                -- H: every prefix line < H ≤ every tail line
  lines    : Nat                    -- number of file lines (blank and warned included) the prefix covers
  openFrom : Day                    -- D: days < D are sealed (their detail dropped, observations archived)
  frame    : Frame                  -- the machine at the end of the prefix
  agg      : Agg                    -- all-time aggregates
  days     : List (Day × DayDetail) -- detail for days ≥ D only
  energy   : List EnergyObs         -- observations of days ≥ D only (still mutable: `sleptMin`, pending)
  durations : List DurationObs      -- days ≥ D only
  lastKept : Option Instant         -- the last kept wake of the prefix (§3.2 locality)
  slept    : List (Day × Nat)       -- slept-by-day, days ≥ D only
  tags     : List (List Char)       -- tags among prefix survivors; ≤ 64 entries or no checkpoint
def Ckpt.wf (c : Ckpt) : Bool      -- keys Nodup, days ≥ openFrom, frame days ≥ openFrom, tags ≤ 64, …
structure Sealed where days : List DayObs; energy : List EnergyObs; durations : List DurationObs
```

**What the prefix-side conditions are, and where they are checked.** `checkpoint` is a
function the kernel runs on its own post-state, so its conditions are *computed*, not trusted:

```lean
def checkpoint (z : Tz) (H : Instant) (D : Day) (a : List (Ix × Entry)) (st : Full) :
    Except CkErr (Ckpt × Sealed)
-- refuses: .notPartitioned (some line of `a` has t ≥ H), .frameBeforeOpen (an open block's
-- pending obs day, the last cut's day or the open interrupt's day is < D), .tooManyTags,
-- .openAfterSplit (D > localDate z H)
```

### 6.3 `seal`, `touched`, and the frame lemma

```lean
def seal (D : Day) (st : Full) : Full × Sealed       -- move days < D out: DayObs + their obs, drop detail
def touched (z) (kept) (st : Full) : Ix × Entry → List Day
  -- the days `step` may write: dayOfK t; for idle and routine also dayOfK (t − min);
  -- for resume the stored interrupt day; for done, the stored cut day; for energy its day
theorem step_frame (z kept slept) (st : Full) (e) (D : Day)
    (h : ∀ d ∈ touched z kept st e, D ≤ d) :
    (seal D (step z kept slept st e)).1 = step z kept slept (seal D st).1 ∧
    (seal D (step z kept slept st e)).2 = (seal D st).2
```

The frame lemma is the one quantifier over all 26 arms. It is tractable because `touched` is
defined **arm by arm next to `step`**, so each case is "the arm writes only under the keys
`touched` lists". `Agg` is never day-keyed, so sealing does not touch it.

### 6.4 `resume` and the guard

```lean
def resumeGuard (z : Tz) (ck : Ckpt) (b : List (Ix × Entry)) : Except GuardErr Unit
  -- G0 ck.version = replayVersion                      → .version
  -- G1 ck.tzKey = z.key                                → .zone
  -- G2 ∀ e ∈ b, ck.splitAt ≤ e.t                        → .retro (line)     (instant partition)
  -- G3 noReach ck.tags b                                → .undoReach (line)
  -- G4 ∀ e ∈ survivors b, ∀ d ∈ touched …, ck.openFrom ≤ d  → .sealedDay (line)
  -- G5 the query's detail range starts ≥ ck.openFrom   → .detailBeforeOpen
def resume (z : Tz) (ck : Ckpt) (b : List (Ix × Entry)) (roll : Option (Instant × Day)) :
    Except GuardErr (Full × Option (Ckpt × Sealed))
  -- kept' := keptFrom z ck.lastKept (wakeInstants (survivors b)); slept' := ck.slept ⊕ first-wakes of b
  -- fold `step` over survivors b from ck's state; `finish`; if `roll = some (H', D')` and the split
  -- conditions hold on the tail, also emit the rolled checkpoint (`checkpoint` on the post-state)
```

### 6.5 The law, in pieces and whole

```lean
/-- (W1) the mask splits. -/                    theorem survivors_append_of_no_reach …   (§4.2)
/-- (W2) the wake index splits. -/
theorem keptWakes_append_of_partition (z) (ws₁ ws₂ : List Instant) (H : Instant)
    (h₁ : ∀ w ∈ ws₁, w < H) (h₂ : ∀ w ∈ ws₂, H ≤ w) :
    keptWakes z (ws₁ ++ ws₂) = keptWakes z ws₁ ++ keptFrom z (keptWakes z ws₁).getLast? ws₂
theorem dayOfK_prefix_of_partition … (ht : t < H) :
    dayOfK z (keptWakes z (ws₁ ++ ws₂)) t = dayOfK z (keptWakes z ws₁) t
theorem dayOfK_resume_of_partition … (ht : H ≤ t) :
    dayOfK z (keptWakes z (ws₁ ++ ws₂)) t = dayOfK z (keptFrom z (keptWakes z ws₁).getLast? ws₂) t
/-- (W3) the pre-pass splits: first-in-file-order per day, days ≥ D only from the tail. -/
theorem sleptByDay_append_of_sealed …
/-- (W4) the frame lemma. -/                   theorem step_frame …                       (§6.3)

/-- **The window law.**  Views and observations of the whole log equal those of the resumed tail. -/
theorem replay_window (z : Tz) (a b : List (Ix × Entry)) (H : Instant) (D : Day)
    (ck : Ckpt) (s : Sealed)
    (hck : checkpoint z H D a (replayFull z a) = .ok (ck, s))
    (hg  : resumeGuard z ck b = .ok ()) (q : Query) (hq : D ≤ q.detailFrom) :
    ∃ r, resume z ck b none = .ok (r, none) ∧
      view q (replayFull z (a ++ b)) = view q r ∧
      canonObs (replayFull z (a ++ b)) = s.energy ++ canonObs r ∧                 -- energy
      canonDur (replayFull z (a ++ b)) = s.durations ++ canonDur r ∧
      dayObsOf D (replayFull z (a ++ b)) = s.days
/-- Rolling: a checkpoint emitted by `resume` is the one `checkpoint` would have emitted
    on the whole prefix — so induction on calls gives every call's correctness. -/
theorem resume_rolls (…) (hroll : resume z ck b (some (H', D')) = .ok (r, some (ck', s'))) :
    checkpoint z H' D' (a ++ b₁) (replayFull z (a ++ b₁)) = .ok (ck', s ++ s')    -- b₁ = b's lines < H'
/-- One code path: the empty checkpoint is a full replay. -/
theorem resume_empty (z) (l) (q) : ∀ r, resume z (ckEmpty z) l none = .ok (r, none) →
    view q (replayFull z l) = view q r
/-- §5.8, both directions. -/
theorem resume_is_refused_when_a_tail_wake_is_retro : ∃ …, resumeGuard … = .error (.retro _)
theorem replay_window_fails_without_G2 : ∃ a b …, view q (replayFull z (a ++ b)) ≠ view q (resumeUnguarded …)
theorem the_guard_admits_a_day_ordered_log : …        -- a small generator-shaped log, every midnight split passes
```

`canonObs` is the stable sort by `(day, line)` (P13). The observation equations hold exactly
because sealed days are below `D` and every tail observation is at day `≥ D` (G4), so the
archive is a prefix in canonical order.

**Proof sketch** (so the build agent knows the size):
1. W1 turns `survivors (a ++ b)` into `survivors a ++ survivors b`.
2. `wakeInstants` distributes over `++`, W2 splits the index, and W3 splits the pre-pass.
3. `foldl_append` splits the fold.
4. On `survivors a`, every instant is `< H`, so `dayOfK_prefix_of_partition` rewrites the step
   index to `a`'s own (congruence of `step` in its index argument on the touched instants:
   `step_congr_index`, a per-arm lemma).
5. `seal` commutes past every tail step by W4 under G4.
6. `finish` commutes with `seal` (sort per day).

**ESTIMATE:** 1,200–2,000 proof lines. The largest parts are W2 (dedup over a sorted append)
and the per-arm `step_congr_index`/`step_frame`.

### 6.6 What the checkpoint does not bound, and the policy

- **Growth.** `Agg` is O(items + completions + instance records + demotions + closes). On the
  3-year synthetic log that is 899 items, 5,849 `(id, date)` done pairs, 2,979 instance records,
  1,561 demotions, 1,251 closes and 123 named events (`split_probe.py`). Making it constant
  would mean summarising `instances` and `doneDates` by what recurrence reads (a first date, a
  count, recent keys). That is stage 5's recurrence denotation's business, with its own
  equivalence law. **Not proposed here:** it would couple the window law to a consumer that
  does not exist yet.
- **Policy** (performance only; the law quantifies over every `H`, `D`):
  - `H` = local midnight of `today − 2`, so a `tm wake 06:05` typed late, or a `--now`
    yesterday, stays in the tail;
  - `D` = min(first day of the current month, `today − 14`), which covers `done_this_period`'s
    month floors and the week review;
  - roll only when `H` moves by at least one day;
  - on a guard refusal, Rust resends the whole log and caches the new checkpoint.

  On the synthetic logs every midnight split is a clean partition (`splits_bad = 0` for all
  five sizes), so the guard fires only on genuine retro edits and far undos.
- **Detail for old dates** (`tm review day 2026-01-03`, `tm log --since 400d`) asks for a
  detail range before `D`. G5 refuses the checkpoint, and Rust sends the whole log. Latency for
  those verbs grows with log age: **OWNER** Q3.

---

## 7. The wire

### 7.1 Request: a new optional `log` section (absent means no replay, and every existing request is unchanged)

```jsonc
{"now":"2026-09-14","blockMin":50,"docs":[…],"cmds":[…],
 "log":{
   "tz":{"key":"America/Chicago|chrono-tz 0.10.4","first":"-06:00",
         "spans":[["2007-03-11T08:00:00Z","-05:00"],["2007-11-04T07:00:00Z","-06:00"], …]},
                                             // instants and offsets are strings the kernel's own
                                             // timestamp/offset grammar reads: one reader, no epoch constant in Rust
   "ckpt": {…} | null,                       // the kernel's own checkpoint JSON, verbatim from the cache
   "firstLine": 44913,                       // 1-based file line number of the first tail line
   "text": "{\"t\":…}\n{\"t\":…}\n",          // the tail's raw bytes as one string (whole file when ckpt is null)
   "badUtf8": [44950],                        // file line numbers Rust blanked because they were not UTF-8
   "query": {"detailFrom":"2026-09-01","detailTo":"2026-09-14",   // ≤ 62 days (R10), else badQuery
             "lines": true,                   // per tail line: tag, id, survives (undo.rs, tm log)
             "all": false},                   // true: also the facts no consumer reads (debug, parity)
   "roll": {"splitAt":"2026-09-12","openFrom":"2026-09-01"} | null   // local dates; kernel computes H
 }}
```

- **R10 bounds**, each with a smart constructor and a rejection theorem:
  - `spans ≤ 4096`;
  - `text ≤ 256 MiB`, far above any log and below Lean's `String` limits;
  - `badUtf8` sorted, ≤ 4096 entries (more than that and Rust refuses to call:
    "log unreadable");
  - `detailTo − detailFrom ≤ 62`;
  - `firstLine ≥ 1`.
- **Refusals by name** (`{"err":{"replay":…}}`): `badTz`, `badQuery`, `badCkpt <JErr|field>`,
  and every `GuardErr`: `version zone retro undoReach sealedDay detailBeforeOpen`, the last
  four with the offending line. **Line warnings are not refusals.** They are data in the
  response, as `Log::parse_bytes` makes them.
- **Gap 44 does not bite the request.** `text` is one string (`jscanTR`/`junescapeTR`). `ckpt`
  arrays are emitted **chunked**: an array longer than 4,096 is an array of ≤ 4,096-element
  arrays. `chunk`/`unchunk` are in `Json.lean` with `unchunk_chunk`, and each chunk's length is
  bounded. Every list the kernel folds over an event list is `foldl`, or has a `@[csimp]`
  tail-recursive twin, so a 100,000-line whole-log request runs on a 2 MiB thread (test A7).

### 7.2 Response: `ok.replay` beside `docs` and `report`

```jsonc
{"ok":{"docs":[…],"report":{…},
  "replay":{
    "days":[{"day":"2026-09-14","wake":[63892004700,0],"sleptMin":480, …, "load":{"num":1235,"den":5},
             "segments":[…],"sinceBreakAnchor":[…],"idleSpans":[…], …}],           // detail range only
    "agg":{"itemMinutes":[["667",140],…],"doneDates":[["d1",[739872,739873]],…], "lastDone":…,
           "instances":…, "events":…, "demotions":…, "openBlock":…, "openInterrupt":…, "lastEventAt":…},
    "obs":{"energy":[…],"durations":[…],"days":[…]},       // observations for days ≥ openFrom (current)
    "sealed":{"energy":[…],"durations":[…],"days":[…]},    // newly sealed: Rust appends to its archive
    "ckpt":{…} | null,                                       // rolled checkpoint, when roll was asked and possible
    "ckptLines": 44990,                                      // file lines the new checkpoint covers
    "lines":[[44913,"start","667",true],[44914,null,null,false,"badField est_min"],…],
    "warnings":[{"line":44950,"w":"invalidUtf8"},{"line":44961,"w":"unknownRoutineStatus"}]}}}
```

- **Encodings on the way out** (JVal `Nat` only):
  - an instant is `[sec, nano]` since 0001-01-01 UTC; the bridge constant `KERNEL_EPOCH =
    62_135_596_800` s before 1970 is pinned by FFI test A5 (a line with a known `t`);
  - a day is its `YYYY-MM-DD` string, rendered by `Cal`'s renderer;
  - `hsw` is `{"neg":b,"num":n,"den":10^k}`, which the bridge turns into f64 by formatting
    `"[-]n e-k"` and `str::parse::<f64>()`. That is the same correctly-rounded conversion serde
    used on the text, so the fit sees the fork point's double: `hsw_decodes_to_serde_value`
    (A6);
  - `load` is `{num, den: 5}`.
- **Emitted in build order**, like every response (`the_response_shapes_emit_in_build_order`),
  and round-tripped: `the_replay_response_parses_back` extends
  `the_response_call_emits_parses_back`.
- **A command request and a log section together:** replay runs **before** the commands, on
  the log as sent. No current kernel command reads replay facts, and stage 5's recurrence will.
  Nothing a command writes goes to the log inside the kernel (§8.1).

---

## 8. The Rust side

### 8.1 What stays Rust

- **File I/O and G9.**
  - `.tm/log.jsonl` is read as bytes and split on `\n`.
  - A line that is not UTF-8 is blanked and its number listed in `badUtf8`, which fixes the
    CLI's whole-command failure (inv §0; **OWNER** Q1).
  - A torn last line is sent as is.
  - Appends go through a new `FsStore::append_line` that writes `\n` first when the file does
    not end in one. That is `Log::append_all`'s repair, on the path the CLI actually uses.
- **The writer.** Verbs construct `Event` values and serialise them with serde, as today.
  `Event` keeps `Serialize` and **loses `Deserialize`**. The grammar therefore has two
  definitions, a Rust writer and a Lean reader, and that is 5.3's shape. It is tamed by
  differential test A3: every kind, generated by proptest, serialised by serde and read back
  through the kernel, must give the same tag, id and fields. **Moving emission into the
  kernel** (commands returning the lines to append) is the proper fix. It is a later step and
  not required by D9: **OWNER** Q5.
- **The checkpoint cache and observation archive**, `.tm/replay.json` (**OWNER** Q2):
  `{"version":…, "prefixLines":N, "prefixBytes":B, "prefixHash":"fnv1a64:…", "tzKey":…,
  "ckpt":{…}, "archive":{"energy":[…],"durations":[…],"days":[…]}}`.
  - It is written atomically, like `state.json`.
  - Last writer wins: any valid checkpoint is correct, so a CLI/TUI race only costs a full
    replay.
  - `tm undo` does not restore it, because it is keyed by content.
  - Deleting it is always safe.
- **The fit.** `energy::fit`, `compare`, `calibration` and `estimate_calibration` take
  `archive ++ response.obs`. `arrivals_from_replay` and review's `lounge_rate` take the
  `DayObs` list. **The fit is checked order-independent** by a property test (A8), because
  observation order changes (P13).
- **Presentation over kernel facts:** `DayReplay::gaps`, `wake_to_arrive_min`, the review
  monitors (plan §3.6, "definitions, not theorems"), and `now` clamping (§5.3).

### 8.2 What is deleted from the decision path

| Rust | fate |
|---|---|
| `log.rs` `Machine`, `replay`, `replay_refs`, `undo_mask`, `UndoMask`, `DayIndex`, `local_midnight`, `hours_since_wake` (reader side), `parse_instance_status`, `stamp_from_key` | **deleted from `tm-core`**; a verbatim copy lives in the parity oracle only (AGENTS §7.3, built from `4748911`) |
| `Log::parse`, `parse_bytes`, `read`, `effective`, `iter_day`, `iter_range`, `iter_item`, `day_index`, `undo_target`, `compensating_undo`; `Event`'s `Deserialize`, `Known`, `field_error`; `ts::deserialize` | deleted |
| `Replay`, `DayReplay`, `ItemReplay`, `EnergyObs`, `DurationObs`, … | **kept as DTOs**, `Deserialize` from the kernel's `replay` object in `kernel_bridge::decode_replay` (new); `f64` fields computed at decode (`load`, `hsw`) |
| `ctx.rs` `read_log` + `log.replay(None, tz)` in `Ctx::load_with`, `Ctx::reload` | `ctx::replay_via_kernel` (new): read bytes → cache check → one kernel call → decode → archive/cache update |
| `day.rs` `since_break_min`, `idle_min_since`, `idle`; `app.rs` `idle_since` | read `DayDetail.sinceBreakAnchor`, `idleSpans`, `Agg.lastEventAt`; clamp in Rust |
| `lifecycle.rs` `log` | `--item`/`--since`/`--tail` select from the response's `lines` (survivors, tag, id, day), print the **raw file line** (Rust holds the bytes); `--since` beyond `D` or `--item` asks `all`/whole log |
| `undo.rs` `log_len`, `new_events` | the response's `lines` for the tail (tag, id); line count from the one byte split |
| **tm-core tests building a `Replay` from logs** (about 220 tests in 20 files: `review_*`, `recur_*`, `planner_*`, `priority_*`, `energy_fit`, `horizon_close`, `log_*`) | `tm-core` cannot link the kernel (it is a `tm` path dependency, excluded from the workspace). Either move these tests to `tm/tests` behind a `replay_of(log_text)` helper that calls the kernel, or keep them on the oracle copy as parity tests. **Recommendation:** `log_replay.rs`, `log_regressions.rs` and `log_serde.rs` become kernel FFI tests; the consumer tests take their `Replay` from `tm/tests/common::replay_of`, which calls the kernel. This is **ESTIMATE** 2–3 days of mechanical moves, and a real cost D9 did not list |

### 8.3 The cache key: the one residual trust, and how it is enforced

1. **Key.** `prefixBytes` and an FNV-1a-64 hash of `bytes[..prefixBytes]` (10 lines of Rust, no
   new dependency), plus `tzKey`, plus `replayVersion`, which the kernel reports in every
   response.
2. **Check every call.** Recompute the hash over the prefix. **ESTIMATE:** a few ms at 3 years
   with `opt-level = 1`; A9 measures it. If the hash matches, send the tail. Otherwise send
   everything, with `ckpt: null`.
3. **Test** (A10): proptest over corpus and generated logs; mutate any byte of the prefix, or
   truncate, or append, and the next call's facts equal a cold full replay's.
4. **Named trust assumption.** `replay_window`'s hypothesis `hck` is discharged by this key, not
   by a proof. It is written into the README next to G9, with what it costs if violated (wrong
   facts until the file changes) and why it cannot be proved (it is a property of the file
   system, T11).

---

## 9. `Goals.lean` statements to add (a new `# STAGE 5 — D9, the log` block)

Add these **at step S0, before any definition exists**, with provisional `def … := sorry` only
where §2–§6 settle the signature (AGENTS §3.2: a goal nobody can state is a goal nobody has
understood). The burn-down rises by the count below. That is deliberate debt, to be named in the
handover. Also fix `Goals.lean`'s stale header sentence ("`PlanCore.log` is `List String`",
inv §7 item 7) in the same commit.

```lean
/-! ### Grammar -/
theorem jparse_jemit_widened (v : JVal) : jparse (jemit v) = .ok v                         -- re-proof, S1
theorem jgetNat_refuses_a_dnum (j : JVal) (k : String) (d : JDec) (h : jget? j k = some (.dnum d)) :
    natField j k = .error "Natural number expected"
theorem parseTs_renderTs (i : Instant) (o : Offset) : parseTs (renderTs i o) = .ok (i, o)
theorem parseTs_instant_ignores_offset : ∀ s₁ s₂ i₁ o₁ i₂ o₂, parseTs s₁ = .ok (i₁, o₁) →
    parseTs s₂ = .ok (i₂, o₂) → sameWallInstant s₁ s₂ → i₁ = i₂                           -- stated precisely at S2
theorem parseLine_emitLine (e : Entry) : parseLine (emitLine e) = .entry e
theorem every_line_warning_is_reachable : ∀ w : LWarnKind, ∃ l, (parseLine l).kind = some w
theorem splitLog_is_splitOn (t : List Char) : splitLog t = (Tm.splitOn '\n' t).map trimCR

/-! ### Undo -/
theorem survivors_snoc_event (es) (p : Ix × Entry) (h : ¬ p.2.ev.isUndo) :
    survivors (es ++ [p]) = survivors es ++ [p]
theorem survivors_snoc_undo (es) (i t of_ id) :
    survivors (es ++ [(i, ⟨t, .undo of_ id⟩)]) = eraseLastP (fun p => matches of_ id p.2) (survivors es)
theorem an_undo_never_survives (es) : ∀ p ∈ survivors es, ¬ p.2.ev.isUndo
theorem a_cancelled_event_is_never_revived (es fs) (i : Ix) (hi : i ∈ es.map (·.1))
    (h : i ∉ (survivors es).map (·.1)) : i ∉ (survivors (es ++ fs)).map (·.1)
theorem an_undo_of_an_undo_cancels_nothing (es i t id) :
    survivors (es ++ [(i, ⟨t, .undo "undo".toList id⟩)]) = survivors es
theorem survivors_append_of_no_reach (a b) (h : noReach (tagsOf (survivors a)) b = true) :
    survivors (a ++ b) = survivors a ++ survivors b
theorem survivors_append_fails_when_an_undo_reaches_back :
    ∃ a b, survivors (a ++ b) ≠ survivors a ++ survivors b

/-! ### Day attribution -/
theorem dayOfK_within_24h_is_the_wake_date (z kept t w) (h : lastLe kept t = some w)
    (h24 : t.ns < w.ns + 86400000000000) : dayOfK z kept t = localDate z w
theorem dayOfK_without_a_recent_wake_is_the_calendar_date (z kept t)
    (h : ∀ w, lastLe kept t = some w → w.ns + 86400000000000 ≤ t.ns) : dayOfK z kept t = localDate z t
theorem keptWakes_one_per_date_run (z ws) : (keptWakes z ws).Chain' (fun a b => localDate z a ≠ localDate z b)
theorem utc_written_entries_are_attributed_in_the_configured_zone : …          -- `day_index_wake_to_wake`, 4 cases
theorem keptWakes_append_of_partition … ; theorem dayOfK_prefix_of_partition … ;
theorem dayOfK_resume_of_partition …                                           -- §6.5 W2
theorem the_two_first_wake_rules_disagree_on_an_out_of_order_append : ∃ …      -- recorded, §3.2

/-! ### Replay facts -/
theorem the_minutes_by_ci_and_the_unknown_sum_to_block_min (z l) (d) (dd : DayDetail)
    (h : lookup d (replayFull z l).days = some dd) :
    (List.finRange 6).foldl (fun s c => s + dd.minutesByCi c) 0 + sumSnd dd.ciUnknown = dd.blockMin
theorem an_instance_is_the_last_record_in_file_order (z l item inst) :
    lookup (item, inst) (replayFull z l).agg.instances =
      ((survivors l).reverse.findSome? (instRecordOf item inst)).map InstRec.ofEntry
theorem last_done_is_the_latest_by_instant (z l id) :
    lookup id (replayFull z l).agg.lastDone = maxInstant? (doneInstants id (survivors l))
theorem instances_and_last_done_order_differently : ∃ …                          -- witness
theorem a_stop_then_done_replaces_the_cut_credit : …                              -- witness pair
theorem a_block_cut_by_start_is_never_replaced_by_done : …
theorem done_sets_grow_without_undo (z a b) (h : ∀ p ∈ b, ¬ p.2.ev.isUndo) :
    (replayFull z a).agg.doneItems ⊆ (replayFull z (a ++ b)).agg.doneItems
theorem cut_day_stored_eq_recomputed : …                                          -- §5.2 item 1

/-! ### Windowing -/
theorem step_frame … ; theorem sleptByDay_append_of_sealed … ; theorem step_congr_index …
theorem replay_window … ; theorem resume_rolls … ; theorem resume_empty …          -- §6.5 verbatim
theorem replay_window_fails_without_G2 : ∃ … ; theorem resume_is_refused_when_a_tail_wake_is_retro : ∃ …
theorem parseCkpt_emitCkpt (c : Ckpt) (h : c.wf = true) : parseCkpt (emitCkpt c) = .ok c
theorem unchunk_chunk (n : Nat) (hn : 0 < n) (xs : List JVal) : unchunk (chunk n xs) = xs
theorem the_replay_response_parses_back (input : List Char) : jparse (jemit (respond input)) = .ok (respond input)
```

**Count:** about 40 goals and 8 provisional definitions. Several are witnesses that will be
discharged by `decide` the day their definition lands. **AGENTS §5.10a applies to every
witness:** build entries as `Entry` values, not parsed text; keep text witnesses ≤ 60
characters; probe each under `MemoryMax=8G timeout 120` in a scratch copy before committing.

---

## 10. The step plan (each step commits green: check.sh 7/7, `cargo test --workspace`, the FFI suite, all capped)

Order is chosen so the shipped binary keeps the fork-point Rust replay until the kernel path is
complete **and** windowed (S8). A switch before windowing would put a whole-log kernel call on
every verb, which the latency test (S8's A11) would be right to fail.

| step | lands | proves / states | tests | ESTIMATE |
|---|---|---|---|---|
| **S0** measure and state | a committed throughput harness `kernel/tm-kernel-ffi/examples/replay-bytes` (a request holding a 1 MiB log string, and a 400 KiB object-heavy request; wall time and peak RSS, 3 runs, capped); `Goals.lean`'s D9 block (§9); README block | 0 proofs; ~40 goals added | none new | 1 d |
| **S1** JSON widened | `JDec`, `dnum`, `chunk`/`unchunk`; `jparse_refuses_…` renamed to its refutation; `jgetNat_refuses_a_dnum` | `jparse_jemit` re-proved; `unchunk_chunk`; `the_response_call_emits_parses_back` re-proved | cheats: a `dnum` read as `Nat`; FFI test: `blockMin:1.5` still refused (new text) | 3–4 d |
| **S2** instants | `Time.lean`: `Instant`, `Offset`, `parseTs`, `renderTs`, `minutesBetween`, `TzTable`, `offsetAt`, `localDate`, `localMidnight` | `parseTs_renderTs`, truncation lemma, `localMidnight` both ways | A2 (timestamp differential), A4 (zone table vs chrono; a test-only `probe` op is **not** added — the test goes through S4's replay with one-line logs, so it waits for S4 and runs there) | 4–5 d |
| **S3** wake index | `DayIx.lean`: `keptWakes`, `lastLe`, `dayOfK`, `wakeOf`, `sleptByDay`, `keptFrom` | W2 lemmas; the four attribution witnesses; both first-wake rules | — | 4–6 d |
| **S4** grammar + wire (no facts yet) | `LogEvent.lean`; `Boundary.lean` reads `log` (tz, text, firstLine, badUtf8, query) and answers `replay.lines` + `warnings` only | `parseLine_emitLine`, `splitLog_is_splitOn`, one witness per warning; R10 rejections | A2, A3 (serde ↔ kernel per kind, proptest 256), A4, A5; FFI: `malformed.jsonl` line-for-line | 6–8 d |
| **S5** undo | `Undo.lean`; `replay.lines[].survives` | §4.2 in full, incl. W1 and its refutation | FFI: `undo_mask_pairs_and_dangling` shape via text; proptest vs oracle mask | 4–5 d |
| **S6** the fold | `Replay.lean`: `Full`, `step` (26 arms), `finish`, `replayFull`; response `days`/`agg`/`obs` (full replay only, `ckpt` ignored) | §5.2's laws; `cut_day_stored_eq_recomputed` | **A1 parity** vs oracle `log::replay` over the corpus and `genlog` 1 mo/6 mo (exception list §15); A6; the Rust consumers still use Rust replay | 10–14 d |
| **S7** window | `Window.lean`: `Ckpt`, `seal`, `touched`, `checkpoint`, `resumeGuard`, `resume`; `ckpt`/`roll`/`sealed` on the wire | W3, W4, `step_congr_index`, `replay_window`, `resume_rolls`, `resume_empty`, both refutations, `parseCkpt_emitCkpt` | A7 (100 k lines, 2 MiB thread), A10's kernel half: random split + resume == full, over generated logs, every midnight | 10–14 d |
| **S8** switch the host | `tz_table.rs`, `.tm/replay.json` cache and archive, `ctx::replay_via_kernel`, `decode_replay`, G9 per-line UTF-8 and `append_line`; consumers moved (§8.2); `undo.rs`, `tm log`, `day.rs`, `app.rs` raw walks replaced; Rust replay deleted from `tm-core`; tm-core replay tests moved | — | A8, A9, A10 host half, **A11 latency with a 3-year log**, the whole `cargo test` green on the kernel replay; TUI tests | 8–12 d |
| **S9** drive and close | §5.13 30-minute drive: `tm wake/start/pause/interrupt/done/undo` over a day, a retro `--now` edit (guard fires, full replay, recovers), delete `.tm/replay.json`, corrupt a prefix byte, a UTF-8-broken line; README "measured" block; AGENTS §10.1 | ratio re-measured (D5: informs) | — | 2 d |

**Every step's README block records:**
- the goals discharged, refuted or added;
- the parity exceptions it adds;
- the observable behaviour rows;
- the new theorems under a `Check.lean` banner (§6.3 of AGENTS: one agent edits `Check.lean` at
  a time);
- `Negative.lean` cheats appended at the end, never renumbered.

**S1 touches `Json.lean`,** which the in-flight stage-5 core may also touch. Take S1 in a
worktree only after that workflow lands.

---

## 11. Acceptance tests

| id | what | where | pass condition |
|---|---|---|---|
| A1 | **parity** vs fork-point `log::replay` (oracle built from `4748911`, AGENTS §7.3) over `kernel/corpus/logs/*` and `genlog.py`/`genlog80.py` at 1 mo, 6 mo and 1 y | `kernel/tm-kernel-ffi/examples/oracle` (extended) | every fact equal, modulo §15; denominators printed |
| A2 | timestamp grammar: chrono `parse_timestamp` vs kernel on a generated set (valid, leap `:60`, `t`/space separators, 0–12 fraction digits, `Z`/`z`/offsets to ±23:59, `-24:00`, no-seconds fallback, padding and spaces) | FFI test (one-line logs) | accept/refuse and the instant agree on every string |
| A3 | event grammar: proptest `Event` values → serde line → kernel `lines` (tag, id) and `days`/`agg` effects; plus the malformed corpus line by line; plus duplicate keys, extra keys, `null` options, u8/u32 overflow, `hsw` forms | FFI test | agreement, or a listed exception |
| A4 | zone table: kernel `localDate` vs chrono `with_timezone(tz).date_naive()` hourly 2000–2035 for 5 zones (incl. 30-minute DST and a midnight transition) | FFI test | equal |
| A5 | epoch constant: a known `t` round-trips through `decode_replay` | FFI test | equal |
| A6 | `hsw` decode equals serde's f64 for 10,000 random decimal strings | `tm` unit test | bit-equal |
| A7 | a 100,000-line whole-log request on a 2 MiB thread | FFI test | answers, no abort |
| A8 | the fit (`fit`, `compare`, `calibration`, `estimate_calibration`) is invariant under permutations of its observations | `tm-core` proptest | equal models |
| A9 | cache-check cost at 3 years | `examples/replay-bytes` | recorded, quoted once (AGENTS §5.11) |
| A10 | window correctness end to end: random prefix mutation, truncation, append, retro line, far undo, tz change → next call's facts equal a cold full replay's | `tm/tests/replay_window.rs` | equal on every case |
| A11 | **latency**: `cli_latency.rs` gains a 3-year `genlog80`-shaped `.tm/log.jsonl` (6.5 MiB). Cold first verb (full replay + cache build) within `FIRST_VERB` (5 s); later verb (windowed) within `LATER_VERB` (1 s); a verb after a retro edit (full replay) within 5 s | `tm/tests/cli_latency.rs` | bounds hold; measured figures recorded |

---

## 12. Cost

| piece | Lean definitions | Lean proofs | Rust | ESTIMATE, agent-days |
|---|---:|---:|---:|---:|
| S1 JSON widening + chunking | 150 | 500–800 (re-proving the round trip over a sixth constructor) | — | 3–4 |
| S2 time + zone | 350 | 700–1,000 | 60 (`tz_table.rs`) | 4–5 |
| S3 wake index | 150 | 600–900 | — | 4–6 |
| S4 grammar + wire | 900–1,200 (26 decoders, warnings, request/response) | 1,000–1,500 | 150 (tests) | 6–8 |
| S5 undo | 120 | 500–800 | 50 | 4–5 |
| S6 fold | 900–1,300 (`step` ≈ `Machine::step`'s 480 Rust lines, plus types and emitters) | 1,500–2,500 | 300 (oracle, parity) | 10–14 |
| S7 window | 500–700 | 1,200–2,000 | 200 (tests) | 10–14 |
| S8 host switch | — | — | +900 / −2,000 (log.rs replay half, raw walks) + ~220 tests moved | 8–12 |
| S9 drive, docs | — | — | — | 2 |
| **total** | **≈ 3,100–4,000** | **≈ 6,000–9,500** | net −1,000 | **≈ 51–70 (10–14 weeks)** |

**For comparison:**
- The plan priced all of stage 5 at 3–4 weeks. D9 alone is larger than that. The owner priced
  "about 1,500 lines" of `log.rs` replay; the Lean side is about twice that in definitions,
  because the wire, the grammar and the zone are new, and 2–3× that again in proofs at the
  stage-4 ratio (4.80 : 1 library-wide).
- The ratio here should come in **lower** than stage 4's, **ESTIMATE** 2–2.5 : 1, because most
  laws are per-arm `simp` and list lemmas, not merge-and-order laws like `Close.lean`'s. Under
  D5 it informs and stops nothing.

**Latency (ESTIMATE, to be replaced by S0's measurement):**
- **A windowed call** carries about 0.5 MiB at 3 years (tail ~30 KiB, checkpoint ≤ 0.45 MiB,
  zone table 5 KiB). `call` materialises `input.toList`: ~0.5 M cons cells, roughly 12–25 MiB
  transient. If the kernel's `jparse` runs at 10–50 MiB/s, that is 10–50 ms of parse plus fold
  and emit, against a 1 s budget.
- **A full replay** at 3 years (6.5 MiB) is 0.15–0.7 s of parse alone and 150–400 MiB
  transient. That is inside `FIRST_VERB`'s 5 s, but it is a real first-run and retro-edit cost.
- **If S0 measures the parse far slower**, the fix is structural, not a tuning knob: stop
  `call`'s eager `input.toList` for the `text` field. A `String`-slice reader with a proved
  agreement to the `List Char` reader is its own step, with its own round-trip theorem.

---

## 13. Risks

| # | risk | likelihood | effect | mitigation |
|---|---|---|---|---|
| K1 | kernel JSON throughput too slow for full replays at 3 y (never measured, inv §4.4) | medium | cold verbs miss 5 s at old logs | S0 measures first; the `String`-slice reader (§12) is the named fallback; the window keeps later verbs small regardless |
| K2 | chrono's fallback `%Y-%m-%dT%H:%M%:z` and RFC 3339 edge acceptance differ from a port | high (padding-agnostic parser) | hand-edited lines warn in one and parse in the other | A2 differential over a generated set; residue recorded as parity exceptions, never guessed |
| K3 | serde duplicate-key / `flatten` behaviour | medium | a line decodes differently | A3; exception P8 |
| K4 | `step`'s 26 arms make `step_frame` and `step_congr_index` long | medium | S7 overruns | `touched` defined next to each arm; per-arm `simp` lemmas generated first; D5 forbids downgrading, so budget S7 at the high end |
| K5 | `Agg` grows without bound (§6.6); a 10-year log's checkpoint ~1.5 MiB | certain, slow | windowed calls slow over years | recurrence's own summary with an equivalence law, later; chunked arrays keep gap 44 away meanwhile |
| K6 | the cache key check (a hash over the prefix) costs more than the replay it saves in debug | low | no latency win | A9; fallback: key on `(prefixBytes, file length, hash of the last 64 KiB)` — weaker, **OWNER** Q2 |
| K7 | the observation order change (P13) matters to a consumer | low | fit or review differs | A8 proptest; if it fails, the kernel emits file order and the archive stores `(line, obs)`; the law becomes a merge-by-line, one more lemma |
| K8 | ~220 tm-core tests lose their replay | certain | S8's mechanical cost | §8.2's move plan; `tm-core` never links the kernel |
| K9 | memory: `decide` witnesses over `parseLine` of long lines | medium | OOM (§5.10a) | `Entry` values in witnesses; text ≤ 60 characters; 8 GB-capped probes |
| K10 | the in-flight stage-5 core edits `Json.lean`, `Boundary.lean`, `Goals.lean` | certain | merge conflicts | S1/S4 start after it lands; separate worktrees; `Check.lean` one editor at a time |
| K11 | a zone whose local date is non-monotone at midnight | low | `localMidnight` law needs `noGapAtMidnight`; windowing is unaffected (G4 is checked) | A4 includes such a zone |
| K12 | `JVal` widening changes free-text error strings the host maps (`kernel_bridge::refusal`) | certain, small | a refusal renders differently | the bridge test updated in S1; a behaviour row |

---

## 14. Genuinely new owner questions

None of these is decided above. Each has a recommended default, so the build is not blocked,
but taking the default is still the owner's call.

1. **Q1: invalid UTF-8 in `.tm/log.jsonl`.** The fork-point CLI fails the whole command
   (`read_to_string`), and `Log::parse_bytes` warns per line. The design warns per line: Rust
   blanks the line and reports its number, and the kernel emits `invalidUtf8`. This is a
   behaviour change within G9. *Default:* per-line warning.
2. **Q2: a derived cache file, and the one trust assumption.** `.tm/replay.json` holds the
   kernel's checkpoint and the sealed observation archive. It is new persisted state beside the
   Markdown database, safe to delete, and not restored by `tm undo`. `replay_window` is sound
   only if Rust hands back the checkpoint for the exact prefix. That is enforced by a full
   prefix hash in Rust (tested, not proved), or by a cheaper, weaker key (K6). *Default:* the
   file, with a full-prefix FNV-1a hash.
3. **Q3: old-date verbs pay a full replay.** `tm review day|week` for a date before the detail
   horizon (the start of the month or 14 days back, whichever is earlier), and `tm log --item`
   or a far `--since`, resend the whole log, so their latency grows with log age (§12:
   0.2–0.7 s of parse at 3 years, ESTIMATE). The alternative is keeping full day detail forever
   in the checkpoint, which makes every call grow at roughly half the log's rate. *Default:*
   full replay for old dates.
4. **Q4: observation order.** The kernel hands observations back in `(day, line)` order, not
   file order (P13). This only needs the owner if A8 shows the fit is order-sensitive.
   *Default:* canonical order, with A8 as the gate.
5. **Q5: event emission stays in Rust for D9.** The log grammar then has two definitions: a
   serde writer and a Lean reader, held together by A3 (§5.3's shape, recorded). Moving
   emission into the kernel, with commands returning the lines to append, is the structural
   fix and a separate tranche. *Default:* defer, and record it as a gap.
6. **Q6: the two "first wake" rules and the two "latest" rules** (inv §7 FLAG 3). Instant
   order is used for the day index and `last_done`; file order for `DayReplay.wake`,
   `slept_by_day` and the instance records. The design ports all four faithfully, with theorems
   naming where they disagree. Unifying them (§5.3) would change behaviour on out-of-order
   appends. *Default:* faithful port.
7. **Q7: per-sub-segment minute truncation** (inv §7 FLAG 4). A block paused `k` times loses up
   to `k` minutes (`close_sub`). The design ports it and records it as rounding site R8 beside
   `Arith`'s R1–R7. Changing it to truncate once per block is a behaviour change. *Default:*
   faithful port, recorded as R8.

**Not owner questions (settled by D9, D10, or by keeping behaviour), but recorded:** the zone as
a host table (§3.1, no behaviour change); `hsw` read from the log, not recomputed (faithful);
porting the unread facts (D9 says all of it); `unknown` keeping only its tag and id (nothing
reads `rest`); the 16 KiB line cap (P9).

---

## 15. Parity exceptions this design adds (continuing README "Stage 5 step 1"'s P1–P6)

| # | site | kernel | fork point | authority |
|---|---|---|---|---|
| P7 | a surrogate-pair `\u` escape in a hand-edited line | line warning `notJson badEscape` | accepted (serde) | gap 42 |
| P8 | a duplicate key on a known event, if A3 shows serde differs | `duplicateKey` warning | serde's behaviour under `flatten` | A3's finding |
| P9 | a line over 16 KiB | `lineTooLong` warning | parsed | gap 44 band |
| P10 | unknown routine status message | named warning with line number | formatted text with timestamp | §2.6 |
| P11 | instants outside `[1970, now + 5 y]` | nearest span's offset | tzdb | §3.1 |
| P12 | minute and count sums above `2^32 − 1` | `Nat` | `saturating_add` | as P5 |
| P13 | observation order | stable-sorted by `(day, line)` | file order, a start's obs at its start | §5.2 item 2, Q4 |
| P14 | `hsw` in the fit | serde-equal double via exact decimal text (A6) | serde double | none: expected zero differences, listed so the harness reports rather than hides one |
| P15 | invalid UTF-8 line (CLI) | per-line warning | whole command fails | Q1 |
| P16 | `Replay.warnings` / `LogWarning.error` text | named constructors | free text | AGENTS §5.7 |
