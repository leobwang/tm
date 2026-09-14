# D9 design, latency-first: the kernel replays the log without paying for its age

Read-only design pass, 2026-09-14, against `rebuild-on-lean` at `c2cf4dc` (working tree with
stage 5 step 1 uncommitted). The fact base is `design/inventory.md`; section numbers written
`inv §n` point into it. The oracle is fork-point `tm-core/src/log.rs`, cited by function name.
Nothing here edits the repo.

Labels. **MEASURED** means this pass ran it, and it says how. **ESTIMATE** means derived, and it
says from what. **OWNER** marks a genuinely new decision; §17 collects them. Everything else is
a design decision taken inside D5, D6, D9, D10, R1 to R12 and AGENTS §4, with its reason.

---

## 0. The design in one page

1. **The log crosses as raw lines, and the kernel is their only reader.** Each line is one JSON
   string element, exactly as documents cross today. Rust reads bytes, splits on `\n` and checks
   UTF-8 per line (G9 stays Rust). The kernel does everything else: `\r` trimming, blank lines,
   JSON, the typed grammar of 25 known kinds plus unknown tags, named per-line warnings, the undo
   mask, wake-based day attribution, the block machine, and every fact.
2. **Three paths, and only the first runs on an ordinary command.**
   - **Hot call.** The request carries a *snapshot* (the kernel's own replay state, folded through
     line `c`) plus the *suffix* (lines `c..n`, normally one or two wake-days). The kernel resumes
     the fold. ESTIMATE at 3 years: 3 to 10 ms, against 85 to 90 ms MEASURED for today's Rust
     whole-log replay.
   - **Daily seal.** On the first command of a new wake-day, the request also asks for a seal. The
     kernel returns a new snapshot, plus *ledger* lines for the days that just became final. Rust
     persists both. ESTIMATE: +40 to 80 ms once a day at 3 years, mostly the prefix digest in a
     debug build.
   - **Rebuild.** With no usable snapshot, Rust feeds the log in calls of 4,096 lines. Each call
     resumes from the previous call's snapshot, and every array is a page of at most 4,096
     elements, so gap 44 cannot fire. When a line refuses, the rebuild backs up to an earlier
     snapshot and resends more pages in one call. The worst case is bounded by memory, never by
     stack. ESTIMATE at 3 years: 0.7 to 1.0 s with a tree-map fast twin, 2.3 to 3.3 s on
     association lists.
3. **One law makes all three paths one replay:**
   `resume (seal empty pre) suf = replay (pre ++ suf)` on the observable view, when the resume
   guards accept. The guards are decidable and exact in the direction that matters. When one
   refuses, the answer is a rebuild, never a wrong fact. Chunked rebuild is the same law applied
   repeatedly. A second law rules out refusal loops: **a snapshot the kernel seals always accepts
   the lines it left unfolded**, so one rebuild settles any refusal.
4. **History is split by what reads it.**
   - Facts that need unbounded history (last completion, completion-date anchor and count, total
     minutes per item, latest named event) live in the snapshot as **per-key aggregates**. Their
     size grows with ids, not with days.
   - Facts about the current periods live in the snapshot for a **window** of at most 31 days.
   - Facts about finished days go to an append-only **ledger** that only Rust statistics and
     reviews read. The kernel's decisions never read the ledger.
5. **Time zones:** the host sends a **span table** for `cfg.tz`: UTC instants where the offset
   changes, generated from `chrono_tz`. Day attribution then equals `DayIndex` exactly, with no
   behaviour change. The table is a named trust boundary, like gap 10's regions.
6. **Undo:** a faithful port of `undo_mask`. The snapshot records which event kinds survive in the
   folded prefix. A suffix undo that finds no target in the suffix, while its kind survives in the
   prefix, is refused by name. The host rebuilds. Sealing never passes the oldest command
   `tm undo` can still pop (within 14 days). A crossing therefore takes a hand-appended,
   misrecorded or very old undo. Undo verdicts that a seal learned are kept in the snapshot, so a
   refusal never repeats.

---

## 1. Numbers this design stands on

### 1.1 Measured in this pass

**The kernel's JSON wire on log-shaped requests.** The probe used a copy of
`kernel/tm-kernel-ffi/target/release/examples/oneshot`, built 2026-09-13 05:36. `Json.lean` has
been unchanged since `b7f504d`, so this is today's `jparse`. It ran from the scratchpad under a
16 GB cap. Requests were `{"docs":[],"log":…}`, and `run` ignores unknown top-level keys, so the
whole payload is parsed and an empty `ok` is emitted. Timings are wall clock, best of 7, including
process start. The empty request `{"docs":[]}` took 1.4 ms. Generator: `design/probe/mkreq.py`;
runners: `run.sh` and `ms.py`.

| request (synthetic log, ~40 events/day) | bytes | best | net of 1.4 ms start | net per MiB | max RSS |
|---|---:|---:|---:|---:|---:|
| 1 month, events as objects | 124 KiB | 3.9 ms | 2.5 ms | 20 ms | 14 MiB |
| 1 month, lines as strings | 145 KiB | 4.4 ms | 3.0 ms | 21 ms | 16 MiB |
| 6 months, objects | 774 KiB | 17.5 ms | 16.1 ms | 21 ms | 54 MiB |
| 6 months, strings | 904 KiB | 19.1 ms | 17.7 ms | 20 ms | 62 MiB |
| 1 year, strings | 1,821 KiB | 41.0 ms | 39.6 ms | 22 ms | 116 MiB |
| 3 years, objects | 4.60 MiB | 0.13 s (10 ms timer) | | | 287 MiB |
| 3 years, strings | 5.38 MiB | 0.17 s (10 ms timer) | | | 340 MiB |
| 3 years, the whole text as ONE string | 5.33 MiB | 120.3 ms | 118.9 ms | 22 ms | 360 MiB |

- **Parse rate: about 22 ms per MiB** of request, whatever the shape.
- **Memory: about 63 MiB of RSS per MiB** of request. The `List Char` materialisation is real.
- **Gap 44 holds for arrays of objects too**, measured with an explicit 2 MiB `RLIMIT_STACK`:
  - 14,941 objects parse;
  - 22,055 objects **abort**, and so do 22,055 strings;
  - one 5.3 MiB string parses.

  This settles inv §4.4's ESTIMATE.
- Caveat: this is the JSON layer only. There is no kernel replay yet, so the step function's cost
  is ESTIMATE below. Step S0 re-measures all of this through a committed harness (AGENTS §5.11),
  and those numbers replace these.

**The replay facts over the synthetic logs** (`design/probe/sizes.py`). The undo mask is a
faithful copy of `undo_mask`; the day is the calendar date of `t`, which is enough for sizing.

| fact family | 1 mo | 1 y | 3 y @40/day | 3 y @61/day |
|---|---:|---:|---:|---:|
| events | 1,191 | 14,941 | 45,172 | 65,771 |
| undos / cancelled / dangling | 4 / 8 / 0 | 58 / 116 / 0 | 167 / 334 / 0 | 172 / 344 / 0 |
| furthest undo reach (lines) | 14 | 14 | 21 | 50 |
| items with minutes | 142 | 822 | 899 | 899 |
| done items / (id, date) done pairs / most dates on one id | 84 / 158 / 27 | 638 / 1,899 / 297 | 874 / 5,745 / 892 | 879 / 5,700 / 881 |
| (id, day) minute pairs | 139 | 1,728 | 5,151 | 5,114 |
| instance records | 82 | 977 | 2,979 | 2,966 |
| named events / distinct (name, id) | 3 / 3 | 35 / 35 | 123 / 115 | 117 / 112 |
| demotions / closes | 42 / 34 | 504 / 417 | 1,561 / 1,251 | 1,549 / 1,251 |
| energy obs / duration obs | 217 / 139 | 2,604 / 1,731 | 7,872 / 5,159 | 7,793 / 5,125 |
| distinct (kind, primary id) keys | 463 | 3,705 | 6,216 | 6,160 |
| event kinds present | 23 | 23 | 23 | 23 |

The generator caps ids at 900, so every per-id family saturates. A real tree mints ids for ever,
and the cli_latency tree alone holds about 2,900. This design therefore sizes per-id aggregates
at **900 to 3,000 ids**. Every time-indexed family grows linearly with days.

### 1.2 From the inventory (measured by the inventory pass)

- **Rust today, debug**, whole-log `Log::parse` plus `replay` on every command (inv §4.3): 3 years
  at 61/day costs 85 to 90 ms. That is about 15 ms per MiB.
- **cli_latency bounds** (inv §4.4): first verb 5 s (measured 0.59 to 0.65 s); a later verb 1 s
  (measured 0.05 to 0.062 s). Its tree has no log.
- **Gap 44:** 21,500 elements read and 22,000 abort on 2 MiB; 80,000 read and 90,000 abort on
  8 MiB. `splitDoc` has the same bands.

### 1.3 The budget this design commits to

| path | 1 month | 1 year | 3 years @61/day | basis |
|---|---:|---:|---:|---|
| Rust today, per command | 4.3 ms | 30 ms | 85 to 90 ms | MEASURED (inv §4.3) |
| **One whole-log kernel call**, JSON layer only (the design D9's costs warned about, rejected) | 3 ms | 40 ms | ~180 ms, and **aborts on a 2 MiB thread** | MEASURED 22 ms/MiB × 8.2 MiB; the abort is MEASURED at 22,055 elements |
| **Hot call:** snapshot plus 1 to 2 wake-days of suffix | 1 to 2 ms | 2 to 5 ms | 3 to 10 ms | ESTIMATE: snapshot 55 to 140 KB (§8.2) and suffix 8 to 16 KB, at 22 ms/MiB, ×2 for decode and resume, plus Rust decoding the facts |
| **Daily seal**, extra | +2 ms | +15 ms | +40 to 80 ms | ESTIMATE: FNV-1a over the prefix in debug Rust at 5 to 10 ns/byte, plus the snapshot emit and write |
| **Rebuild** (first run, a refusal, a changed kernel) | ~30 ms | ~0.3 s | 0.7 to 1.0 s with a tree map; 2.3 to 3.3 s on lists | ESTIMATE, §8.8 |
| Kernel memory per call | <10 MiB | <10 MiB | <15 MiB hot; ~35 MiB per rebuild chunk | MEASURED 63 MiB of RSS per MiB of request |

Against cli_latency, a later verb at 3 years stays near today's 0.06 s. The first verb (a rebuild
plus the automatic close) stays under 4 s even on lists, inside the 5 s bound. **The tree-map twin
(S6b) is still required before the host is wired**, because 3.3 s leaves too little margin on a
busy machine.

---

## 2. What D9 actually has to port

D9's text says "about 13 event kinds". The fork point has **25 known tags plus `Unknown`**:
`define_events!` and `EVENT_NAMES` (inv §1). Spec §10.1's examples cover 14. The port is all 25.
The replay part of `log.rs` runs from `undo_mask` to `replay_refs`, about 1,570 lines, matching
D9's "about 1,500".

This lens leaves the event semantics as `Machine::step` defines them (inv §2.4), with four
exceptions:

- **(a)** where the step writes, so the seal guards can see it;
- **(b)** what gets aggregated;
- **(c)** what gets emitted;
- **(d)** the bounded widths R10 forces.

---

## 3. The wire

### 3.1 Request

The existing request keys (`docs`, `cmds`, `now`, `blockMin`) are unchanged. New keys:

```jsonc
{
 "docs": [...], "cmds": [...], "now": "2026-09-14", "blockMin": 50,
 "at": "2026-09-14T09:00:00-05:00",           // NEW: the instant. When present, `now` must equal
                                              // its local date under `tz` (else "nowDisagrees")
 "tz": {                                      // NEW, §5. Required whenever `log` or `at` is present
   "name": "America/Chicago",                 // informational, at most 64 chars
   "from": "2026-09-10T00:00:00Z",            // table domain [from, to); outside it: tzOutOfRange
   "to":   "2027-10-19T00:00:00Z",
   "spans": [["2026-09-10T00:00:00Z","-05:00"], ["2026-11-01T07:00:00Z","-06:00"], ...]
 },
 "log": {                                     // NEW, §3–§8. Absent: no replay, as today
   "snap": null | <the snapshot JVal exactly as the kernel last emitted it>,
   "base": 45120,                             // index of the first line in `lines`; must equal snap.through (0 with null)
   "seam": null | "<text of line base-1>",    // must equal snap.seam (checked by the kernel)
   "lines": [["{\"t\":…}", null, "", …], …], // pages of ≤ 4,096 lines; null = not valid UTF-8 (host-detected)
   "seal": null | {"maxLine": 45100} | {"keepDays": 2, "maxLine": 45100},
   "want": {"core": true, "entries": [from, to] | null, "items": true | false}
 }
}
```

- **Lines are strings, not typed objects.** At suffix size (normally under 200 lines) the ~15%
  extra bytes and the second parse pass cost well under a millisecond. The payoff is a single
  reader of the log format (AGENTS §5.3), and it matches how documents already cross (AGENTS §2.4).
- **Pages of at most 4,096 elements (`pageMax`).** This is 5.2× below the 2 MiB abort
  (MEASURED). **Every array the log path reads or emits is at most `pageMax` long.** Larger
  collections, `lines` included, are pages, arrays of arrays, so `jtail`'s recursion depth is
  bounded by the page size and not by history. That is how the log path escapes gap 44 without
  touching `Json.lean`'s element twin. A call may carry many pages. The host's normal calls carry
  one; only a rebuild's back-up (§8.8) carries more, and it is bounded by memory.
- **`seal.maxLine`** is the host's undo-reach input (§8.5), and **`seal.keepDays`** is the
  rebuild's (§8.8). The kernel computes the actual fold point and ledger day itself.
- **Numerals the kernel emits in the `log` member stay below 2^53.** The host holds the snapshot as
  a `serde_json::Value`, and this bound (R10's stated width) makes Value's round trip exact whether
  a number lands in u64 or f64. Seconds since 0001-01-01 are about 6.4·10^10.

### 3.2 Response: the `ok` shape gains `log`

```jsonc
{"ok": {"docs": [...], "report": {...},
  "log": {
    "through": 45188,                         // base + lines.length
    "warnings": {"count": 3, "shown": [{"line": 45012, "why": "badField", "key": "est_min"}]},  // shown ≤ 64
    "open": {"block": null | {"id":"144","started":S,"workedMin":35,"since":S|null,"paused":false},
             "interrupt": null | {"start":S,"id":"144"|null}},
    "days":   [DayFacts…],                    // the open days (≥ L): the snapshot's openDays plus days the suffix touches
    "window": {"minutes": [[[id, day, min]…]…], "doneDates": [[[id, day]…]…],
               "instances": [[[item, inst, t, status, raw, actual|null]…]…]},   // day ≥ H, paged
    "named":  [[[name, id|null, lastT]…]…],
    "items":  [[[id, minutes, blocks, done, lastDone|null, firstDate|null, dateCount]…]…],  // only if want.items
    "loc":    {"lounge": n, "total": n, "byWakeHour": [[h, n, l]…], "streak": [lastDay, k]},
    "lastDay": day|null, "lastEffective": S|null, "unknown": n,
    "entries": [[[line, name, primaryId|null, t, off, fields]…]…],   // only if want.entries
    "snap":   null | {…},                     // only when sealing
    "ledger": [[LedgerDay…]…]                 // days sealed by this call, paged; [] otherwise
  }}}
```

- `S` is an instant: seconds since 0001-01-01T00:00:00Z as a `Nat`, with `"ns":k` added only when
  a sub-second part exists. Rust converts with the named constant
  `KERNEL_EPOCH_UNIX = 62_135_596_800`.
- `hsw` appears inside observations as `{"num":n,"den":d}`, plus `"neg":true` when negative.
- Instants in facts carry no offset. Every Rust consumer uses `with_timezone(cfg.tz)` (inv §3);
  only `tm log`'s display needs an event's own offset, which is why `entries` carries `off`.

### 3.3 New refusals

All of these come before any document is touched. `err` shapes gain a `log` member:

```jsonc
{"err": {"log": {"undoCrossesSnapshot": {"line": n}}}}      // G1
{"err": {"log": {"wakeBeforeSeal":      {"line": n}}}}      // G2
{"err": {"log": {"eventBeforeSeal":     {"line": n, "day": d}}}}   // G3
{"err": {"log": {"baseMismatch": {"snap": c, "base": b}}}}
{"err": {"log": {"seamMismatch": n}}}
{"err": {"log": {"badSnap": "<field>"}}}                    // includes a version the kernel does not read
{"err": {"log": {"tzOutOfRange": S}}}
{"err": {"log": {"badTz": "<why>"}}}                        // unsorted spans, offset ≥ 24 h, > 512 spans
{"err": {"log": {"pageTooLong": "<member>"}}}
"nowDisagrees"                                              // free-text jsonErr, beside badNow
```

- **Host reaction to G1, G2, G3, `baseMismatch`, `seamMismatch` and `badSnap`:** rebuild (§8.8),
  then re-issue the same request once. Requests are pure, so a retry is safe.
- **Host reaction to `tzOutOfRange`:** widen the table to cover the named instant and re-issue.
- **Anything else is a fault** (`kernel_bridge::fault_issue`).

---

## 4. The typed event grammar (Lean)

New module **`Log.lean`**. It imports `Json`, `Cal`, `Line` and `Arith`, and sits after `Arith`
in `TmKernel.lean` (AGENTS §8.3: count the imports).

### 4.1 Instants and offsets (added to `Cal.lean`, the calendar's module)

```lean
/-- An instant: whole seconds since 0001-01-01T00:00:00Z plus a sub-second part.
    Bounded (R10): years 1..9999, so sec < 315537897600. -/
structure Instant where
  sec : Nat
  ns  : Fin 1000000000
def Instant.wf (i : Instant) : Bool := i.sec < 315537897600
def Instant.lt / le                        -- lexicographic (sec, ns); total order
def Instant.minutesBetween (a b : Instant) : Nat   -- chrono num_minutes, truncated, floored at 0
/-- `±HH:MM` or `Z`. |offset| < 24 h (chrono `FixedOffset::east_opt`). -/
structure Offset where
  neg : Bool
  min : Fin 1440
def parseOffset  : List Char → Option (Offset × List Char)
def renderOffset : Offset → List Char     -- "Z" never rendered; "+00:00"
/-- RFC 3339 as `parse_timestamp` reads it: date `T` HH:MM, optional `:SS`, optional `.fraction`,
    then `Z`/`z`/`±HH:MM`. Fractions beyond 9 digits are truncated (to confirm against chrono,
    §15 P13). -/
def parseStamp  : List Char → Option (Instant × Offset)
def renderStamp : Instant → Offset → List Char    -- fmt_timestamp: whole seconds, with offset
```

- **One reader of an offset.** `parseOffset` reads the offset inside every `t`, every
  `tz.spans[i][1]` and the request's `at`.
- **One reader of a date.** `parseStamp` reuses `Field.parseDate`'s date grammar and extends
  `parseClock` to seconds, so the date and time grammars stay the `Line.lean` ones.
- **Clock arithmetic belongs in `Cal.lean`**, per AGENTS §8.3's trap and gap 10.
- **Instant order ignores the offset**, as `hsw_matches_spec` expects (inv §0.2).

### 4.2 Numerals in log lines: one parser, two modes

A log line may hold `hsw` (`0.95`, `-0.5`) and unknown payloads with any JSON numeral (inv §1).
The wire's `jparse` refuses those (`jparse_refuses_what_the_fragment_has_no_type_for`), and must
keep refusing them on the wire.

**The route: widen `JVal` visibly**, which AGENTS §8.3's trap permits "visibly, in a diff, with the
round trip extended". Add one constructor and a mode to the parser:

```lean
inductive JVal | null | bool (b : Bool) | num (n : Nat) | lit (t : Numeral) | str (s : List Char) | arr … | obj …
/-- An RFC 8259 numeral's text, validated: -? int frac? exp?.  At most 32 chars (R10). -/
structure Numeral where text : List Char   -- + Bool check numeralWf, Subtype
inductive JMode | wire | log
def jparseM (m : JMode) (l : List Char) : Except JErr JVal
def jparse := jparseM .wire                -- unchanged meaning: `num` only, `lit` never produced
```

Rules for the two modes:

- In `.wire` mode, a numeral that is not a bare natural is refused exactly as today, so the
  existing theorem keeps its statement, restated as `jparseM .wire`.
- In `.log` mode, a bare natural is still `num` and any other valid numeral is `lit`.
- `jemit (.lit t) = t.text`.
- The round trip extends: `jparseM .log (jemit v) = .ok v` for every `v` whose `lit`s are `wf`
  and are not bare naturals.
- **Why not a separate log parser:** one would be a second JSON grammar (AGENTS §5.3).
- **Why not Rust pre-parsing:** that makes Rust a reader of the log (D9).
- **The cost is re-proof** in `Json.lean` (every `JVal.rec` motive) and a new `| .lit _ =>` arm
  wherever `Boundary.lean` matches exhaustively. Most of those already fall through `| _`.

`Dec` is the exact reading of a `lit`, used only where the grammar types a field as decimal (`hsw`):

```lean
structure Dec where neg : Bool; q : Arith.Pos      -- q.den = 10^k·(2^e or 5^e) from the exponent
def Dec.ofNumeral? : Numeral → Option Dec          -- refuses |exp| > 400 or > 17 significant digits
```

The 400 and 17 bounds prevent memory bombs such as `1e999999999`, and 17 digits is the most ryu
writes. A line whose `hsw` is refused becomes a `badField hsw` warning.

### 4.3 Bounded field types (R10, each with a smart constructor and a rejection theorem)

| type | carrier | used for |
|---|---|---|
| `U8` | `Fin 256` | `pred rep went ci` (serde `u8`) |
| `U32` | `Fin 4294967296` | every `u32` field |
| `LStr` | `{s : List Char // s.length ≤ 4096}` | `id item inst loc status name from to field hash text attributed where of`, `window[i]` |
| `LList` | `{xs : List LStr // xs.length ≤ 256}` | `tags`, `dropped` |
| `Line` | `{s : List Char // s.length ≤ 65536}` | a whole line; longer is a `tooLong` warning |

The widths are R10's stated widths. The fork point has none, so a line past them is parity
exception P7 (§15).

### 4.4 The events

```lean
inductive LogEv
  | wake (slept : U32) (onset : Option U32)
  | arrive (loc : LStr) (window : LStr × LStr) (budget : U32)
  | start (id : LStr) (pred : U8) (rep : Option U8) (hsw : Dec) (slept : U32) (loc : LStr)
          (blocksDone : U32) (sinceBreak : U32)        -- defaults per `#[serde(default)]`; hsw default 0
  | done (id : LStr) (est actual : U32) (went : Option U8) (tags : LList) (ci : U8) (partial : Bool)
  | extend (id : LStr) (by : U32)          | stop (id : LStr) (remaining : U32)
  | brk (planned : U32) (actual : Option U32) (where_ : Option LStr)
  | energy (pred rep : U8) (hsw : Dec) (loc : LStr)
  | interrupt (id : Option LStr)          | resume (lost : U32) (dropped : LList)
  | pause (id : LStr)                     | unpause (id : LStr)
  | idle (attributed : LStr) (min : U32)
  | routine (item inst status : LStr) (actual : Option U32)
  | skip (item inst : LStr)
  | plan (hash : LStr) (replans drift : U32)
  | named (name : LStr) (id : Option LStr)
  | demote (id from to : LStr) (est : U32)
  | readopt (id : LStr) | move (id from to : LStr) | drop (id : LStr)
  | edit (id field from to : LStr) | note (text : LStr) | loc (loc : LStr)
  | close (period key : LStr)
  | undo (of : LStr) (id : Option LStr)
  | unknown (name : LStr) (pid : Option LStr)          -- `rest` is validated JSON, not kept
def LogEv.name : LogEv → LStr                           -- EVENT_NAMES, and the unknown tag
def LogEv.primaryId : LogEv → Option LStr               -- Event::primary_id, rest["id"] for unknown
structure Entry where
  line : Nat
  t    : Instant
  off  : Offset
  ev   : LogEv
```

### 4.5 Reading a line: warnings, never refusals

```lean
inductive LineWarn
  | invalidUtf8 | tooLong | notJson (e : JErr) | notAnObject | noT | badT
  | evNotString | missing (k : LStr) | badField (k : LStr)
def readLine (n : Nat) : Option (List Char) → Option (Except LineWarn Entry)
      -- none = blank (after trimming a trailing '\r'), skipped silently
```

The rules follow `Log::parse_bytes` and the hand-written `Deserialize` (inv §0.1, §0.2), each
pinned by a `decide` witness on a short `List Char` literal (AGENTS §5.10a):

- `ev` is read first. A known name decodes **strictly**, and a bad payload is a warning, never
  `unknown`. Any other string is `unknown`.
- Extra keys on a known event are ignored. `null` means `none` for option fields. An absent
  defaulted field takes its default.
- A top-level array is `notAnObject`, and `"ev":7` is `evNotString`.
- `wake` without `slept_min` is `missing slept_min`, and `est_min:"sixty"` is `badField est_min`.
- An unparseable `t` is `badT`, and a missing one is `noT`.
- A torn last line is `notJson`. A torn line that happens to be valid JSON is accepted.
- A key carried twice in one line: whatever serde does (probably last wins) is **measured against
  the oracle in S3 with crafted lines, then either reproduced or made a named warning** (P14).
  Log mode's key lookup (`jgetLast`, or a named `duplicateKey` warning) must not silently borrow
  the wire's `duplicateKey` refusal.
- `-0`, `3.0` for a `u8`, and `256` for a `u8` are likewise pinned to serde's verdict in S3.

`LogWarning.text` wording is not reproduced; the kernel names the reason (P10).

---

## 5. Time zones and day attribution

### 5.1 The choice: a host-generated span table

| option | exact parity with `DayIndex`? | what it cannot do | verdict |
|---|---|---|---|
| (a) host sends each event's local date | no | `day_of` is also applied to **derived** instants (`idle`'s `t − min`, `resume`'s interrupt start, `wake + 24h` in `bounds`, the local midnights of future days in D10's lookahead) | rejected |
| (b) **span table for `cfg.tz`** | **yes** | trusts that the host's table matches tzdb | **chosen** |
| (c) each event's own offset | no: `day_index_wake_to_wake` asserts a UTC-written entry lands on the Chicago date; the CLI stamps the machine's offset, not `cfg.tz`'s (inv §0) | behaviour change on travel, UTC writers and derived instants | rejected; it would be an **OWNER** change |

(b) is a trust boundary of the same kind as gap 10's `region_of`: the kernel believes the table it
is given. It is **not** a behaviour change, so it is not an owner question.

### 5.2 Kernel side

```lean
structure TzSpan where
  start : Instant
  off   : Offset
structure TzTable where
  name  : LStr
  from  : Instant
  to    : Instant
  spans : List TzSpan
def tzWf (z : TzTable) : Bool :=
  -- nonempty, head.start = from, starts strictly increasing and < to, length ≤ 512, every Instant.wf
abbrev Tz := { z : TzTable // tzWf z = true }
def Tz.ofJson? : JVal → Except String Tz               -- badTz / rejection theorem
def offsetAt   (z : Tz) (i : Instant) : Except TzErr Offset       -- tzOutOfRange outside [from,to)
structure Local where
  day : Nat
  sec : Fin 86400
  ns  : Fin 1000000000
def localOf   (z : Tz) (i : Instant) : Except TzErr Local
def dateIn    (z : Tz) (i : Instant) : Except TzErr Nat    -- `t.with_timezone(&tz).date_naive()`
def instantOf (z : Tz) (d : Nat) (s : Fin 86400) : Except TzErr Instant
      -- the earliest instant whose local time is (d,s); in a gap, the first valid instant up to
      -- 4 h later (`local_midnight`'s rule); `from_utc_datetime` as the last resort
```

`DayIndex` becomes:

```lean
/-- Surviving wake instants, sorted, deduplicated per `dateIn` keeping the earliest by instant. -/
def wakeIndex (z : Tz) (ws : List Instant) : Except TzErr (List Instant)
def dayOf (z : Tz) (ws : List Instant) (t : Instant) : Except TzErr Nat
  -- last w ≤ t; if t − w < 24 h then dateIn z w else dateIn z t
def boundsOf (z : Tz) (ws : List Instant) (d : Nat) : Except TzErr (Instant × Instant)
```

- **Days are `Nat` results**, never `Day`, per AGENTS §8.3's `omega` trap.
- **Both first-wake rules are kept by name** (inv §7 FLAG 3):
  - `wakeIndex` keeps the earliest wake by instant, as `DayIndex` does;
  - `firstWakeInFileOrder` keeps the first in file order, as `DayReplay.wake` and `slept_by_day`
    do.

  §17 asks whether to unify them.

### 5.3 Host side (Rust, `kernel_bridge.rs`)

**`tz_table(cfg.tz, from, to)`:**

1. Sample `cfg.tz.offset_from_utc_datetime` at every UTC midnight in `[from, to)`.
2. Wherever two samples differ, bisect to the second.
3. Emit spans.
4. An offset with non-zero seconds (pre-1937 LMT) cannot be written `±HH:MM`, so the host refuses
   the command with a host error naming the zone.

**Ranges:**

- **Hot call:** `from` = snapshot `ledgerDay − 3 days` (read from the snapshot in `.tm/replay.json`), and
  `to` = `now + 400 days`. The 400 days cover D10's lookahead through most due dates; beyond that
  the kernel's `tzOutOfRange` asks for more. That is about 1 to 3 spans, ESTIMATE under 1 ms to
  generate in debug.
- **Rebuild:** `from` = 1970-01-01 (widened on `tzOutOfRange`), and `to` = `now + 400 days`. That
  is about 115 spans, generated once per rebuild; ESTIMATE ~10 to 20 ms in debug.

---

## 6. Undo

### 6.1 The mask, ported

```lean
def undoMask (es : List Entry) : List Bool          -- `undo_mask`, verbatim semantics (inv §2.2)
def survivors (es : List Entry) : List Entry
def UndoMask.pairs …                                -- (cancelled − dangling) / 2
```

What the port keeps, each pinned by a witness:

- an undo always cancels itself;
- the target is the greatest earlier uncancelled non-undo entry with `name = of` and, when `id` is
  given, `primaryId = id`;
- `of` may name any tag, including `plan`, `note`, unknown tags and verb names;
- undoing an undo always dangles;
- there is no redo;
- time and day are ignored;
- `undo_mask_pairs_and_dangling`'s `[T,T,T,T,T,F,T]` with `dangling = [4,6]` is a `decide` witness.

### 6.2 The crossing guard (G1), and the verdicts a seal remembers

The snapshot carries two things for undo.

- **`kinds : KindSet`**: a `Fin 25 → Bool` over known names, plus up to 16 unknown tag names with
  an overflow flag. It records the kinds that survive in the folded prefix.
- **`pending : List (Nat × Option Nat)`**, at most 1,024 entries. For every **unfolded** undo line
  `u` whose target the sealing call found **before** the fold point, or found nowhere, it stores
  that verdict: `some j` for a target line `j` already excluded from the fold, `none` for a
  dangling undo. An undo whose target is itself unfolded is not stored; it is recomputed.

On resume, run `undoMask` on the suffix, applying `pending`'s verdicts in file order. **G1 refuses**
only when an undo that is not in `pending` dangles within the suffix **and** `of ∈ kinds` (or `of`
is unknown and the overflow flag is set).

- **Sound:** if G1 accepts, the suffix's survivors under the whole-log mask are exactly its
  survivors here, and no prefix entry is cancelled. This is proved (§11) from
  `undoMask_append_of_noCross` and `pendingSound`, the invariant that every stored verdict is the
  whole-log verdict. `seal` establishes that invariant, because the call that stores a verdict saw
  both the undo and every candidate at or after its own base, and its own G1 accepted.
- **Over-approximate:** it names kinds, not (kind, id) keys. A spurious refusal needs a *new* undo
  (appended after the last seal) with no target in the suffix whose kind survives in the prefix,
  and it costs one rebuild.
- **Loop-free:** the rebuild backs up until one call sees the undo together with its target, or
  with line 0 (§8.8). The resulting snapshot stores the verdict in `pending`, so the same line
  never refuses again (`a_sealed_snapshot_accepts_its_own_suffix`, §11).
- **Why kinds and not keys:** the exact key set measures 6,216 entries at 3 years (§1.1) and grows
  with ids, and it would be parsed on every call. `KindSet` is constant-size, and `pending` is
  bounded by the undos not yet folded (normally under 50).
- **The host keeps crossings rare** by never sealing past the oldest command `tm undo` can pop,
  within 14 days (§8.5).

### 6.3 What `tm undo` does under D9

- **Unchanged:** it restores file bytes and `state.json`, and appends one `undo{of,id}` per
  recorded event, most recent first, or `undo{of: verb}`. `move_has_no_inverse_command` stands:
  replay is the undo.
- **Changed:** `Recorder` stores `log_line`, the host's split index, blank lines included, and
  `UndoEntry` gains that field. `new_events` asks the kernel for
  `want.entries = [log_line, n]` and records the `name` and `primaryId` it returns.
- **Effect:** `log_len`'s blank-and-malformed count and `new_events`' parsed count no longer
  disagree (inv §0). Behaviour row P12.

---

## 7. What the kernel derives, what it returns, and where each fact lives

### 7.1 The replay machine

New module **`Replay.lean`**. `Machine::step` is ported event by event (inv §2.4):

- saturating `U32` arithmetic;
- `close_sub`'s per-sub-segment truncation, named as rounding site **R8** in `Arith`'s table
  (inv §7 FLAG 4); nothing else rounds;
- `load` kept as an exact pair with denominator 5 (FLAG 6);
- logged `hsw` read, not recomputed (FLAG 5);
- **every write the step performs goes through one of seven write channels**, each tagged with the
  day or key it touches. That tagging is what lets the guards and the compaction see exactly what
  an event changes:

```lean
inductive Touch
  | day (d : Nat)                 -- DayFacts of day d (segments, starts, breaks, obs, credit…)
  | itemDay (id : LStr) (d : Nat) -- minutes_by_day
  | item (id : LStr)              -- totals, done flag, last_done, done-date count/first
  | doneDate (id : LStr) (d : Nat)
  | inst (item inst : LStr)       -- instance record (keyed by the inst date or ordinal)
  | named (name : LStr) (id : Option LStr)
  | machine                       -- block / last_cut / interrupt
def touches (z) (ws) (m : MachineState) (e : Entry) : Except TzErr (List Touch)
def step (z) (ws) (s : State) (e : Entry) : Except TzErr State
theorem step_writes_only_what_it_touches …   -- the frame law the guards stand on (§11)
```

### 7.2 The fact catalogue

"History" says what the fact needs; "lives in" is §8's split: **S** snapshot, **W** the snapshot's
31-day window, **L** the ledger, **O** the open days recomputed on each call.

| fact (fork-point name) | consumers (inv §3) | history needed | lives in | bounded form, and size at 3 years |
|---|---|---|---|---|
| `done_items`, `is_done` | recur, priority, reviews, `day_extras` | all | S | `done` bit per id; 874 / ~3,000 |
| `last_done[id]` (latest by **timestamp**) | `after_done_state` | all | S | `Option Instant` per id |
| `done_dates[id]`: `.first()` and `.len()` only (grep: no other external reader) | `calendar_instances` anchor, `completion_count`, `next_ordinal` | all | S (first, count) + W (the dates ≥ H, to deduplicate retro dates) | 2 numbers per id; the 5,745 pairs collapse to ~874 records plus ≤ 31 days of dates |
| `ItemReplay.minutes`, `.blocks`; `done_minutes_map` | TUI queue, month review, §6.4 progress | all | S | 2 numbers per id |
| `minutes_by_day[(id, d)]`; `block_minutes_on` | `done_this_period`, `close_day`/`day_remaining` | current day, week and month | W | `(id, d, min)` for `d ≥ H`; ~5/day, ≤ 155 |
| `instances[item][inst]` (last in **file order**) | `logged_status`, `logged_instances`, `done_this_period`, `next_ordinal`, `completion_count` | date keys: the window; ordinal keys: all | W (date ≥ H) + S (every `#N`) | synthetic: ~93 date records in window, 0 ordinal |
| `events[name]` | `waiting_state`/`arrival_of` (max `t` filtered by id and date ≥ since), `collect_candidates` (names), `event_occurred` | latest only | S | `(name, id?) → last t`; 115 keys. Exact: max-then-filter equals filter-then-max for a `≥ since` filter |
| `DayReplay` for today and yesterday | `wake_time`, `slept_min`, `today_slots`, `plans_today`, planner, status line, TUI | open days | O | `DayFacts`, ~2 KB/day |
| `DayReplay` for finished days | reviews (day, week, month), `lounge_rate`, `arrivals_from_replay` | all, but read only by Rust | L | 1 ledger line/day, ~2.5 KB |
| `lounge_rate` (every day's `loc`, wake hour, streak ≤ week end) | week review | all | S aggregate + L for old weeks | `(lounge, total, byWakeHour[24], streak)`, constant |
| `energy`, `durations` (`EnergyObs`, `DurationObs`) | fit, compare, `estimate_calibration`, posterior (today), reviews | all, read only by Rust | L (ledgered days) + O (open days: the snapshot's `openDays` plus the suffix) | 7,872 + 5,159 at 3 years, never on the hot path |
| `demotions` | reviews (by `t`'s calendar date, `from` key) | all, read only by Rust | L + O | 1,561 at 3 years |
| `open_block`, `open_interrupt`, `last_cut` | planner, `active_elapsed_min` | machine | S | constant |
| `days.keys().last` | `status_line` | latest | S | `lastDay` |
| last effective instant | `day::idle` | latest | S | one instant |
| today's pauses, breaks, first start | `since_break_min`, `idle_min_since`, `idle_since` | open days | O | ported as the kernel facts `sinceBreakMin`, `idleMinSince`, `lastInstantOn`: these two Rust loops use their own pairing rule, which is not the machine's segments, so they are ported as named facts, not re-derived in Rust |
| `unknown`, warning count | none by grep | count | S | 2 numbers |
| `ItemReplay.{stops, extended_min, done_at, partial_done_at}`, `closes`, `dropped_items`, `longest_leak`, `DayReplay.{replans_today, last_plan_hash, loc_changes, dropped}`, `interrupts` beyond each day's lost minutes and dropped ids | **no external reader** (inv §3) | — | L only (days' records) or nowhere | **S5 must first check `--json` serialisation of `Replay`**, which the inventory did not; anything a `--json` output shows is kept in L |

**`view`** is the conjunction of every row's *observable* reading: the queries a consumer can make,
not the internal state. It is the right-hand side of every law in §11. A consumer reading a fact
the view omits is a Rust-side audit failure. S7 carries a grep test naming each accessor.

---

## 8. Snapshot, window, ledger: the windowing scheme and its law

### 8.1 Three horizons, all kernel-computed

- **`c` (`through`):** lines `[0, c)` are folded into the snapshot state, in file order.
- **`L` (`ledgerDay`):** every day `< L` is final, and its facts are in the ledger. Days `≥ L` that
  folded events touched keep their `DayFacts` in the snapshot (`openDays`, normally 2 to 3 days).
  **Invariant:** no unfolded line touches a day `< L`, and no folded day `≥ L` is in the ledger.
- **`H(L) = min (monthStart L) (isoMonday L)`:** window facts (`itemDay`, `doneDate`, date-keyed
  `inst`) are kept for `d ≥ H` and compacted away below. Since `L ≤ today`, every day, week and
  month period containing today starts at or after `H`, and `L − H ≤ 30`.

### 8.2 Snapshot contents and size

```lean
structure Snap where
  v        : Nat              -- snapVersion; any other value is badSnap
  through  : Nat              -- c
  seam     : Option Line      -- text of line c−1
  ledgerDay : Nat             -- L
  maxT     : Option Instant   -- latest instant among folded survivors (G2)
  wakes    : List Instant     -- the kept wakes with dateIn ≥ L−2 (enough for dayOf/boundsOf of any day ≥ L)
  kinds    : KindSet          -- G1
  pending  : List (Nat × Option Nat)  -- G1's remembered verdicts, ≤ 1,024 (§6.2)
  openDays : List DayFacts    -- facts of days ≥ L that folded events touched
  machine  : MachineState     -- block (with its pending obs), last_cut, interrupt
  items    : Page (List ItemAgg)      -- id, minutes, blocks, done, lastDone, firstDate, dateCount
  window   : WindowFacts              -- itemDay, doneDate, inst (date ≥ H)
  ordinals : Page (List InstRec)      -- every `#N` instance record
  named    : Page (List NamedLatest)
  loc      : LocAgg
  lastDay  : Option Nat
  lastEff  : Option Instant
  unknown  : Nat
  warnings : Nat
def encodeSnap : Snap → JVal
def decodeSnap : JVal → Except String Snap     -- every field bounded, pages ≤ pageMax
```

**Size at 3 years** (ESTIMATE from §1.1). A positional per-id record such as
`["144",1234,17,1,63916329600,739512,27]` is ~40 bytes, so:

- `items`: 36 KB at 900 ids, 120 KB at 3,000;
- `window`: ≤ 155 + 93 + ~155 records ≈ 9 KB;
- `named`: ~3.5 KB;
- `openDays`: 2 to 3 days, ~5 KB;
- the rest: under 1 KB.

**The total is 55 to 140 KB, and grows with ids, not days.** At 3,000 ids that is about the size
of the plan tree the same verb already sends.

### 8.3 The resume guards (checked in suffix order; a refusal names the line)

- **G1, undo crossing:** §6.2.
- **G2, a wake that would move folded history.** A suffix wake `w` with `w ≤ maxT` is refused.
  `dayOf` looks back at most 24 h, so a new wake can re-attribute only instants `≥ w`, and none of
  those is folded. The wake's own day is subject to G3, so `slept_by_day` of a ledgered day never
  changes. The per-date deduplication meets only folded wakes earlier than `w`, and those are in
  `wakes`.
- **G3, a write to a ledgered or compacted day.** Any `Touch.day d` with `d < L`, or
  `Touch.itemDay _ d`, `Touch.doneDate _ d` or date-keyed `Touch.inst` with `d < H`, is refused.
  This covers:
  - a routine done for an instance dated before `H`;
  - an `idle` whose start falls before `L`;
  - a `resume` whose record day is `< L`;
  - a hand-appended retro event.
- **G0, provenance:** `base = snap.through` (`baseMismatch`), `seam = snap.seam`
  (`seamMismatch`), `decodeSnap` succeeds (`badSnap`).

What does not need a guard, and why:

- **`last_done`** is a max by timestamp, which commutes.
- **`done_dates`' count** deduplicates against the W dates, and by G3 no retro date falls below
  `H`.
- **`named`** is a max.
- **Ordinal instances** are all kept, so a last-in-file-order overwrite is exact.
- **Machine-state events** (a `done` writing `went` onto the open block's obs, `uncredit_cut`, a
  `resume` closing an old interrupt) are covered by the seal rule below, which never ledgers a day
  the machine can still write.

### 8.4 The seal

`seal z s suf target` computes, over one call:

1. **The call-wide mask.** Run `undoMask` over the suffix with `pending` applied, as in §6.2. G1
   to G3 have already accepted.
2. **The fold point `c'`:** the longest prefix of the suffix such that
   - (i) every survivor in it touches only days `< F'`, where `F' = dayOf at − 1`, or in a rebuild
     call `min (dayOf at − 1) (maxDay call − keepDays)`, so today's and yesterday's lines stay
     unfolded and a late `tm wake 06:05` never refuses;
   - (ii) `c' ≤ target.maxLine`, so `tm undo`'s reach stays unfolded;
   - (iii) every unfolded wake is later than the folded `maxT`, so G2 cannot fire on the lines
     left behind;
   - (iv) it leaves at most 1,024 undo verdicts for `pending`.

   Shrinking `c'` preserves (i) to (iv), so the longest such prefix exists. File order is kept:
   one future-dated line early in the file only stops the prefix. That is correct, merely less
   compaction.
3. **The ledger day:**
   `L' = min F' (the least day any unfolded survivor touches) (the day of machine.block's start, if
   it holds an obs) (the day of last_cut.t, if set) (the day of the open interrupt's start)`, floored
   at `s.ledgerDay`, since a ledger day never moves back.
   - Taking the least day of an unfolded survivor keeps any day an unfolded line will write out of
     the ledger. This is the rule that keeps a retro line from refusing on every call.
   - A retro line appended behind today's lines is folded two days later, when the lines ahead of
     it become foldable; `L` then catches up.
4. **Emit:**
   - the new `Snap` at `c'`, with `pending` recording the unfolded undos whose verdict lies before
     `c'` or is dangling, `openDays` holding the folded facts of days in `[L', ∞)`, and the window
     compacted to `H(L')`;
   - one `LedgerDay` for each day in `[L, L')`, holding every day-scoped fact of that day. That
     includes obs, durations, demotions, closes, interruptions and named events, each with its
     `t`, so Rust can re-bucket demotions by calendar date as `day_review` does (inv §3).

**Stalls** (an open block with an obs, a `stop` never followed by `start`, an open interrupt) hold
`L'` back. Latency then degrades by the stall's length; answers are never wrong. `tm check` names a
stall longer than 7 days (S9).

**The no-loop law.** Steps 2 and 3 are exactly the conditions under which G1 to G3 accept the
remaining lines `[c', n)`: `a_sealed_snapshot_accepts_its_own_suffix`, §11. A refusal therefore
comes only from a line appended after the seal, and one rebuild settles it.

### 8.5 The host's seal policy

- **When:** seal when the snapshot's `ledgerDay` is older than yesterday by the host's calendar,
  which is at most one seal per day. The request's `seal` is `{"maxLine": m}`.
- **`maxLine`:** `m = min(entry.log_line)` over undo-stack entries younger than 14 days, or no
  bound when there are none. `tm undo` can then never cross a seal it caused.
- **Undo reach is capped at 14 days:** an older entry is ignored, so a light user's months-old
  stack cannot pin the suffix. Undoing such a command is a G1 crossing: one rebuild, the same
  answer.

### 8.6 Persistence (all Rust, G9)

**`.tm/replay.json`**, written atomically (`write_json`) and read on every command:

```jsonc
{"format": 1, "kernel": "<TM_KERNEL_ID>", "tz": "America/Chicago", "logBytes": B, "prefixFnv": "<16 hex>",
 "ledgerDays": k, "snap": { … the kernel's JVal … }}
```

- `TM_KERNEL_ID` is an FNV-1a of the linked kernel archive, computed in `tm-kernel-ffi/build.rs`
  and emitted with `cargo:rustc-env`. **Any kernel change means a rebuild.** Correctness therefore
  does not depend on anyone remembering to bump `snapVersion`. The version still exists, for
  `badSnap` on a hand-copied file.
- `B` is the byte offset of line `c`. Rust owns the newline convention, as for documents.

**`.tm/replay-days.jsonl`**, append-only, one line per sealed day, read only by reviews, the fit,
`tm log --since` and `tm model`:

```jsonc
{"through": c', "day": 739872, "facts": { … LedgerDay as the kernel emitted it … }}
```

**Write order and recovery:**

1. Append the ledger lines, then write `replay.json`.
2. On load, drop ledger lines whose `through` is greater than the snapshot's (an unfinished seal).
3. If fewer than `ledgerDays` lines match, rebuild.

**Integrity:**

| check | when | what it catches |
|---|---|---|
| file length ≥ B | every call (host) | truncation, a deleted log |
| `seam` equals line `c−1` | every call (kernel, G0) | a rewritten tail, a swapped log file |
| `prefixFnv` over `[0, B)` | every seal (host, once per wake-day) | an edit anywhere in sealed history; ESTIMATE 35 to 70 ms debug at 6.9 MiB |

A hand edit of a sealed line is therefore seen at the next seal, not at the next command.
**OWNER Q1.**

**Concurrency** (§1.3's writers). `replay.json` is written with `write_guarded` semantics. If
another process changed it since this command read it, this command skips its seal; its answers
are still correct, and the next command seals. A `snap.through` larger than the log this process
read (another process appended and sealed in between) is handled by re-reading the log once, then
rebuilding.

### 8.7 Compaction

```lean
def compact (d : Nat) (s : State) : State      -- drop itemDay/doneDate/date-keyed inst with day < H d
theorem compact_keeps_the_view_at_H (d s) : viewAt (H d) (compact d s) = viewAt (H d) s
theorem step_commutes_with_compact (d s e) (h : guard d s e = true) :
    viewAt (H d) (step (compact d s) e) = viewAt (H d) (compact d (step s e))
```

### 8.8 Rebuild and range reading

**Rebuild** (host):

1. Read the whole log, split it, and send calls of one page (4,096 lines) each, with
   `seal: {"keepDays": 2, "maxLine": …}` and no documents.
2. The kernel folds each call through `F' = maxDay(call) − 2`, so about two days of lines ride
   into the next call. That absorbs late wakes, short-reach undos and retro routine logs without
   any refusal.
3. The host keeps each call's `(snapshot, ledger lines)` on a stack in memory (17 × ≤ 140 KB at
   3 years) and writes the ledger only when the rebuild finishes.

**Backing up.** A refusal (G1 to G3) inside a rebuild means a line in this call reaches something
an earlier call already folded or ledgered. The host pops `j` entries (1, 2, 4, …) and re-sends
everything from that snapshot's `through` to the end of the refusing call, as several pages in one
call.

- **It terminates:** with the empty snapshot nothing is folded, so G0 to G3 cannot refuse.
- **It is bounded by memory, not stack:** pages keep every array ≤ 4,096. The worst case is one
  call carrying the whole log: ESTIMATE ~520 MiB at 3 years @61/day, from the MEASURED 63 MiB per
  MiB. Every accepted call is an instance of `resume_is_replay`, so the result does not depend on
  how many times it backed up (`chunked_rebuild_is_one_replay`).
- **After a rebuild, the suffix it left is accepted**, by the no-loop law (§8.4).

**Cost ESTIMATE at 3 years @61/day** (65,771 lines, 17 chunks):

| component | cost | basis |
|---|---:|---|
| wire and line parsing | ~360 ms | 2 passes × 22 ms/MiB × 8.2 MiB, MEASURED rate |
| step on tree maps | 0.2 to 0.35 s | ~5 µs/event, ESTIMATE |
| step on association lists | 1.8 to 2.6 s | ~40 µs/event, ~450 `LStr` comparisons per lookup across several maps, ESTIMATE |
| snapshot re-parse and emit per chunk | 35 to 100 ms | 17 chunks |
| ledger emit, Rust decode and append | 100 to 200 ms | 1,095 lines, ~2.7 MiB |
| **total** | **0.7 to 1.0 s** (tree maps) / **2.3 to 3.3 s** (lists) | |

Memory is about 35 MiB per chunk.

**Range reading.** A query about finished days never calls the kernel: Rust reads
`replay-days.jsonl`. A review of an old week or month reads those lines, and so do the fit and
`tm log --since`, which needs the old days' wakes, stored in `LedgerDay`. **The only slow path is
the rebuild.**

---

## 9. Observations back to Rust

- **`tm model --fit/--compare`:** Rust reads every `LedgerDay`'s `energy`, `durations` and
  `arrival`/`loc`, then the open days from a hot call, and hands them to `energy::fit`
  (`FitInput::new`). `fit_replay` is deleted; `fit` and `compare` stay.
  - ESTIMATE ~50 to 100 ms at 3 years: serde over ~13,000 observations in 2.7 MiB of ledger, debug.
  - Today that verb pays a whole replay.
- **Reviews:** `day_review`, `week_review` and `month_review` read the relevant `LedgerDay` lines
  plus the open days. `estimate_calibration` over **all** durations reads the ledger. `lounge_rate`
  reads `LocAgg` for the current week and scans ledger lines for an old one.
- **The posterior (`today_slots`):** today's obs come from the open days, as now.
- **`hsw` to f64** is `num as f64 / den as f64` with `den = 10^k`. This is correctly rounded, and
  bit-identical to parsing the decimal text, whenever `num ≤ 2^53` and `k ≤ 22`. The fork point's
  `round`-to-0.01 values always satisfy that. P9 covers hand-written values that do not.
- **Is persisting kernel-emitted observations "Rust keeping only the fit"?** This design reads D9
  as "Rust derives nothing". Storing the kernel's output verbatim is storage, not derivation, and
  it is the difference between ~0.1 s and ~1 s for `tm model` and the review verbs. **OWNER Q3**
  asks the owner to confirm that reading.

---

## 10. The Rust side

**Stays Rust:**

- all file I/O: reading `log.jsonl` from `B − seam length` to the end, `append_text`, the two
  sidecars, atomic writes, guards;
- the newline split and the per-line UTF-8 check (G9: an invalid line is sent as `null`, and the
  command no longer fails, P8);
- `tz_table` generation;
- the seal policy;
- the rebuild loop;
- `TM_KERNEL_ID`;
- the statistical fit;
- the reviews' monitors and rendering;
- `tm log`'s formatting.

**Deleted from the shipped path:**

- `tm/src/cli/ctx.rs`: `read_log`'s `Log::parse`, `Ctx.log: Log`, `Ctx.replay: Replay` built by
  `log.replay(None, cfg.tz)` in `Ctx::load_with` and `Ctx::reload`.
- `tm-core/src/log.rs`: `undo_mask`, `UndoMask`, `DayIndex`, `hours_since_wake`' replay use,
  `local_midnight`, `Machine`, `replay`, `replay_refs`, `Log::effective`/`iter_day`/`iter_range`/
  `iter_item`/`day_index`/`undo_target`/`compensating_undo`, and the `Replay` builders.
  - **`LogEntry`, `Event` and `fmt_timestamp` stay:** they are the **writer** (OWNER Q4).
  - **The oracle stays available:** the fork point `4748911`'s `log.rs`, built by the differential
    oracle (AGENTS §7.3), is the parity source. The shipped tree does not need a live copy.
- `tm-core/src/energy.rs`: `fit_replay`, `arrivals_from_replay`.
- The raw log loops: `tm/src/cli/day.rs` `since_break_min`, `idle_min_since`, and `idle`'s
  `effective().last()`; `tm/src/tui/app.rs` `idle_since`; `tm/src/cli/undo.rs` `log_len` and
  `new_events`' parse.

**Changed (transitional, until stage 5 moves recurrence and priority, and stage 6 the planner, into
the kernel):**

- `kernel_bridge.rs` gains `ReplayFacts` (decoded through smart constructors, as `decode_report`
  already is), `replay_call`, `rebuild`, `seal_policy`, `tz_table`.
- `Ctx` holds `facts: ReplayFacts`. `ReplayFacts` exposes the fork-point accessor names
  (`day`, `is_done`, `last_done`, `done_dates_first`, `done_date_count`, `instances_of`,
  `events_named`, `block_minutes_on`, `blocks_done`, `energy_on`, `done_minutes_map`,
  `open_block`), so the Rust consumers change by type, not by logic.
- **Two logic changes, each a behaviour row:**
  - `recur.rs` reads `done_dates_first` and `done_date_count` instead of `done_dates(key)` as a
    `Vec`;
  - `review.rs` `lounge_rate` reads `LocAgg` for the current week.
- **Latency of the transition:** `Ctx::load_with` makes one replay-only kernel call (no documents)
  before anything else. A verb that later calls `apply` pays a second call's documents, not a
  second snapshot, because `apply` omits `log` until stage 5 needs both in one request.

---

## 11. `Goals.lean` statements to add (under `# STAGE 5`, "D9")

**Header fixes (D9 exists now):**

- Rewrite the stale `PlanCore.log` sentence (inv §7 item 7).
- Move D1 and D2 out of "not stateable yet": `LogEv` and `Entry` now exist. The recurrence step
  states them; this tranche does not.

Signatures are provisional, as declared in §4 to §8. Each goal carries its verdict letter.

```lean
/-! ## D9 — the log grammar -/
theorem parseStamp_renderStamp (i : Instant) (o : Offset) (h : i.wf = true) :
    parseStamp (renderStamp i o) = some (⟨i.sec, 0⟩, o) := sorry                -- P*
theorem parseStamp_orders_by_the_instant_not_the_offset :
    ∃ a b i oa ob, parseStamp a = some (i, oa) ∧ parseStamp b = some (i, ob) ∧ oa ≠ ob := sorry   -- P*, non-vacuity
theorem jparseM_log_jemit (v : JVal) (h : litsWf v = true) : jparseM .log (jemit v) = .ok v := sorry   -- P*
theorem jparseM_wire_never_yields_a_lit (l : List Char) (v : JVal) :
    jparseM .wire l = .ok v → noLit v = true := sorry                           -- P*, the wire is unchanged
theorem readLine_known_payload_error_is_a_warning (n) (l) (k) (hk : k ∈ knownNames) … :
    readLine n (some l) = some (.error w) := sorry                              -- P*, never `unknown`
theorem readLine_reads_every_rendered_event (e : Entry) (h : entryWf e = true) :
    readLine e.line (some (renderEntry e)) = some (.ok e) := sorry               -- P*, the writer-reader seam

/-! ## D9 — time zones and days -/
theorem instantOf_localOf (z : Tz) (i : Instant) (l : Local)
    (h : localOf z i = .ok l) (hu : unambiguousAt z l = true) :
    instantOf z l.day l.sec = .ok ⟨i.sec, 0⟩ := sorry                           -- P*
theorem dayOf_is_the_recent_wakes_date (z ws t w)
    (hw : lastWakeLe (wakeIndex z ws) t = some w) (h24 : t.sec < w.sec + 86400) :
    dayOf z ws t = dateIn z w := sorry                                          -- P*
theorem dayOf_is_the_calendar_date_without_a_recent_wake … := sorry             -- P*
theorem a_wake_day_is_shorter_than_a_day (z ws d a b)
    (h : boundsOf z ws d = .ok (a, b)) : b.sec ≤ a.sec + 86400 := sorry         -- P*

/-! ## D9 — undo -/
theorem undoMask_append_of_noCross (pre suf : List Entry)
    (h : noCross (kindsOf (survivors pre)) suf = true) :
    survivors (pre ++ suf) = survivors pre ++ survivors suf := sorry            -- P*, the two-run law of G1
theorem noCross_is_needed :
    ∃ pre suf, survivors (pre ++ suf) ≠ survivors pre ++ survivors suf := sorry  -- R* witness: the guard is not vacuous
theorem undo_of_an_undo_dangles (es i) (hi : isUndoOfUndo es i) : dangles es i := sorry   -- P*

/-! ## D9 — the replay and the windowing scheme -/
theorem step_writes_only_what_it_touches (z ws s e q)
    (hq : ∀ τ ∈ touches z ws s.machine e, ¬ q.reads τ) :
    ask (step z ws s e) q = ask s q := sorry                                    -- P*, frame law
theorem resume_is_replay (z : Tz) (pre suf : List Entry) (d : Nat) (s s' : Snap) (led : List LedgerDay) (f : Facts)
    (hs : sealFrom z empty pre d = .ok (s, led))
    (hwire : decodeSnap (jparseM .log (jemit (encodeSnap s))) = .ok s')        -- §5.9: through the disk
    (hr : resume z s' suf = .ok f) :
    viewAt (H s.ledgerDay) f = viewAt (H s.ledgerDay) (replay z (pre ++ suf))
    ∧ ledgerView led ++ openDays f = dayView (replay z (pre ++ suf)) := sorry   -- P*, THE law
theorem resume_refuses_exactly_what_would_change_the_view … := sorry            -- P* one direction,
    -- R* the other: a refusal is allowed to be spurious (KindSet over-approximates); state both
theorem chunked_rebuild_is_one_replay (z) (chunks : List (List Entry)) (ss) (h : chainOk z chunks ss) :
    finalView ss = viewAt _ (replay z chunks.join) := sorry                     -- P*, induction on resume_is_replay
theorem compact_keeps_the_view_at_H (d s) : viewAt (H d) (compact d s) = viewAt (H d) s := sorry   -- P*
theorem seal_never_ledgers_a_writable_day (z s suf t s' led)
    (h : seal z s suf t = .ok (s', led)) :
    (∀ b, s'.machine.block = some b → b.obs.isSome → dayOfI b.started ≥ s'.ledgerDay)
    ∧ ∀ e ∈ unfolded s' suf, ∀ d ∈ touchedDays e, d ≥ s'.ledgerDay := sorry      -- P*
theorem a_sealed_snapshot_accepts_its_own_suffix (z s suf t s' led r)
    (h : seal z s suf t = .ok (s', led))
    (hr : resume z s' (suf.drop (s'.through - s.through)) = .error r) :
    r.isGuard = false := sorry                                                  -- P*, the no-loop law (§8.4)
theorem pendingSound_of_seal (z pre s suf t s' led)
    (hs : pendingSound pre s = true) (h : seal z s suf t = .ok (s', led)) :
    pendingSound (pre ++ suf) s' = true := sorry                                -- P*, G1's remembered verdicts are the whole-log ones
theorem backing_up_ends_at_the_empty_snapshot (z es r)
    (hr : resume z Snap.empty es = .error r) : r.isGuard = false := sorry       -- P*, the rebuild's back-up terminates (§8.8)
theorem decodeSnap_encodeSnap (s : Snap) (h : snapWf s = true) : decodeSnap (encodeSnap s) = .ok s := sorry   -- P*
theorem every_log_array_is_a_page (r : JVal) (h : r = logSection …) : pagesWf r = true := sorry   -- P*, gap 44
theorem ledger_obs_are_the_replays_obs (…) :
    (led.flatMap (·.energy)) ++ openObs f = (replay z (pre ++ suf)).energy := sorry   -- P*, D9's hand-back
```

**§7.4's self-check, stated now so the build cannot quietly narrow:**

- **What makes `view` honest:**
  - `viewAt` must include every row of §7.2's table.
  - A cheat (§12) that deletes `lastDone` from `viewAt` must break
    `resume_is_replay_on_the_witness_log`.
  - The witness log exercises every one of the 25 kinds, one within-suffix undo, one retro wake
    inside the suffix, one stall, and one compaction that actually drops a record.
- **`resume_is_replay` quantifies over the snapshot after `jemit` and `jparseM`,** not the
  in-memory value (§5.9).
- **Two-run laws are proved, not property-tested** (D5). The FFI property test in §14 is evidence
  beside the proof, never instead of it.

---

## 12. `Negative.lean` cheats to add

Append at the end (AGENTS §6.2). At `c2cf4dc` plus step 1 the next free number is 75; re-check.

| # | cheat | must fail because |
|---|---|---|
| 75 | a `U8` field decoding `256` | `U8.ofNat?` rejection theorem |
| 76 | a `TzTable` with two equal span starts passes `tzWf` | `tzWf` is a strict order |
| 77 | `Dec.ofNumeral?` accepts `1e999` | the exponent bound |
| 78 | `resume` without G1 equals `replay` on `noCross_is_needed`'s witness | the refutation |
| 79 | `viewAt` without `lastDone` still satisfies `resume_is_replay_on_the_witness_log` | the view is honest |
| 80 | a page of 4,097 elements passes `pagesWf` | gap 44's bound |
| 81 | `decodeSnap` accepts `through ≠ base` | G0 |
| 82 | `compact` keeping a record below `H` changes nothing observable at `H − 1` | the window is where it says |
| 83 | a seal that folds an undo's target without recording the verdict in `pending` still satisfies `a_sealed_snapshot_accepts_its_own_suffix` on the witness | the no-loop law bites |

---

## 13. Step plan

Each step is committable green: check.sh 7/7, `cargo test --workspace`, and cli_latency. New gaps
start at 76 (re-check the README).

- **S0: measure first** (no semantics).
  - A committed probe example, `kernel/tm-kernel-ffi/examples/logprobe.rs`, plus a deterministic
    log generator (a Rust port of `design/genlog.py`/`genlog80.py`) under
    `tm/tests/support/loggen.rs`.
  - Record the wire parse rate, RSS per MiB and the 2 MiB and 8 MiB bands for arrays of strings,
    objects and pages, replacing §1.1's scratch numbers.
  - *Green:* adds only an example and a test helper.
- **S1: instants, offsets, tz tables** (`Cal.lean`, `Line.lean`).
  - `Instant`, `Offset`, `parseStamp`, `renderStamp`, `Tz`, `localOf`, `dateIn`, `instantOf`, with
    round trips, rejections and DST witnesses (a Chicago 2026-03-08 gap and a 2026-11-01 fold).
  - No wire change. Goals: the first two time goals.
- **S2: `JVal.lit` and `JMode`** (`Json.lean`, `Boundary.lean` arms).
  - Re-prove `jparse_jemit` as `jparseM_log_jemit` plus `jparseM_wire_never_yields_a_lit`, and
    keep `jparse_refuses_what_the_fragment_has_no_type_for` for `.wire`.
  - Update `the_response_call_emits_parses_back` if its statement names `jparse`.
  - *Green:* the wire is byte-identical, and FFI tests unchanged.
- **S3: `Log.lean`**, the event grammar and `readLine` with its warnings.
  - `decide` witnesses per kind, on short literals only (§5.10a).
  - FFI differential: for every line of the four corpus logs and `malformed.jsonl`, plus crafted
    edge lines (duplicate key, `-0`, `3.0` as `u8`, fractional seconds, `:60`, lowercase `t`/`z`,
    no seconds), compare the kernel's verdict (entry or warning class) with `Log::parse_bytes` at
    the fork point.
  - Record P13 and P14's outcomes.
- **S4: `undoMask`, `wakeIndex`, `dayOf`, `boundsOf`** (`Replay.lean`, part 1).
  - Laws: `undoMask_append_of_noCross`, the refutation witness, and the day goals.
- **S5: the machine and the facts, full replay from empty** (`Replay.lean`, part 2).
  - Wire: `log` with `snap: null` and `seal: null`, and the `want` profiles.
  - FFI differential against fork-point `replay` over the corpus logs and the generator's 1-month
    log. Host still on Rust replay. First check `--json` for `Replay` (§7.2's last row).
- **S6: snapshot, seal, guards, compaction, ledger.**
  - `resume_is_replay`, `chunked_rebuild_is_one_replay`, `compact_*`, `decodeSnap_encodeSnap`,
    `every_log_array_is_a_page`, `a_sealed_snapshot_accepts_its_own_suffix`, `pendingSound_of_seal`,
    `seal_never_ledgers_a_writable_day`, `backing_up_ends_at_the_empty_snapshot`.
  - FFI property test: for random seal days and chunkings over the 1-year generated log, the
    snapshot path's view equals the whole path's.
- **S6b: the tree-map fast twin.** `Std.TreeMap` (present in the v4.33.1 toolchain with
  `Std/Data/TreeMap/Lemmas.lean`) behind `@[csimp]`, proved equal to the list spec, following the
  stage-4 hardening pattern for `planWf`. **Required** if S0's harness measures a 3-year rebuild
  above 1.5 s on lists.
- **S7: the host.**
  - `ReplayFacts`, `replay_call`, `.tm/replay.json` and `.tm/replay-days.jsonl`, the seal policy,
    the rebuild loop, `tz_table`, `TM_KERNEL_ID`, and `UndoEntry.log_line`.
  - `Ctx` switches to kernel facts; recur and review take their two logic changes.
  - The new cli_latency test (§14, A1) lands in this commit.
  - Behaviour rows P7 to P14 recorded in the README.
- **S8: observations and history readers.** `tm model` and the reviews read the ledger;
  `fit_replay` and `arrivals_from_replay` deleted; `lounge_rate`'s old-week scan.
- **S9: the raw readers.** `since_break_min`, `idle_min_since`, `idle`, `idle_since`, `tm log`
  (`want.entries` plus ledger wakes), `undo.rs` onto kernel facts, and `tm check`'s stall notice.
  After S9, `grep -rn 'Log::parse\|\.replay(' tm/src` returns nothing.
- **S10: handover.** README block, gap entries, AGENTS §8.3's trap closed ("the log has nowhere to
  live"), the D1 and D2 statements handed to the recurrence step, and the §5.13 30-minute drive:
  - a real three-year log;
  - a hand-appended deep undo;
  - a hand edit to an old line;
  - a plan directory copied to another machine with a different `cfg.tz`.

---

## 14. Acceptance tests

**A1, latency, the gate.** `tm/tests/cli_latency.rs` gains
`a_verb_on_a_tree_with_three_years_of_log_takes_well_under_a_second`. It uses the existing
`history_tree()` plus a generated 3-year log at 61 events/day (~66,000 lines, ~6.9 MiB), written
before timing starts. The existing test is left untouched.

| verb | bound |
|---|---|
| first verb: rebuild, automatic close, drop | < 5 s |
| a later verb | < 1 s |
| `--now` + 1 day: a seal | < 1 s |
| after hand-appending an `undo` whose target is 30 days old: rebuild and answer | < 5 s |

The test also asserts:

- `replay.json`'s `through` advanced;
- the ledger has one line per sealed day;
- the deep undo's effect is visible (the target item is no longer done);
- the verb after the deep-undo rebuild does not rebuild again (no refusal loop), and neither does
  the verb after a routine logged for an instance three days old.

**A2, parity:** the kernel's view equals the fork point's `replay` over the corpus logs and the
generated 1-month and 1-year logs, except P1 to P14.

**A3, windowing:** the snapshot path equals the whole path over random seals and chunkings (S6's
property test), plus **the same verb run twice**, once with the sidecars deleted, gives
byte-identical `--json` output.

**A4, gap 44:** the rebuild of an 80,000-line generated log runs on a **2 MiB** test thread without
overflow, which only paging makes possible.

**A5, tolerance:**

- a torn last line gives one warning, and the command succeeds;
- an invalid UTF-8 line gives one `invalidUtf8` warning, and the command succeeds (P8);
- a malformed line inside the recorded range leaves `tm undo` cancelling the right events (P12).

**A6, integrity and recovery:**

- a hand edit to a sealed line is reflected after the next seal;
- a truncated log leads to a rebuild;
- a crash simulated between the ledger append and the snapshot write recovers;
- two concurrent `tm` processes (one sealing) both answer correctly.

**A7, time zones:**

- a UTC-written wake lands on the Chicago date (`day_index_wake_to_wake`'s cases);
- a DST-gap midnight;
- `tzOutOfRange` leads the host to widen and retry;
- a `cfg.tz` change leads to a rebuild, because the zone name is part of `replay.json`'s key.

**A8, the writer seam:** every `Event` variant the CLI can write, serialised by
`LogEntry::to_json`, reads back through `want.entries` to the same name, primary id, `t` and
field values.

---

## 15. Parity exceptions this design adds

Continues the stage-5 list after P6.

| # | site | kernel | fork point | why |
|---|---|---|---|---|
| P7 | lines over 65,536 chars, string fields over 4,096, lists over 256 | named warning | accepted | R10 widths |
| P8 | a line that is not UTF-8 | warning on that line | the CLI fails the whole command (`read_to_string`) | G9, and `Log::parse_bytes`' own rule |
| P9 | `hsw` with more than 2^53 in its mantissa or scale > 22 | exact pair; Rust's f64 division may differ from serde's parse by an ulp | serde f64 | only hand-written values |
| P10 | warning text | named reason | serde's error message | named diagnostics (AGENTS §5.7) |
| P11 | facts no consumer reads (§7.2's last row) | not emitted (unless `--json` shows them) | serialised in `Replay` | latency; checked in S5 |
| P12 | `tm undo` after a malformed line | records by kernel line number | `log_len`/`new_events` disagree | inv §0 defect |
| P13 | fractional seconds beyond 9 digits, `:60` | S3 decides against chrono | chrono | to confirm |
| P14 | duplicate keys, `-0`, `3.0` in a log line | S3 decides against serde | serde | to confirm |
| P15 | a hand edit to a sealed line | effective at the next seal | effective at once | OWNER Q1 |

---

## 16. Cost, and the risks that could move it

### Cost (ESTIMATE; ranges, not points)

- **Lean definitions** ~3,700 lines:
  - instants and tz ~400;
  - `lit` and mode ~150;
  - grammar ~600;
  - mask and days ~250;
  - machine and facts ~1,000;
  - snapshot, seal, guards, compaction and ledger ~900;
  - wire ~400.
- **Lean proofs and witnesses:** at the library's measured 4.80 : 1 (AGENTS §4, D5), about 12,000
  to 18,000 lines, the snapshot laws and `Json.lean`'s re-proof dominating.
- **Rust:** ~2,000 to 3,000 lines including tests. Deletions (log.rs replay, `fit_replay`, raw
  loops) are about −1,800.
- **Time:** about 3 to 5 weeks of agent time, which is **more than the plan's 3 to 4 weeks for all
  of stage 5**. D9 alone is most of a stage.

### Risks

1. **The step's real cost.** This is the largest unknown: no kernel replay exists to measure.
   Mitigation: S0 and S5 measure early, and S6b is gated on the number.
2. **`JVal` widening re-proof** in `Json.lean` (2,641 lines) and `Boundary.lean`'s exhaustive
   matches. Mitigation: the mode keeps the wire's statements unchanged.
3. **Two grammars for one format:** Rust serde writes, and the kernel reads. Mitigation: A8, plus
   `readLine_reads_every_rendered_event` once the kernel has a renderer. **OWNER Q4.**
4. **A view that does not cover a consumer** (AGENTS §5.2: the law compiles and means less).
   Mitigation: §7.2's table as the definition, the cheat-79 pattern, and the S7 grep test per
   accessor.
5. **Stalls** (an open block for days) grow the suffix. Correct but slower; `tm check` names them.
6. **Stage 6's TUI gate (5 ms per call).** The 55 to 140 KB snapshot parse (ESTIMATE 2 to 6 ms) is
   alone near that budget. The known next move, not built here: per-id pages selected by the ids
   in the request's documents, with the kernel checking a digest of the full id set so a missing
   page is refused rather than silently absent. Recorded as a gap in S10.
7. **`TM_KERNEL_ID`** makes every kernel rebuild during development invalidate sidecars. That is
   intended, and it costs one rebuild per new binary.
8. **A plan directory synced across machines** (git, Dropbox): conflicting `replay.json` copies are
   harmless (a mismatch means a rebuild), but the ledger can conflict textually. **OWNER Q3**
   covers whether sidecars may exist at all.
9. **The host tz table is trusted.** A wrong table gives consistently wrong dates. Mitigation: A7,
   and the `nowDisagrees` cross-check on every call.
10. **Refusal loops**, where a refused line left unfolded refuses again on every call. Excluded by
    construction and by law: §8.4's fold and ledger rules, `pending`, and
    `a_sealed_snapshot_accepts_its_own_suffix`. A1's no-loop assertion is the observable check.

---

## 17. Owner questions (genuinely new)

1. **Staleness of hand edits (P15).** A hand edit to a log line that is already sealed (older than
   about a day) takes effect at the next seal (the prefix digest), not on the next command. The
   fork point re-reads the whole file on every command. The alternative, a full-prefix digest on
   every command, costs ESTIMATE 35 to 70 ms per command in debug at 3 years. Accept the seal-time
   check?
2. **Out-of-order appends (inv FLAG 3).** The fork point holds two "first wake" rules (earliest by
   instant for `DayIndex`; first in file order for `DayReplay.wake` and `slept_by_day`) and two
   "latest" rules (last in file order for instance records; latest by timestamp for `last_done`).
   This design ports all four faithfully (parity). AGENTS §5.3 calls two definitions of one concept
   the bug. Keep parity, or unify, which changes behaviour only for out-of-order appends and would
   add parity entries?
3. **Derived sidecars.** `.tm/replay.json` (the snapshot) and `.tm/replay-days.jsonl` (the ledger:
   finished days' facts and the observations the fit reads) are new user-visible files. Deleting
   them is always safe (they are rebuilt). Two parts to confirm:
   - that storing kernel-emitted observations for Rust's fit and reviews satisfies D9's "Rust keeps
     only the statistical fit" (storage, not derivation);
   - that plan directories synced between machines may carry them, or that they should be ignored
     by sync.
4. **Who writes log lines.** Under D9 the kernel is the only reader, but Rust (`LogEntry::to_json`)
   still composes every appended line, which gives two grammars for one format. Keep the Rust
   writer with the echo test (A8), which this design assumes, or widen D9 so that the kernel emits
   the lines to append?

Not questions (decided here, with reasons above):

- the tz span table (§5.1);
- names-only undo summaries (§6.2);
- the 14-day undo reach cap (§8.5);
- faithful `hsw`, R8's truncation and exact `load` (§7.1);
- R10 widths (P7);
- paging at 4,096 (§3.1).
