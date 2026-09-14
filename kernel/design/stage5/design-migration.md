# D9, migration-first: the Lean kernel replays `.tm/log.jsonl`

Design pass, read-only, 2026-09-14, against branch `rebuild-on-lean` at `c2cf4dc` plus the
uncommitted stage-5 step-1 tree (`Tree.lean` untracked). It builds on the fact base
`design/inventory.md`, cited below as **INV §n**. Rust is cited by function **name**.
Anything measured here says how it was measured. Anything estimated is marked
**ESTIMATE**. Anything that is really a new owner decision is marked **OWNER Q** and
collected in §15. The design takes none of those decisions silently.

The lens is **migration-first**. The shipped binary is green at every commit. At no
commit longer than one does the shipped binary hold two readers of the log (AGENTS §5.3).
Where the lens and another concern pull apart, the lens wins, and the trade-off is
written down where it was made.

---

## 0. The plan in one page

1. **Only one switch is atomic: which reader feeds `Replay`.** The undo mask and the
   wake-based day index sit under *every* replay fact. So the reader cannot move one fact
   at a time without two masks and two day indexes in the binary. Everything else moves
   one consumer or one fact family per commit, before the switch or after it.
2. **Before the switch** (binary untouched, one reader, which is Rust):
   - the kernel gains its prerequisites (gap 44's stack, an exact decimal in `JVal`,
     instants, a zone table), then the event grammar, then the replay, then windowing;
   - every stage is proved and compared field by field against the in-tree Rust through
     a test-only FFI op (§11 Phases 0, 1, 3, 4);
   - in parallel, the Rust consumers that read the raw log move onto one chokepoint,
     `Ctx::replay_of`, one per commit (§11 Phase 2). After that, nothing outside the
     chokepoint parses, masks or attributes a log line.
3. **The switch** (one commit, §11 Phase 5): the chokepoint's body becomes a kernel call
   plus a decoder into the *same* `Replay` struct, and the Rust reader is deleted in the
   same commit. Consumers do not change. The differential test becomes a kernel-versus-
   fork-point parity test.
4. **After the switch** (§11 Phase 6), one fact family per commit:
   - `tm model --fit` consumes kernel-returned observations;
   - each decision fact's last Rust consumer moves into a stage-5 kernel function
     (recurrence, priority, capacity), and the decoded Rust field is deleted with it.
   That is "the Rust replay deleted for decision facts".
5. **Windowing is a checkpoint** (§8): the kernel's own fold state at a cut, stored by
   Rust as an opaque file.
   - A call carries the checkpoint plus the lines after the cut, never the whole log.
   - Correctness is a proved two-run law: `resume (seal a) b = ok k → k = seal (a ++ b)`,
     plus its completeness twin.
   - The resume refuses by name whenever the suffix could change the prefix's facts: an
     undo reaching behind the cut, a wake earlier than the prefix's latest instant, or an
     event attributed to a sealed day. A refusal falls back to an older checkpoint.
6. **Measured here, and it forces windowing.** A proxy put the kernel's JSON path at
   roughly **170 to 190 ms per MiB of request, and ~95 bytes of RSS per request byte** at log scale. One
   year of log in one call is +268 ms; three years is +911 ms and 448 MB RSS. Rust's
   whole replay is 15 ms/MiB (INV §4.3). Whole-log-per-call is therefore not
   latency-green past a few months, and the switch must ship with the checkpoint (§2).

---

## 1. Constraints, and how each one binds this design

| constraint | source | what it forces here |
|---|---|---|
| One reader of the log in the shipped binary, never two for more than one commit | AGENTS §5.3; the brief | the reader switch is atomic (§0.1). The kernel's reader may exist *in the repository* before the switch, as library code that only tests call (the same status `Tree.lean`'s `remainingMin` has at step 1); it is not a reader of the user's log until the switch. **This is the reading of §5.3 the whole plan rests on, stated so it can be objected to** |
| Green at every commit, latency included | brief; `tm/tests/cli_latency.rs` | a log-bearing latency test lands *before* the switch, against the Rust reader (§11 R2.13), so the switch is measured, not assumed |
| D5: two-run laws are proved, never downgraded | AGENTS §4 | the windowing law is a theorem (§8.6); a step whose law will not close is not done (§14 R4) |
| D6: parents derived | AGENTS §4 | no interaction; replay reads ids as strings, not the tree |
| R9: only `String` crosses the FFI | AGENTS §3 | the log travels inside the request's JSON as strings; the checkpoint comes back as JSON the host stores verbatim |
| R10: every bounded type has a smart constructor and a rejection theorem; every integer crossing has a stated width | AGENTS §3 | §4.3's field-type table; `Min32 := Fin 2^32`, `U8 := Fin 256` to match serde's accepted range exactly; line length, nesting depth and lines-per-call are bounded refusals |
| `JVal` has `Nat` numerals only | `Json.lean` `JVal`, `jparse_refuses_what_the_fragment_has_no_type_for` | the log carries `hsw` (`0.95`, `-0.5`) and arbitrary numbers in unknown events, so the kernel must read decimals: `JVal` is widened *visibly* (§4.2), the route AGENTS §8.3 names as the sanctioned one |
| Gap 44: `jarr`/`jtail`/`jobj`/`jotail`/`jemitTail`/`jemitOTail`/`splitDoc` overflow a 2 MiB stack at ~21,500 elements | README gap 44; INV §4.4 | fixed first (§11 S0.1); a genesis replay of a year of log is a 15k-to-30k-element array |
| The statistical layer stays Rust | AGENTS §4; plan §3.6 | the kernel emits observations (energy, duration, arrival) as exact data; `energy::fit`, `compare`, `calibration`, `Posterior`, `EnergyObs::weight`, `DurationObs::ratio` stay Rust |
| File I/O and G9 stay Rust | PLAN §4 G9 | Rust reads bytes, splits on `\n`, decides "this line is not UTF-8", repairs a torn last line before appending, and stores checkpoints atomically; the kernel owns everything about a line's *content* (§4.5) |
| `decide` has a budget; memory is not heartbeats | AGENTS §5.10, §5.10a | grammar and replay witnesses stay small `List Char` literals; realistic sizes are instances of round-trip theorems; every probe runs under `systemd-run … MemoryMax=8G` first |
| No `Float`, no `Rat` | AGENTS §4 | `load` is a numerator over 5; `hsw` is an exact lexical decimal; nothing in the replay divides |

---

## 2. What was measured in this pass, and what it decides

### 2.1 A proxy for the kernel's cost per request byte

**How it was measured.**
- **Binary:** `design/tm-bin`, a copy of the debug-profile stage-4 final-repair binary (INV §4.3).
- **Tree:** `tm init --example`, swept once with `tm now`.
- **Load:** every line of a synthetic log appended to `backlog.md` *as prose*, since a line
  starting with `{` is not an item. The log's exact characters therefore travel through
  `jparse` inside `docs[].lines`, and then through `splitDoc`, the prose scan and the fast
  check.
- **Verb:** `tm --now 2026-09-14T09:00:00-05:00 drop ^a1`.
- **Timing:** best of 3, a fresh copy each run, under `systemd-run --user --scope -p MemoryMax=16G`.
- **Script:** `design/d9mig/bench/run.sh`.

| appended lines (bytes) | wall | max RSS |
|---:|---:|---:|
| 0 | 10.7 ms | 19 MB |
| 1,191 (124 KB, 1 month @40/day) | 21.6 ms | 30 MB |
| 7,422 (772 KB, 6 months) | 80.7 ms | 91 MB |
| 14,941 (1.56 MB, 1 year) | 268 ms | 165 MB |
| 45,172 (4.70 MB, 3 years) | 911 ms | 448 MB |

**What this proxy is not.** It includes `loadPlan`'s work on those lines and whatever
housekeeping kernel call `drop` makes on a swept tree; the two were not separated. It is
an **upper bound on `jparse` alone**, but a fair **lower bound** on "parse a line, then do
something with it", which is what replay does. AGENTS §5.11 applies: the committed harness
(§11 S0.4) re-measures on the real log op before any number is quoted in the README.

**What it decides.**
- At 1 year, one whole-log call already costs a quarter-second before any replay work, and
  at 3 years close to a second and half a gigabyte.
- A windowed call carries a checkpoint of about 300 to 400 KB at 3 years (ESTIMATE, §2.2)
  plus at most 1,024 lines (~110 KB). At the proxy rate that is roughly 60 to 100 ms: under
  the 1 s bound, but not free. §8.9 lists the levers if S4.4's measurement comes in worse.
- The per-call memory of a genesis (no-checkpoint) replay must be bounded by chunking
  (§8.7), not by the log's age.

### 2.2 The size of what a checkpoint must carry

**How it was measured.** `design/d9mig/size.py` runs over the synthetic logs (INV §4.2).
- Days are the calendar date of `t`. The generator writes one wake per day, so wake-based
  attribution agrees.
- The undo mask is ignored (it is 0.3% of lines).
- Byte counts use compact JSON with the per-record sizes stated in the script, so they are
  **ESTIMATE**s.

| all-history aggregate | 1 y @40 | 3 y @40 | 3 y @61 |
|---|---:|---:|---:|
| distinct `(tag, primary id)` keys (the undo reach index, §8.3) | 3,699 (~64 KB) | 6,207 (~108 KB) | 6,153 |
| `done_dates` entries | 1,929 (~30 KB) | 5,849 (~82 KB) | 5,799 |
| routine `instances` | 977 (~59 KB) | 2,979 (~179 KB) | 2,966 |
| `demotions` | 504 (~45 KB) | 1,561 (~140 KB) | 1,549 |
| items with minutes / done | 796 (~58 KB) | 898 (~71 KB) | 899 |
| energy observations / duration observations | 2,604 / 1,789 | 7,872 / 5,326 | 7,793 / 5,297 |
| **total, if everything all-history rode in the checkpoint** | ~265 KiB | ~617 KiB | ~613 KiB |

**What it decides.**
- **Observations, demotions and old day records do not ride in the checkpoint.** They are
  per-day records, and once their day is sealed they never change, so they go to Rust-side
  sealed storage (§8.5).
- **What stays in the checkpoint** is what a decision reads across all history:
  - `done_items`, `last_done`, `done_dates`, item totals;
  - `instances`, `events`;
  - the reach index, the kept wakes that still matter, and the live window.
- Its size grows with the **number of distinct ids and routine instances**, not with the
  number of events. Keys went from 3.7k at 1 year to 6.2k at 3 years.

---

## 3. The end state, in one picture

```
 Rust (tm)                                              Lean kernel (TmKernel)
 ────────────────────────────────────────────           ─────────────────────────────────────────
 read .tm/log.jsonl bytes (G9)                          Json.jparse (gap 44 fixed, JDec added)
 split on '\n'; non-UTF-8 line → null                   Stamp: RFC 3339 → Instant × Offset
 load .tm/cache/replay/ckpt (fingerprint ok?)  ──req──▶ Log.parseLine: 26 kinds + unknown,
 tz table (chrono-tz probe, cached)                       named warnings, bounds
 lines[cut..n], reseal{keep:512}                        Replay.undoMask → Replay.dayIndex
                                                        Replay.walk (effect lists) → facts
                                                        Seal.resume / Seal.reseal (guards)
 decode facts → tm_core::log::Replay (same struct) ◀─resp─ {facts, warnings, headers, view,
 write sealed/YYYY-MM.json, then ckpt (rename)             reseal:{ckpt', sealed span+bundles}}
 energy::fit(observations)  — statistics only
 review.rs, recur/priority (until stage-5 moves them), TUI: read Replay
```

---
## 4. The typed event grammar

### 4.1 Where it lives

There are four new modules. `kernel/TmKernel/TmKernel.lean` gains one import line for each,
in dependency order (AGENTS §8.3 warns this is the easiest thing in the stage to lose):

| module | imports | holds |
|---|---|---|
| `Stamp.lean` | `Cal`, `Json` | `Instant`, `Offset`, `Stamp`, the RFC 3339 reader and renderer, `TzTable`, `localDate` |
| `Log.lean` | `Stamp` | `Ev`, `Entry`, `LWarn`, `Verdict`, `parseLine`, `renderLine`, `tagOf`, `primaryId` |
| `Replay.lean` | `Log`, `Arith` | `undoMask`, `keptWakes`, `dayOf`, `Effect`, `State`, `walk`, `Facts`, observations |
| `Seal.lean` | `Replay` | `Ckpt`, `seal`, `sealed`, `resume`, `sealRule`, the checkpoint and bundle codecs |

`Boundary.lean` imports `Seal` and gains the request's `log` section (§9). Nothing in
`Plan.lean` changes. **The log does not live in `PlanCore`.** It lives in the request.
Kernel decision functions take `Replay.Facts` as a plain argument, which is stage 5 step 1's
type rule (c). That answers AGENTS §8.3's trap "the log has nowhere to live". It also makes
`Goals.lean`'s stale header sentence about `PlanCore.log` (INV §7 item 7) removable at S1.2.

### 4.2 `JVal` learns exact decimals (a visible widening)

The log carries non-`Nat` numbers: `hsw` (`0.95`, `-0.5`) in known events, and anything at
all in unknown ones. There are three ways to read them.

- **Rust re-encodes the numbers.** Rejected: Rust would then be reading each line's JSON
  and deciding which lines are malformed. That is a second reader.
- **A second, log-only JSON parser.** Rejected: two definitions of JSON (§5.3).
- **Widen `JVal`,** the route AGENTS §8.3 names. **Chosen.**

```lean
structure JDecRaw where
  neg  : Bool                      -- a leading '-'
  int  : Nat                       -- the integer digits' value
  frac : List Char                 -- the fraction digits exactly as written ([] = no '.')
  exp  : Option (Bool × Nat)       -- 'e'/'E', negative?, the exponent digits' value
def JDecRaw.plain (d : JDecRaw) : Bool := !d.neg && d.frac.isEmpty && d.exp.isNone
def JDecRaw.wf (d : JDecRaw) : Bool := !d.plain && d.frac.all isDigit   -- frac ≠ [] when '.' was read
abbrev JDec := { d : JDecRaw // d.wf = true }
inductive JVal | null | bool (b : Bool) | num (n : Nat) | dec (d : JDec) | str (s : List Char)
               | arr (xs : List JVal) | obj (kvs : List (List Char × JVal))
```

**The rule.**
- `jparse` returns `.num n` exactly when the numeral has no sign, no fraction and no
  exponent. So every existing request reader, which matches `.num`, is unchanged.
- Anything else is `.dec`.
- `jemit (.dec d)` writes `-`, the digits, `.frac` and `e-digits` as present. It is never
  plain, which is why `wf` excludes plain.

**What stays proved, and what is new.**
- **`jparse_jemit` stays unconditional.** It is re-proved with one new case.
- **The exponent is never evaluated anywhere.** The kernel stores `hsw` and passes it back.
  No `10^e` is computed, so a line like `1e999999999` costs its characters and nothing more.
  That makes it memory-safe by construction (§5.10a).
- **New theorems:**
  - `jparse_reads_a_plain_numeral_as_num`
  - `jparse_reads_a_signed_decimal_as_dec`, with the witness `-0.5`
  - `a_request_number_that_is_not_a_nat_is_refused_by_its_reader`: `"blockMin":-3` gives
    `badBlockMin`, `"min":1.5` gives `Natural number expected`.
- **`jparse_refuses_what_the_fragment_has_no_type_for` is refuted as written**, then renamed
  and restated at the reader level. This follows the stage-4 pattern.
- **Behaviour row.** A request carrying `-3` changes its error text from
  `bad json: notAValue '-'` to the field reader's name. Grep shows that no FFI or CLI test
  pins the old text: `kernel.rs` pins `expectedKey`, `unterminatedObject` and the surrogate
  refusal.

**Folded into the same step, because in D9 the kernel's JSON is the log's JSON (serde's
`serde_json` read these lines before):**
- **Gap 43: leading zeros are refused**, as RFC 8259 and serde do. Today the kernel reads
  `"slept_min":007`, a line serde warns on. Behaviour row; no host sends leading zeros.
- **Gap 42: a valid surrogate pair is read** and combined into its scalar value. A lone
  surrogate is still refused. Behaviour row. It changes `a_parse_refusal_names_its_reason`'s
  third assertion into two tests: a pair is read, and a lone `\ud83d` is refused.
- If the owner would rather keep either gap, it becomes parity entry P10 or P17 (§12).

### 4.3 Instants and stamps (`Stamp.lean`)

**`Instant`.**
- It is `structure Instant where sec : Nat; ns : Nat`, with `Instant.ok := ns < 10^9`,
  `ValidInstant := {i // i.ok = true}`, and `mkInstant?` as the only constructor the reader
  uses (R10).
- `sec` counts seconds since 0001-01-01T00:00:00Z. That origin is `Cal.toDay`'s times 86,400,
  so `localDate` renders through `Cal.ofDay` with no second calendar.
- Year 9999 is about 3.2·10¹¹ seconds: a small scalar `Nat`.
- A local time whose offset would put it before the origin is refused `badT`.

**`Offset`.** It is `{west : Bool, sec : Nat}` with `sec < 86400`.
- The spellings are `Z`, `z`, `±HH:MM`, and `±HH:MM:SS` in the zone table only.
- `-00:00` is UTC.

**`Stamp`.** It is `{at : ValidInstant, off : ValidOffset}`. The written offset is kept only
so the stamp can be rendered back (`tm log`, `DateTime<FixedOffset>` in decoded facts). Every
comparison reads `at`.

**`parseStamp` accepts exactly what fork-point `parse_timestamp` accepts:**
- RFC 3339 through `DateTime::parse_from_rfc3339`: seconds, optional fraction, and `Z` or an
  offset;
- the fallback `%Y-%m-%dT%H:%M%:z` with no seconds.
- The precise edges must be pinned against chrono by **T3** (§12) *before* the grammar is
  frozen, not guessed: the accepted separators (`T`, `t`, space?), fractions longer than
  9 digits (truncated to nanoseconds?), second `60`, year `0000`.

**`renderStamp` is fork-point `fmt_timestamp`:** whole seconds, `±HH:MM`, and `+00:00` for a
zero offset.

**`minutesBetween a b : Nat`.**
- It is chrono's `num_minutes` of `b − a`, truncated, and 0 when `b < a`. That is the
  `.max(0)` in `Machine::close_sub`.
- It is computed over total nanoseconds, all `Nat`.
- `subMinutes t m` (for an idle start `t − min`) saturates at the origin. That is unreachable
  from a real log, and recorded.

**Laws.**
- `parseStamp_renderStamp`, for whole-second stamps.
- `renderStamp_is_fmt_timestamp`: witnesses `2026-09-07T06:05:00-05:00` and a UTC stamp.
- `stamp_order_is_the_instant_order`: `2026-09-08T03:00:00+00:00` and
  `2026-09-07T22:00:00-05:00` compare equal.
- `minutesBetween_truncates`: 119 s gives 1.

### 4.4 The line, and who is the tolerance authority

**Rust (I/O, G9)** does four things to the file:
- reads its bytes;
- splits them on `\n`;
- drops exactly one trailing empty segment when the file ends in `\n` (the documents'
  convention);
- sends each segment as a JSON string when it is valid UTF-8, and as `null` otherwise.

A line's physical number is its 1-based position. That is fork-point `LogWarning.line`, and
it is the only line number anything uses from here on.

**The kernel owns everything about content.** `parseLine n seg : Verdict`, with
`Verdict := blank | entry (e : Entry) | warn (line : Nat) (w : LWarn)`, runs these checks in
order:

1. `seg = none`: `invalidUtf8`.
2. Trim one trailing `\r`.
3. Blank after trimming Unicode `White_Space` (Rust's `str::trim` set, tabulated as data per
   §5.5 and cross-checked by T1): `blank`. It is skipped silently, like the fork point.
4. More than `maxLineChars = 65,536` characters: `lineTooLong`. This is a bound the fork point
   lacks (R10); parity P11.
5. Bracket nesting deeper than `maxLineDepth = 64`, found by a cheap pre-scan: `lineTooDeep`.
   `jparse` recurses once per nesting level, and gap 44's fix does not remove that. Parity P11.
6. `jparse` fails with `e`: `notJson e`, carrying the parser's own `JErr` name.
7. Not an object: `notAnObject`.
8. `t` missing: `noT`. Not a string, or not a stamp: `badT`.
9. `ev` missing: `noEv`. Not a string: `evNotString`.
10. `ev` is one of the 26 known tags: the fields are decoded **strictly** through `jget`.
    - A required field that is missing gives `missingField k`.
    - A wrong type, an out-of-range integer, or `null` in a non-`Option` field gives
      `badField k`.
    - `null` in an `Option` field is absent. An absent `def` field takes its default.
    - Extra keys are ignored.
    - A key the grammar reads that appears twice gives `duplicateKey k`. What serde does with
      a repeated key is pinned by T1 before the step lands.
11. Any other `ev`: `entry (unknown tag rest)`, where `rest` is every other pair sorted by key.
    That is serde's `Map` order, so the renderer matches.

Warnings are data, each with its line and name. Where the CLI surfaces `Log.warnings` today,
it surfaces these names after the switch. `grep -rn warnings tm/src` at R2.8 finds the site.

### 4.5 Every kind, with the kernel's field types

The column order is the fork point's `define_events!` declaration order, which is the
renderer's key order. Fork-point types are serde's (INV §0.2, §1). The kernel types are:
- `U8 := Fin 256` and `U32 := Fin 4294967296`, exactly serde's accepted ranges and not the
  semantic 0..5 (no range check exists in `log.rs`; the only clamp is `ci.min(5)` inside
  credit);
- `Str := List Char`, bounded by the line bound, with `lineTooLong_bounds_every_string` as its
  R10 statement;
- `Num := num Nat | dec JDec`, a JSON number held lexically.

| `ev` | fields (kernel types; `?` = `Option`, `=d` = default when absent) | `primaryId` |
|---|---|---|
| `wake` | `slept_min : U32`, `onset_min : U32?` | — |
| `arrive` | `loc : Str`, `window : Str × Str` (a 2-array of strings, `badField window` otherwise; not validated as `HH:MM`, as the fork point), `budget : U32` | — |
| `start` | `id : Str`, `pred : U8`, `rep : U8?`, `hsw : Num =0`, `slept_min : U32 =0`, `loc : Str`, `blocks_done : U32 =0`, `since_break_min : U32 =0` | `id` |
| `done` | `id : Str`, `est_min : U32`, `actual_min : U32`, `went : U8?`, `tags : List Str =[]`, `ci : U8`, `partial : Bool =false` | `id` |
| `extend` | `id : Str`, `by_min : U32` | `id` |
| `stop` | `id : Str`, `remaining_min : U32` | `id` |
| `break` | `planned_min : U32`, `actual_min : U32?`, `where : Str?` | — |
| `energy` | `pred : U8`, `rep : U8`, `hsw : Num =0`, `loc : Str` | — |
| `interrupt` | `id : Str?` | `id` if set |
| `resume` | `lost_min : U32`, `dropped : List Str =[]` | — |
| `pause` / `unpause` | `id : Str` | `id` |
| `idle` | `attributed : Str` (not validated), `min : U32` | — |
| `routine` | `item : Str`, `inst : Str`, `status : Str` (parsed at replay), `actual_min : U32?` | `item` |
| `skip` | `item : Str`, `inst : Str` | `item` |
| `plan` | `hash : Str`, `replans_today : U32`, `drift_min : U32` | — |
| `event` | `name : Str`, `id : Str?` | `id` if set |
| `demote` | `id : Str`, `from : Str`, `to : Str`, `est_min : U32` | `id` |
| `readopt` / `drop` | `id : Str` | `id` |
| `move` | `id : Str`, `from : Str`, `to : Str` | `id` |
| `edit` | `id : Str`, `field : Str`, `from : Str`, `to : Str` | `id` |
| `note` | `text : Str` | — |
| `loc` | `loc : Str` | — |
| `close` | `period : Str`, `key : Str` | — |
| `undo` | `of : Str`, `id : Str?` | `id` if set |
| any other tag | `rest : List (Str × JVal)`, sorted | `rest["id"]` when it is a string |

**The canonical renderer.**
- `renderLine : Entry → List Char` renders `{"t":…,"ev":…,<fields>}`, following serde's
  attributes: `skip_serializing_if` on `partial`, `None` as `null` or omitted exactly as
  `define_events!` says.
- **T2 pins byte identity against the Rust writer.** Serde renders the `hsw` `f64` with ryu;
  the kernel renders the lexical `Num`. They agree on every value the writer produces, because
  the kernel only ever re-emits what it read.
- Its first uses are `tm log --json` and the round-trip law. Its possible third use is the
  writer (OWNER Q4).

**Laws (S1.2).**
- `the_log_reads_what_it_renders`: `e.canonical = true → parseLine e.line (some (renderLine e)) = .entry e`.
  Here `canonical` means a whole-second stamp, sorted distinct `rest` keys, and in-bound
  strings.
- **Both directions (§5.8).** Each is a `decide` over one short literal line from
  `tests/fixtures/logs/malformed.jsonl`, and every one is ≤ 90 characters, per §5.10a:
  - `a_known_event_missing_a_field_is_a_warning` (`wake` without `slept_min`);
  - `a_known_event_with_a_wrong_type_is_a_warning` (`est_min:"sixty"`), paired with
    `a_known_event_is_never_read_as_unknown`;
  - `an_unknown_tag_is_never_a_warning` (`{"ev":"mood","level":3}`);
  - `an_extra_key_on_a_known_event_is_ignored`;
  - `ev_seven_is_evNotString`;
  - `a_top_level_array_is_notAnObject`.
- **The corpus.** `the_malformed_corpus_reads_as_the_fork_point_did` gives all 11 verdicts,
  proved per line, not over the file.
- **Probe first.** Every witness runs under `systemd-run … MemoryMax=8G timeout 120` in a
  scratch file before it is committed.

---

## 5. Timezone and day attribution

### 5.1 What has to be reproduced

`DayIndex` computes every calendar date by converting the instant into the IANA zone
`cfg.tz`, DST included. An entry's own offset fixes only the instant. The test
`day_index_wake_to_wake` pins "UTC-written entries are attributed in the configured zone"
(INV §2.3). The offsets in the file are the writing machine's `Local` offset (INV §0), so
they are not `cfg.tz`'s.

### 5.2 The options

| option | kernel reads | behaviour | verdict |
|---|---|---|---|
| A. Host sends a local date per event | dates | exact | **rejected**: Rust would parse every `t`, a second reader of the timestamp grammar (§5.3), and the request grows per event |
| **B. Host sends the zone as an offset table** (UTC transition instants and offsets) | table + stamps | **exact** for every instant inside the table's span | **chosen**: the tz database stays where it is (chrono-tz) as *data*; every rule that reads the log is the kernel's |
| C. Offsets only: each event's written offset decides its date | stamps | **changes behaviour** whenever the writer's offset differs from `cfg.tz`'s: travel, `--now` with another offset, a UTC-configured machine. `day_index_wake_to_wake` fails | not needed, since B is exact; would be an owner decision |
| D. A rule table in the kernel (POSIX `TZ` string) | rule string | exact only for current rules; historical changes are lost | rejected: reimplements tzdb and is still wrong for old data |

### 5.3 The table

**Rust builds it (S1.4, `tm-core/src/tz_table.rs`).**
- chrono-tz 0.10.4 does **not** re-export `TimeSpans`. Its `lib.rs` re-exports only
  `GapInfo, OffsetComponents, OffsetName, TzOffset`. So the table is found by probing.
- **The probe:** `tz.offset_from_utc_datetime(dt).fix().local_minus_utc()` at every UTC
  midnight from 1900-01-01 to 2200-01-01. Wherever two probes differ, bisect to the second
  (≤ 17 probes). Record the offset in force at 1900 as `base`.
- **Cost:** about 110,000 probes (ESTIMATE: a few ms in release).
- **Cache:** `.tm/cache/replay/tz.json`, keyed by `(cfg.tz name, chrono_tz::IANA_TZDB_VERSION, span)`.
- A zone with two transitions inside one UTC day would be missed. T4 exists to catch that.

**Wire.**
```jsonc
"tz": {"name": "America/Chicago", "base": "-05:50:36",
       "then": [["1883-11-18T18:00:00Z", "-06:00:00"], ["1918-03-31T08:00:00Z", "-05:00:00"], …]}
```
Instants and offsets are strings, read by the kernel's own `parseStamp` and offset reader, so
there is one reader of each spelling. JSON has no negative numbers to worry about.

**Kernel.**
- `TzTable := {base : Offset, trans : List (ValidInstant × Offset)}`.
- `mkTzTable?` refuses `badTz` for: instants not strictly increasing, `|offset| ≥ 24 h`, or
  more than 4,096 transitions (R10).
- `offsetAt tz t` is the offset of the last transition `≤ t`, else `base`.
- `localDate tz t : Nat` is `(t.sec ± offset) / 86400` in `Day` numbering.
- **Out of span** it is the edge offset: exact inside [1900, 2200), possibly different from
  chrono outside (P13).
- The kernel never interprets `name`. It is part of the checkpoint's invalidation key.

**Laws (S1.3).**
- `localDate_is_constant_between_transitions`
- `offsetAt_reads_the_last_transition`, in both directions: before the first, and at
  exactly a transition.
- Witnesses on a four-entry Chicago table:
  - 2026-03-08T07:59:59Z gives 2026-03-08 at −06:00; 08:00:00Z is −05:00;
  - 2026-11-01T06:59:59Z is −05:00; 07:00:00Z is −06:00;
  - `2026-09-08T03:00:00+00:00` gives 2026-09-07.

### 5.4 The day index (S3.2, `Replay.lean`)

**Definitions.**
- `keptWakes tz ws` sorts the survivors' wake instants with core `List.mergeSort` (stable),
  then drops each wake whose `localDate` equals the previously kept one. That keeps the
  earliest wake per local date, as `DayIndex::new`'s `dedup_by` does.
- `dayOf tz kw t`: let `w` be the last kept wake `≤ t`. If it exists and `t − w < 24 h`
  strictly (in nanoseconds), the day is `localDate tz w`; otherwise it is `localDate tz t`.
- `DayIndex::bounds` and `wake_of` are **not ported unless a caller outside `log.rs` exists at
  S3.2.** `grep -rn '\.bounds(\|wake_of(' tm tm-core --include=*.rs` found none in this pass.

**Laws.**
- `dayOf_is_the_wake_date_within_a_day`
- `a_wake_day_is_shorter_than_24_hours`
- `the_earliest_wake_of_a_date_is_kept`, with `a_second_wake_on_a_date_does_not_stretch_the_day`
- `dayOf_ignores_the_written_offset` (stated on `Stamp`)
- The four cases of `day_index_wake_to_wake` as witnesses: after midnight before the next
  wake, a stale wake, no wake that date, before the first wake.

### 5.5 Two "first wake" rules, ported both

- `keptWakes` keeps the **earliest wake by instant** per date; attribution uses it.
- `DayReplay.wake`/`slept_min`/`onset_min` and `slept_by_day` keep the **first wake in file
  order** attributed to the day.
- They differ only when wakes are appended out of time order (INV §2.3, §7 item 3).

The port reproduces both, because parity is the stage's acceptance. The theorem that
separates them is `the_kept_wake_is_not_the_first_logged_wake`: two wakes on one date,
appended later-first. This is one concept with two definitions, the pattern §5.3 names.
Recorded as a gap. **OWNER Q1** asks whether to unify.

### 5.6 Time that stays in Rust

- `ctx.today` and every display conversion stay Rust: `now.with_timezone(cfg.tz)`,
  `wake.hour()`.
- `review.rs` `lounge_rate` calls `.hour()` on a `DateTime<FixedOffset>`, so it takes the
  **written** offset's hour, not `cfg.tz`'s. That is fork-point behaviour, and it stays,
  because decoded facts keep the written offset.
- **Two zone evaluators now exist:** chrono for `today` and display, the table for
  attribution. They are tied by **T4**: 10,000 random instants from 1970 to 2100 in each of
  `America/Chicago`, `Europe/Berlin`, `Asia/Kolkata` (+05:30), `Pacific/Chatham` (+12:45) and
  `Australia/Lord_Howe` (a 30-minute DST). Stage 6, which moves `now` into the kernel, removes
  the second evaluator. Recorded as a gap.

---

## 6. Undo

### 6.1 The mask, ported (S3.1)

`undoMask : List Entry → List Bool` scans in file order. Each `undo{of, id?}` cancels itself
and the **greatest earlier uncancelled non-undo** entry whose `tagOf = of` and, when `id` is
given, whose `primaryId = id`. With no such entry the undo is dangling and cancels only itself.

- `of` is compared with the tag string, so it can name any tag: `plan`, `note`, an unknown
  tag, or a verb that is no event at all.
- `isStateChange` does **not** restrict the mask.
- An undo of an undo always dangles. There is no redo.

**The spec is a structural scan.** It does not reduce well at scale: the lookback makes a
hostile log O(n²). **The runtime is a `@[csimp]` fast twin** with per-tag and per-`(tag,id)`
stacks of uncancelled positions, and lazy deletion for id-less undos. The equality theorem
beside it follows the `parentRef_eq_parentRefFast` pattern (AGENTS §5.3, stage 4 final
step 3). Proofs live on the spec.

**Laws.**
- `undoMask_length`
- `undoMask_cancels_every_undo`
- `undoMask_cancels_the_latest_match` (the characterisation of a target)
- `an_undo_of_an_undo_dangles`
- `undoMask_pairs`: `count cancelled − dangling = 2 · pairs`
- Witness: `undo_mask_pairs_and_dangling`'s exact `[T,T,T,T,T,F,T]`, dangling `[4,6]`.

### 6.2 The law `tm undo` rests on (S3.7)

`move_has_no_inverse_command` proved that no inverse command exists, so `tm undo` must replay
(INV §2.2). The constructive twin, stated over what the CLI appends:

```lean
def undosFor (E : List Entry) : List Ev :=
  E.reverse.map fun e => .undo (tagOf e.ev) (primaryId e.ev)

theorem undoing_the_last_command_replays_the_log_without_it
    (tz : TzTable) (L E : List Entry)
    (hE : E.all (fun e => !e.ev.isUndo) = true)
    (hl : linesIncreasing (L ++ E ++ stampAfter E (undosFor E)) = true) :
    eraseLines (facts tz (L ++ E ++ stampAfter E (undosFor E))) = eraseLines (facts tz L)
```

**Why it holds.** The undos are taken most recent first. Each finds its own event, because
every later event of `E` is already cancelled and nothing follows. The surviving wakes are
`L`'s, so the day index is too, and the walk sees exactly `L`'s survivors. `eraseLines` drops
the source-line tags the facts carry for ordering, which renumbering changes.

**Its refutation twin**, for the case the CLI actually produces (§6.3), is
`undo_of_a_silent_verb_cancels_an_older_event`. With `L = [move{id:"a"}]` and `E = []`, the CLI
appends `undo{of:"move"}`, which cancels `L`'s `move`.

### 6.3 A latent defect the law exposes (reported, not fixed)

When the undone command appended no event, `undo.rs` `undo` appends `undo{of: entry.verb, id: None}`.
Several verbs are recorded under an **event's tag** yet can append nothing:
- **`tm move` and `tm readopt` on a line without an id.** The "Old path" branches in `items.rs`
  record `"move"` or `"readopt"`, call `horizon::move_item` or `horizon::readopt`, and append
  no event.
- **`tm close` whose run closed nothing but changed files or `state.json`.** `lifecycle.rs`
  `close` records `"close"`; `closing.rs` appends `Event::Close` only per closed period.

Undoing such a command cancels the most recent **older** event of that tag, which a different
command wrote.
- **No replay fact a consumer reads changes today:** `move` and `readopt` feed nothing, and
  `close` feeds only the unread `closes`.
- **`tm log` does change:** it hides the older event.
- **OWNER Q2:** write a tag no event can carry for a silent verb (for example
  `of:"verb:move"`), which changes the bytes written to the log. Or keep this and record it.

### 6.4 What `undo.rs` gets

- **`Recorder::start` counts physical lines.** It uses the same byte split the request uses
  (§4.4), replacing `log_len`'s `lines().filter(non-blank)`. A malformed line then no longer
  offsets which events get recorded (INV §0: `log_len` counts it, `new_events` skips it).
  Behaviour row B4 / parity P15.
- **`Recorder::finish` asks the kernel for headers.** A `log` call with
  `want.headersFrom = start + 1` (§9) returns `{line, ev, id?}` per entry. `tagOf` and
  `primaryId` are the same functions the mask applies, so an undo `tm undo` writes is matched
  by construction. That makes "primary id" one definition.
- **`undo` itself does not change.** It appends the undos (the writer), restores file bytes
  and `state.json`, runs the §1.3 conflict guard, and reloads.
  - The reload is a checkpointed replay. If an undone event lies behind the cut, the kernel
    refuses `reach` and Rust falls back (§8.7).
  - **An undo never deletes or restores a checkpoint.** The log is append-only, so every
    stored checkpoint stays a checkpoint of a prefix of the log.
  - `Log::undo_target` and `Log::compensating_undo` have **no callers** outside `log.rs`
    (grep, this pass). They are deleted at the switch and not ported.

---
## 7. The replay machine

### 7.1 Shape: a step computes effects, and effects are applied

```lean
inductive Effect
  | dayAdd    (d : Nat) (f : DayDelta)            -- a per-day sum or record (DayReplay's fields)
  | itemAdd   (i : Str) (f : ItemDelta)           -- all-history item totals (minutes, blocks)
  | itemDay   (i : Str) (d : Nat) (m : Nat)       -- minutes of item i on day d, added
  | itemDaySub (i : Str) (d : Nat) (m : Nat)      -- the stop-then-done uncredit, saturating
  | global    (g : GlobalDelta)                   -- done sets, last_done, done_dates, instances, events
  | obs       (o : Obs)                           -- an energy or duration observation, with day and line
  | machine   (m : Machine)                       -- the new block / lastCut / interrupt
def effects (tz : TzTable) (kw : List ValidInstant) (st : State) (e : Entry) : List Effect
def step tz kw st e := applyEffects st (effects tz kw st e)
def walk tz kw (st : State) (es : List Entry) : State := es.foldl (step tz kw) st
```

Fork-point `Machine::day_mut`, `item_mut`, `segment` and `credit` each map onto one `Effect`
constructor. **Why this shape.** The windowing partition (§8.6 law 3) needs "a step touches
only the days its effects name". With effects as data, that is one generic theorem,
`applyEffects_only_touches_named_days`, not twenty-six per-arm lemmas. It is mandated from S3.3
so that Phase 4 does not refactor a proved machine.

### 7.2 State

The state is fork-point `Machine`:
- `block : Option Block` with `id`, `started`, `since?`, `paused`, `pausedAt?`, `workedMin`,
  and `obs?`. `obs` holds the pending start observation **itself**, not an index into a
  vector, so a later `done` writing `went` patches machine state, not an emitted record.
- `lastCut : Option {id, t, min}`.
- `interrupt : Option {t, id?}`.

The output aggregates are carried alongside (§7.4).

### 7.3 The event rules

They are INV §2.4's table, transcribed. Rules a builder is likely to "fix", and must not
(each gets a witness):

1. `start` cuts any open block, including one with the same id, and then sets
   `lastCut := none`. So a block cut by the next `start` is never replaced by a later `done`.
2. A matched `done` discards the clock minutes; `actual_min` is authoritative.
   - An unmatched `done` with `actual_min > 0`, no open block, and `lastCut.id = id` uncredits
     the cut.
   - Then the credit is always applied.
3. `credit`'s day is the **closing** event's `dayOf`.
   - `minutes_by_day[day]` gains its key even at 0 minutes (the snapshot shows it).
   - `ci` is clamped `min 5`.
   - `ci = none` with `min > 0` goes to `ci_unknown`.
4. `close_sub` credits whole minutes, **truncated per sub-segment** (R8, §7.6).
5. `close_pause` does not clear `paused`.
6. A `resume` record's day is `dayOf` of the interruption's start, else of `t`.
7. An idle segment's day is `dayOf (t − min)`. The day's `longest_leak` is replaced only by a
   strictly larger `min`, so the first maximum wins.
8. `routine` with a status outside `done|pending|missed|expired|skipped|skip` gives the
   warning `unknownInstanceStatus raw` (fork-point `Replay.warnings`) and is treated as
   `Pending`.
   - `instances[item][inst]` is the last record in **file order**.
   - A done date is `inst` read as a date, else the day.
9. `mark_done`'s `last_done` is the maximum **by instant**, not by file position.
   - Nothing removes from the done sets except the mask.
   - A `routine done` followed by `routine pending` leaves the item done (INV §2.4).
10. `demote`'s stamp comes from `stamp_from_key`: an ISO week key gives `Week w`, a date gives
    `Day dom`, anything else nothing. The kernel reads those keys with `Line.lean`'s existing
    week and date readers, not new ones (§5.3).
11. `finish` sorts each day's segments by start with core `List.mergeSort`. It is stable, and
    the stability theorem is cited at S3.3. It writes out `open_block`.
12. **There is no range.** The fork point's `range` argument has no CLI caller (INV §4.4
    growth law), so `in_range` is the constant `true` and is not ported. Windowing replaces it.

### 7.4 Which facts, and which not

**Ported** means every field a consumer reads in INV §3, plus the Phase-2 seam facts:

| family | facts (Rust `Replay` names) | step |
|---|---|---|
| F1 block | `ItemReplay.{minutes, blocks, minutes_by_day}`; `DayReplay.{block_min, blocks_done, minutes_by_ci, ci_unknown, load (as fifths), starts, first_start, lost_min, segments (Block, Pause, Interrupt)}`; `open_block`; duration observations; the start observation's `went` | S3.3 |
| F2 completion | `done_items`, `last_done`, `done_dates`, `instances`, `DayReplay.{done, routine_min}`, `Routine` segments | S3.4 |
| F3 day header and records | `DayReplay.{wake, slept_min, onset_min, arrival, loc, window, budget, plans, drift_min, breaks, idle, leak_min, longest_leak}`, `Break`/`Idle` segments, energy observations (with slept bound late), `events`, `demotions` | S3.5 |
| F4 seam facts (§11 Phase 2) | `DayReplay.last_t` (the latest instant attributed to the day), `Replay.last_effective_t` (the last survivor's instant in file order), `DayReplay.idle_marks` (the day's pause, interrupt, unpause, resume and break marks in file order), `entry_count`, `headers`, `view` | S3.6 |

**Not ported, because nothing reads them** (INV §3's grep):
- `ItemReplay.{stops, extended_min, done_at, partial_done_at}`;
- `Replay.{closes, dropped_items, interrupts (beyond the day's lost/dropped), open_interrupt, unknown, longest_leak (global), range}`;
- `DayReplay.{replans_today, last_plan_hash, loc_changes, dropped}`.

Phase 2's R2.11 deletes them from the Rust struct *before* the port, so the struct the kernel
fills is exactly what gets read. `Replay.warnings` is replaced by the named line warnings.
D9 says the kernel "derives every replay fact"; this reads that as every fact something reads.
**OWNER Q3.**

### 7.5 Observations: what Rust's fit gets

- **`EnergyObs`** has: `line`, `t : Stamp`, `day`, `pred : U8`, `rep : U8`, `hsw : Num`,
  `loc`, `slept : U32?`, `went : U8?`, `id?`, `fromStart`.
- **`DurationObs`** has: `line`, `t`, `day`, `id`, `ci : U8`, `tags`, `est : U32`,
  `actual : U32`, `went?`, `partial`.
- **Arrivals are not a new type.** They are `DayReplay.{date, arrival, loc}`, which the kernel
  emits anyway. Rust's `energy::arrivals_from_replay` keeps its body: converting time of day
  into `cfg.tz` is feature extraction for the fit.
- **Order.** Fork-point `replay.energy` is in file order of the producing event. Each kernel
  observation carries its source `line`, and the decoder sorts by it. Law:
  `observations_are_in_file_order`.
- **`slept` is bound late.** The fork point builds `slept_by_day` from every survivor
  **before** the walk, so an `energy` line logged before its day's `wake` still sees the
  wake. The kernel stores `day` and resolves `slept` from the final `sleptByDay` at emission.
  They are equal by construction; the law is `energy_obs_slept_is_the_days_first_logged_sleep`.
- **`hsw` is never interpreted.** It goes back lexically, so `serde_json` in Rust reads the
  same characters it would have read from the file. Same parser, same bytes: the same `f64`.

### 7.6 Arithmetic sites (added to `Arith.lean`'s header table beside R1 to R7)

- **R8, the per-sub-segment floor** (`close_sub`). Faithful to the fork point.
  - Laws: `worked_minutes_floor_each_subsegment`, and
    `worked_minutes_is_not_the_floor_of_the_block` as its refutation witness (two 90-second
    sub-segments give 2 minutes, not 3).
  - Not a D9 decision. **OWNER Q5** (optional).
- **R9, `load` is exact fifths:** `loadFifths = Σ min × min(ci,5)`, `load = loadFifths / 5` in
  Rust at display. Law: `load_is_exact_fifths`.
- **Conservation.** The fork point's invariant becomes `credit_conserves_the_day_minutes`:
  `Σ minutes_by_ci + Σ ci_unknown = block_min` per day, proved over `walk`.
- **No saturation.** Sums are `Nat`; the fork point saturates `u32`. The Rust decoder refuses
  more than `u32::MAX` by name (`minutesOverflow`). Parity P8.

---

## 8. Windowing: a proved checkpoint

### 8.1 Why a fold state and not a date range

A date range cannot be exact. Decisions read all of history:
- the `every:Nd` anchor is `done_dates.first()`;
- completion counts come from `done_dates.len()`;
- `next_ordinal` reads every instance;
- `done_minutes_map` is all-time.

A checkpoint is the machine's own state at a cut, so it is exact wherever the suffix cannot
reach back into the prefix. The guards (§8.3) decide exactly that, and refuse otherwise.

### 8.2 Definitions (`Seal.lean`)

- `replay tz L : Facts`: the whole-log reference of §7. The laws are stated against it.
- `seal tz S L : Ckpt`: the checkpoint after all of `L` with seal day `S` (§8.4 lists the
  contents).
- `sealed tz S L : Bundles`: per-day bundles for days `< S`. Each has the day's record, its
  energy and duration observations, its item-day minutes, and its demotions.
- `sealedSpan tz S S' L`: the bundles for days in `[S, S')`, with the span explicit.
- `resume tz k B reseal? : Except Refusal (Ckpt × Option (Ckpt × Bundles))` walks `B` from
  `k`'s state, under the guards. It optionally produces the next checkpoint and the newly
  sealed bundles.
- `live k : Facts`: what Rust decodes. That is `k`'s aggregates, its live day records and live
  observations, and the open block.

### 8.3 The guards

`resume` evaluates them over `B`'s survivors under `B`'s own mask. Each has a name on the wire
and a cheat in `Negative.lean`.

| guard | refuses when | why the prefix's facts could otherwise change |
|---|---|---|
| **G1 `reach {line}`** | a survivor `undo` in `B` has no target in `B`, and its key is in `k.reach` (`(tag,id)`, or the tag alone for an id-less undo) | it would cancel a prefix event. If the key is not in `reach`, it is dangling in the whole log too, and that is exact, with no refusal |
| **G2 `wakeBehindCut {line}`** | a survivor `wake` in `B` has `t ≤ k.maxT` | it could change `dayOf` of a prefix instant, or which wake a date keeps |
| **G3 `sealedDay {line, day}`** | a step over `B` names a day `< k.sealDay` in its effects, or queries `dayOf` at an instant earlier than the oldest kept wake `k` still carries | it would change a sealed bundle Rust has already stored |

Both directions of each guard get a theorem (§5.8). A refusing construction:
`an_undo_of_a_sealed_done_refuses_reach`. A near-miss that does not refuse:
`a_cancelled_retro_wake_does_not_refuse`, where `B`'s own undo cancels the wake.

### 8.4 What a checkpoint carries

| piece | why | size at 3 years, ESTIMATE (§2.2) |
|---|---|---|
| machine state: the block with its pending start observation, `lastCut`, the interruption | the fold is sequential | O(1) |
| **aggregates**: `done_items`, `last_done`, `done_dates`, item totals, `instances`, `events` | decisions read all of history | ~330 KB |
| **live** per-day records, observations, item-day minutes and demotions for days `≥ sealDay` that prefix lines contributed | the suffix may still add to those sums | up to ~37 days (§8.8) |
| kept wakes from the last one before `sealDay − 1` onward; `sleptByDay` for days `≥ sealDay` | `dayOf` for any suffix instant that is not refused; late-bound `slept` | ~40 entries |
| `reach` (`(tag,id)` keys of prefix survivors plus the tag set); `cancelledLines`; `entryCount` | G1 exactness; `tm log`'s view of old lines; `LogOut.total` | ~108 KB; O(undos) |
| `cut`, `maxT`, `sealDay`, and the zone table **trimmed** to transitions from `sealDay − 2` onward plus the one in force | line alignment; G2; G3; attribution without resending the table | O(1) |
| `v` (format version) and `buildId` (the kernel's compiled version string) | invalidation | O(1) |

**Encoding.** The checkpoint is JSON through `jemit`, kernel-private, and compact:
- days as `Day` numerals;
- instants as `[sec, ns, west, offSec]`;
- instance statuses as numerals.

`readCkpt` is a smart decoder that refuses `badCkpt <field>` (R10). Rust stores it verbatim
and never looks inside.

### 8.5 Sealed storage (Rust files holding kernel-emitted data)

**What a reseal returns.** `sealed: {from: S, to: S', days: [bundle, …]}`, covering every day
in the span that has any record. Rust **replaces** all bundles in `[S, S')`, including days
the kernel now reports as empty. It never merges, because a re-seal after a fallback may have
removed records that an undo cancelled.

**Files.**
- `.tm/cache/replay/sealed/YYYY-MM.json` holds `{"v":1,"days":{"<Day>":bundle}}`. Each month
  file is written to a temporary file and renamed.
- Then comes `.tm/cache/replay/ckpt.json`, which carries Rust's meta: the FNV-1a-64 of the
  prefix bytes, the prefix byte length, the `tz` name, `IANA_TZDB_VERSION`, and `buildId`.
- The ladder (§8.7) is `ckpt-YYYY-MM.json`.

**Who reads the sealed files.**
- `review.rs`: day, week and month reviews, and `lounge_rate`, which reads every day;
- the fit's inputs: every observation and every arrival;
- `status_line`'s last-day fallback, when that day is sealed.

They are loaded lazily, once per process (`Ctx::sealed()`), into the same record structs.
By law 1 the merge with the live facts is disjoint by day key.

**Crash safety.** Sealed files are written first and the checkpoint last. After a crash in
between, the old checkpoint's next reseal re-emits the same span and overwrites identical
bundles.

### 8.6 The laws (D5: proved)

1. `seal_facts_are_the_replay`: `merge (sealed tz S L) (live (seal tz S L)) = replay tz L`, for
   every `S`. The partition loses and duplicates nothing.
2. **Two-run.** `resume_is_replay`: `resume tz (seal tz S a) b none = .ok (k, none) → k = seal tz S (a ++ b)`.
3. **Two-run.** `resume_keeps_the_sealed_days`: `resume tz (seal tz S a) b r = .ok _ → sealed tz S (a ++ b) = sealed tz S a`.
   What Rust stored is still true.
4. `resume_ok_iff_reachFree`: `(resume tz (seal tz S a) b r).isOk ↔ reachFree tz S a b`.
   - `reachFree` is stated on the **whole list**, which is the spec side:
     - in `undoMask (a ++ b)`, no survivor undo of `b` targets a position of `a`;
     - every survivor wake of `b` is later than every instant of `a`;
     - every day `walk` names while stepping `b` from `seal tz S a` is at least `S`.
   - The `→` half is completeness: the guards never over-bite. The `←` half is soundness of
     the refusals. Those are §5.8's two directions.
5. **Two-run.** `reseal_is_seal`:
   `resume tz (seal tz S a) b (some keep) = .ok (_, some (k', bs))` implies
   `k' = seal tz S' (a ++ b.dropLast keep)`, `bs = sealedSpan tz S S' (a ++ b.dropLast keep)`
   and `S ≤ S'`, with `S' = sealRule …` (§8.8).
6. `resume_iterates`, a corollary of 2 and 5: any chain of resumes and reseals is the replay
   of the concatenation.
7. `readCkpt_emitCkpt`: `k.wf → readCkpt (emitCkpt k) = .ok k`, and
   `readBundles_emitBundles` for sealed data. Rust decodes the bundles; the kernel's emitter
   is the one definition, and T6 re-reads them through the wire.

**The proof route (for the builder).**
1. `undoMask_append`: no survivor undo of `b` reaches `a` gives
   `undoMask (a ++ b) = undoMask a ++ undoMaskFrom (reachOf a) b`. This is the hardest lemma.
   The greedy scan's invariant is "the uncancelled positions of each key form a stack".
2. `dayOf_append`: when `b`'s wakes are later than `maxT a`, `dayOf` agrees on every instant
   `≤ maxT a`, and the trimmed kept wakes agree on every instant a non-refused step of `b`
   queries.
3. `List.foldl_append` for `walk`.
4. `applyEffects_only_touches_named_days` for the partition.
5. The stability of `mergeSort` for `finish`.

No per-event case analysis is needed beyond the effects naming their days, and that holds by
construction.

### 8.7 The fallback chain (Rust, `kernel_log.rs`)

1. **The in-memory checkpoint** from this process's previous call. CLI `reload` and TUI
   reload reuse it with only the lines appended since, under the same law.
2. **The latest stored checkpoint.**
3. **The ladder:** the first checkpoint written in each of the last three months. On a
   `reach`, `wakeBehindCut` or `sealedDay` refusal, Rust retries from each older ladder entry
   in turn. It cannot know the refusing target's line, and it needs no parsing to walk back.
4. **Genesis:** `ckpt: null` with the whole table, and the lines in chunks of
   `CHUNK = 8,192`.
   - Each chunk is called with `reseal {keep: 512}`, so consecutive chunks overlap by 512
     lines.
   - A refusal inside genesis resends from the previous chunk's checkpoint with the window
     doubled. The worst case is one call spanning the refusing undo's whole reach.
   - Genesis writes `sealed/` into a temporary directory and renames it over the old one.

**Invalidation, which goes straight to genesis:**
- the prefix fingerprint differs (the file's first `cut` lines were rewritten, e.g. by a git
  merge of `log.jsonl`);
- the `tz` name or `IANA_TZDB_VERSION` changed;
- the checkpoint's `v` or `buildId` differ;
- `badCkpt`.

**The FNV-1a-64** is implemented locally in `kernel_log.rs`, 15 lines, with no new dependency
(R7). It is I/O integrity, not a reading of the log.

### 8.8 The reseal policy

**Rust's constant, not semantics.**
- `M = 512`. Rust sends `reseal {keep: M}` whenever the lines after the stored cut exceed
  `2M = 1,024`. After the first reseal every call carries 512 to 1,024 lines.
- Laws 2 to 6 hold for any cut, so `M` is a performance knob.
- 512 lines is about 12 days at 40 events a day, which covers the 50-entry undo stack in any
  realistic use.

**The kernel's rule for the new seal day** is part of law 5:
```
S' = max S (min [ first day any line at or after the new cut names
                , Monday of the ISO week of dayOf maxT
                , first day of the month of dayOf maxT
                , day of the open block's start
                , day of the open interruption's start
                , day of lastCut.t ])
```
- **The week and month terms** keep every period a stage-5 decision reads (`done_this_period`,
  `min:` floors) live inside the kernel, so no kernel decision ever needs Rust's sealed files
  back. They cost a live window of up to about 37 days of records.
- **The open-state terms** keep the machine from ever pointing into a sealed day.
- **A block left open for weeks delays sealing.** That is harmless, and recorded.

### 8.9 Levers if S4.4 measures the steady-state call too slow

Apply them in order, and re-measure after each:
1. Drop the week and month terms from `sealRule`. Stage-5 kernel functions then take the
   current period's sealed bundles as a request field.
2. Move `reach` into a side file sent only after a new `needReach` refusal, so that rare case
   takes two calls.
3. Lower `M` to 256.
4. Seal calendar-routine `instances` older than `S` into the bundles.

None of these changes a law. Each changes what a checkpoint carries, and so its proofs'
definitions.

---

## 9. The wire

### 9.1 Request

`Boundary.lean` reads it with a new `parseLogReq`; `docs` and `cmds` are exactly as today.

```jsonc
{"docs": [], "cmds": [],
 "log": {
   "tz":     null | {"name": "America/Chicago", "base": "-05:50:36", "then": [["1883-11-18T18:00:00Z", "-06:00:00"], …]},
   "ckpt":   null | { …kernel-private… },       // null = genesis, and then tz is required (tzAbsent)
   "from":   44661,                              // physical line number of lines[0]; = ckpt.cut + 1 (cutMismatch)
   "lines":  ["{\"t\":…}", null, …],             // null = not UTF-8; at most 65,536 elements (tooManyLines)
   "reseal": null | {"keep": 512},
   "want":   {"facts": true,
              "headersFrom": null | 45170,
              "view": null | {"item": null | "667", "sinceDay": null | 739000, "tail": null | 20}}
 }}
```

- A request without `log` is read exactly as today.
- A `close` or a stage-5 decision that later needs facts in the same call puts both sections
  in one request. That is not needed for D9's switch.

### 9.2 Response

Keys are in build order (`the_response_shapes_emit_in_build_order` is extended).

```jsonc
{"ok": {"docs": [], "report": {"closes": []},
  "log": {
    "lines":    45172,                                        // last physical line seen
    "warnings": [{"line": 17, "why": "missingField", "key": "slept_min"}, …],
    "facts":    null | { …§7.4 in the checkpoint's compact encoding… },
    "headers":  [{"line": 45171, "ev": "done", "id": "667"}, …],
    "view":     [{"line": 45100, "day": 739812, "cancelled": false, "entry": "<renderLine>"}, …],
    "reseal":   null | {"ckpt": {…}, "sealed": {"from": 739780, "to": 739812, "days": [ … ]}}
  }}}
```

### 9.3 Refusals

They use a new `err` shape, `{"err":{"log":{…}}}`. `kernel_bridge::refusal` maps the names;
`every_named_refusal_reaches_the_message_by_name` is extended.

| name | meaning |
|---|---|
| `reach {line}`, `wakeBehindCut {line}`, `sealedDay {line, day}` | G1 to G3: Rust falls back (§8.7) and never shows these to the user |
| `badCkpt <field>`, `cutMismatch` | the checkpoint is corrupt or stale: genesis |
| `tzAbsent`, `badTz <why>` | host defect: a loud fault |
| `tooManyLines`, `badLogReq <field>` | host defect: a loud fault |

**A line of the log never refuses the request.** It is a warning.

---
## 10. The Rust side, file by file

| file | stays Rust | deleted or moved, and when |
|---|---|---|
| `tm-core/src/log.rs` | **the writer:** `Event` (`Serialize`, `name()`), `LogEntry::{new, to_json}`, `fmt_timestamp`, `hours_since_wake` (computes `hsw` when `start`/`energy` are appended). **The decoded view:** `Replay` and its record structs, and the accessors consumers call, decoded from kernel output | **switch (P5):** `impl Deserialize for Event` with `Known`; `ts::deserialize`; `LogEntry::{parse, local, calendar_date}`; `LogWarning`; `UndoMask`, `undo_mask`; the whole `Log` (`parse`, `parse_bytes`, `read`, `append`, `append_all`, `push`, `iter`, `effective`, `undo_target`, `compensating_undo`, `day_index`, `iter_day`, `iter_range`, `iter_item`, `replay`); `local_midnight`, `DayIndex`; `Block`, `Cut`, `Machine`, `replay`, `replay_refs`; `parse_instance_status`, `stamp_from_key`; `Event::{primary_id, is_state_change}`. `parse_timestamp` goes too, unless `--now` parsing uses it (`grep` at P5). **R2.11:** the unread facts (§7.4). ESTIMATE −1,700 lines |
| `tm-core/src/store.rs` | `FsStore::read_text`, `append_text`, `LOG_PATH`; new `CACHE_REPLAY_DIR` | R2.10: before appending to `LOG_PATH`, when the file is non-empty and its last byte is not `\n`, write `\n` first (G9) |
| `tm-core/src/tz_table.rs` (new, S1.4) | `tz_table(tz, span) -> TzTableWire`: probing and bisection (§5.3) | — |
| `tm/src/cli/kernel_log.rs` (new, P5, ESTIMATE ~700 lines) | the byte split and UTF-8 test; zone table cache; checkpoint store with fingerprint, ladder and sealed files; the fallback chain; request build; response decode into `Replay`; `headers_from`; `view`; the sealed loader | — |
| `tm/src/cli/ctx.rs` | `append_event`, `append_entry` (writer); `now`, `today` | R2.8: the `log` field and `read_log` go; `log.replay(None, tz)` becomes `Ctx::replay_of` (the chokepoint). P5: its body becomes `kernel_log::replay` |
| `tm/src/cli/undo.rs` | `UndoStack`, `Recorder` (snapshot and diff), `undo` (append undos, conflict guard, restore, reload) | R2.6: `log_len` becomes the physical line count; `new_events` becomes `Replay::headers_from`. P5: `kernel_log::headers_from` |
| `tm/src/cli/day.rs` | verbs, `EnergyCtx` | R2.1: `since_break_min` reads `DayReplay.{breaks, first_start}`. R2.2: `idle_min_since` reads `DayReplay.idle_marks`. R2.3: `idle` reads `Replay.last_effective_t`. No `iter_day` or `effective` is left |
| `tm/src/cli/lifecycle.rs` | review verbs (reading `Replay`), `day_extras` | R2.5: `log` reads `Replay::view(filter)` (P5: `kernel_log::view`). S6.1: `model` calls `energy::fit_observations` |
| `tm/src/cli/planning.rs`, `tm-core/src/planner.rs` | everything that reads `Replay` | R2.7: `PlanInput.log` is deleted (`grep` finds no reader in `planner.rs`) |
| `tm/src/tui/mod.rs` | `notify` watcher (200 ms debounce), `load`, `reload` via `Ctx::load` | R2.4: `AppData.log` goes. P5: nothing more, because `data_of` reads `Ctx::replay`, and each debounced change is one checkpointed call |
| `tm/src/tui/app.rs` | every screen reading `Replay`; the review screen loads sealed bundles lazily | R2.4: `idle_since` reads `DayReplay.last_t`; `App.log` goes |
| `tm/src/tui/queue.rs`, `necessities.rs` | unchanged: `done_minutes_map`, `waiting_state` | Phase 6 moves their decision facts with the stage-5 tranches |
| `tm-core/src/review.rs` | **all of it:** the presentation arithmetic over facts (`gaps`, adherence, `wake_to_arrive_min`, `lounge_rate`, `mix_and_load`) | R2.9: `load` is read through `DayReplay::load()` over fifths. P5: reviews of sealed periods read `ctx.replay_with_sealed()` |
| `tm-core/src/energy.rs` | **the statistical layer:** `fit`, `shrunken_mean`, `observation_weight`, `compare`, `calibration`, `estimate_calibration`, `Posterior::*`, `EnergyObs::weight`, `DurationObs::ratio`, `arrivals_from_replay` | S6.1: `fit_replay` becomes `fit_observations(cfg, &Observations, today)`, with `Observations` = sealed plus live, decoded from the kernel |
| `tm-core/src/{recur,priority,capacity,horizon}.rs` | read the decoded `Replay` until Phase 6 | Phase 6: each decision fact's last Rust reader moves into a kernel function, and the field goes |
| `tm/src/cli/kernel_bridge.rs` | `apply`, `decode_report` | P5: `refusal` learns the `log` names (§9.3) |
| `tm-core/tests/*` (17 files, 27 call sites build `Replay` from a log) | their assertions | R2.12: every site calls `tests/common/replay.rs` `replay_of_text(text, tz)`. P5: that helper calls the kernel through a `tm-kernel-ffi` dev-dependency (a path crate `tm` already links, so no new crate enters the graph; R7 named in the commit) |

---

## 11. The step plan

**Every step's commit runs both acceptance suites, capped (AGENTS §7.5):**
- `check.sh`: seven `ok` lines;
- `cargo test --workspace`: passed / 0 failed. Record the count in the README block.
- Some steps add named acceptance, listed below.

**"Readers in the binary" is 1 at every step** except inside P5's commit.

**Steps that add a module** add its `import` line in the same commit. `cat TmKernel.lean`
before committing.

**Kernel steps before P5** land where the parallel stage-5 workflow does not edit:
- new modules first;
- `Boundary.lean`'s `log` section appended at the end of the file;
- `Check.lean` under a banner `APPENDED <date> (stage 5, D9)`, and never edited in parallel
  (§6.3);
- `Negative.lean` cheats appended from 75 onward (stage 5 step 1 used 70 to 74).

### Phase 0: prerequisites (kernel; the binary's behaviour changes only in named request error texts)

| step | what | new theorems (names) | acceptance |
|---|---|---|---|
| **S0.1** gap 44 | Accumulating twins, each with a `@[csimp]` equality, the `junescapeTR`/`jscanTR` pattern already in `Json.lean`: `jtailAcc`, `jotailAcc`, and the emitters `jemitTailAcc`, `jemitOTailAcc` over a reversed chunk list, reversed once. `splitDoc`'s loop gets the same treatment. Nesting depth still recurses, and is bounded per line (§4.4) | `jtail_eq_jtailAcc`, `jotail_eq_jotailAcc`, `jemitTail_eq_jemitTailAcc`, `jemitOTail_eq_jemitOTailAcc`, `splitDoc_eq_splitDocAcc` | FFI test `a_200000_element_array_reads_on_a_2mib_thread` (`std::thread::Builder::stack_size(2 << 20)`); `oneshot` numbers recorded; gap 44 closed |
| **S0.2** exact decimals and leading zeros | `JDecRaw`/`JDec`/`JVal.dec` (§4.2); `jparse` refuses leading zeros (gap 43) | `jparse_jemit` re-proved unconditionally; `jparse_reads_a_plain_numeral_as_num`; `jparse_reads_a_signed_decimal_as_dec`; `jparse_refuses_a_leading_zero`; `jparse_refuses_what_the_fragment_has_no_type_for` refuted and restated as `a_request_number_that_is_not_a_nat_is_refused_by_its_reader` | new FFI tests for `-0.5`, `1e5`, `007` and a request `-3`; behaviour rows for the request error texts and gap 43 |
| **S0.3** surrogate pairs (gap 42) | `junescape` combines a valid high/low pair; a lone surrogate is still refused | `junescape_jescape` kept; `junescape_reads_a_surrogate_pair`; `junescape_refuses_a_lone_surrogate` | `a_parse_refusal_names_its_reason` split into a pair read and a lone surrogate refused; behaviour row |
| **S0.4** measurement harness | `kernel/tm-kernel-ffi/examples/logbench.rs`: generates logs of §2.1's shapes (seeded port of `genlog.py`) at 1 month, 6 months, 1 year and 3 years at 40 and 61 events/day; prints wall ms and `VmHWM`. It measures the docs-path proxy now, the `log` op at S1.4, and windowed calls at S4.4 | — | the example runs under `MemoryMax=8G`; README quotes one measurement per number (§5.11) |

### Phase 1: the grammar (kernel; nothing in the binary calls it)

| step | what | new theorems | acceptance |
|---|---|---|---|
| **S1.1** `Stamp.lean` | `Instant`, `Offset`, `Stamp`, `parseStamp`, `renderStamp`, `minutesBetween`, `subMinutes` | `parseStamp_renderStamp`, `renderStamp_is_fmt_timestamp`, `stamp_order_is_the_instant_order`, `minutesBetween_truncates`, `mkInstant?_refuses_a_bad_nanosecond`; cheat 75 (a stamp ordered by its written clock) | check.sh; probes under 8 GB |
| **S1.2** `Log.lean` | §4.4 and §4.5: `Ev`, `Entry`, `LWarn`, `parseLine`, `renderLine`, `tagOf`, `primaryId`. `Goals.lean` gains the grammar goals (§13) and loses its stale `PlanCore.log` sentence | §4.5's laws; cheats 76 (an unknown tag read as a warning) and 77 (a known event with a bad field read as unknown) | check.sh; every witness probed under 8 GB first |
| **S1.3** zone table | `TzTable`, `mkTzTable?`, `offsetAt`, `localDate` | §5.3's laws; cheat 78 (a transition applied one second early) | check.sh |
| **S1.4** the `log` op, grammar only | `parseLogReq`; a response with `lines`, `warnings`, `headers`, `view` (no facts); `tm-core/src/tz_table.rs`; the Rust writer's event generator `tm/tests/common/log_gen.rs` | extends `the_response_shapes_emit_in_build_order` | **T1** `kernel_reads_the_corpus_logs_as_the_fork_point_did`; **T2** `kernel_reads_what_the_rust_writer_writes` (proptest, 256 cases, byte-identical `renderLine`); **T3** `kernel_reads_every_timestamp_spelling_chrono_reads`; **T4** `kernel_localdate_matches_chrono`. All live in `tm/tests/kernel_log_grammar.rs`, and their in-tree Rust side is test-only |

### Phase 2: the Rust seams (one reader, which is Rust; interleaves with Phases 1, 3 and 4)

Each step deletes a raw path and adds a fact to the Rust `Replay`, which the Rust machine
computes. A unit test compares the old function with the new over the four corpus logs, and
is deleted with the old function in the same commit.

| step | what | acceptance (beyond both suites) |
|---|---|---|
| **R2.1** | `day.rs` `since_break_min` reads `DayReplay.{breaks, first_start}` | `cli_day` green; equivalence over the corpus |
| **R2.2** | `DayReplay.idle_marks` (the day's pause, interrupt, unpause, resume and break marks in file order); `idle_min_since` reads them | same |
| **R2.3** | `Replay.last_effective_t`; `day.rs` `idle` reads it | same |
| **R2.4** | `DayReplay.last_t`; `app.rs` `idle_since` reads it; `AppData.log` and `App.log` removed | `tui_*` green |
| **R2.5** | `Replay::view(filter)` rows `(line, entry, day, cancelled)` plus `entry_count`; `lifecycle.rs` `log` reads them | `cli_lifecycle` log tests green; `tm log --json` bytes unchanged on the corpus |
| **R2.6** | `Replay::headers_from(line)` and physical line counts in `Recorder` | `cli_undo` green; new `a_malformed_line_does_not_shift_the_recorded_events` (behaviour row B4) |
| **R2.7** | `PlanInput.log` deleted | planner suites green |
| **R2.8** | `Ctx.log` and `read_log` removed; `Ctx::replay_of(store, cfg) -> Replay` is the only code that touches `LOG_PATH` for reading | **one-reader grep:** `grep -rn 'LOG_PATH\|Log::parse\|iter_day\|effective()\|day_index(\|undo_mask' tm/src tm-core/src --include=*.rs` shows only the chokepoint, the writer and `log.rs` |
| **R2.9** | `DayReplay.load` becomes `load_fifths` with `load()`; the reviews read `load()` | review suites green, with any tie-rounding difference recorded as P7 (**the display change happens here, in Rust, so the switch changes no display**) |
| **R2.10** | torn-line repair before appending (G9) | new `an_append_after_a_torn_line_starts_a_new_line` (behaviour row B5) |
| **R2.11** | unread facts deleted from `Replay` (after OWNER Q3) | `log_replay__three_days_replay.snap` updated in the same commit; nothing else changes |
| **R2.12** | test chokepoint `replay_of_text`; 17 files and 27 sites switched mechanically | tm-core suites green |
| **R2.13** | latency with history: `cli_latency.rs` gains `a_verb_with_a_year_of_log_takes_well_under_a_second`, the history tree plus a generated 365-day log at about 40 events/day with a fixed seed; bounds `FIRST_VERB` 5 s and `LATER_VERB` 1 s. A 3-year variant is `#[ignore]`d and its numbers are recorded, not gated | green against the **Rust** reader; its numbers are the switch's baseline |

### Phase 3: the kernel replay (kernel; differential test-only)

Every step extends **T5** `tm/tests/kernel_replay_parity.rs`. It decodes the kernel's `facts`
and compares them field by field with `Ctx::replay_of` (Rust) over three inputs:
- the 4 corpus logs;
- the synthetic 1-month and 6-month logs;
- 256 generated sequences with time moving forward (`log_gen.rs`, including undos,
  out-of-order wakes and retro `break`/`idle`).

Exceptions come only from §12's list.

| step | what | new theorems | T5 compares |
|---|---|---|---|
| **S3.1** mask | `undoMask` with its fast twin | §6.1's laws plus `undoMask_eq_undoMaskFast`; cheat 79 (an undo that does not cancel itself) | cancelled line set |
| **S3.2** day index | `keptWakes`, `dayOf` | §5.4's laws and `the_kept_wake_is_not_the_first_logged_wake`; cheat 80 (a day of 25 hours) | every survivor's day |
| **S3.3** effect machine and F1 | §7.1 to §7.3 for `start`, `pause`, `unpause`, `interrupt`, `resume`, `stop`, `done` | `applyEffects_only_touches_named_days`, `credit_conserves_the_day_minutes`, `worked_minutes_floor_each_subsegment`, `worked_minutes_is_not_the_floor_of_the_block`, `a_stop_for_another_id_is_ignored`, `a_stop_for_the_open_id_cuts`, `a_done_after_a_stop_replaces_the_cut_credit`, `a_done_after_a_start_cut_does_not`, `load_is_exact_fifths`; cheat 81 (a done adding clock minutes to `actual_min`) | F1 fields |
| **S3.4** F2 | `routine`, `skip`, the done sets | `last_done_is_the_latest_instant`, `an_instance_is_its_last_logged_record`, `a_later_pending_does_not_undo_a_done_date`, `an_unknown_status_warns_and_is_pending` | F2 fields and warnings |
| **S3.5** F3 | `wake`, `arrive`, `loc`, `plan`, `break`, `idle`, `energy`, `event`, `demote` | `energy_obs_slept_is_the_days_first_logged_sleep`, `the_first_leak_maximum_wins`, `a_demote_stamp_reads_the_week_or_date_key` | F3 fields |
| **S3.6** F4 and observations | seam facts, `headers`, `view`, observations with lines | `observations_are_in_file_order`; the whole `facts` emitter's shape | **the entire `Replay`** |
| **S3.7** L4 | §6.2 | `undoing_the_last_command_replays_the_log_without_it`, `undo_of_a_silent_verb_cancels_an_older_event` | T5 adds 64 generated (log, command) pairs: facts(L ++ E ++ undos) = facts(L) |
| **S3.8** loaded witnesses | `three-days.jsonl` day one's hand-computed values (`day_one_matches_hand_computed_values`), each witness a decided statement over a shortened literal | the witnesses; probes under 8 GB | — |

### Phase 4: windowing (kernel; test-only)

| step | what | new theorems | acceptance |
|---|---|---|---|
| **S4.1** types and codecs | `Ckpt`, bundles, `emitCkpt`, `readCkpt`, `emitBundles`, `readBundles`. The windowing goals enter `Goals.lean` here (§13) | law 7; cheat 82 (a checkpoint decoder that defaults a missing `sealDay`) | check.sh |
| **S4.2** seal and resume | `seal`, `sealed`, `sealedSpan`, `resume`, `sealRule`, the guards | laws 1 to 6 with §8.6's route; cheats 83 (a resume that accepts an undo reaching behind the cut), 84 (a seal day that moves backwards) | check.sh; **stop condition if law 2 or law 4 will not close (§14 R4)** |
| **S4.3** wire | `ckpt`, `from`, `reseal`, the refusals | extends the response-shape theorem | **T6** `resume_equals_genesis_at_fifty_cuts` (kernel vs kernel over the 6-month log); **T7** `undo_behind_the_cut_refuses_reach`, `a_retro_wake_refuses_wakeBehindCut`, `a_retro_break_into_a_sealed_day_refuses_sealedDay`, each followed by a fallback that equals genesis; **T8** `genesis_in_chunks_equals_one_call` |
| **S4.4** measurement gate | `logbench` windowed: genesis total, steady call (checkpoint plus 1,024 lines), RSS, at 1 month, 6 months, 1 year and 3 years | — | **Gate:** at 3 years @61 the steady call is ≤ 150 ms (debug) and ≤ 200 MB RSS, and genesis at 1 year is ≤ 2 s. Otherwise apply §8.9's levers before P5 |

### Phase 5: the switch (**one commit**)

**Contents.**
1. `tm/src/cli/kernel_log.rs` (§10). `Ctx::replay_of`, `Recorder`, `tm log` and the sealed
   loader call it.
2. §10's deletions in `log.rs`. `Replay`'s serde derives follow the kernel's field names, or a
   `wire` module converts.
3. The test chokepoint `replay_of_text` calls the kernel (dev-dependency).
4. `tm-core/tests/log_replay.rs` and `log_regressions.rs` run through the chokepoint, with
   assertions unchanged except listed exceptions. `log_serde.rs` keeps its writer tests; its
   reader tests are T1 and T2 now.
5. **T5 is retargeted.** Its in-tree Rust side is gone. The oracle becomes fork-point
   `4748911`'s replay, emitting the same JSON through AGENTS §7.3's oracle scaffolding (moved
   to the fork point as §8.3 requires). The exception list is §12's.
6. The `kernel_bridge::refusal` names.

**Acceptance.**
- check.sh 7/7, and `cargo test --workspace` green (record the count).
- R2.13's latency tests green; record them against R2.13's Rust baseline.
- **One-reader grep:**
  `grep -rn 'fn replay\b\|undo_mask\|DayIndex\|parse_bytes\|LogEntry::parse\|Log::parse\|Machine' tm-core/src tm/src --include=*.rs`
  returns nothing.
- New CLI tests (**T9**):
  - `tm_undo_across_a_seal_restores_the_facts`
  - `invalid_utf8_line_is_a_warning_not_a_failure` (P9)
  - `deleting_the_replay_cache_changes_nothing`: run verbs, `rm -r .tm/cache/replay`, rerun,
    and compare every `--json` output
  - `a_changed_tz_invalidates_the_checkpoint`
  - `a_rewritten_log_prefix_invalidates_the_checkpoint`
- **The 30-minute drive (§5.13)** on a copy of a real `.tm/`, with at least:
  - `now`, `start`, `pause`, `done`, `undo` ×3 (one reaching behind the cut);
  - `review week`, `model --fit`, `log --since 7d`;
  - the TUI through two reloads.

**Why this is safe as one commit.**
- Consumers do not change: they read the same `Replay`.
- T5 proved field equality over the corpus, synthetic logs and generated sequences before the
  commit.
- The cache is derived: deleting `.tm/cache/replay` is always a valid recovery, and a revert
  needs no data migration.

### Phase 6: decision facts leave the Rust struct; the fit reads observations

| step | what | acceptance |
|---|---|---|
| **S6.1** | `energy::fit_observations`; `lifecycle.rs` `model` uses sealed plus live observations; `fit_replay` deleted | `energy_fit.rs` green; **T11** `model_fit_is_the_fork_points_on_the_corpus`: `tm model --fit` on `energy-14d.jsonl` writes `model.json` byte-identical to fork point `4748911`'s |
| **S6.2** recurrence family (with the stage-5 `Recur.lean` tranche) | `done_dates`, `last_done`, `instances`, `events`, `is_done` for recurrence read inside the kernel; `recur::*` callers become kernel calls; the Rust fields and accessors deleted in the same commit | that tranche's parity; grep shows no Rust reader |
| **S6.3** priority family (with `Priority.lean`) | `done_items`, item-day minutes, `done_minutes_map` (and `tm-core/src/horizon.rs` `close_day`/`day_remaining`'s `block_minutes_on`, if still live then; deleted if dead) | same |
| **S6.4** capacity family (with D10) | `energy_on(today)`, `blocks_done(today)` read inside the kernel | same |

**End state.** The decoded Rust `Replay` holds only what `review.rs`, the TUI's display and the
fit read. **The Rust replay is deleted for decision facts.**

### Phase 7 (optional; OWNER Q4): the writer joins the reader

Appending verbs would send typed events, and the kernel would return the lines to append.
`Event: Serialize` and `hours_since_wake` move into the kernel, and
`the_log_reads_what_it_renders` becomes end to end. Until then, T2 is the guard.

---
## 12. Acceptance: the named tests, and the parity exception list

### 12.1 New tests, by the step that lands them

| id | test | where | step |
|---|---|---|---|
| T0 | `a_200000_element_array_reads_on_a_2mib_thread` | `kernel/tm-kernel-ffi/tests` | S0.1 |
| T1 | `kernel_reads_the_corpus_logs_as_the_fork_point_did`: per line, entry, warning or blank, with the warning *class* mapped from serde's error text to the kernel's name by a table the test owns; pins duplicate keys, `null` in a `def` field, Unicode-blank lines | `tm/tests/kernel_log_grammar.rs` | S1.4 |
| T2 | `kernel_reads_what_the_rust_writer_writes`: proptest, 256 events, `parseLine` ∘ serde gives the same event, and `renderLine` gives byte-identical text | same | S1.4 |
| T3 | `kernel_reads_every_timestamp_spelling_chrono_reads`: `Z`, `z`, `+00:00`, `-00:00`, fractions of 1 to 12 digits, the no-seconds form, `t` and space separators, second `60`, year `0000`, `24:00` | same | S1.4 |
| T4 | `kernel_localdate_matches_chrono`: 5 zones × 10,000 instants, 1970 to 2100 | same | S1.4 |
| T5 | `kernel_replay_parity`: in-tree Rust until P5, fork point after | `tm/tests/kernel_replay_parity.rs` | S3.1 to S3.7 |
| T6 | `resume_equals_genesis_at_fifty_cuts` | `kernel/tm-kernel-ffi/tests/log.rs` | S4.3 |
| T7 | `undo_behind_the_cut_refuses_reach`, `a_retro_wake_refuses_wakeBehindCut`, `a_retro_break_into_a_sealed_day_refuses_sealedDay`, each with its fallback equal to genesis | same | S4.3 |
| T8 | `genesis_in_chunks_equals_one_call` | same | S4.3 |
| T9 | `tm_undo_across_a_seal_restores_the_facts`, `invalid_utf8_line_is_a_warning_not_a_failure`, `deleting_the_replay_cache_changes_nothing`, `a_changed_tz_invalidates_the_checkpoint`, `a_rewritten_log_prefix_invalidates_the_checkpoint`, `an_append_after_a_torn_line_starts_a_new_line` (R2.10), `a_malformed_line_does_not_shift_the_recorded_events` (R2.6) | `tm/tests/cli_undo.rs`, new `tm/tests/cli_log.rs` | R2.x, P5 |
| T10 | `a_verb_with_a_year_of_log_takes_well_under_a_second`, plus the `#[ignore]`d 3-year variant | `tm/tests/cli_latency.rs` | R2.13 |
| T11 | `model_fit_is_the_fork_points_on_the_corpus` | `tm/tests/cli_lifecycle.rs` | S6.1 |

### 12.2 Existing suites that must stay green, with assertions unchanged

- **CLI:** `cli_undo`, `cli_day`, `cli_lifecycle`, `cli_plan`, `cli_json_matrix`,
  `cli_close_kernel`, `cli_latency`.
- **TUI:** all eleven `tui_*`.
- **tm-core:** `review_day`, `review_week`, `review_month`, `review_edges`, `review_fixture`,
  `recur_cases`, `recur_fixture`, `recur_regressions`, `priority_*`, `planner_dynamics`,
  `planner_regressions`, `planner_invariants` (proptest), `energy_fit`, `horizon_close`,
  `horizon_moves`, `store_state`, `log_replay` (through the chokepoint), `log_regressions`.
- **Kernel:** the FFI crate's tests (check.sh checks 5 and 6).

Where a listed exception forces an assertion to change, the change is in the step that
introduces the exception, never in P5.

### 12.3 Entries for README "The stage-5 parity exception list" (continuing P1 to P6)

| # | site | the kernel | the fork point | step |
|---|---|---|---|---|
| P7 | `DayReplay.load` | exact fifths, divided once at display | an accumulated `f64` sum; `round1` can differ at a tie | R2.9 |
| P8 | minute sums above `u32::MAX` | `Nat`; the decoder refuses `minutesOverflow` by name | `saturating_add` | S3.3 |
| P9 | a log line that is not UTF-8 | a per-line `invalidUtf8` warning, and the verb runs | `read_to_string` fails the whole command | P5 |
| P10 | a surrogate-pair escape in a line | read (S0.3); **only an exception if S0.3 is not taken** | read | S0.3 |
| P11 | a line over 65,536 characters, or nested over 64 deep | `lineTooLong` / `lineTooDeep` warning | read | S1.2 |
| P12 | the unread facts of §7.4 | absent | present in `Replay` | R2.11 (OWNER Q3) |
| P13 | an instant outside [1900, 2200) | the table's edge offset | chrono-tz's value | S1.3 |
| P14 | `tm log --json` bytes | the kernel renderer; byte identity is the target and T2/T3 pin it, so any residue is listed here | serde | R2.5/P5 |
| P15 | the undo recorder's line count | physical lines | `log_len` counts non-blank lines while `new_events` skips malformed ones | R2.6 |
| P16 | an append after a torn last line | starts a new line | the concatenation corrupts both lines | R2.10 |
| P17 | a leading-zero numeral in a line | refused, as serde does (S0.2); **only an exception if gap 43 stays open** | refused | S0.2 |

**Not exceptions; exact by design.**
- day attribution in `cfg.tz` (inside the span);
- `hsw`;
- observation order;
- late-bound `slept`;
- both first-wake rules;
- the per-sub-segment floor;
- `last_done` by instant, and instances by file order;
- the undo mask, dangling undos included.

---

## 13. `Goals.lean`: what to add, and when

Each block is added in the step whose definitions let the statement elaborate. That is the
file's rule: provisional `def … := sorry` only where the spec settles a signature, and here
the design settles them, so no provisional defs. A statement is deleted when it is proved in
its module and appended to `Check.lean`. The burn-down therefore rises at S1.2, S3.1, S3.2, S3.3 and
S4.1, by the counts below, each rise a deliberately admitted debt named in that step's
handover.

```lean
/-! ############################################################################
# STAGE 5 — D9: the kernel replays the log
Design: the D9 migration design (grammar, mask, day index, machine, checkpoint).
############################################################################ -/

-- S1.2 (4)
theorem the_log_reads_what_it_renders (e : Log.Entry) (h : e.canonical = true) :
    Log.parseLine e.line (some (Log.renderLine e)) = .entry e := sorry
theorem a_known_event_is_never_read_as_unknown (n : Nat) (l : List Char) (e : Log.Entry)
    (h : Log.parseLine n (some l) = .entry e) (hk : Log.isKnownTag (Log.tagOf e.ev) = true) :
    e.ev.isUnknown = false := sorry
theorem an_unknown_tag_is_never_a_warning (n : Nat) (l : List Char) (w : Log.LWarn)
    (hobj : Log.isObjectWithStampAndTag l = true) (hu : Log.isKnownTag (Log.tagIn l) = false)
    (hlen : l.length ≤ Log.maxLineChars) : Log.parseLine n (some l) ≠ .warn n w := sorry
theorem lineTooLong_bounds_every_string (n : Nat) (l : List Char) (e : Log.Entry)
    (h : Log.parseLine n (some l) = .entry e) : ∀ s ∈ e.strings, s.length ≤ Log.maxLineChars := sorry

-- S3.1 (5)
theorem undoMask_cancels_every_undo (es : List Log.Entry) (i : Nat) (e : Log.Entry)
    (h : es[i]? = some e) (hu : e.ev.isUndo = true) : (Replay.undoMask es)[i]? = some true := sorry
theorem undoMask_cancels_the_latest_match (es : List Log.Entry) (i j : Nat) :
    Replay.targetOf es i = some j ↔ Replay.isLatestUncancelledMatch es i j = true := sorry
theorem an_undo_of_an_undo_dangles (es : List Log.Entry) (i : Nat) (e : Log.Entry)
    (h : es[i]? = some e) (hu : e.ev = .undo "undo".toList none) : Replay.targetOf es i = none := sorry
theorem undoing_the_last_command_replays_the_log_without_it (tz : TzTable) (L E : List Log.Entry)
    (hE : E.all (fun e => !e.ev.isUndo) = true)
    (hl : Log.linesIncreasing (L ++ E ++ Replay.stampAfter E (Replay.undosFor E)) = true) :
    Replay.eraseLines (Replay.replay tz (L ++ E ++ Replay.stampAfter E (Replay.undosFor E)))
      = Replay.eraseLines (Replay.replay tz L) := sorry
theorem undo_of_a_silent_verb_cancels_an_older_event :
    ∃ (tz : TzTable) (L : List Log.Entry) (u : Log.Entry),
      u.ev = .undo "move".toList none ∧
      Replay.eraseLines (Replay.replay tz (L ++ [u])) ≠ Replay.eraseLines (Replay.replay tz L) := sorry

-- S3.2 (3)
theorem dayOf_is_the_wake_date_within_a_day (tz : TzTable) (kw : List ValidInstant) (t w : ValidInstant)
    (hw : Replay.lastWakeLe kw t = some w) (h24 : Stamp.lt24h w t = true) :
    Replay.dayOf tz kw t = Stamp.localDate tz w := sorry
theorem the_earliest_wake_of_a_date_is_kept (tz : TzTable) (ws : List ValidInstant) (w : ValidInstant)
    (hm : w ∈ ws) (hmin : ∀ v ∈ ws, Stamp.localDate tz v = Stamp.localDate tz w → Stamp.le w v = true) :
    w ∈ Replay.keptWakes tz ws := sorry
theorem the_kept_wake_is_not_the_first_logged_wake :
    ∃ (tz : TzTable) (es : List Log.Entry) (d : Nat),
      Replay.keptWakeOn tz es d ≠ Replay.firstLoggedWakeOn tz es d := sorry

-- S3.3 (2)
theorem credit_conserves_the_day_minutes (tz : TzTable) (es : List Log.Entry) (d : Nat) :
    Replay.sumByCi (Replay.replay tz es) d + Replay.sumCiUnknown (Replay.replay tz es) d
      = Replay.blockMin (Replay.replay tz es) d := sorry
theorem applyEffects_only_touches_named_days (st : Replay.State) (fx : List Replay.Effect) (d : Nat)
    (h : d ∉ Replay.daysNamed fx) : Replay.dayView (Replay.applyEffects st fx) d = Replay.dayView st d := sorry

-- S4.1 (5)
theorem seal_facts_are_the_replay (tz : TzTable) (S : Nat) (L : List Log.Entry) :
    Seal.merge (Seal.sealed tz S L) (Seal.live (Seal.seal tz S L)) = Replay.replay tz L := sorry
theorem resume_is_replay (tz : TzTable) (S : Nat) (a b : List Log.Entry) (k : Seal.Ckpt)
    (h : Seal.resume tz (Seal.seal tz S a) b none = .ok (k, none)) : k = Seal.seal tz S (a ++ b) := sorry
theorem resume_keeps_the_sealed_days (tz : TzTable) (S : Nat) (a b : List Log.Entry) (r : Option Nat) (x)
    (h : Seal.resume tz (Seal.seal tz S a) b r = .ok x) : Seal.sealed tz S (a ++ b) = Seal.sealed tz S a := sorry
theorem resume_ok_iff_reachFree (tz : TzTable) (S : Nat) (a b : List Log.Entry) (r : Option Nat) :
    (Seal.resume tz (Seal.seal tz S a) b r).isOk = Seal.reachFree tz S a b := sorry
theorem reseal_is_seal (tz : TzTable) (S keep : Nat) (a b : List Log.Entry) (k k' : Seal.Ckpt) (bs : Seal.Bundles)
    (h : Seal.resume tz (Seal.seal tz S a) b (some keep) = .ok (k, some (k', bs))) :
    let S' := Seal.sealRule tz S (a ++ b) (b.length - keep)
    S ≤ S' ∧ k' = Seal.seal tz S' (a ++ b.dropLast keep) ∧ bs = Seal.sealedSpan tz S S' (a ++ b.dropLast keep) := sorry
```

**Counts.** 19 goals in total. They are shaped for a builder to refine, not compiled here:
every name they use is defined by §4 to §8's steps. `readCkpt_emitCkpt` and the grammar's
`decide` witnesses are proved in the step that states them, so they never enter the file.

---

## 14. Cost (ESTIMATE throughout)

| piece | Lean definitions | Lean proofs | Rust |
|---|---:|---:|---:|
| S0.1 gap 44 twins | 120 | 700 | 40 (test) |
| S0.2–S0.3 decimals, leading zeros, surrogates | 130 | 800 | 60 |
| S1.1 `Stamp` | 250 | 700 | — |
| S1.2 grammar and renderer | 900 | 3,000 (the round trip is `Json.lean`-scale; `Json.lean` is 2,641 lines) | — |
| S1.3–S1.4 zone table and `log` op | 250 | 400 | 450 (`tz_table.rs`, T1–T4, `log_gen.rs`) |
| Phase 2 seams | — | — | ~600 changed, ~300 test |
| S3.1–S3.2 mask (spec and fast twin), day index | 350 | 1,700 | 250 (T5 scaffold) |
| S3.3–S3.6 machine, facts, observations | 1,250 | 1,900 | 150 |
| S3.7–S3.8 L4, loaded witnesses | 60 | 1,500 | 60 |
| S4.1–S4.3 checkpoint, seal, resume, codecs, wire | 850 | 5,500 | 300 (T6–T8) |
| P5 switch | — | — | +700 `kernel_log.rs`, −1,700 `log.rs`, ~400 test sites, 250 T9 |
| S6.1 fit on observations | — | — | 120 |
| **total** | **~4,200** | **~16,000** | **~+3,300 / −1,700** |

**What the totals mean.**
- **Proof : definition ratio:** about 3.8 : 1 (stage 4 final: 4.80 : 1). Under D5 it informs
  and stops nothing.
- **Agent time: 6 to 8 weeks.** Phase 0 about 1; Phase 1 about 1.5; Phase 2 about 0.5,
  interleaved; Phase 3 about 2; Phase 4 about 2; P5 about 0.5; S6.1 about 0.2. S6.2 to S6.4
  ride the stage-5 tranches they belong to.
- **This is larger than the "about 1,500 lines of `log.rs` replay" D9 priced.** That figure is
  the fork point's definitions. It does not count the proofs, the windowing scheme, the
  decimal widening, gap 44, or the seams. **OWNER Q7.**

---

## 15. Risks

| # | risk | evidence | mitigation |
|---|---|---|---|
| R1 | Kernel JSON throughput makes even the windowed call slow | §2.1 proxy: 170–190 ms/MiB | S0.4/S4.4 measure the real op; the S4.4 gate; §8.9's levers in order |
| R2 | Genesis memory on an old log | proxy: 448 MB RSS for a 4.7 MB request | `CHUNK = 8,192` lines (~0.9 MB, ~85 MB RSS by the proxy); `tooManyLines` caps any single call |
| R3 | A grammar witness is a memory bomb | AGENTS §5.10a (123 GB, twice) | short literals; round-trip theorems for large inputs; every probe under `MemoryMax=8G timeout 120` first |
| R4 | `undoMask_append` or `resume_is_replay` will not close | the greedy scan's invariant is subtle | the effect-list shape from S3.3; the stack invariant stated as its own lemma first; **under D5 a law that will not close is a stop condition (§9.1), raised to the owner, never replaced by T6's property test**. Whole-log-per-call is not the fallback, because it fails R2.13's latency test |
| R5 | serde tolerance quirks diverge from the kernel's | serde's behaviour on duplicate keys, `null` in `def` fields and Unicode blanks is unverified | T1 to T3 pin them **before** S1.2's grammar is frozen, and each divergence is decided or listed |
| R6 | A checkpoint is stale or corrupt | a hand edit, a git merge of `log.jsonl`, a tz change, a kernel rebuild | fingerprint, `v`, `buildId`, tz key; `readCkpt` refuses by field; genesis; T9 |
| R7 | The CLI and TUI write the cache at once | TUI reloads on a 200 ms debounce | temp-file writes and atomic renames; any stored checkpoint of an append-only log is valid for a prefix; the fingerprint catches a rewrite |
| R8 | A synced plan directory carries the cache | `.tm/` may be under git | OWNER Q6 |
| R9 | Collision with the parallel stage-5 workflow | it is editing `Boundary.lean`, `Check.lean`, `Goals.lean` and `Negative.lean` now | new modules first; `Boundary.lean` appended at the end; §6.3's no-parallel-`Check.lean` rule; cheats numbered at merge |
| R10 | The switch commit is too big to review | 17 test files, deletions, a new module | Phase 2 reduces P5 to a body swap plus deletions; the commit is a revert unit |
| R11 | A reader outside grep's reach | examples, benches, skills | R2.8 greps `LOG_PATH\|log.jsonl\|Log::` across the whole workspace, `examples/` and `kernel/tm-kernel-ffi/examples/` included |
| R12 | The tz probe misses a transition | two changes within one UTC day | T4 over five zones, including 30- and 45-minute offsets |
| R13 | 2 MiB test threads overflow on a large wire | libtest's default stack | S0.1 first; T0 runs on an explicit 2 MiB thread |
| R14 | The latency test is green but real trees are slower | R2.13 uses synthetic ids and a fixed rate | the `#[ignore]`d 3-year variant is recorded; the §5.13 drive on a real `.tm/` |

---

## 16. Owner questions (genuinely new; none is decided here)

| # | question | why it is a decision, not an engineering choice | recommendation | blocks |
|---|---|---|---|---|
| **Q1** | **Unify the two "first wake" rules?** Attribution keeps the earliest wake by instant per date; `DayReplay.wake`/`slept_min` and `slept_by_day` keep the first wake in file order | one concept with two definitions (§5.3). Unifying changes behaviour when wakes are appended out of time order (e.g. `tm wake 06:05` typed after a later wake) | port both now (parity); unify on earliest-by-instant as a later behaviour row if the owner agrees | nothing (S3.2 ports both) |
| **Q2** | **The compensating undo of a silent verb** (§6.3): `tm undo` of a recorded `move`/`readopt` (no-id path) or a no-op `close` writes `undo{of:<verb>}` and cancels an older event of that tag | changes bytes written to `.tm/log.jsonl`. Today no read fact changes, only `tm log`'s view | write `of:"verb:<name>"` for silent verbs, with a behaviour row, landing with R2.6 | nothing |
| **Q3** | **"Every replay fact"**: port the §7.4 facts nothing reads (`closes`, `dropped_items`, `stops`, `extended_min`, `done_at`, `partial_done_at`, `open_interrupt`, `unknown`, global `longest_leak`, `replans_today`, `last_plan_hash`, `loc_changes`, `dropped`), or delete them from the Rust struct | D9's wording says "every". Porting them costs ~300 definition lines and their witnesses and proves nothing a decision uses | delete (R2.11); P12 | R2.11 only |
| **Q4** | **Does D9 include the writer?** Rust's serde still writes the lines the kernel reads | two definitions of one grammar (writer and reader) remain; T2 guards them byte for byte | not in D9's tranche; Phase 7 later | nothing |
| **Q5** | **R8: truncate each sub-segment** (fork point) **or floor the block's total?** | a block paused *k* times loses up to *k* − 1 minutes today. That is a rounding site not in R1 to R7 | keep faithful now; record R8 in `Arith.lean`'s table | nothing |
| **Q6** | **Where the derived replay cache lives, and whether a synced plan carries it**: `.tm/cache/replay/` (checkpoint, ladder, sealed months, tz table), a new on-disk artifact | spec §10 lists `.tm/`'s files; a git-synced plan would merge a derived cache, and a merged `log.jsonl` invalidates it anyway | `.tm/cache/` inside the plan, excluded from sync (a `.gitignore` line written by `tm init`), and always deletable | P5 (needs a path) |
| **Q7** | **The price.** ESTIMATE ~4,200 definition and ~16,000 proof lines, 6 to 8 agent-weeks (§14), against D9's "about 1,500 lines" | D9 was taken on a stated cost this exceeds | confirm; or narrow Phase 4 (for example, keep sealed files but drop G1's exactness and fall back to genesis on any cross-cut undo) and accept a named worst-case latency | Phase 4 |

**Decided in this design, reversible, and recorded (not owner questions):**
- the zone as a host-supplied offset table (§5.2 B, exact);
- the kernel as the tolerance authority, with Rust sending `null` for a non-UTF-8 line;
- the `JVal` widening, with leading zeros and surrogate pairs fixed to serde's reading;
- `hsw` carried lexically;
- the fold-state checkpoint with guards G1 to G3;
- `M = 512`, `CHUNK = 8,192`, and `sealRule`'s week and month terms;
- the ladder of three months;
- the FNV-1a-64 fingerprint;
- deleting `undo_target`, `compensating_undo`, `bounds` and `wake_of` (no callers);
- keeping `review.rs`'s presentation arithmetic in Rust.

---

## 17. Gaps and behaviour rows to record (numbers are the next free ones at `c2cf4dc` plus step 1; re-check before writing)

**Gaps**, each in the README's four-part form: what, why not now, cost, when.
- **76.** Two first-wake rules (Q1).
- **77.** R8, the per-sub-segment floor (Q5).
- **78.** A silent verb's compensating undo (Q2).
- **79.** Reviews' presentation arithmetic (`gaps`, adherence, `wake_to_arrive_min`,
  `lounge_rate` with the written offset's hour) stays Rust over kernel facts.
- **80.** The writer is Rust (Q4).
- **81.** Two zone evaluators, chrono for `today` and display, until stage 6 moves `now`.
- **82.** Cache location (Q6).
- **83.** `arrive.window` strings and `idle.attributed` are not validated (fork-point behaviour,
  kept).
- **84.** A block left open for weeks holds `sealRule` back.

**Behaviour rows.**
- a request's non-`Nat` number error text (S0.2);
- leading zeros refused (S0.2);
- a surrogate pair read (S0.3);
- B4: the undo recorder counts physical lines (R2.6);
- B5: an append repairs a torn last line (R2.10);
- an invalid-UTF-8 line is a warning (P5, P9);
- `lineTooLong` / `lineTooDeep` (S1.2, P11).

**AGENTS.md updates at P5.**
- §2.4 gains the `log` request and response shapes.
- §8.3's trap "the log has nowhere to live" gets its answer (the request's `log` section and
  `Replay.Facts` as a plain argument).
- §10.1's module map gains four modules.
