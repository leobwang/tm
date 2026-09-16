# Stage 5, D9 and D10: the one plan

A read-only design pass by the judge and synthesizer, written 2026-09-14 and **revised the same day
against a completeness critique** (`design/critique.md`: 3 blockers, 17 major, 12 minor). Every blocker
and major item is fixed below. Most minor items are fixed too. §21 lists each item, where it landed, and
the one fix taken in a different form from the critique's, with the reason. **Nothing in the repo was
edited, built or committed.**

**What it was read against.** Branch `rebuild-on-lean` at `ce140bd`. Stage 5 step 3 (`Capacity.lean`,
the EDF pass) has **landed** as `fea3f81`, followed by the cheat-elaboration repair `ce140bd`. The first
draft of this document read step 3 while it was still uncommitted. Every name taken from it has been
re-read in the committed tree.

**What it synthesizes.**
- The fact base, `design/inventory.md` (cited "inv §n").
- Three competing D9 designs: `design-proof.md` ("PROOF"), `design-latency.md` ("LAT") and
  `design-migration.md` ("MIG").
- The D10 design, `design-lookahead.md` ("LOOK").
- The critique, `design/critique.md` ("CRIT n" for its item n).

**How to read it.**
- Rust is cited by function name. The oracle is the fork point `4748911`.
- **MEASURED** means a figure some pass actually ran. The text says which pass and how.
- **ESTIMATE** means a derived figure. The text says what it was derived from.
- **OWNER** marks a genuinely new human decision. All of them are in §4.
- Everything else is a decision taken inside D5, D6, D9, D10, the hard rules and AGENTS §4, with its
  reason written beside it (§3).
- **"Site Rn"** means a rounding site in `Arith.lean`'s table: R1–R7 exist, and this plan adds sites
  R8–R11. **Rn alone** means an AGENTS hard rule, so R10 is "every bounded type has a smart constructor".
  The two lists share letters in the repository, so the prose always says "site" for the first.

**Facts checked for this pass** that the input designs did not have, or had wrong:

| fact | where | consequence |
|---|---|---|
| Step 3 **landed** and used parity **P10–P12**. Gaps run to **81**, cheats to **90** (README "Stage 5 repair": "Gaps still run to 81 and cheats to 90") | README, `Negative.lean` | this plan's parity entries start at **P13** (§17), gaps at **82** (§20), cheats at **91** (§16) |
| Committed `Capacity.lean` has `Den`, `denOf?`, `DayCapacity {day, numAt}`, `DayCapacity.minutesAt`, `Deadline`, `Deadline.ofRemaining`, `availUntil`, `reserveRest`/`reserveOut`, `sortDue`, `Grant`, `grantOf`, `edf (den : Den)`, `edfGrants`, `Grant.availQ`/`reservedQ`/`shortfallQ`, `lookaheadOf?`, and the three EDF goals, proved | `Capacity.lean` | LOOK's L1–L2 are superseded. D10's remaining work is a module that *produces* step 3's `List DayCapacity` (§13) |
| `Priority.lean` has `binOfQ`, `binOfScaledQ bins s rem (avail : Pos)` and `binOfScaledQ_congr` | `Priority.lean` | the lookahead's units need no new comparator (§13.4) |
| `horizon::auto_close` runs in `Ctx::load` housekeeping before any verb. It catches up at most `AUTO_CLOSE_CATCHUP = 16` days and calls `close_day`, then `day_remaining`, then `replay.block_minutes_on(key, date)`. `tm close day <date>` (`lifecycle.rs`) takes **any** date | fork `horizon.rs`, `ctx.rs`, `lifecycle.rs` | the item-day minutes of old dates have kernel-relevant readers. The window horizon covers `L − 16`, and older dates read sealed window records (§9.1, CRIT 2) |
| `review.rs` `lounge_rate` iterates `replay.days.values()` (every day ever). `energy::estimate_calibration(cfg, &replay.durations, date)` reads **every** duration | fork `review.rs`, `energy.rs` | `review day` and `review week` read all sealed months (§11.1, §18.6, CRIT 4) |
| `Ctx::wake_time` keeps seconds (`d.wake…time()`). `log::hours_since_wake` is `(secs / 36.0).round() / 100.0`, and `energy::bucket` floors it and clamps it to `0..12` | fork `ctx.rs`, `log.rs`, `energy.rs` | whole minutes are not exact. The lookahead ports hundredths from seconds as site R11, which also deletes LOOK's range-key exception (§13.3, CRIT 6) |
| `parse_timestamp`, `Replay::events_for` and `Replay::stamps` have **no caller outside `log.rs`** | `git grep` at `4748911` | the human `tm log` formats `e.t` itself, so the kernel emits that display text (§11.4). The stamp reader is deleted at S (CRIT 20, 23) |
| `day::idle` is the last `t` **in file order** over `effective()`. `app.rs` `idle_since` is the **max** `t` over `iter_day(today)`. Both read survivors of every kind | fork `day.rs`, `app.rs`, `log.rs` | the two seam facts are specified separately (§8.4, CRIT 24) |
| Rust reserves in three places: `priority::compute`, `planner.rs`'s week allocation (`capacity::reserve(std::slice::from_mut(day), take, c.ci)`) and `tui/queue.rs` | fork | a `DayCapacity` consumer table (§13.8, CRIT 5) |
| Tests that build a `Replay` or `Log`: 18 tm-core files with 45 call sites, and 3 tm files (`tui_common/mod.rs`, `tui_queue_common/mod.rs`, `tui_today_prompts.rs`) | `git grep -c` at `4748911` | R12's counts corrected (§14.3, CRIT 31) |
| The undo stack lives in `.tm/undo.json` (`UNDO_PATH`, `MAX_ENTRIES = 50`), not in `state.json`. `tm undo` restores `state.json` bytes but pops the stack; it never restores it | fork `undo.rs` | a restored state cannot lower the seal's `maxLine` (§9.6, CRIT 27) |
| `Event::Close` has no primary id, so `tm undo` of a close writes `undo{of:"close", id:null}` | fork `log.rs` `primary_id` | the undo law needs interleaved housekeeping, and it is a live defect (§7.3, CRIT 12) |
| No CLI output serialises `Replay`, `DayReplay` or `ItemReplay`. The fields inv §3 lists as unread have no reader outside `log.rs`, and `longest_leak` is read only per day | grep, first pass | whether to port the unread fields is OWNER Q7 (CRIT 16) |
| `tm log` prints `serde_json::to_value(LogEntry)` (a re-serialisation), and `total = log.entries.len()` | `lifecycle.rs` `log` | the kernel renders entries (§11.4) |
| `[profile.dev] opt-level = 1` | `Cargo.toml` | a full-prefix digest per call is affordable (§18) |
| chrono-tz `0.10.4` exports `IANA_TZDB_VERSION` but not `TimeSpans` | `Cargo.lock`, registry source | the zone table is probed, and its cache is keyed by tzdb version (§6) |
| `capacity::local_dt`: `Single` returns that time; `Ambiguous` the earliest; `None` the first valid local time at +1..180 min, else `from_utc_datetime` | `tm-core/src/capacity.rs` | ported literally as `Cal.instantOf` (§6.3) |
| v4.33.1 core has `List.mergeSort_perm`, `List.pairwise_mergeSort` and `List.eraseP_append`, and `Std.TreeMap` ships `Lemmas.lean` | toolchain source | the day index, the mask proofs and the tree-map twin stand on existing lemmas |
| `PLAN-lean-kernel.md` §4 lists **G9** (`Log::read` on invalid UTF-8; `append_all` on a torn last line) as a recorded defect, verdict **M**: "Rust; I/O stays in Rust" | PLAN §4 | the torn-line repair is G9's planned fix. Where warnings become visible is OWNER Q9 (CRIT 18) |

---

## 0. The plan on one page

1. **The spine is MIG's.** The shipped binary has exactly one reader of `.tm/log.jsonl` at every commit.
   - **Before the switch**, the kernel's reader is library code that only tests call. The Rust consumers
     that walk the raw log move onto one chokepoint, `Ctx::replay_of`, one commit each.
   - **The switch** is one commit. It swaps the chokepoint's body for a kernel call that decodes into the
     same reshaped `Replay`, with the sealed history each verb family needs already merged in. The same
     commit deletes the Rust reader.
   - **After the switch**, decision facts leave the Rust struct as each stage-5 kernel tranche takes over
     its consumer.
2. **The kernel reads lines and Rust splits bytes.**
   - Rust sends the log as a JSON array of line strings, with `null` for a line that is not UTF-8, plus
     whether the file ends in a newline.
   - The kernel owns everything about a line's content: JSON, the typed grammar of 25 known kinds plus
     unknown tags, named per-line warnings, the undo mask, wake-based day attribution in `cfg.tz`, the
     block machine, and every observable fact.
   - Every recursion over a list the wire can make large has a tail-recursive twin, gap 44's included.
3. **There is one JSON grammar, widened once.**
   - `JVal` gains `dec`, an exact lexical decimal, and `jparse_jemit` stays unconditional.
   - Gaps 42 and 43 are fixed to serde's reading.
   - Wire readers still refuse a decimal, by the field's name.
4. **The zone is data.** Rust probes chrono-tz **hourly** for `cfg.tz`'s UTC-offset transitions over
   [1900, 2200), bisects each to the second, and sends the table. The kernel does all date arithmetic.
   Stage 6 and D10's window reuse the table.
5. **Windowing is a checkpoint of the fold, anchored to the request's `now`, with proved laws (D5).**
   - A call carries the checkpoint plus the lines after its cut, never the whole log.
   - The checkpoint holds the all-time aggregates, the open days `≥ L` and the window facts
     `≥ H = min(month start, ISO Monday, L − 16)`. Finished days and finished window facts go once into
     Rust-stored, generation-named month files.
   - A kernel decision about **today** reads only the checkpoint. A query about an explicitly old date
     reads that date's sealed record, whose correctness is law 1.
   - Guards refuse by name whenever the tail could change what the checkpoint holds. A refusal names
     how far back the host must rebuild, and it is always a rebuild, never a wrong fact.
   - The laws are query-indexed, and they are stated through the disk. They also cover the reseal's own
     answer and the rule that nothing is ever sealed past `now`.
6. **D10 builds on step 3's EDF.** A new `Lookahead.lean` produces `List DayCapacity` over one
   denominator: `numAt l = w·lounge l + (capDen − w)·home l`, mixed **after** each location's budget
   limit. It pulls stage 6's window (E7, in real seconds through D9's zone table), the slot cut and
   future-day energy (hours since wake in exact hundredths, from seconds) forward into stage 5. That
   is OWNER Q2. `capDen`'s size is OWNER Q8. Every Rust reserve over capacities works in exact units, and
   floors appear only in display.
7. **The cost is large, and this document states it** (§14.9, OWNER Q1). ESTIMATE, D9 and D10
   together: ≈ 6,550 Lean definition lines, ≈ 23,300 proof lines and ≈ 124–166 agent-days. By the stage-4
   audit figures that is about 1.7 times the library's definition lines and 1.2 times its proof lines.

---

## 1. Judgement: the three replay designs scored

**The scale.** 1 is poor and 5 is strong. For cost, 5 means cheapest *as honestly priced*. Each cell
gives the score and its reason.

| criterion | PROOF | LAT | MIG |
|---|---|---|---|
| **Proof strength** | **4**: the best decomposition (W1–W4 plus `foldl_append`, `resume_rolls`, `resume_empty`) and both refutations. But the law is stated over the in-memory checkpoint, not through `jemit`/`parseCkpt` (AGENTS §5.9). It has no no-loop or completeness law, and no undo law | **4**: `resume_is_replay` is stated through the disk, with a no-loop law, a chunked-rebuild law and `pendingSound`. But the guards are sound in one direction only, by design. And compacting `view` to today's consumers makes the law only as honest as the consumer table, which is LAT's own risk 4 | **5**: exact guards with an iff completeness law (§5.8 both directions), the seal partition law and `reseal_is_seal`. It adds the constructive undo law `undoing_the_last_command_replays_the_log_without_it` with its refutation twin, and closes gap 44 with proved twins |
| **Latency at a 3-year log** | **3**: a 10–50 ms windowed call is plausible. But the all-time `Agg` grows about 100–150 KiB a year. Old-date verbs and every refusal resend the whole log in one call (≈ 440 MiB RSS at 3 y, at the measured 63 MiB of RSS per MiB of request). And an undo refused inside the 2-day tail refuses again on every call | **5**: the only design that measured the real wire (22 ms per MiB, 63 MiB RSS per MiB, gap 44 on arrays of objects). Its snapshot grows with ids, not days. Old-date reads never replay, the rebuild is chunked and bounded, and the tree-map twin is gated on a measurement | **4**: reaches the right conclusion (windowing is mandatory), but on a proxy that includes `loadPlan` and reads 7–8× slower than the direct measurement. A ≈ 330 KB checkpoint, a 108 KB reach index and 512–1,024 lines on every call is ≈ 12 ms at the measured rate: fine, not lean. Old dates read sealed month files |
| **Migration safety** (never two readers for more than one commit) | **3**: the Rust replay stays until S8. But S8 packs the host switch, the raw-walk replacement, the consumer moves and ≈ 220 test moves into one 8–12-day step, with no pre-switch seams and no differential test against the in-tree Rust | **2**: S7 moves `Ctx` onto kernel facts while `since_break_min`, `idle`, `idle_since`, `tm log`, `undo.rs` and `fit_replay` keep parsing the log in Rust until S8–S9. That is two readers across three steps | **5**: the only design that states the invariant per commit. The Rust seams move to one chokepoint first; T5 compares field by field against the in-tree Rust; one atomic switch decodes into the same `Replay`; and it is revertable because the cache is derived |
| **Total cost** | **3**: the smallest law set (≈ 40 goals, 6–9.5 k proof lines), priced at 10–14 weeks. It omits the Rust seam work it would hit at S8 | **3**: 3,700 definition lines and 12–18 k proof lines priced at 3–5 weeks. That price is not credible at the library's 4.80 : 1, and the ledger, pending verdicts and back-up add real surface | **2**: the most expensive, at ≈ 4,200 definition and ≈ 16,000 proof lines. The exact reach index, gaps 42–44 and 13 Rust seam commits are all extra. Priced at 6–8 weeks |
| **Fidelity to D9's one reader** | **4**: the kernel is the only reader and every fact is ported. But printing raw file lines in `tm log` changes that verb's output without flagging it, and `unknown` drops `rest`, which `tm log` prints | **3**: one reader at the end, two during the transition. `hsw` reaches Rust as a num/den division, an ulp-level parity exception. `recur` and `review` logic changes to fit the compaction | **4**: one reader; `hsw` stays lexical (serde reads the same characters); observations are ordered by source line (exact); `renderLine` feeds `tm log`. It narrows "every replay fact" to facts something reads (flagged), and keeps two zone evaluators until stage 6 |
| **total** | **17** | **17** | **20** |

**The winner's spine is MIG's.** Latency and cost are recoverable by grafts; migration safety and proof
strength are not. LAT's measured numbers are the latency budget's base. PROOF's algebra is the proof
route.

**The critique changed no score.**
- Two of its blockers trace to a LAT idea the first draft dropped: the fold bounded by the request's
  instant. That idea is grafted back as G-w.
- The third blocker (the law cannot see compacted window facts) sat in the synthesis, not in any input
  design.
- Its memory finding (CRIT 10) strengthens LAT's latency score's caveat, not its number.

---

## 2. Synthesis: the spine, the grafts, and what was rejected

### 2.1 Grafts (each is used below, and marked where it lands)

| # | graft | from | lands in |
|---|---|---|---|
| G-a | Phases, the one-reader invariant per commit, the `Ctx::replay_of` chokepoint, T5 (kernel against in-tree Rust, field by field), and one atomic switch into the same `Replay` | MIG §0, §11 | §14 spine |
| G-b | Gap 44 closed at the source by proved accumulating twins, extended here to every recursion over a wire-sized list | MIG S0.1; CRIT 10 | §14 A1, rule D9-21 |
| G-c | `JVal.dec` with an unconditional round trip; gaps 42 and 43 fixed toward serde; a decimal refused by the reader of the field | MIG §4.2, PROOF §2.1 | §5.1 |
| G-d | The `finiteF64` check matching serde's out-of-range failure, applied to every numeral serde materialises | PROOF §2.4; CRIT 15 | §5.4 |
| G-e | The chrono `parse_rfc3339` port details (leap second, fraction digits, fallback) | PROOF §2.3 | §5.3 |
| G-f | The zone table at second precision over [1900, 2200), cached by `IANA_TZDB_VERSION`; the probe is hourly | MIG §5.3; CRIT 11 | §6.1 |
| G-g | `local_dt`'s gap rule ported literally, used by D10 | PROOF §3.1, fork `capacity::local_dt` | §6.3 |
| G-h | The mask as a stack fold with `List.eraseP` (the spec), `survivors_snoc_event`/`_undo` as its characterisation, and a per-key fast twin behind `@[csimp]` | PROOF §4.1 + MIG §6.1 | §7.1 |
| G-i | The undo law `undoing_the_last_command_replays_the_log_without_it`, generalised here to interleaved housekeeping, and the silent-verb defect | MIG §6.2, §6.3; CRIT 12 | §7.3, OWNER Q6(d), Q6(f) |
| G-j | The machine as **effect lists**, each effect naming the key it writes, so the frame lemma is one generic theorem | MIG §7.1 + LAT §7.1 `Touch` | §8.2 |
| G-k | The fact catalogue split by what reads each fact: checkpoint aggregates, a current-period window, open days, sealed records. Per-id aggregates grow with ids, not days | LAT §7.2, §8 | §8.4 |
| G-l | The seal rule and the **no-loop law**; LAT's `pending` verdicts become a `settled` set of unfolded undos that cancel nothing in the suffix | LAT §8.4, §6.2 | §9.4 |
| G-m | Never sealing past the undo stack's reach (14-day cap) | LAT §8.5 | §9.6 |
| G-n | The chunked genesis rebuild. Its back-up pops **exactly** to the checkpoint a refusal names, not by exponential guessing | LAT §8.8; MIG §8.3's reach idea, reduced to one line per tag | §9.7 |
| G-o | The `Std.TreeMap` `@[csimp]` twin, gated on a measurement | LAT S6b | §14 W4 |
| G-p | `resume_is_replay` stated over the checkpoint **after `jemit` and `readCkpt`** | LAT §11 | §15 |
| G-q | `TM_KERNEL_ID` invalidation; crash-safe write order | LAT §8.6 | §9.8 |
| G-r | Sealed per-month files that a reseal *replaces* per day, never merges; here immutable and generation-named, with a manifest in the checkpoint file | MIG §8.5; CRIT 7 | §9.8 |
| G-s | Observations carry their source line, so Rust restores the fork's exact order; `slept` is bound late | MIG §7.5 | §11.2 |
| G-t | `resume_from_empty_is_replay`: a full replay is the same code path | PROOF §1 | §15 |
| G-u | The `view` honesty cheat: a view that forgets a fact must break the witness | LAT §11–12 | §16 |
| G-v | All of LOOK, re-based onto step 3's `Capacity.lean`, with E7 and hours since wake computed in real seconds through D9's zone table | LOOK + this pass; CRIT 6 | §13 |
| **G-w** | **The fold bounded by the request's day**: `F = min (T − keepDays) (maxDay − keepDays)`, and nothing is ever sealed past `now` | LAT §8.4 (i) `F' = dayOf at − 1`; CRIT 1 | §9.1, §9.4 |

### 2.2 Rejected, with the reason

| rejected | from | why |
|---|---|---|
| The log as one JSON string that the kernel splits | PROOF §0.1 | Rust already splits bytes for line numbers, the digest and the UTF-8 check. Once gap 44 is closed, an array of line strings costs the same (MEASURED 22 ms/MiB either way, LAT §1.1) and needs no second line splitter |
| An instant-partition split `H` (every tail line at or after a midnight) | PROOF §1, §6 | It refuses every retro event behind `H`, including a late `tm break`. Stored wakes plus a sealed-day guard admit those exactly (§9.3) |
| Observations re-ordered by `(day, line)` | PROOF §5.2 | Carrying the source line gives the fork's order exactly (G-s), so no exception is needed |
| `JMode`, a two-mode parser | LAT §4.2 | A mode parameter is a second grammar with a switch. Refusal by the reader keeps the wire's behaviour with one grammar |
| Pages of ≤ 4,096 everywhere | LAT §3.1 | It works around gap 44 at every array instead of closing it (G-b) |
| An append-only ledger `.jsonl` | LAT §8.6 | After a fallback a seal must *replace* a span. Generation-named month files replace it atomically (G-r) |
| Seam check per call, full digest only at seal | LAT §8.6 (its Q1) | It changes *when* a hand edit to an old line takes effect. The full digest per call keeps fork behaviour at an affordable cost (§18.2). The seal-time digest stays a recorded lever |
| An exact `(tag, id)` reach index in every checkpoint | MIG §8.3 | It is ≈ 108 KB parsed on every call. One line per tag (`tagLast`, ≤ 89 entries) names an exact rebuild point for id-less undos and a sound one for the rest (§7.4) |
| A ladder of monthly checkpoints | MIG §8.7 | Chunked genesis with exact pops is bounded and simpler, and a refusal names its line |
| The proxy figure of 170–190 ms/MiB | MIG §2.1 | It includes `loadPlan` over prose lines. LAT's direct `oneshot` measurement is used, and the harness (A3) replaces both |
| LOOK L1–L2 (types, EDF) | LOOK §8 | Built by step 3. A second `DayCap`/`edf` would be AGENTS §5.3's bug |
| LOOK's whole minutes since wake | LOOK §4.3 | Exact only for whole-minute wakes. Today's wake keeps seconds (CRIT 6). Hundredths from seconds (site R11) are exact always, and delete LOOK's range-key exception |
| **A chunked back-up** (resend from the popped checkpoint in `CHUNK`-sized calls) | CRIT 10's fix | It can loop. A fold of the chunk holding an undo's target cannot see the undo in the next chunk, so it folds the target again and the next chunk refuses again. Exact pops plus a per-call memory cap with a named fault are used instead (§9.7, §21) |
| **Refusing `tm close day` for old dates** | CRIT 2, option 2 | It is a behaviour change, and unnecessary. Sealed window records answer any old date exactly (§9.1) |

### 2.3 How D10 is ordered against D9 and against stage 6's pieces

```
step 3 (Capacity.lean, EDF) ── landed (fea3f81) ── nothing waits on it any more
D9  A1 gap 44 + TR rule → A2 JDec, gaps 42, 43 → A3 harness
    B1 Cal time+tz → B2 Stamp → B3 Log grammar → B4 wire (grammar only) + tz_table.rs
    R-audit, R1…R14 Rust seams (any time, one commit each; Rust stays the only reader)
    C1 mask → C2 day index → C3–C5 machine → C6 facts/obs/headers → C7 undo law      (T5 against in-tree Rust)
    W1 codecs → W2 seal/resume laws → W3 wire+genesis+files → W4 tree-map twin (gated) → W5 measurement gate
    S  the switch, fit included (one commit) → F2… decision families with their tranches

D10 L1 mixture ──────────────┐
    [needs B1] L2 E7 → L3 cut ┤→ L5 lookahead → L6 capacity on the wire (closes gap 77) → L7 parity twin
    [needs B1] L4 energy+limit┘   → L8 wiring + Rust unit reserves, jointly with the priority wiring
    [needs S]  L9 day 0 in the kernel
```

- **D10's L1 and L3–L7 run in parallel with D9's C and W.** They touch disjoint modules
  (`Lookahead.lean` against `Replay.lean`/`Seal.lean`), and `Check.lean` edits stay serialised
  (AGENTS §6.3).
- **L2 and L4 wait for B1**, D9's zone arithmetic. The window and hours since wake are then computed in
  the fork's real seconds, and DST days need no parity exception. If the owner wants D10 sooner than B1
  can land, both may use civil time and record the conditional exception P28 (§17). They must move onto
  `instantOf` when B1 lands.
- **Stage 6 shrinks** by E7, the slot cut and `predict` (LOOK's ≈ 2 weeks). `dayPlan` must reuse
  `cutSlots` and `futureEnergy`, never a second copy.

---

## 3. Decisions taken inside D9 and D10, with reasons

### 3.1 D9: architecture

- **D9-1: one reader per commit, read strictly.** Kernel log code may exist in the repository before
  the switch as library code that only tests call. `Tree.lean`'s `remainingMin` had the same status at
  step 1, and it is not a reader of the user's log until the switch commit.
  - *Reason:* AGENTS §5.3 is about two definitions deciding one answer in the shipped binary.
  - A differential test that holds both definitions is how the switch is proven safe (T5). It is not an
    instance of the bug.
- **D9-2: the log crosses as `lines : [string | null]` plus `terminated : bool`, and Rust splits bytes.**
  - Rust splits on `\n`, drops exactly one trailing empty segment when the file ends in `\n`, sends
    `null` for a segment that is not UTF-8, and sends `terminated = false` when the last segment has no
    `\n`.
  - The kernel owns trimming `\r`, blank lines, JSON and every warning. It never folds an unterminated
    last segment (§9.4 (vi)).
  - *Reason:* G9 is I/O and stays in Rust (PLAN §4). Anything about a line's content is the log's
    grammar, and D9 makes that the kernel's. Line numbers are physical positions: one definition used by
    warnings, `tm undo` and `tm log`.
- **D9-3: one JSON grammar, widened visibly (§5.1).** Config decimals keep step 1's `Nat`-pair route, and
  a request field read as a `Nat` refuses a `dec` by the field's name.
  - *Reason:* the log carries `hsw` (`0.95`, `-0.5`) and unknown payloads with any number. A second
    reader for log JSON would be AGENTS §5.3's bug. AGENTS §8.3 names visible widening as the sanctioned
    route.
  - Step 1's sentence "`JVal` is not widened" was about config decimals, and those still do not use it.
- **D9-4: gaps 42 and 43 are fixed toward serde (§5.1).** In D9 the kernel's JSON replaces serde's as the
  log's reader, so matching serde removes two parity exceptions instead of adding them. Both are behaviour
  rows (§20).
- **D9-5: gap 44 is closed first (A1).** A genesis chunk is 8,192 elements, and `docs` already grows
  toward the band.
- **D9-6: instants and offsets (§5.2).**
  - An instant is UTC `(sec, ns)` since 0001-01-01, matching `Cal.Day`'s origin, so
    `Instant.sec / 86400` is a `Day`.
  - An offset is a sign plus seconds below 86,400.
  - *Reason:* `close_sub` truncates `num_minutes` of a nanosecond difference, `hours_since_wake` rounds
    whole seconds, and zone offsets before 1970 have seconds.
- **D9-7: the zone is a host table, probed hourly (§6).**
  - *Reason:* the zone is a fact about the world (AGENTS §5.5), not a tm concept, and the kernel keeps one
    reader of `t`.
  - Offsets written in the log alone would change `day_index_wake_to_wake`, and a tzdb port would be data
    nobody maintains.
  - The probe is hourly because a daily probe misses an A→B→A change inside one UTC day (CRIT 11).
- **D9-8: faithful port of the oracle's semantics, quirks included.**
  - That covers both first-wake rules, file-order instances against instant-order `last_done`, site R8's
    per-sub-segment truncation, the silent-verb undo, the housekeeping-close undo and saturating widths
    (as `Nat`, P17).
  - *Reason:* parity against the fork point is the stage's acceptance.
  - Each quirk gets a theorem that separates it from its alternative, and each is offered to the owner as
    a later behaviour change (OWNER Q6). None is taken silently.
- **D9-9: the machine is `effects` then `applyEffects` (§8.2).**
  - Every effect names its key: a day, an item-day, an item, a done date, an instance, a named event, the
    machine or a global counter.
  - **Every effect and every line header that carries a day names `Key.day`** (CRIT 9).
  - *Reason:* windowing needs "a step touches only the keys it names". With effects as data that is one
    generic theorem, not 26 lemmas, one per arm.
- **D9-10: windowing is a guarded checkpoint of the fold, anchored to `now` (§9).**
  - The horizons are:
    - the request's day `T` (the existing wire field `now`, which is `Ctx::today`);
    - the cut `c`;
    - the ledger day `L`;
    - the window horizon `H = min (monthStart L) (isoMonday L) (L − 16)`.
  - G4 refuses a request with `T < L`, and a reseal never seals past `T − keepDays`.
  - *Reason:* the whole-log kernel call measured ≈ 180 ms and 520 MiB at 3 years (§18). The latency test
    must stay green, and answers about today must never depend on how the log's last line is dated
    (CRIT 1).
  - `16` is `AUTO_CLOSE_CATCHUP`, so every date housekeeping can close lies in the window.
- **D9-11: undo across a checkpoint uses `tagLast` plus a `settled` set (§7.4).**
  - `tagLast` holds, per tag present among folded survivors, the line of the latest one.
  - `settled` holds the lines of unfolded undos that cancel nothing in the unfolded suffix: either their
    whole-log target is already folded and cancelled, or they dangle.
  - A tail undo that dangles in the tail, is not settled, and names a tag in `tagLast` refuses
    `undoReach {line, below = tagLast[tag]}`.
  - *Reason:* constant size on every call. The refusal names an exact rebuild point for an undo without an
    id and a sound one otherwise. The seal no longer has to hold the cut below an unfolded undo's target,
    which removes CRIT 19's 30-day pin.
- **D9-12: genesis is chunked, with exact pops and a per-call memory cap (§9.7).**
  - Chunks are 8,192 lines or 1 MiB, whichever comes first. *(Superseded at W3 by gap 102's measurement: 8,192 lines or 1,536 KiB, chunks of 4,096 lines or 768 KiB; README "Stage 5 D9 W3".)*
  - A refusal pops to the newest checkpoint that its named bound admits.
  - A resend over 32,768 lines or 4 MiB is the named fault `reachTooFar` (OWNER Q9 (iii)). *(Superseded at W3 by gap 102's measurement: 8,192 lines or 1,536 KiB, chunks of 4,096 lines or 768 KiB; README "Stage 5 D9 W3".)*
  - *Reason:* per-call RSS stays ≤ 256 MiB at any log age, on a machine with no swap.
- **D9-13: finished records are sealed into Rust-stored month files (§9.8).**
  - **Day records** are written for days `< L`, and **window records** (item-day minutes, done dates,
    date-keyed instances) for days `< H`.
  - **Who reads them:** Rust reads them for history (reviews, the fit, `lounge_rate`, `tm log`). The
    kernel reads a sealed record back **only** for a query that names an explicitly old date (`tm close
    day <date>` once the close tranche is in the kernel), and the host checks the record's generation
    against the checkpoint in hand. A kernel decision about today reads only the checkpoint.
  - *Reason:* old-date verbs must not pay a replay that grows with age. Reading kernel output back is the
    checkpoint's own trust category, not a second reader, and law 1 makes each record exact.
  - OWNER Q3 confirms storage and read-back.
- **D9-14: integrity is a full-prefix FNV-1a-64 on every call**, plus `prefixBytes ≤ file length`,
  `prefixBytes` ending right after a `\n`, a tz key, a format version and `TM_KERNEL_ID`.
  - *Reason:* it keeps the fork's semantics that a hand edit anywhere takes effect on the next command.
  - A seal-time digest is a recorded lever that would need the owner.
- **D9-15: observations carry their source line, `hsw` stays lexical, and `slept` is bound late
  (§11.2).** Each gives the fork's exact value and order with no exception.
- **D9-16: Rust stays the writer for D9 (OWNER Q5).** `Event: Serialize` and `LogEntry::to_json` stay,
  guarded by T2.
- **D9-17: `tm log` and `tm undo` read kernel headers, renderings and display text (§11.4).**
  - `undo_target`, `compensating_undo`, `DayIndex::bounds`, `wake_of`, `events_for`, `stamps` and
    `parse_timestamp` have no callers outside `log.rs`, so they are deleted at S, not ported.
- **D9-18: tests move with the reader.** At R12 the 45 tm-core call sites (18 files) and the 3 tm test
  modules call one helper, `replay_of_text(text, tz)`. At S the tm-core ones move to `tm/tests/` and the
  helper calls the kernel. No `tm-core → tm-kernel-ffi` Cargo edge is added (R7).
- **D9-19: presentation over kernel facts stays in Rust.** That covers `DayReplay::gaps`,
  `wake_to_arrive_min`, the review monitors, `now`/`state.break_` clamping, and `arrivals_from_replay`'s
  time-of-day extraction. *Reason:* plan §3.6 calls these "definitions, not theorems". Gap entry in §20.
- **D9-20: tm-core keeps reading `&Replay`; the host fills it per verb family (§11.1).**
  - `Ctx::replay_with(scope)` builds the reshaped `tm_core::log::Replay` from the checkpoint's answer,
    merged with the sealed records the scope needs. Scopes are `Hot`, `Dates(from, to)` and `All`.
  - No tm-core function signature changes.
  - *Reason:* tm-core cannot reach the tm crate's file I/O (CRIT 4), and a lazy trait would add a second
    access path to every reader.
- **D9-21: every recursion over a list the wire can make large has a tail-recursive twin behind
  `@[csimp]`, or is a `foldl`** (CRIT 10).
  - The list covers `jparse`/`jemit`/`splitDoc` (A1), `readLine` over `lines`, `survivors`, `keptWakes`,
    the effects fold, the association-list updates, the header and record emitters, `readCkpt`'s list
    decoders, `wallOverlap`'s range and `lookahead`'s days.
  - T0 checks the rule end to end on a 2 MiB thread.
- **D9-22: a future-dated line is folded and fenced, never a pin (§9.4).**
  - A line is future-dated when `localDate t > T + 2`. It is exempt from the fold's recency condition.
  - Its instant enters `futureFloor`, not `maxT`, and G2 refuses a tail wake within 2 days before it.
  - *Reason:* a clock-skewed device or a `--now` typo must neither corrupt today's facts nor grow the tail
    without bound (CRIT 1). Whether `tm check` names such lines is OWNER Q9 (ii).
- **D9-23: a reseal that did not advance anything is not repeated the same day (§9.6).** *Reason:* a
  stall must not rewrite the checkpoint on every TUI reload (CRIT 19).
- **D9-24: an unwritable cache degrades to an in-memory checkpoint with a named notice (§9.8).**
  *Reason:* a read-only synced viewer must not pay genesis silently on every verb (CRIT 26).

### 3.2 D10

- **D10-1: build on step 3's `Capacity.lean` and never restate it.**
  - The lookahead's output is `List DayCapacity` with `den = capDen`, checked by step 3's `lookaheadOf?`.
  - The bin reads `Grant.availQ` through `Priority.binOfScaledQ`, and `binOfScaledQ_congr` makes the
    denominator unobservable.
- **D10-2: `capDen` is one constant, sized by OWNER Q8.** The build takes Q8's recommendation, `10^18`,
  unless the owner answers otherwise.
  - A weight is `w ≤ capDen`, decoded from Rust's decimal pair only when `den ∣ capDen`.
  - Unit counts cross the wire as digit strings from L6 onward, whatever the answer, so the host never
    narrows a numeral.
  - The host holds units in `u128`.
  - *Reason:* `the_bin_does_not_see_capDen` makes the constant a one-line change, and strings make R10's
    2^53 bound hold by construction.
- **D10-3: mix after each location's budget limit.** D10 says "expected minutes", and the expectation is
  taken over the day each location would have. Mixing first gives a different answer, pinned by
  `mixing_before_the_budget_is_not_the_expectation`.
- **D10-4: the kernel applies the model-then-config fallbacks** (`Model::p_lounge_on`,
  `Model::expected_arrival_on`). Rust sends both raw. *Reason:* a host-side pick between two readings is
  what AGENTS §5.6 forbids.
- **D10-5: E7 is restated to overlap semantics and refuted as written.** `Goals.lean` STAGE 6's
  `wallsInside` counts walls wholly inside the window. The fork clips, merges and counts overlap, and the
  fork is the oracle.
- **D10-6: pull the general slot cut, `predict` with the home cap, and the budget limit forward from
  stage 6 (OWNER Q2).** The limit is a per-level greedy, proved equal to the fork's per-slot sort.
- **D10-7: parity through a threshold twin.** The kernel runs with each weight forced to `0` or `capDen`
  (`2w ≥ capDen`) and must equal fork `lookahead × capDen` exactly. The real run is checked against the
  twin's bounds.
- **D10-8: emit the first `min(days, 7)` days, and priorities carry exact pairs.** Every display integer
  is the floor of **its own** exact value, never derived from other displayed integers (OWNER Q4).
- **D10-9: day 0 is a host histogram until L9**, recorded as a gap. From L9 (after the switch) the
  kernel derives it.
- **D10-10: site R3 is reopened.** `windowMin = halfUpQ (60 · windowHours)` is a kernel-owned half-up
  site, and `Arith.lean`'s row is corrected in L2.
- **D10-11: hours since wake are exact hundredths from whole seconds, site R11 (§13.3).**
  - `hsw100 s = sign s · ((|s| + 18) / 36)` for `s` whole seconds, as `(s / 36.0).round()` computes (ties
    away from zero, and no representable quotient lies within an ulp of a tie).
  - `bucket = min 11 (hsw100 / 100)` when `hsw100 > 0`, else 0.
  - A range key `num/den` compares as `hsw100 · den` against `100 · num`.
  - *Reason:* today's wake keeps seconds (CRIT 6). This is exact against the fork for every input, which
    deletes LOOK's range-key exception.
- **D10-12: every Rust reserve over capacities works in exact `u128` units** (`planner.rs`'s week loop,
  `tui/queue.rs`), with floors only at display, until those consumers move into the kernel (§13.8).
  *Reason:* D10 forbids rounding inside the EDF, and a floored second reserve would be AGENTS §5.3's bug
  twice.
- **D10-13: the lookahead covers at most 3,660 days** (`lookaheadTooLong` beyond). A `due:` later than
  that reads the capacity of the first 10 years (P30). *Reason:* R10 needs a bound, and it keeps every
  emitted unit count within `u128` and every day count below 2^53.

### 3.3 Readings of the owner's own words taken here (flagged; object and they change)

| wording | reading taken | why | cost if read the other way |
|---|---|---|---|
| D9: "Rust keeps **only** the statistical fit" | Rust may **store and read back** kernel-emitted observations and sealed records (§9.8), and keeps review *presentation* arithmetic over kernel facts | storing kernel output is persistence (G9's side), not derivation. The alternative makes every old-date verb replay | OWNER Q3 asks directly |
| D10: "carried through the EDF pass" | Carried through step 3's `edf`, **after** each location's budget limit | §3.2 D10-3 | — |
| PLAN §4 G9 (verdict M) | Torn-line repair and per-line tolerance of invalid UTF-8 are G9's planned fix | the fork's own `Log::parse_bytes` is the designed tolerance, and the CLI never called it | behaviour rows P13 and P19. **Where warnings show is not a reading: OWNER Q9** |

"Every replay fact" and "exact numerator/denominator pairs" appeared here in the first draft. They are
owner questions now (Q7, Q8), because reading them narrowly changes what is derived or what is accepted.

---

## 4. Genuinely new owner questions

Nine questions. Each has a recommended default so the build is not blocked, but taking a default is
still the owner's call. "Blocks" names the first step that must not start without an answer (or an
explicit "take the default").

### Q1: The price. Confirm it, or narrow the scope.

**The situation.** D9 was chosen "knowing the stated costs", which quoted a port of about 1,500 lines
of `log.rs`. That figure counts only the fork's definitions. Most of the cost is elsewhere:
- the proofs D5 requires, since the window laws cannot be downgraded;
- the wire, the grammar and the zone;
- gap 44 and the tail-recursion rule;
- the Rust seams;
- the fixes the completeness review forced: the anchoring to `now`, the sealed window records, the
  generation files, the future-line fence and the exact units in Rust.

**ESTIMATE (§14.9).** Agent-days are shown, but the stage-4 pace makes them unreliable, so compare lines.

| tranche | definitions | proofs | agent-days |
|---|---:|---:|---:|
| D9 | ≈ 5,300 | ≈ 19,450 | ≈ 97–126 |
| D10 | ≈ 1,250 | ≈ 3,850 | ≈ 27–40 |
| **total** | **≈ 6,550** | **≈ 23,300** | **≈ 124–166** |

For comparison, the stage-4 audit put the whole library at 3,917 definition and 18,815 proof lines
(AGENTS §4, D5's row). The plan priced all of stage 5 at 3–4 weeks.

**The options.**
- **(a) Confirm, and run the two tracks in parallel** (§2.3).
- **(b) Confirm, but D10 first.** The capacity mixture ships on the Rust replay (L1–L8), and D9 follows.
- **(c) Narrow.** These levers change the cost without touching the substance of D9 or D10:
  - the Rust-histogram interim for D10 (Q2): −2 weeks now, +2 in stage 6;
  - leave gap 42 open as a parity exception: −3 days;
  - defer `tm log`'s history path: −3 days. Old-range `tm log` would then pay a chunked scan whose
    latency grows with age.

  The window laws and the undo law cannot be narrowed under D5.

**Recommendation:** (a). **Blocks:** scheduling only.

### Q2 (D10): Stage 6's window, slot cut and energy prediction. Move them into stage 5?

**The situation.** To mix lounge and home capacity for a future day, something must compute each
location's per-level minutes. That needs:
- §8.1's window (E7);
- §8.2's slot cut;
- future-day `predict` with the home cap;
- the budget limit.

The plan puts all of these in stage 6.

**The options.**
- **(a) Pull them forward.**
  - The kernel computes both histograms from the tree, the config and the fitted model (as data).
  - It keeps one reader of walls, so gap 45's comment-blind Rust parser does not decide capacity.
  - ESTIMATE ≈ 2 weeks more now, ≈ 2 weeks less in stage 6.
- **(b) Rust sends two `[u32; 6]` per future day** (fork `lookahead` with the location forced), and the
  kernel only mixes and runs the EDF.
  - It saves ≈ 2 weeks in stage 5.
  - It adds a Rust summary format, and Rust's wall reading stays authoritative until stage 6.

**Recommendation:** (a). **Blocks:** L2.

### Q3 (D9): The derived replay cache. Allow it, allow the kernel to read it back, and decide whether synced plans carry it

**The situation.** Windowing needs files beside the Markdown database, under `.tm/cache/replay/`:
- **`ckpt.json`**: the kernel's opaque checkpoint, Rust's integrity metadata, and a manifest naming the
  current month files.
- **`sealed/YYYY-MM.g<gen>.json`**: immutable month files, each holding two kinds of record exactly as
  the kernel emitted them:
  - finished **day records**: day facts, energy and duration observations, demotions, and line headers
    for `tm log`;
  - finished **window records**: item-day minutes, done dates and date-keyed routine instances.
- **`tz.json`**: the probed zone table.

**Who reads them.**
- **Rust reads them back** for old-date reviews, the fit, `lounge_rate`, `estimate_calibration` and
  `tm log` history.
- **The kernel reads one back** only when a query names an explicitly old date. Today that is
  `tm close day <date>` once the close tranche is in the kernel. Law 1 proves each record equals the
  replay's.

Deleting the directory is always safe, because the next command rebuilds it (T9). `tm undo` never
touches it. Upgrading tm rebuilds it once: ≈ 1–4 s on the first command after an upgrade, at 3 years of
log.

**Three things to confirm.**
- **(i)** That *storing and reading back* kernel output fits D9's "Rust keeps only the statistical fit".
  This design reads it as persistence, not derivation.
- **(ii)** That the kernel may read a sealed record back for an old-date query. This is the same trust
  the checkpoint already needs (named beside G9), and it is not a second reader.
- **(iii)** Whether a plan directory synced by git or Dropbox carries the cache:
  - **(a) Excluded from sync.** `tm init` writes a `.gitignore` line for `.tm/cache/`. A merged
    `log.jsonl` invalidates the checkpoint anyway, through the digest.
  - **(b) Carried.** Harmless, because a mismatch triggers a rebuild, but noisy in diffs and racy under
    Dropbox.

**Recommendation:** yes to (i) and (ii); (a) for (iii). **Blocks:** W1, which freezes the record
formats.

### Q4 (D10): What `--json` shows for capacities that are no longer whole minutes

**The situation.** These fields become exact rationals:
- `tm plan --week --json`: `days[].minutes_at_level: [u32;6]` and `total`;
- the priorities output and the TUI: `Prio.avail_min`, `allocation_min` and `shortfall_min`.

**The options.**
- **(a) Keep the integer fields as documented floors, and add `…_exact: {num, den}` beside them.**
  Each integer is the floor of its own exact value. `total` is `floor(Σ exact)`, not `Σ floor`. So
  `avail_min − allocation_min` may differ from `shortfall_min` by one, and the documentation says so.
- **(b) A breaking change to pairs.**
- **(c) Integers only**, with the exact values hidden.

**Recommendation:** (a). **Blocks:** L8.

### Q5 (D9): Who writes log lines?

**The situation.** After D9 the kernel is the only reader, but Rust's serde (`LogEntry::to_json`) still
writes every appended line. That is two definitions of one format, held together by T2 (byte identity
of every writable `Event`).

**The options.**
- **(a) Keep the Rust writer for D9 and record the gap.**
- **(b) Appending verbs send typed events, and the kernel returns the lines to append.** ESTIMATE ≈ 1–1.5
  weeks, best done after the switch.

**Recommendation:** (a). **Blocks:** nothing.

### Q6: Oracle quirks. Port them faithfully now, and say which to fix later

**The situation.** Parity is the stage's acceptance, so the default ports every row faithfully. Each row
gets a theorem separating it from its alternative, and a gap. Fixing a row later is a behaviour change
with its own parity entry.

| # | quirk | effect today | what a fix would change | recommendation |
|---|---|---|---|---|
| (a) | **Two "first wake" rules.** Day attribution keeps the earliest wake *by instant* per run of one date; `DayReplay.wake`/`slept_min` and `slept_by_day` keep the first wake *in file order* | differ only when wakes are appended out of time order | unify on earliest by instant | fix later |
| (b) | **Two "latest" rules.** Routine instance records keep the last *in file order*; `last_done` keeps the latest *by instant* | differ on a retro append | unify on instant | keep: they answer different questions |
| (c) | **Site R8.** `close_sub` truncates minutes per sub-segment, so a block paused *k* times loses up to *k* minutes | a small under-credit | floor the block's total | fix later |
| (d) | **The silent-verb undo.** `tm undo` of a recorded `move`/`readopt` on an id-less line, or of a `close` that closed nothing, writes `undo{of:<verb>}`, which cancels an *older* event of that tag | no decision fact changes today; `tm log` hides the older line | write `of:"verb:<name>"` for silent verbs, which changes the bytes appended | fix, after the switch |
| (e) | **The multi-day wall.** `window_and_budget` clips walls only at the arrival, so a Monday 09:00–Wednesday 17:00 wall counts Wednesday evening on two days | inflated future capacity | bound the window to its day | fix later |
| (f) | **Housekeeping between a command and its undo.** `Event::Close` has no id. Say `tm close week` writes closes, and a later verb's `auto_close` appends another close. A `tm undo` of the week close then writes `undo{of:"close", id:null}`, which cancels the **automatic** close, not the week's | the automatic close's report vanishes from `tm log`, and the week close's stays; no decision fact reads closes today | give `close` a primary id (`period:key`), which changes the bytes written | fix, after the switch |
| (g) | **Two definitions of "today".** `Ctx::today` is the calendar date in `cfg.tz`; the replay's days are wake-attributed. At 00:30, before a new wake, `replay.day(today)` is empty and tonight's blocks sit on yesterday | `blocks_done(today)` reads 0 after midnight until the next wake | define today as the replay's day of `now` | keep until stage 6 moves `now` into the kernel; decide then |

**Recommendation:** as in the last column. **Blocks:** nothing.

### Q7 (D9): "Derives every replay fact." Port the fields nothing reads, or delete them?

**The situation.** These fork `Replay` fields have no reader and appear in no output, by grep:
- `ItemReplay.{stops, extended_min, done_at, partial_done_at}`;
- `Replay.{closes, dropped_items, open_interrupt}`;
- the global `longest_leak`, and the interrupts beyond each day's lost and dropped minutes;
- `DayReplay.{replans_today, last_plan_hash, loc_changes, dropped}`.

D9's words are "derives every replay fact". Deleting these fields before the port (step R11) narrows
that, and after the switch no Rust replay exists to re-derive them. Restoring them later means a kernel
port plus a rebuild of every sealed record.

**The options.**
- **(a) Delete them from Rust's `Replay` in R11, before the port.** Parity entry P22. Nothing visible
  changes.
- **(b) Port them.** The kernel derives them, and they go into the sealed day records, not the
  checkpoint. ESTIMATE ≈ 300 definition lines, ≈ 900 proof lines and witnesses, 4–6 agent-days. Sealed
  records grow ≈ 15%.

**Recommendation:** (a), because an unread fact is parity surface with no user. **Blocks:** R11 and W1,
which freezes the record formats.

### Q8 (D10): How precise may `p_lounge` be?

**The situation.** D10 carries the lounge weight as an exact fraction. The fork accepts any `f64` in
`model.json`, and spec §8.5 invites hand edits ("hand edits become the new prior"). The fit writes
two-decimal values, but a hand edit can write `0.3333333`. The kernel needs one denominator `capDen`
dividing every weight's decimal denominator.

**The options.**
- **(a) `capDen = 10^6`.**
  - A weight with more than 6 decimal places is refused by name.
  - The host fails every verb that computes capacity, naming the file and key: `model.json:
    p_lounge.Mon = 0.3333333 has more than 6 decimal places`.
  - Units fit `u64`.
- **(b) `capDen = 10^18`.**
  - Only more than 18 decimal places, or a value outside [0, 1], is refused. The shortest `f64` text of a
    lounge probability never needs more places unless it is below 10^-18.
  - The host holds units in `u128`, and unit counts cross as digit strings. ESTIMATE +1–2 agent-days.
- **(c) Round to 6 places when `model.json` loads, with a notice.** A new rounding site outside the
  mixture. D10 forbids rounding only inside the mixture, but this still changes the weight used.

**Recommendation:** (b), because it keeps the fork's acceptance of hand edits with no rounding.
**Blocks:** L6.

### Q9 (D9): A damaged or hand-edited log. What shows, and what happens at the extremes?

**The situation.** The fork fails **every command** when `.tm/log.jsonl` has an invalid UTF-8 line, and
silently skips other malformed lines (the CLI never calls `parse_bytes`, so nothing prints them). Under
D9 every such line is a named warning, and the verb runs (G9's planned fix). But nothing shows the
warnings, so a corrupt line would go from loudly fatal to invisible. There are three sub-questions.

**(i) Where do log warnings show?**
- **(a) `tm check` lists each warning line** as a warning-level problem (`log.jsonl:950: not UTF-8`).
  The exit code is unchanged. The kernel keeps up to 256 named warnings in the checkpoint plus an
  overflow count.
- **(b) (a), plus a one-line stderr notice** on any verb whose request surfaced a new warning.
- **(c) Silent,** with only a count.

**(ii) Future-dated lines.** A line dated more than 2 days after `now` (a wrong device clock, a `--now`
typo) is folded correctly and fenced (D9-22). Should `tm check` name it?
- **(a) Yes, as a warning.**
- **(b) No.**

**(iii) Beyond the rebuild's memory bound.** Some line may be so far out of place that no rebuild can
window around it within 32,768 lines or 4 MiB in one call: a hand-written undo whose target is further
back, a retro wake, or a retro line into a sealed day. *(Superseded at W3 by gap 102's measurement: 8,192 lines or 1,536 KiB, chunks of 4,096 lines or 768 KiB; README "Stage 5 D9 W3".)*
- **(a) A named fault.** Every verb except `tm check` fails with `log.jsonl line N reaches M lines back;
  move or delete it`, and `tm check` reports it as an error.
- **(b) Raise the cap for that rebuild, with a notice.** This risks an OOM on a swapless machine, ≈
  250 MiB per 4 MiB of log. *(Superseded at W3 by gap 102's measurement: 8,192 lines or 1,536 KiB, chunks of 4,096 lines or 768 KiB; README "Stage 5 D9 W3".)*

  CLI-written logs cannot reach this bound: the undo stack's reach is ≤ 50 commands, and retro CLI
  lines fall within `keepDays`. It is a hand-edit outcome.

**(iv) For information, not a choice unless you want one.** `tm log` prints a hand-appended unknown
event's numerals as written (`1.50`, `1e3`), where the fork re-serialises them through serde (`1.5`,
`1000.0`). Lines tm writes are unaffected (T2). Porting serde's float printing for hand-written lines
only is not worth its cost (P29); say so if it is.

**Recommendation:** (i)(a), (ii)(a), (iii)(a). **Blocks:** S for (i) and (iii); nothing for (ii).

**Not owner questions** (settled above, or behaviour is unchanged):
- the zone table (D9-7);
- `tagLast` and `settled` (D9-11);
- the 14-day cap on the undo reach (§9.6);
- R10 widths (§10.4);
- the full digest per call (D9-14);
- the observation order, which is exact;
- torn-line repair (G9);
- site R11 (exact);
- the future-line fence (D9-22), whose visibility is Q9 (ii);
- today's-day unification, which is Q6(g), kept as a gap.

---

## 5. The typed event grammar

### 5.1 JSON: `JVal` widened once (`Json.lean`, step A2)

```lean
namespace Tm
/-- A JSON numeral that is not a bare natural, kept exactly as written.  Never evaluated. -/
structure JDec where
  neg  : Bool                    -- a leading '-'
  int  : Nat                     -- the integer digits' value (leading zeros refused: gap 43)
  frac : List (Fin 10)           -- the fraction digits, verbatim; [] iff no '.' was read
  exp  : Option (Bool × List (Fin 10))   -- 'e'/'E', a negative exponent?, the exponent DIGITS (never a value; §5.4)
deriving DecidableEq, Repr
def JDec.plain (d : JDec) : Bool := !d.neg && d.frac.isEmpty && d.exp.isNone
inductive JVal
  | null | bool (b : Bool) | num (n : Nat)
  | dec (d : { d : JDec // d.plain = false })   -- the widening (AGENTS §8.3: visibly, in a diff)
  | str (s : List Char) | arr (xs : List JVal) | obj (kvs : List (List Char × JVal))
```

**The rules.**
- `jparse` returns `.num n` exactly when the numeral has no sign, no fraction and no exponent.
  Everything else is `.dec`.
- `jemit (.dec d)` writes `-`, the integer digits, `.` and the fraction digits verbatim, then `e`,
  `-` if negative, and the exponent digits.
- `1E+05` reads to the same `JDec` as `1e5`. The exponent keeps its digits, so `1e0005` re-emits as
  written (K18).
- The exponent is stored as digits, not as a `Nat` value, so no reader can build `10^e` from a
  13-character numeral by accident (CRIT 14). §5.4's `finiteF64` is the only function that looks at
  its size.

**What is proved in A2.**

| theorem | what it says |
|---|---|
| `jparse_jemit` | re-proved **unconditionally** over the widened `JVal` |
| `jparse_reads_a_plain_numeral_as_num` | a bare natural is still `num` |
| `jparse_reads_a_signed_decimal_as_dec` | witness `-0.5` |
| `jparse_refuses_a_leading_zero` | gap 43: `01` gives the new `JErr.leadingZero` |
| `junescape_reads_a_surrogate_pair`, `junescape_refuses_a_lone_surrogate` | gap 42 |

**Renamed under the stage-4 pattern.** `jparse_refuses_what_the_fragment_has_no_type_for` is false after
widening. Its refutation is `jparse_reads_what_the_fragment_had_no_type_for` (`-3`, `1.5` and `1e3` now
parse). Beside it goes the law that keeps the wire honest,
`a_request_number_that_is_not_a_nat_is_refused_by_its_reader`: `"blockMin":1.5` gives `badBlockMin`.

**Behaviour rows (§20):**
- a request carrying `-3` or `1.5` is still refused, now by the field's name instead of
  `bad json: …`;
- leading zeros are refused;
- a surrogate pair is read.

`kernel_bridge::refusal`'s tests pin `expectedKey`, `unterminatedObject` and the surrogate refusal. The
last of these is split into "a pair is read" and "a lone surrogate is refused" (MIG §4.2).

**Sequencing.** A1 and A2 edit `Json.lean`. They start only after the in-flight stage-5 core has
committed (§14.0).

### 5.2 Instants and offsets (`Cal.lean`, step B1)

Clock arithmetic belongs in `Cal.lean` (AGENTS §8.3's trap). Day-valued results are typed `Nat`
(the `omega` trap).

```lean
namespace Tm.Cal
structure Instant where sec : Nat; ns : Nat      -- UTC, seconds since 0001-01-01T00:00:00Z
deriving DecidableEq, Repr
/-- chrono's leap-second representation: ns may reach 1,999,999,999 only on second 59 of a minute. -/
def Instant.wf (i : Instant) : Bool := i.ns < 2000000000 && (i.ns < 1000000000 || i.sec % 60 == 59)
                                        && i.sec < 315537897600                 -- year ≤ 9999 (R10)
abbrev VInstant := { i : Instant // i.wf = true }
def Instant.nanos (i : Instant) : Nat := i.sec * 1000000000 + i.ns
instance : LT Instant := ⟨fun a b => a.nanos < b.nanos⟩     -- chrono orders (secs, frac) lexicographically; equal here
structure Offset where west : Bool; sec : Nat               -- ±HH:MM[:SS]; UTC is ⟨false, 0⟩
def Offset.wf (o : Offset) : Bool := o.sec < 86400
abbrev VOffset := { o : Offset // o.wf = true }
/-- chrono 0.4.45 `DateTime::signed_duration_since`, ported with its leap-second adjustment
    (`NaiveTime::signed_duration_since`: a leap nanosecond counts only when the other side is not in
    the same leap second).  Signed, as whole seconds plus nanoseconds. -/
def durationBetween (a b : Instant) : Int × Int
/-- `num_minutes` of `b − a`, truncated toward zero; `.max(0)` as in `close_sub`. -/
def minutesBetween (a b : Instant) : Nat
/-- `num_seconds` of `b − a`, truncated toward zero, signed (`hours_since_wake`, site R11). -/
def secondsBetween (a b : Instant) : Int
def subMinutes (t : Instant) (m : Nat) : Instant          -- idle's `t − min`; saturates at the origin
```

**Proved in B1:**
- `minutesBetween_truncates` (119 s gives 1);
- `minutesBetween_zero_of_le`;
- `secondsBetween_truncates_toward_zero` (−59.5 s gives −59);
- `Instant.lt_iff_nanos`;
- `mkInstant?_refuses_a_bad_nanosecond`;
- `durationBetween_across_a_leap_second`: chrono's own documented examples for
  `signed_duration_since` with a `:60` second, as witnesses (CRIT 29).

T5 adds one generated case with a `:60` stamp inside a block (§14.4).

### 5.3 The timestamp grammar (`Stamp.lean`, step B2; imports `Cal`, `Line`)

`parseStamp : List Char → Except StampErr (VInstant × VOffset)` is a port of chrono 0.4.45
`format::parse::parse_rfc3339`, followed by `parse_timestamp`'s fallback. It reuses
`Field.parseDate` and `Field.parseClock`'s digit readers, so there is no second date grammar
(AGENTS §5.3).

1. At least 19 bytes. `YYYY-MM-DD`, validated by `Cal.Date` validity. Otherwise `StampErr.badDate`.
2. The separator is `T`, `t` or a space.
3. `HH:MM:SS` with hour ≤ 23 and minute ≤ 59. Second `60` is accepted as second 59 plus 10^9 ns
   (chrono's leap rule).
4. An optional `.` and one or more digits. The first 9 digits count; the rest are skipped.
5. The offset: `Z`, `z` or `±HH:MM` (HH ≤ 23, MM ≤ 59), then end of input.
6. **The fallback**, taken only when steps 1–5 fail: `%Y-%m-%dT%H:%M%:z`, with no seconds.

Instant = local time minus offset. A local time whose offset would put it before the origin is
`StampErr.beforeOrigin`.

**Every edge is pinned by T3 before B3 freezes the grammar.** T3 compares against chrono's own parser:
separators, 0–12 fraction digits, `:60`, `-00:00`, `24:00`, year `0000`, padding and spaces in the
fallback. Any residue is parity entry P23, never a guess.

`renderStamp : VInstant → VOffset → List Char` is `fmt_timestamp`: whole seconds, `±HH:MM`, and
`+00:00` for UTC. `displayStamp` is the human `tm log` column (`YYYY-MM-DD HH:MM` in the written
offset, fork `e.t.format("%Y-%m-%d %H:%M")`), so Rust never parses a stamp (§11.4).

**Proved in B2:**
- `parseStamp_renderStamp`, on whole seconds and whole-minute offsets;
- `renderStamp_is_fmt_timestamp`, with witnesses `2026-09-07T06:05:00-05:00` and a UTC stamp;
- `stamp_order_is_the_instant_order`: `2026-09-08T03:00:00+00:00` equals `2026-09-07T22:00:00-05:00`.

### 5.4 Events (`Log.lean`, step B3; imports `Json`, `Stamp`)

These are the 25 `define_events!` tags in `EVENT_NAMES` order, plus `unknown`. Field names and serde
types are the fork point's (inv §1). The widths are serde's accepted ranges, not the semantic ones:
- `U8 := Fin 256`;
- `U32 := Fin 4294967296`.

Strings are bounded by the line bound (`lineTooLong_bounds_every_string`, R10).

```lean
namespace Tm.Log
abbrev Id := List Char
inductive Num | nat (n : Nat) | dec (d : { d : JDec // d.plain = false })   -- `hsw`, lexical
inductive Event
  | wake      (sleptMin : U32) (onsetMin : Option U32)
  | arrive    (loc : List Char) (window : List Char × List Char) (budget : U32)
  | start     (id : Id) (pred : U8) (rep : Option U8) (hsw : Num) (sleptMin : U32) (loc : List Char)
              (blocksDone : U32) (sinceBreakMin : U32)            -- the last two decoded, never read by replay
  | done      (id : Id) (estMin actualMin : U32) (went : Option U8) (tags : List (List Char)) (ci : U8) (isPartial : Bool)
  | extend    (id : Id) (byMin : U32)
  | stop      (id : Id) (remainingMin : U32)
  | brk       (plannedMin : U32) (actualMin : Option U32) (where_ : Option (List Char))   -- tag "break"
  | energy    (pred rep : U8) (hsw : Num) (loc : List Char)
  | interrupt (id : Option Id)
  | resume    (lostMin : U32) (dropped : List Id)
  | pause     (id : Id) | unpause (id : Id)
  | idle      (attributed : List Char) (min : U32)
  | routine   (item inst status : List Char) (actualMin : Option U32)
  | skip      (item inst : List Char)
  | plan      (hash : List Char) (replansToday driftMin : U32)
  | named     (name : List Char) (id : Option Id)                 -- tag "event"
  | demote    (id : Id) (from_ to : List Char) (estMin : U32)
  | readopt   (id : Id) | move (id : Id) (from_ to : List Char) | drop (id : Id)
  | edit      (id : Id) (field from_ to : List Char)
  | note      (text : List Char) | loc (loc : List Char) | close (period key : List Char)
  | undo      (of_ : List Char) (id : Option Id)
  | unknown   (tag : List Char) (rest : List (List Char × JVal))   -- rest sorted by key (serde's Map order)
structure Entry where line : Nat; t : Cal.VInstant; off : Cal.VOffset; ev : Event   -- `at` is a tactic keyword
def Event.tag : Event → List Char            -- `Event::name`
def Event.primaryId : Event → Option Id      -- `Event::primary_id`; unknown: rest["id"] when a string
def Event.isUndo : Event → Bool
def Event.isStateChange : Event → Bool       -- ported for completeness of the grammar; the mask does not read it
```

`unknown` keeps `rest`, because `tm log` prints unknown lines (§11.4).

**Field decoding** is strict per kind. It follows `Event`'s hand-written `Deserialize` (inv §0.2) and
this table:

| JSON at a field | `U8`/`U32` field | `Option _` field | `String` field | `hsw` (`Num`) | `window` |
|---|---|---|---|---|---|
| absent | `#[serde(default)]` field: 0; otherwise `missingField k` | `none` | default `[]`/`false` if defaulted, else `missingField k` | default `nat 0` | `missingField` |
| `null` | `badField k` | `none` | `badField k` | `badField` | `badField` |
| `.num n` in width | `n` | `some n` | `badField` | `nat n` | `badField` |
| `.num n` out of width | `badField k` | `badField` | `badField` | `nat n` | `badField` |
| `.dec d` | `badField k` (**pinned by T1**: serde's verdict on `-0`, `3.0`) | `badField` | `badField` | `dec d` | `badField` |
| a string, array or object | `badField k` | `badField` | the string / `badField` | `badField` | exactly two strings, else `badField window` |
| a key repeated | **last one wins** (default; pinned by T1 against serde's `Map` collection, residue P24) | same | same | same | same |

**`finiteF64`, applied to every numeral in the line, at any depth, known or unknown** (G-d, CRIT 15).
- **Why every numeral.** Fork `impl Deserialize for Event` first collects the whole object as
  `Map::<String, Value>::deserialize`. Every numeral anywhere in the line becomes a
  `serde_json::Number` before any field is read, and one out of `f64` range fails the whole line.
  An `unknown` line with `"x":1e400` is therefore a **warning** in the fork, not an entry.
- **The check** runs in `readLine` right after `jparse`, over every `num` and `dec` in the tree. A
  failure is the line warning `numberOutOfRange`.
- **Its cost is bounded by the line, never by a numeral's value** (CRIT 14). For a numeral with
  mantissa digits `m` (leading zeros dropped), fraction length `f` and exponent digits `x`:
  - `m = 0` is finite (serde gives `0.0`);
  - `x` longer than 6 digits: a positive exponent is not finite, a negative one is finite (underflow).
    `|m| ≤ 65,536` digits cannot bring a 7-digit exponent back into range;
  - otherwise `k = digits m − f ± value x` (an `Int` of at most 7 digits). `k ≤ 308` is finite and
    `k ≥ 310` is not;
  - `k = 309` compares exactly: `m · 10^(±x − f) < 2^1024 − 2^970`. The power has at most
    `309 + 65,536` digits, bounded by the line.
- **The band is serde's, not IEEE's.** serde_json without `float_roundtrip` parses decimals on its own
  fast path. T1 pins the `k ∈ [308, 310]` band on crafted values before B3 freezes; any residue is
  P25.

### 5.5 Lines, warnings and tolerance (`Log.lean`, step B3)

```lean
inductive LWarn
  | invalidUtf8 | lineTooLong | lineTooDeep | notJson (e : JErr) | numberOutOfRange | notAnObject
  | noT | badT (e : Stamp.StampErr) | noEv | evNotString
  | missingField (k : List Char) | badField (k : List Char)
inductive Verdict | blank | entry (e : Entry) | warn (line : Nat) (w : LWarn)
def maxLineChars : Nat := 65536
def maxLineDepth : Nat := 64
def readLine (n : Nat) : Option (List Char) → Verdict
def renderLine : Entry → List Char     -- serde's writer: `{"t":…,"ev":…,<fields>}`, skip_serializing_if as define_events!
```

`readLine n seg` runs these checks in order (a port of `Log::parse_bytes`):
1. `seg = none` is `invalidUtf8`.
2. Trim one trailing `\r`.
3. If the line is blank after trimming Unicode `White_Space` (Rust's `str::trim` set, tabulated as data
   per AGENTS §5.5), return `blank`.
4. More than `maxLineChars` characters is `lineTooLong` (P14).
5. Bracket nesting deeper than `maxLineDepth`, found by a pre-scan, is `lineTooDeep` (P14). `jparse`
   still recurses per nesting level after gap 44's fix, so this bound is what keeps it on the stack.
6. `jparse` failing with `e` is `notJson e`.
7. Any numeral failing `finiteF64` is `numberOutOfRange` (§5.4).
8. Not an object is `notAnObject`.
9. `t` missing is `noT`; not a string or not a stamp is `badT`.
10. `ev` missing is `noEv`; not a string is `evNotString`.
11. A known tag decodes strictly (§5.4). A bad payload is a warning, never `unknown`.
12. Any other tag is `entry (unknown tag rest)`.

A routine event with an unknown status is not a line warning. It is the replay warning
`unknownInstanceStatus (line)`, and the instance is treated as `Pending` (§8.3).

**Where warnings go.** The checkpoint keeps the first 256 folded line warnings plus an overflow count
(§9.2), and each call returns its tail's. Whether and where the user sees them is OWNER Q9 (i). The
default is that `tm check` lists them.

**Proved in B3** (every `decide` witness is a short literal of ≤ 90 characters, probed first under
`MemoryMax=8G timeout 120`):
- `the_log_reads_what_it_renders` (Goals, discharged in B3);
- `a_known_event_is_never_read_as_unknown`;
- `an_unknown_tag_is_never_a_warning`, under the hypothesis that every numeral is finite;
- `an_out_of_range_numeral_warns_even_in_an_unknown_event` (witness `{"t":…,"ev":"mood","x":1e400}`);
- `lineTooLong_bounds_every_string`;
- `finiteF64_reads_only_the_digit_counts_beyond_seven_exponent_digits` (the cost bound above);
- one witness per `LWarn` constructor, `every_line_warning_is_reachable`, from
  `tests/fixtures/logs/malformed.jsonl`'s lines: `wake` without `slept_min`, `est_min:"sixty"`,
  `"ev":7`, a top-level array, an unparseable `t`, `{"ev":"mood","level":3}` read as unknown;
- `the_malformed_corpus_reads_as_the_fork_point_did`, all verdicts, proved **per line**, each line its
  own `theorem` over a literal of ≤ 90 characters. The `White_Space` table is reached through
  `simp only [isWhite]` rewrites, never unfolded under `decide` (CRIT 13).

Corpus-sized agreement is a cargo test (T1), never a `decide`.

### 5.6 Small grammars

- **`parseInstanceStatus`**: `done | pending | missed | expired | skipped | skip`, anything else
  `none`.
- **`instDate?`**: exactly 10 characters of `%Y-%m-%d`, read through `Field.parseDate`.
- **`stampFromKey`**: an ISO week key through `Line.lean`'s existing week reader, else a date, else
  `none`. It must not add a second week reader. If `IsoWeek::parse` accepts forms the kernel's reader
  does not, that is a finding for B3 to record, not something to paper over.

---

## 6. Time zone and day attribution

### 6.1 The zone table: Rust probes it, the kernel reads it

**Rust** (`tm/src/cli/tz_table.rs`, new in B4, ≈ 110 lines):
- For `cfg.tz`, sample `tz.offset_from_utc_datetime(dt).fix().local_minus_utc()` at **every UTC hour**
  in [1900-01-01, 2200-01-01): ≈ 2.63 million probes.
- Where two consecutive samples differ, bisect to the second (≤ 12 probes each).
- Record the offset in force at 1900-01-01T00:00:00Z as `base`. For `America/Chicago` that is
  `-06:00:00` (it left LMT in 1883).
- ESTIMATE ≈ 500 transitions for Chicago, ≈ 20 KB on the wire, and 0.1–0.3 s of probing once per
  `(zone, tzdb version)`. A3 measures it.
- Cache it in `.tm/cache/replay/tz.json`, keyed by `(cfg.tz name, chrono_tz::IANA_TZDB_VERSION, span)`.
  chrono-tz 0.10.4 does not export its spans (a_head), so probing is the only route.

**The stated assumption.** Hourly sampling misses a zone whose offset changes and changes back inside one
hour (A→B→A). No such pair is known in tzdb, but the design does not rely on memory:
- T4 (c) sweeps the five test zones at **minute** resolution over [1900, 2200) as an `#[ignore]`d test,
  run at B4 and recorded in the README;
- T4 (d) checks every table transition at −1 s, 0 and +1 s against chrono, for **every** chrono-tz zone,
  over [1970, 2100), as an `#[ignore]`d test run at B4;
- risk K10 remains, with its lever (a quarter-hour probe for a zone T4 (d) flags).

**The kernel** (`Cal.lean`, B1):

```lean
structure TzTable where
  key   : List Char                        -- "America/Chicago|2025b|1900-2200": enters the checkpoint
  base  : Offset                           -- in force before the first transition
  trans : List (Instant × Offset)          -- strictly increasing; each offset in force from its instant
def TzTable.wf (z : TzTable) : Bool          -- key ≤ 128 chars; instants wf and strictly increasing; offsets wf; ≤ 4096 transitions
abbrev Tz := { z : TzTable // z.wf = true }
def mkTz? (z : TzTable) : Option Tz          -- the only constructor the decoder uses (R10)
def offsetAt (z : Tz) (t : Instant) : Offset                 -- last transition ≤ t, else base
def localSec (z : Tz) (t : Instant) : Nat                    -- t.sec ± offsetAt (saturating at the origin)
def localDate (z : Tz) (t : Instant) : Nat := localSec z t / 86400
```

- Outside the table's span the edge offset applies (P16). Every instant tm writes falls inside.
- The kernel never interprets `key` beyond comparing it.
- `offsetAt` over ≤ 4,096 transitions is a `foldl` (D9-21). A binary-search twin behind `@[csimp]` is
  W4's lever if A3 shows it matters.

**Proved in B1:**
- `offsetAt_reads_the_last_transition`, in both directions: before the first transition, and exactly
  at one;
- `localDate_is_constant_between_transitions`;
- `mkTz?_refuses_an_unsorted_table`;
- witnesses on a four-transition Chicago table: `2026-03-08T07:59:59Z` is 2026-03-08 at −06:00 and
  `08:00:00Z` is at −05:00; `2026-11-01T06:59:59Z` is at −05:00 and `07:00:00Z` at −06:00;
  `2026-09-08T03:00:00+00:00` is 2026-09-07.

### 6.2 The day index (`Replay.lean`, step C2)

```lean
namespace Tm.Replay
def keptWakes (z : Cal.Tz) (ws : List Cal.Instant) : List Cal.Instant   -- `DayIndex::new`
  -- (ws.mergeSort (·.nanos ≤ ·.nanos)) then CONSECUTIVE dedup keeping the first of a run with equal localDate
def lastWakeLe (kw : List Cal.Instant) (t : Cal.Instant) : Option Cal.Instant   -- `last_wake_before`
def dayOf (z : Cal.Tz) (kw : List Cal.Instant) (t : Cal.Instant) : Nat  -- `day_of`
  -- match lastWakeLe kw t with | some w => if t.nanos < w.nanos + 86400·10^9 then localDate z w else localDate z t
  --                             | none   => localDate z t
def keptFrom (z : Cal.Tz) (last : Option Cal.Instant) (ws : List Cal.Instant) : List Cal.Instant  -- continue a dedup run
def firstLoggedWakeOn (z : Cal.Tz) (kw : List Cal.Instant) (es : List Log.Entry) (d : Nat) : Option Log.Entry
```

**Porting trap.** `dedup_by` is consecutive, so `keptWakes` is "earliest per *run* of one date", not
"earliest per date". The two differ when local dates are non-monotone in instant (a DST fold at
midnight). Name this in the module header. T5 generates the case (§14.4).

**Proved in C2:**
- `dayOf_is_the_wake_date_within_a_day`;
- `dayOf_without_a_recent_wake_is_the_local_date`;
- `a_wake_day_is_shorter_than_a_day`;
- the four cases of `day_index_wake_to_wake` as witnesses, with instants as `Nat` literals
  (≈ 6.4·10^10, which `Nat.decEq` handles), no text parsing, and each probed under the 8 GB cap;
- `keptWakes_append_of_later` and `dayOf_agrees_below_a_later_wake` (the locality W2 needs, §9.5);
- `the_kept_wake_is_not_the_first_logged_wake` (quirk Q6a, gap 82).

**Not ported:** `DayIndex::bounds`, `wake_of` and `local_midnight` (no callers outside `log.rs`).

### 6.3 `instantOf`: the fork's `local_dt`, for D10 (`Cal.lean`, step B1)

```lean
/-- `capacity::local_dt`: the instant of local (day, clock) in `z`.  Single → it; ambiguous → the
    earliest; in a gap → the first valid local time 1..180 minutes later (earliest); else read the
    local time as UTC (`from_utc_datetime`). -/
def instantOf (z : Tz) (d : Nat) (c : Clock) : Instant
```

**Proved in B1:** `instantOf_localSec`, the round trip on an unambiguous time; a DST-gap witness
(Chicago 2026-03-08 02:30 gives 03:00 CDT); and a fold witness (2026-11-01 01:30 gives the earlier
of the two instants).

### 6.4 Time that stays in Rust (a recorded gap), and the tests that tie the two evaluators

- `ctx.today`, `ctx.now` and every display conversion (`with_timezone(cfg.tz)`) stay in chrono until
  stage 6 moves `now` into the kernel (gap 90).
- **Two definitions of "today" survive** (CRIT 20): `Ctx::today` is the calendar date of `now` in
  `cfg.tz`, while the replay's days are wake-attributed. At 00:30, before a new wake, `replay.day(today)`
  is empty. This is fork behaviour, offered as OWNER Q6(g) and recorded as gap 87.
- `review.rs` `lounge_rate`'s `.hour()` reads the *written* offset's hour, which is fork behaviour.
  Decoded instants therefore keep the written offset.
- **Chrono and the table are two zone evaluators, tied together by T4** (CRIT 11):
  - (a) 10,000 random instants over [1970, 2100) in each of Chicago, Berlin, Kolkata (+05:30), Chatham
    (+12:45) and Lord Howe (30-minute DST);
  - (b) every table transition of those five zones at −1 s, 0 and +1 s, over the whole span;
  - (c) the minute sweep of §6.1 (`#[ignore]`, run at B4);
  - (d) every chrono-tz zone's transitions at ±1 s over [1970, 2100) (`#[ignore]`, run at B4).
- **The day-attribution edge cases the owner named are T5 generator cases** (§14.4): a wake at 01:30
  on the fall-back day with the ambiguous hour used twice; a wake after midnight whose previous wake is
  under 24 hours old; events 23–25 real hours after a wake across both transitions; a date where
  consecutive dedup differs from earliest-per-date; one day with mixed written offsets (`-05:00` then
  `+02:00`); `cfg.tz` different from the writer's `Local`.

---

## 7. Undo

### 7.1 The mask (`Replay.lean`, step C1)

```lean
def matches (of_ : List Char) (id : Option Log.Id) (e : Log.Entry) : Bool :=
  e.ev.tag == of_ && id.all (fun x => e.ev.primaryId == some x)
/-- The survivor stack, most recent first.  An undo removes the first (= most recent) match and never enters. -/
def maskStep (st : List Log.Entry) (e : Log.Entry) : List Log.Entry :=
  match e.ev with
  | .undo of_ id => st.eraseP (matches of_ id)
  | _            => e :: st
def survivors (es : List Log.Entry) : List Log.Entry := (es.foldl maskStep []).reverse
def dangles (es : List Log.Entry) (u : Log.Entry) : Bool      -- u is an undo and `eraseP` found nothing at its step
def survivorsFast (es : List Log.Entry) : List Log.Entry      -- per-tag and per-(tag,id) stacks of lines, lazy deletion
@[csimp] theorem survivors_eq_survivorsFast : @survivors = @survivorsFast
```

**Why this is `undo_mask`.** At step *i* the stack holds exactly the entries *j < i* that are neither
cancelled nor undos, most recent first. So "the greatest *j < i* that is uncancelled, not an undo, with
the name and id matching" is the first stack element that matches. Undos never enter the stack, so an
undo of an undo always dangles and there is no redo. The mask ignores `isStateChange` and time
(inv §2.2).

**The fast twin** replaces a lookback that is O(n²) on a hostile log. The proofs stay on the spec, as
with `parentRef_eq_parentRefFast`. Both are `foldl`s, so neither recurses per line (D9-21).

**Proved in C1:**
- `survivors_snoc_event`, `survivors_snoc_undo` (Goals, §15);
- `an_undo_never_survives`;
- `a_cancelled_event_is_never_revived`;
- `a_dangling_undo_dangles_in_every_extension`;
- `an_undo_of_an_undo_cancels_nothing`;
- `the_mask_ignores_isStateChange` (witness: `undo{of:"note"}` cancels a note);
- `undo_mask_pairs_and_dangling_ported`: the fork test's `[T,T,T,T,T,F,T]` with dangling `[4,6]`,
  built from `Entry` values, not text.

### 7.2 What `tm undo` gets

- **`Recorder::start`** records the physical line count from the same byte split the request uses.
  It replaces `log_len`'s non-blank count, so a malformed line no longer shifts the recorded events
  (P18).
- **Housekeeping is outside the recording.** `Ctx::load` runs `horizon::auto_close` before any verb's
  `Recorder::start`, so its closes are not part of the command. §7.3's law accounts for them.
- **`Recorder::finish`** reads the kernel's `headers` for lines after `start`: `(line, tag, primaryId)`.
  These come from `Event.tag` and `Event.primaryId`, the same functions `matches` uses, so an undo
  `tm undo` writes is matched by construction.
- **`UndoEntry`** gains `log_line : Option<u64>`, the first line its command appended. The seal policy
  reads it (§9.6).
  - The stack lives in `.tm/undo.json` (`UNDO_PATH`, `MAX_ENTRIES = 50`), not in `state.json`.
  - An entry written before R6 has no `log_line` and reads as `None` (CRIT 27).
- **`undo` itself does not change.** It appends `undo{of,id}` per recorded event, most recent first,
  restores bytes and `state.json`, runs the conflict guard, pops the stack and reloads.
  `move_has_no_inverse_command` stays the reason undo is replay.

### 7.3 The undo law, with housekeeping in between (Goals, step C7)

**Why the law needs a middle part `M`** (CRIT 12). A command's events are not always the log's last
lines when it is undone:
- `Ctx::load` runs `horizon::auto_close` as housekeeping **before** any verb's `Recorder::start`, and it
  appends `close` events.
- `tm now`, `tm plan` and the TUI append without an `UndoEntry`.
- The stack spans up to 50 commands.

So `tm undo` of command X sees `L ++ E ++ M` and appends `undosFor E`, where `M` holds events X did not
write.

```lean
def undosFor (E : List Log.Entry) (n : Nat) (t : Cal.VInstant) : List Log.Entry   -- one `undo (tag e) (primaryId e)` per e, most recent first, at lines n, n+1, … with stamp t
/-- No event of `M` is an undo, and none matches the pattern of any undo `tm undo` writes for `E`. -/
def untouchedBy (E M : List Log.Entry) : Bool :=
  M.all (fun m => !m.ev.isUndo && E.all (fun e => !matches e.ev.tag e.ev.primaryId m))
theorem undoing_a_command_replays_the_log_without_it (z : Cal.Tz) (L E M : List Log.Entry) (n : Nat) (t : Cal.VInstant)
    (hE : E.all (fun e => !e.ev.isUndo) = true) (hM : untouchedBy E M = true)
    (hl : Log.linesIncreasing (L ++ E ++ M ++ undosFor E n t) = true) :
    factsView (replay z (L ++ E ++ M ++ undosFor E n t)) = factsView (replay z (L ++ M))
```

**Why it holds.** Taken most recent first, each undo finds its own event:
- every later event of `E` is already cancelled;
- `hM` rules out `M`.

The surviving wakes are then those of `L ++ M`, so the day index is too, and the fold sees exactly the
survivors of `L ++ M` in file order. `factsView` omits the line bookkeeping (entry count, headers),
which appending changes. The first draft's `M = []` law is the corollary
`undoing_the_last_command_replays_the_log_without_it`.

**Its two refutation twins** are the quirks in Q6(d) and Q6(f):
- `undo_of_a_silent_verb_cancels_an_older_event`: `L = [move "a"]`, `u = undo "move" none`; the survivors
  of `L ++ [u]` lose `L`'s move.
- `undo_after_housekeeping_cancels_the_housekeeping`: `E = [close week]`, `M = [close day]` (the
  automatic close), `undosFor E = [undo "close" none]`. The survivors are `L ++ E`, not `L ++ M`. This
  is live today, because `close` has no primary id.

T5 gains 64 generated `(L, E, M)` triples. Half satisfy `untouchedBy`, and those must meet the law. Half
violate it, and those must reproduce the fork's cancellation.

### 7.4 Undo across a checkpoint: `tagLast`, `settled`, exact rebuild points, and no loop

**A checkpoint stores:**
- **`tagLast`**: for each tag present among the folded survivors, the line of the latest such survivor.
  Up to 25 known tags plus 64 unknown ones, then `tagOverflow`.
- **`settled`**: the lines of *unfolded* undos that cancel nothing in the unfolded suffix, at most 1,024.
  An undo is settled for either of two reasons:
  - its whole-log target lies at or before the cut, and the call that folded that target already knew
    it was cancelled;
  - it dangles in the whole log.

**Guard G1, `undoReach {line, below}`.** Mask the tail alone, skipping settled undos. G1 refuses at the
first undo `u` that meets all three conditions:
- it dangles in that mask;
- its line is not settled;
- its `of` is in `tagLast`, or `of` is unknown and `tagOverflow` is set.

The refusal carries `below = tagLast[of]`, or 0 on overflow.

**Sound.** If G1 accepts, `survivors (a ++ b) = survivors a ++ survivorsSkipping settled b`. There are
three cases.
- **A tail undo whose target is in the tail** finds the same target in the whole log, because the
  greatest earlier surviving match lies in the tail when any does.
- **A tail undo that dangles in the tail with a tag absent from `a`'s survivors** dangles in the whole
  log.
- **A settled undo** cancels nothing after the cut. Its record is exact because `reseal_is_seal`
  computes it from the call-wide mask, and `a_cancelled_event_is_never_revived` keeps it true in every
  extension.

**The rebuild point is exact for an undo without an id.** Its whole-log target is the latest surviving
event of its tag, which is `tagLast[of]` when that event is folded. A rebuild from any checkpoint whose
cut is below `below` carries the target and the undo in one call.

**For an undo with an id it is sound.** The target is at or below `below`, but it may be older. A
refusal from the older checkpoint then names a strictly smaller `below`, because that checkpoint's
`tagLast[of]` is below its own cut, which is below the previous `below`. So the pops terminate at
`Ckpt.empty`, which never refuses (§9.7).

**Conservative.** A spurious refusal needs an undo carrying an id whose tag survives in the prefix while
its `(tag, id)` does not. It costs one pop, never a wrong fact (`a_spurious_tag_refusal_exists`).

**Loop-free.** A reseal adds to `settled` every unfolded undo whose call-wide target is folded or absent.
Every other unfolded undo targets an unfolded line. So the unfolded suffix passes G1
(`a_resealed_checkpoint_accepts_its_own_suffix`).

Unlike the first draft, **the seal no longer holds the cut below an unfolded undo's target.** CRIT 19's
30-day pin after a far undo is gone. The fold stops early only when `settled` would exceed 1,024.

---

## 8. The replay machine and the fact catalogue (`Replay.lean`, steps C3–C6)

### 8.1 State

The state is fork `Machine` (inv §2.4), with two storage changes that are not observable:
- **A block's pending start observation lives in the block** (`obs : Option EnergyObs`), not as an
  index into `energy`. A `done` writes `went` onto it. It is emitted when the block closes, or at
  `finish`, carrying its **start line**, so Rust's sort by line restores the fork's order (G-s).
- **`Cut.day` and the open interruption's day are computed when stored.** The fork recomputes
  `day_of(cut.t)` and `day_of(s)` later; within one index they agree
  (`cut_day_stored_eq_recomputed`). Storing them lets the checkpoint drop older wakes.

```lean
structure Block where id : Log.Id; started : Cal.Instant; startDay : Nat; since : Option Cal.Instant; paused : Bool
                      pausedAt : Option Cal.Instant; workedMin : Nat; obs : Option EnergyObs
structure Cut where id : Log.Id; t : Cal.Instant; day : Nat; min : Nat
structure Machine where block : Option Block; lastCut : Option Cut
                        interrupt : Option (Cal.Instant × Nat × Option Log.Id)
```

### 8.2 Effects, keys and the step

```lean
inductive Key
  | day (d : Nat) | itemDay (i : Log.Id) (d : Nat) | item (i : Log.Id) | doneDate (i : Log.Id) (d : Nat)
  | instDate (item inst : List Char) (d : Nat) | instOther (item inst : List Char)
  | named (name : List Char) (id : Option Log.Id) | machine | global
inductive Effect
  | dayAdd (d : Nat) (δ : DayDelta)             -- DayReplay's sums and records, segments, starts, breaks, idle, wake/arrive
  | header (d : Nat) (h : HeaderRec)            -- every entry's (line, tag, id?, cancelled, display), on its day
  | itemAdd (i : Log.Id) (δ : ItemDelta)        -- all-time minutes, blocks, done bit, lastDone (max by instant), doneDates first/count
  | itemDay (i : Log.Id) (d : Nat) (m : Nat) | itemDaySub (i : Log.Id) (d : Nat) (m : Nat)
  | doneDate (i : Log.Id) (d : Nat)
  | inst (item inst : List Char) (r : InstRec)  -- last in FILE order wins (overwrite)
  | named (name : List Char) (id : Option Log.Id) (t : Cal.Instant)   -- latest by instant
  | obs (o : Obs)                                -- carries o.day
  | machine (m : Machine) | global (g : GlobalDelta)   -- lastEffective, entryCount, unknown, warnings
def Effect.key : Effect → Key
  -- dayAdd d _ ↦ .day d;  header d _ ↦ .day d;  obs o ↦ .day o.day  (CRIT 9: every dated output names its day)
  -- itemDay i d _ / itemDaySub i d _ ↦ .itemDay i d;  doneDate i d ↦ .doneDate i d;  inst ↦ instDate or instOther
def effects (z : Cal.Tz) (kw : List Cal.Instant) (slept : List (Nat × Nat)) (st : State) (e : Log.Entry) : List Effect
def applyEffects (st : State) (fx : List Effect) : State
def step z kw slept st e := applyEffects st (effects z kw slept st e)
def replay (z : Cal.Tz) (es : List Log.Entry) : Facts :=
  let sv := survivors es; let kw := keptWakes z (wakeInstants sv); let slept := sleptByDay z kw sv
  finish z kw (sv.foldl (step z kw slept) State.init)
```

**Every line produces a `header` effect**, cancelled lines included (they are emitted by a second pass
over the whole list, not the survivors, with `cancelled := true`). So a retro `note`, `move` or
`unknown` dated into a sealed day names `Key.day d` and is refused by G3 or placed by genesis into the
right day record (CRIT 9).

`effects` is `Machine::step`, **one arm per constructor, all 26**. The helpers are ported by name:
`close_sub` becomes `closeSub`, `close_pause` `closePause`, `credit` `credit`, `uncredit_cut`
`uncreditCut`, `cut` `cut`, `mark_done` `markDone` and `segment` `segment`. The specification is inv
§2.4's table. **`range` is not ported:** the CLI only ever passes `None`.

**The arms of events whose facts nothing reads** (CRIT 21). Under OWNER Q7's default, `extend`'s only
fact (`extended_min`) is not derived, so its arm emits exactly `header` and `global`. It is still a named
arm with a witness, `an_extend_changes_only_the_bookkeeping`, and `every_known_event_has_an_arm` is a
theorem over the `Event` constructors, not a comment. `close`, `note`, `edit`, `move`, `readopt`,
`drop` and `loc` are the same shape where Q7 removes their facts. If the owner answers Q7 with (b), those
arms gain their `dayAdd`/`itemAdd` effects in C5.

**Proved in C3–C6:**
- `applyEffects_touches_only_named_keys` (the frame law, Goals);
- `every_known_event_has_an_arm`;
- `every_dated_output_names_its_day_key` (Goals, C6; CRIT 9);
- `credit_conserves_the_day_minutes`: `Σ minutesByCi + Σ ciUnknown = blockMin`;
- `load_is_exact_fifths`: `loadFifths = Σ min × min(ci, 5)`, site R9;
- site R8: `worked_minutes_floor_each_subsegment`, with its refutation twin
  `worked_minutes_is_not_the_floor_of_the_block` (two 90-second sub-segments give 2 minutes, not 3);
- witnesses for the rules a builder is tempted to "fix":
  - `a_start_cuts_any_open_block_even_the_same_id`;
  - `a_block_cut_by_start_is_never_replaced_by_done`;
  - `a_stop_then_done_replaces_the_cut_credit`;
  - `a_stop_for_another_id_is_ignored`;
  - `a_matched_done_discards_the_clock_minutes`;
  - `close_pause_does_not_clear_paused`;
  - `the_first_leak_maximum_wins`;
  - `a_retro_done_marks_done_and_credits_nothing`;
  - `a_later_pending_does_not_undo_a_done_date`;
  - `an_unknown_status_warns_and_is_pending`;
  - `a_demote_stamp_reads_the_week_or_date_key`;
  - `a_partial_done_credits_but_does_not_complete` and `a_partial_done_after_stop_replaces_the_cut`
    (CRIT 22; fork `uncredit_cut` ignores `partial`);
  - `an_extend_changes_only_the_bookkeeping`;
  - `idle_and_idle_since_read_different_orders` (CRIT 24; §8.4);
- `last_done_is_the_latest_by_instant`, `an_instance_is_its_last_record_in_file_order`, and
  `instances_and_last_done_order_differently` (quirk Q6b);
- `energy_obs_slept_is_the_days_first_logged_sleep` (late binding);
- `observations_are_in_file_order`, over each observation's source line.

Each witness is built from at most 8 `Entry` values with instants as `Nat` literals, and is probed
under `MemoryMax=8G timeout 120` before it is committed (§14.0, CRIT 13).

### 8.3 Replay warnings

`RWarn.unknownInstanceStatus (line : Nat) (raw : List Char)`. The instance is treated as `Pending`,
as fork `parse_instance_status` does. The message text is named, not formatted (P15).

### 8.4 The fact catalogue: every observable fact, who reads it, and where it lives

**Where a fact can live:**
- **A**: all-time aggregates in the checkpoint.
- **W**: window facts in the checkpoint, for dates `≥ H`.
- **O**: open days in the checkpoint (days `≥ L` touched by folded lines, future-dated days included),
  plus the tail's days.
- **DR**: sealed **day records**, for days `< L`.
- **WR**: sealed **window records**, for dates `< H`.

DR and WR are Rust-stored (§9.8). A kernel decision about today reads only A, W and O. A query naming
an explicitly old date reads DR or WR, and law 1 makes each record equal to the replay.

**R-audit** (§14.3) re-greps each accessor below and records its call sites in the README **before W1
freezes the formats**. Every accessor is named individually, not by family. If any consumer needs more
than the column gives, the family moves to the fuller form, never the other way.

| fact (fork accessor) | readers at `4748911` | lives in | form | size at 3 y (ESTIMATE, 900–3,000 ids) |
|---|---|---|---|---|
| `done_items`, `is_done` | recur (`is_done`), priority, reviews, `day_extras` | A | done bit per id | in the item record |
| `last_done(id)`, latest **by instant** | recur `after_done_state` | A | instant plus written offset | in the item record |
| `done_dates(id)`: `.first()` and `.len()` | `calendar_instances` anchor; recur `completion_count` and `next_ordinal` (`.len()`) | A (first, count of distinct dates) + W (dates `≥ H`, to deduplicate) + WR (older dates) | 2 numbers per id plus a day list | item record plus ≈ 3 KB |
| `ItemReplay.minutes`, `.blocks`; `done_minutes_map` | TUI queue, month review, progress | A | 2 numbers per id | item record |
| `block_minutes_on(id, d)` | `priority::done_this_period` (the current period, `≥ H`); `horizon::day_remaining` via `close_day`: auto-close dates `≥ T − 16 ≥ H`, and `tm close day <date>` for **any** date | W (`d ≥ H`) + WR (`d < H`) | `(id, d, min)` | W ≈ 5 KB (≤ 33 days); WR ≈ 0.3 KB per day |
| `block_minutes_on_day(d)` | reviews | O + DR (a day sum) | in `DayFacts` | — |
| `instances_of(item)`, last in **file order** | `logged_status`, `logged_instances`, `done_this_period`, `next_ordinal`, `completion_count` | W (date-keyed, date `≥ H`) + WR (older) + A (every non-date key) | a record | ≈ 7 KB + ordinals |
| `events_named(name)` / `events[name]` | `waiting_state`/`arrival_of` (max `t` over `id ∈ {none, key}` with date ≥ since), `collect_candidates` (names), `event_occurred` | A | latest instant per `(name, id?)`. Exact, because a `≥ since` filter commutes with max | ≈ 3.5 KB |
| `events_for(id)`, `stamps(id)` | **none outside `log.rs`** (grep, CRIT 23) | not derived | deleted at S | — |
| `DayReplay` of an open day | `wake_time`, `slept_min`, `today_slots`, `plans_today`, planner, status line, TUI | O | `DayRecord` | ≈ 2.5 KB per day × 2–3 |
| `DayReplay` of a finished day | reviews (day, week, month); `lounge_rate` (**every day**); `arrivals_from_replay`; `status_line`'s last-day fallback | DR | `DayRecord` | ≈ 2.5 KB per day, on disk |
| `energy`, `durations` | fit (all), `estimate_calibration` (**all durations**), `compare`, `calibration`, posterior (today) | O + DR | with source line | ≈ 13,000 records on disk; never on the hot path |
| `demotions` | reviews: by `t`'s **local date** in `day_review`; by `from` key in `month_review` | O + DR | with `t` and written offset | ≈ 1,550 on disk |
| `open_block`, `last_cut`, open interrupt | planner, `active_elapsed_min` | A (machine) | constant | < 1 KB |
| `days.keys().last` | `status_line` | A | `lastDay` | 1 number |
| **`lastEffective`** (`day::idle`) | `day.rs` `idle` | A | the `t` (instant plus written offset) of the **last survivor in file order**, of any kind | 1 instant |
| **`lastT`** (`app.rs` `idle_since`) | TUI | O | `DayFacts.lastT` = the **maximum** `t` over survivors of any kind (`plan`, `note` and `unknown` included) whose day is `d` | in `DayFacts` |
| since-break anchor, idle marks (Phase R seam facts) | `since_break_min`, `idle_min_since` | O | `DayFacts.sinceBreak`, `idleMarks` | in `DayFacts` |
| entry count; line headers `(line, tag, id?, day, cancelled, display)` | `tm log` (`total`, selection, human output), `undo.rs` | A (count) + O (headers of folded lines in open days) + tail + DR (headers of every entry, cancelled included) | numbers and a 16-character display | ≈ 1.6 MB on disk at 3 y |
| line warnings | `tm check` (OWNER Q9) | A: the first 256 `(line, LWarn)` plus an overflow count | named constructors | < 8 KB |
| `unknown` count | none by grep; surfaced as a count | A | 1 number | — |
| the unread fields of OWNER Q7 | **no reader, no output** | per Q7: not derived (default), or DR | — | P22 |

**The witnesses the witness table was missing** (CRIT 22, 24):
- **`a_partial_done_credits_but_does_not_complete`**: a partial `done` credits minutes and pushes a
  `DurationObs`, and leaves the done bit unset.
- **`a_partial_done_after_stop_replaces_the_cut`**: fork `uncredit_cut` ignores `partial`.
- **`idle_and_idle_since_read_different_orders`**: on a two-line log `[note 09:00, plan 08:00]`,
  `lastEffective` is 08:00 and `lastT` is 09:00.

**Totals (ESTIMATE).**
- The checkpoint is ≈ 75 KB at 900 ids and ≈ 180 KB at 3,000 ids, and grows with ids, not days.
- Sealed files are ≈ 120 KB a month on disk.

`view` is the record of every A, W, O, DR and WR reading above, as total query functions.
`factsView` is `view` without the line bookkeeping. A consumer reading a fact `view` omits is caught in
Rust, because the decoded struct has no field for it, and in Lean by cheat 97 (§16).

---

## 9. Windowing: the checkpoint, its guards, and its laws (`Seal.lean`, steps W1–W3)

### 9.1 Four horizons, all computed by the kernel, one anchored to `now`

- **`T`** is the request's day: the existing wire field `now`, which is fork `Ctx::today`, the calendar
  date in `cfg.tz`. It is required on every `log` request.
- **`c` (`cut`).** Lines `1..c` are folded into the checkpoint, in file order. Rust sends lines `c+1..n`:
  the **tail**.
- **`L` (`ledgerDay`).** Every day `< L` is final, and its day record went out once. Days `≥ L` that
  folded lines touched stay in the checkpoint as **open days**.
- **`H = horizonOf L = min (monthStart L) (isoMonday L) (L − 16)`**, saturating at 0.
  - Window facts (item-day minutes, done dates, date-keyed instances) are kept for dates `≥ H`. Below
    `H` they went out once, as window records.
  - `16` is `AUTO_CLOSE_CATCHUP`. `L − H ≤ 30`.

**The anchor** (CRIT 1).
- **Guard G4, `nowBelowLedger`,** refuses a request with `T < L`.
- **A reseal never seals past `T − keepDays`** (§9.4).
- So on every accepted request (`an_accepted_resume_covers_now`):
  - `L ≤ T`, so today's day is open;
  - every day, week and month period containing `T` starts at or after `H`;
  - every date `auto_close` can close (`≥ T − 16`) is at or after `H`.
- How the log's last line is dated never moves these horizons past `now`.

### 9.2 The checkpoint and the sealed records

```lean
namespace Tm.Seal
structure Header where
  line : Nat; tag : List Char; id : Option Log.Id; day : Nat; cancelled : Bool
  display : List Char          -- "YYYY-MM-DD HH:MM" in the line's written offset (fork `e.t.format`)
structure DayRecord where      -- one day, exactly as Rust stores it once the day is < L
  day : Nat; facts : Replay.DayFacts; obs : List Replay.Obs; demotions : List Replay.DemRec
  headers : List Header        -- every entry attributed to this day, cancelled ones included
structure WindowRecord where   -- one date's window facts, exactly as Rust stores them once the date is < H
  day : Nat; itemMin : List (Log.Id × Nat); doneIds : List Log.Id
  inst : List ((List Char × List Char) × Replay.InstRec)   -- date-keyed instances of this date
structure Ckpt where
  v           : Nat                         -- format version; any other is `badCkpt v`
  tzKey       : List Char                   -- the Tz.key it was attributed under (G0)
  cut         : Nat                         -- c
  ledgerDay   : Nat                         -- L;  H is `horizonOf ledgerDay`, never stored
  resealDay   : Nat                         -- the T of the reseal that produced it (host back-off only; no guard reads it)
  maxT        : Option Cal.Instant          -- latest instant among folded entries that are not future-dated (G2)
  futureFloor : Option Cal.Instant          -- earliest instant among folded future-dated entries (G2)
  wakes       : List Cal.Instant            -- the last kept wake dated < L − 2, then every kept wake dated ≥ L − 2
  sleptByDay  : List (Nat × Nat)            -- days ≥ L
  tagLast     : List (List Char × Nat)      -- per tag among folded survivors, the latest line (G1)
  tagOverflow : Bool                        -- more than 64 unknown tags were seen
  settled     : List Nat                    -- unfolded undos that cancel nothing in the suffix (≤ 1,024)
  machine     : Replay.Machine
  items       : List ItemAgg                -- A: id, minutes, blocks, done, lastDone, doneFirst, doneCount
  window      : List WindowRecord           -- W: dates ≥ H
  instOther   : List ((List Char × List Char) × Replay.InstRec)   -- A: non-date instance keys
  named       : List ((List Char × Option Log.Id) × Cal.Instant)  -- A: latest per (name, id?)
  openDays    : List DayRecord              -- O: days ≥ L touched by folded entries, future-dated days included
  lastDay     : Option Nat
  lastEff     : Option (Cal.Instant × Cal.Offset)
  entryCount  : Nat
  unknown     : Nat
  warnings    : List (Nat × Log.LWarn)      -- the first 256 folded line warnings
  warnOverflow : Nat
def horizonOf (L : Nat) : Nat := min (min (Cal.monthStart L) (Cal.isoMonday L)) (L - 16)
def Ckpt.wf (k : Ckpt) : Bool   -- keys Nodup; openDays ≥ L; window ≥ horizonOf L; machine days ≥ L; settled > cut;
                                -- every length and string within §10.4; every instant wf
def Ckpt.empty (z : Cal.Tz) : Ckpt      -- cut 0, ledgerDay 0, nothing folded
def emitCkpt : Ckpt → JVal
def readCkpt : JVal → Except CkErr Ckpt           -- smart decoder, refuses `badCkpt <field>` (R10)
def emitDayRecord : DayRecord → JVal
def readDayRecord : JVal → Except CkErr DayRecord
def emitWindowRecord : WindowRecord → JVal
def readWindowRecord : JVal → Except CkErr WindowRecord
```

**The encoding** is compact and positional:
- days are `Day` numerals;
- instants are `[sec, ns, west, offSec]`, keeping the written offset for display and `lounge_rate`;
- instance statuses are numerals.

Rust stores `emitCkpt`'s output verbatim and never looks inside it. The kernel emits a small
**`meta`** object beside it, `{cut, ledgerDay, horizon, resealDay, maxT, futureFloor}`, which the host
uses for policy and for genesis pops (§9.7).

### 9.3 The guards (checked in tail order; the first refusal is returned and names its bound)

| guard | refuses | why the checkpoint could otherwise be wrong |
|---|---|---|
| **G0** `badCkpt f`, `zone`, `cutMismatch` | `readCkpt` fails; `ckpt.tzKey ≠ tz.key`; the request's `from ≠ cut + 1` | provenance |
| **G4** `nowBelowLedger {now, ledgerDay}` | `T < L` | today's day, periods or auto-close dates could lie in sealed records (§9.1) |
| **G1** `undoReach {line, below}` | §7.4 | a tail undo would cancel a folded event |
| **G2** `wakeBehindCut {line, t}` | a surviving tail `wake` `w` with `w ≤ maxT`, or with `futureFloor = some f` and `f ≤ w + 172,800 s` | it could re-attribute a folded instant, or change which wake a date keeps |
| **G3** `sealedDay {line, day}` | a tail entry of any kind (cancelled included) whose header day is `< L`; a tail entry whose instant is before `wakes.head`; a surviving tail line with an effect naming `Key.day d`, `d < L`. This includes an observation's day and a machine write to the cut's day (CRIT 9) | it would change a sealed day record, its headers or observations |
| **G3w** `sealedWindow {line, day}` | a surviving tail line with an effect naming `itemDay`, `doneDate` or `instDate` at a date `< H` | it would change a sealed window record |

**What needs no guard, and why.**
- **`lastDone` and `named`** are maxima by instant, and maxima commute.
- **`doneCount`** deduplicates against W's dates, and G3w keeps retro dates at or after `H`.
- **Non-date instances** are all kept, so a last-in-file-order overwrite is exact.
- **Machine effects** (a `done` writing `went` onto the open block's observation, `uncreditCut`, a
  `resume` closing an old interruption) name days `≥ L`, because the seal never ledgers a day the machine
  can still write (§9.4).
- **`dayOf` for a tail instant `t ≥ wakes.head`** needs only the stored wakes, because the last wake at or
  before `t` is stored.
- **The two edge cases of `wakes`** (CRIT 25):
  - *A tail instant before `wakes.head`.* The head is dated `< L − 2`, so `t`'s true day is at most the
    head's date plus one day, which is `< L`. True G3 refuses it, so refusing without computing `dayOf`
    is exact (`an_instant_before_the_stored_wakes_is_sealed`; the one day absorbs a DST fold at
    midnight).
  - *No wake at all.* `wakes = []` holds exactly when no surviving wake was folded, because a folded
    wake is always kept, either as the head or as dated `≥ L − 2`. Then the fork's `last_wake_before` over
    the whole log sees only tail wakes, and `dayOf` from the tail's wakes is exact
    (`dayOf_with_no_folded_wake_reads_the_tail`).

### 9.4 Reseal: the fold point `c'`, the new ledger day `L'`, future-dated lines, and the no-loop law

`resume z T k b (some policy)` first accepts `b` under G0–G4. It then computes the **call-wide mask**
over `b` (skipping `k.settled`) and chooses the new cut.

**Definitions.**
- An entry is **future-dated** when `localDate z t > T + 2`.
- `M` is the greatest header day among the call's non-future survivors (or `T` when there are none).
- `F = min (T − keepDays) (M − keepDays)`, saturating. This is G-w, and it is bounded by `now` (CRIT 1).

**The fold point `c'`** is the **largest** `j` with `c ≤ j ≤ c + |b|` such that the prefix `b.take (j − c)`
meets all five conditions:
- **(i)** every entry in it that is not future-dated has header day `< F`;
- **(ii)** `j ≤ policy.maxLine`, when a `maxLine` is given (§9.6);
- **(iii)** every unfolded surviving wake `w` has `w > maxT'` and, when `futureFloor' = some f`,
  `f > w + 172,800 s`, where `maxT'` and `futureFloor'` are computed over the folded entries after the
  fold (so G2 cannot fire on what is left);
- **(iv)** `settled'` has at most 1,024 lines. `settled'` is every unfolded undo whose call-wide target
  is folded or absent, plus the old `settled` still unfolded;
- **(v)** it does not end with an unterminated last segment (`terminated = false`, CRIT 8).

`j = c` always qualifies: G2 accepted every tail wake against the unchanged `maxT`/`futureFloor`, and
G1 accepted every undo. So `c'` exists.

**Validity is not monotone in `j`.** Shrinking a prefix can unfold a wake that an out-of-order folded
line is later than, which breaks (iii). So `foldPoint` is a greatest-valid search: one pass with prefix
maxima and suffix minima of wake instants. It is specified as the greatest `j` satisfying `validCut`,
with `foldPoint_valid` and `foldPoint_greatest`.

**Future-dated lines** (CRIT 1, D9-22).
- They are exempt from (i), so a line dated 2027 folds as soon as (ii)–(v) allow.
- Its instant goes into `futureFloor`, not `maxT`. So it neither advances `F` nor pins `c'`, and G2 does
  not refuse ordinary wakes.
- Its day becomes an open day, which cannot be sealed before `T` passes it, because `L' ≤ T − keepDays`.
- The 2-day margin makes "a wake more than 2 days before every folded future instant" leave both that
  instant's `dayOf` and the wake dedup unchanged (`dayOf_agrees_two_days_before`): 24 hours plus any
  offset change is less than 2 days.

**The ledger day and the window horizon.**

```
L' = max L (min [ F
               , least header day among unfolded entries
               , least day key (day, itemDay, doneDate, instDate) named by any unfolded survivor's effects
               , day of machine.block.started, if the block holds an observation
               , machine.lastCut.day, machine.interrupt's day ])
H' = horizonOf L'
```

Every unfolded survivor's window keys are then `≥ H'`, since `H' ≤ L'`. A retro routine record for an
old instance keeps `L'` at or below that instance's date until it folds.

**What the reseal emits.**
- The checkpoint at `c'`. `openDays` holds the folded records of days `≥ L'`, and `window` is compacted
  to `H'`.
- One `DayRecord` for **every** day in `[L, L')`, including days now empty.
- One `WindowRecord` for **every** date in `[H, H')`.
- `meta`, and the new `settled`.

**The law against sealing past now.** `a_reseal_never_seals_past_now`: `L' = L ∨ L' ≤ T − keepDays`,
and so `H' ≤ T`.

**No loop.** Conditions (i)–(v) and the `L'` rule are exactly what makes G0–G4 accept the remaining lines
`b.drop (c' − c)` for any later `T' ≥ T` (`a_resealed_checkpoint_accepts_its_own_suffix`, §15). A
refusal can come only from a line appended after the last reseal, or from a `now` earlier than `L'`.

**Stalls.** An open block holding an observation, a `stop` never followed by a `start`, or an open
interruption holds `L'` back. It does not hold `c'` back.
- The checkpoint's open days grow by ≈ 2.5 KB a stalled day.
- §9.6's back-off keeps it to one reseal a day.
- `tm check` names a stall longer than 7 days (gap 88).

### 9.5 The laws (D5; full signatures in §15), and the proof route

Every law carries `hs : sealable z T₀ L a r = true`, where `T₀` is the day the checkpoint was sealed at: no survivor of the unfolded remainder `r` names a day
below `L` or a window date below `horizonOf L`, and the machine's days are `≥ L`. Without it `ckptOf`
would accept checkpoints no `resume` builds, and the laws would be false or vacuous (CRIT 3).

1. **The partition, query by query** (CRIT 3). Each is stated as an equation between a query on the
   stored form and the same query on `replay z es`:
   - `the_answer_reads_the_aggregates`: every A query;
   - `the_answer_reads_the_open_days`: every day query at `d ≥ L`;
   - `the_answer_reads_the_window`: every window query at `q ≥ horizonOf L`;
   - `a_day_record_is_the_replays_day`: every day query at `d < L`, read from `dayRecordsBelow`;
   - `a_window_record_is_the_replays_window`: every window query at `q < horizonOf L`, read from
     `windowRecordsBelow`;
   - their conjunction, `seal_partition_is_the_replay`: `merge (dayRecordsBelow …) (windowRecordsBelow …)
     (answer …) = view (replay z es)`, where `view` is total over every date.
2. **Two-run.** `resume_is_replay`: resuming the checkpoint of `a` over `b` at any `T ≥ L`, **after
   `emitCkpt`, then `jemit`, then `jparse`, then `readCkpt`** (AGENTS §5.9), gives the answer of the
   checkpoint of `a ++ b`.
3. **The reseal's own answer.** `resume_answer_ignores_the_policy`: a resume with `some p` returns the same
   answer as with `none`. With law 2, the answer a verb actually uses on the hot path has a law (CRIT 3).
4. **Two-run.** `resume_keeps_the_sealed_records`: the day records below `L` and the window records below
   `horizonOf L` of `a ++ b` equal those of `a`. What Rust stored is still true.
5. **Both directions (§5.8).** `resume_ok_iff`: acceptance is exactly
   `L ≤ T && reachFree z T₀ L a b && tagsClear z T₀ L a r b`.
   - `reachFree` is stated on the whole list, the spec side, in four parts:
     - in `survivors (a ++ b)`, no undo of `b` cancels a line of `a` that a settled record does not
       already account for;
     - every surviving wake of `b` is later than every folded non-future instant, and more than two days
       before every folded future instant;
     - every key a line of `b` names is at or above the horizons;
     - no instant of `b` is before `wakes.head`.
   - `tagsClear` is G1's conservative condition.
   - Beside it: `a_spurious_tag_refusal_exists` and `resume_without_the_guards_is_not_replay`.
6. **Two-run.** `reseal_is_seal`: a reseal's checkpoint and records are `ckptOf`, `dayRecordsBetween` and
   `windowRecordsBetween` of `a ++ b.take (c' − c)`, with `L ≤ L'`. It is paired with
   `a_reseal_never_seals_past_now`.
7. **No loop.** `a_resealed_checkpoint_accepts_its_own_suffix`, for every `T' ≥ T`.
8. **One code path.** `resume_from_empty_is_replay` and `resume_from_empty_never_refuses_by_guard`.
9. **Chunking and pops are invisible.** `chunked_genesis_is_one_replay`, by induction on laws 2, 4 and 6
   over any sequence of accepted calls whose starts are checkpoints that earlier calls produced.
10. **Codecs.** `readCkpt_emitCkpt`, `readDayRecord_emitDayRecord`, `readWindowRecord_emitWindowRecord`.
11. **Observations.** `sealed_and_live_observations_are_the_replays`: the day records' observations
    followed by the live ones, sorted by line, equal `replay`'s.
12. **Keys.** `every_dated_output_names_its_day_key`: every observation, header and record carries the
    day its `Key.day` names (CRIT 9).
13. **Width.** `the_log_op_emits_only_numerals_below_2_53`: every numeral the log op emits is below
    2^53, or the op refuses `counterOverflow` (CRIT 14).

**The proof route** (for the builder; ESTIMATE 4,600 proof lines for laws 1–9):

| lemma | job | source and cost |
|---|---|---|
| **W1** `survivors_append_of_tagsClear` | the mask splits, settled undos skipped | from `survivors_snoc_event`, `survivors_snoc_undo` and `List.eraseP_append_right`, with the invariant "the stack is the reversed survivor list" stated first |
| **W2** `keptWakes_append_of_later`, `dayOf_agrees_below_a_later_wake`, `dayOf_agrees_two_days_before`, `dayOf_from_the_stored_wakes`, `dayOf_with_no_folded_wake_reads_the_tail` | the day index splits under G2 and G3 | list lemmas over `mergeSort` (`pairwise_mergeSort`, `mergeSort_perm`), plus one `localDate` bound: an offset change is under 24 h |
| **W3** `sleptByDay_append_of_sealed` | the first-wake pre-pass splits | first in file order per day, for days `≥ L` |
| **W4** `applyEffects_touches_only_named_keys` | the frame law | the effect-list shape makes it one theorem (D9-9) |
| `List.foldl_append` | the fold splits | free |
| `effects_congr_index` | the step reads the index only at the instants it queries | one per arm, but mechanical: `dayOf` agrees there by W2 |
| `finish_commutes_with_seal` | the end of the fold | stable `mergeSort` per day |
| `foldPoint_valid`, `foldPoint_greatest` | the fold point | the one-pass scan against its `validCut` spec |
| `sealRecords_partition` | records below the horizons plus the live answer cover every query exactly once | per-key case split on `d < L` / `q < H` |

### 9.6 Host policy: when to reseal (performance only; the laws hold for any policy)

- **When.** Rust sends `reseal` in two cases:
  - the tail holds more than 512 **foldable** lines (lines at or below `maxLine`, below), so an undo stack
    that pins the cut does not trigger a reseal on every call;
  - `T − ledgerDay > 2` **and** the stored checkpoint's `resealDay < T`.

  The second clause is CRIT 19's back-off. A stall costs one checkpoint write a day, not one per TUI
  reload.
- **`keepDays = 2`.** Today's and yesterday's lines stay unfolded, so a `tm wake 06:05` typed after
  `tm start`, or a `--now` yesterday, never refuses.
- **`maxLine`** is the smallest `UndoEntry.log_line` among undo-stack entries younger than 14 days, or
  none.
  - The stack holds at most `MAX_ENTRIES = 50` and lives in `.tm/undo.json`.
  - `tm undo` pops it and never restores it (it restores only `state.json`). So `maxLine` can fall only
    when a new command pushes an entry, which is a performance effect, not a correctness one.
  - Entries written before R6 have no `log_line` and are ignored (CRIT 27).
  - An entry older than 14 days is ignored, so a light user's stale stack does not pin the tail.
    Undoing such a command is a G1 crossing: one rebuild, same answer.

### 9.7 Genesis: the chunked rebuild with exact pops

**When it runs:**
- the first run;
- a guard refusal on the hot path;
- invalidation (§9.8);
- a missing or corrupt cache.

A G4 refusal (a `--now` earlier than `L`) runs genesis at that `T` and **does not persist it**, so tests
that alternate past and present `now` do not thrash the cache.

**How it runs** (Rust, `kernel_log.rs`):
1. Read and split the whole log.
2. Cut chunks of **8,192 lines or 1 MiB of line bytes**, whichever is smaller. *(Superseded at W3 by gap 102's measurement: 8,192 lines or 1,536 KiB, chunks of 4,096 lines or 768 KiB; README "Stage 5 D9 W3".)*
3. Call `resume` from `Ckpt.empty` on each chunk, with `reseal {keepDays: 2, maxLine}` and `T`, and no
   documents. Each call resumes from the previous call's checkpoint, with the lines from its `cut`
   onward.
4. Keep a stack of `(ckpt, meta)`: 9 entries at 3 years at 61 events a day.

**On a refusal, pop exactly to what the refusal names** (CRIT 10):

| refusal | pop to the newest stack entry with | notes |
|---|---|---|
| `undoReach {line, below}` | `cut < below` | `Ckpt.empty` if none |
| `wakeBehindCut {line, t}` | `maxT < t` and no `futureFloor ≤ t + 2 d` | |
| `sealedDay {line, day}` | `ledgerDay ≤ day` | |
| `sealedWindow {line, day}` | `horizon ≤ day` | |

Then resend every line from that entry's `cut + 1` through the end of the refusing chunk, **in one
call**, with `reseal`.

**Why one call, not a chunked back-up.** A chunked back-up can loop. The call folding the chunk that
holds an undo's target cannot see the undo in the next chunk, so it folds the target again, and the next
chunk refuses again. One call carrying both ends is what lets the call-wide mask settle the undo.

**The memory cap.** A resend over **32,768 lines or 4 MiB** is not sent. Genesis fails with the named
fault `reachTooFar {line, kind, reach}` (OWNER Q9 (iii)), and the host prints the line and its kind. *(Superseded at W3 by gap 102's measurement: 8,192 lines or 1,536 KiB, chunks of 4,096 lines or 768 KiB; README "Stage 5 D9 W3".)*

**It terminates.**
- Each refusal pops to a strictly earlier start, or the resend carries both ends of the refused relation,
  so the same guard cannot refuse that line again (`resume_ok_iff`).
- For an undo with an id, `below` strictly decreases across repeated refusals (§7.4).
- `Ckpt.empty` folds nothing, so no guard can refuse it (`resume_from_empty_never_refuses_by_guard`).

**It is bounded by memory, not by stack.**
- Per chunk: ≤ 1 MiB × 63 MiB per MiB ≈ 63 MiB, plus the checkpoint.
- Per resend: ≤ 4 MiB × 63 ≈ 250 MiB. *(Superseded at W3 by gap 102's measurement: 8,192 lines or 1,536 KiB, chunks of 4,096 lines or 768 KiB; README "Stage 5 D9 W3".)*
- Two processes rebuilding at once stay under 520 MiB.
- CLI-written logs cannot reach the cap: the undo reach is ≤ 50 commands, and retro CLI lines fall
  within `keepDays`.

**Finish:** write the records and the checkpoint as §9.8 says.

### 9.8 Persistence and integrity (Rust; G9)

**Files** under `.tm/cache/replay/` (OWNER Q3):

| file | holds |
|---|---|
| `ckpt.json` | `{"format":2, "kernel":"<TM_KERNEL_ID>", "tzKey":…, "prefixLines":c, "prefixBytes":B, "prefixFnv":"<16 hex>", "gen":"<16 hex>", "prevGen":"<16 hex>", "manifest":{"2026-08":"sealed/2026-08.g<gen>.json", …}, "meta":{…}, "ckpt":{…kernel JVal…}}` |
| `sealed/YYYY-MM.g<gen>.json` | `{"v":1, "days":{"<Day>": dayRecord, …}, "window":{"<Day>": windowRecord, …}}`. **Immutable once written.** `gen` is a random 64-bit tag, so two concurrent writers never collide |
| `tz.json` | the probed table, keyed as in §6.1 |

**A reseal writes in this order:**
1. For each month touched by `[L, L')` or `[H, H')`:
   - read the file the current manifest names for it, if any;
   - replace exactly those day keys, in `days` or in `window`;
   - write the result as a **new** file `YYYY-MM.g<new>.json`, via a temp file and rename.

   This is a read-modify-write of an immutable input into a new output. Nothing is merged in place
   (CRIT 7).
2. Write `ckpt.json` with `gen = new`, `prevGen = old` and the updated manifest, via a temp file and
   rename.
3. Delete month files named by neither the new nor the previous manifest, and older than 10 minutes by
   mtime, so in-flight writers keep theirs.

**Genesis** writes every month under one fresh `gen`, then `ckpt.json`, then runs the same collection. It
never renames over a directory.

**Crash recovery.** After a crash between steps 1 and 2, the new month files are orphans, which the old
manifest ignores and a later collection deletes. The old checkpoint stays valid.

**Readers take one snapshot** (CRIT 7):
- A process reads `ckpt.json` **once**.
- It loads month files only by that file's manifest.
- It uses day records only for `d < meta.ledgerDay`, and window records only for `d < meta.horizon`, of
  that same `ckpt.json`.
- If a named file is missing, because two reseals by another process ran during a long TUI session, it
  re-reads `ckpt.json` and retries once. After that it rebuilds in memory, with the notice
  `replay cache changed underneath; rebuilt in memory`.

**Invalidation goes straight to genesis** when any of these hold:
- `prefixBytes > file length`, or byte `prefixBytes − 1` is not `\n` (CRIT 8);
- the FNV-1a-64 over `bytes[..prefixBytes]` differs. This is **checked on every call** (D9-14), and
  catches a git merge of `log.jsonl` or a hand edit;
- `tzKey` differs: a `cfg.tz` change, or a tzdb upgrade;
- `format` or `TM_KERNEL_ID` differs. `TM_KERNEL_ID` is an FNV-1a of the linked kernel archive, emitted
  by `tm-kernel-ffi/build.rs` through `cargo:rustc-env`, so each kernel change costs one rebuild. At 3
  years that is ≈ 1–4 s on the first command after an upgrade, stated in the README and in Q3 (CRIT 26);
- the kernel answers `badCkpt`.

**An unwritable cache** (a read-only synced viewer, a permission error) is not fatal (CRIT 26):
- the host prints one named notice per process: `replay cache .tm/cache/replay is not writable (<os
  error>); each command rebuilds in memory`;
- it keeps the in-memory checkpoint for that process. The TUI therefore pays genesis once per session,
  not once per reload.

**Concurrency** between the CLI and the TUI's 200 ms debounce:
- Every write is a temp file plus rename, and every month file is immutable.
- A checkpoint of an append-only prefix is valid for that prefix, and the digest catches a rewrite.
- A process whose read of `ckpt.json` is stale writes a checkpoint of its own prefix. That checkpoint is
  still valid, and the next process's digest decides whether to use it.

**The trust assumption, named beside G9 in the README.** The window laws assume Rust hands back the
checkpoint, and any sealed record the kernel reads, for the exact prefix bytes it was made from. The
digest and the manifest enforce that, and T10 tests it. It cannot be proved in the kernel, because it is
a property of the file system.

---

## 10. The wire

### 10.1 Request

The existing keys (`docs`, `cmds`, `now`, `blockMin`) are unchanged. A request without `tz`, `log` or
`capacity` is read exactly as today. `now` is the `T` of §9.1.

```jsonc
{"docs": [], "cmds": [], "now": "2026-09-14", "blockMin": 50,
 "tz": {                                              // required when `log` or `capacity` is present, else `tzAbsent`
   "key":  "America/Chicago|2025b|1900-2200",
   "base": "-06:00:00",                               // the offset in force at 1900-01-01T00:00:00Z (Chicago left LMT in 1883)
   "then": [["1918-03-31T08:00:00Z", "-05:00:00"], ["1918-10-27T07:00:00Z", "-06:00:00"], …]   // ≤ 4,096
 },                                                   // instants and offsets are strings read by the kernel's own readers
 "log": {
   "ckpt":       null | { …the kernel's checkpoint JVal, verbatim… },   // null = genesis from Ckpt.empty
   "from":       44661,                               // physical line number of lines[0]; must be ckpt.cut + 1 (cutMismatch)
   "lines":      ["{\"t\":…}", null, "", …],          // null = not UTF-8; ≤ 32,768 elements (tooManyLines)  // W3: ≤ 8,192 (gap 102)
   "terminated": true,                                // false: the last element had no trailing \n and is never folded
   "reseal":     null | {"keepDays": 2, "maxLine": 45100 | null},     // keepDays ≤ 31
   "want":       {"facts": true,                      // the decoded view (§11.1)
                  "headersFrom": null | 45170,        // headers for tail lines ≥ this
                  "render": [45101, 45102]},          // canonical renderings of these tail lines (≤ 4,096)
   "sealed":     null | {"days": [dayRecord…], "window": [windowRecord…]}   // only for a kernel query naming an old date (≤ 62 records)
 },
 "capacity": { … §13.6 … }
}
```

Rust also enforces **≤ 4 MiB of line bytes per request** before sending (§9.7). *(Superseded at W3 by gap 102's measurement: 8,192 lines or 1,536 KiB, chunks of 4,096 lines or 768 KiB; README "Stage 5 D9 W3".)* The kernel cannot
measure bytes before parsing, so the line count and the per-line bound are its half.

### 10.2 Response

The `ok` object gains `log` and, for D10, `lookahead`. Keys are emitted in build order, and
`the_response_shapes_emit_in_build_order` is extended.

```jsonc
{"ok": {"docs": [], "report": {"closes": []},
  "log": {
    "lines":    45172,                                // last physical line seen
    "warnings": [{"line": 17, "w": "missingField", "key": "slept_min"}, {"line": 950, "w": "invalidUtf8"}, …],   // this call's tail
    "replayWarnings": [{"line": 961, "w": "unknownInstanceStatus", "raw": "maybe"}],
    "facts":    null | {"items": […], "window": [windowRecord…], "instOther": […], "named": […],
                        "days": [dayRecord…], "open": {"block": …, "lastCut": …, "interrupt": …},
                        "lastDay": d|null, "lastEffective": I|null, "entryCount": n, "unknown": n,
                        "warnings": {"first": [[17, "missingField", "slept_min"], …], "overflow": n}},
    "headers":  [[45171, "done", "667", 739872, false, "2026-09-14 08:00"], …],
    "render":   [[45101, "{\"t\":\"2026-09-14T08:00:00-05:00\",\"ev\":\"start\",…}", "2026-09-14 08:00"], …],
    "reseal":   null | {"ckpt": {…}, "meta": {"cut": 45100, "ledgerDay": 739870, "horizon": 739855,
                                             "resealDay": 739872, "maxT": [..], "futureFloor": null},
                        "days": [dayRecord…], "window": [windowRecord…]}
  },
  "lookahead": { … §13.6 … }}}
```

### 10.3 Refusals

The new `err` shape is `{"err": {"log": {…}}}`, and `kernel_bridge::refusal` maps each name. **A line
of the log never refuses a request. It is a warning.**

| name | the host's reaction |
|---|---|
| `undoReach {line, below}`, `wakeBehindCut {line, t}`, `sealedDay {line, day}`, `sealedWindow {line, day}` | genesis (§9.7), then re-issue the same request once; never shown to the user |
| `nowBelowLedger {now, ledgerDay}` | genesis at that `now`, **not persisted** (§9.7) |
| `badCkpt <field>`, `cutMismatch`, `zone` | genesis |
| `tzAbsent`, `badTz <why>`, `tooManyLines`, `badLogReq <field>`, `renderNotInTail {line}`, `counterOverflow <field>`, `lookaheadTooLong` | host defect or an impossible log: a loud fault (`kernel_bridge::fault_issue`) naming the field |
| (host-side) `reachTooFar {line, kind, reach}` | OWNER Q9 (iii): every verb except `tm check` fails naming the line; `tm check` reports it as an error |

### 10.4 R10: every bounded value crossing, with its smart constructor and rejection theorem

The critique found the first draft's table incomplete (CRIT 14). This one is meant to be exhaustive, and
W1 and L6 check it against the decoders before they freeze.

| value | bound | constructor | refusal |
|---|---|---|---|
| lines per call | ≤ 32,768 (Rust: ≤ 4 MiB of bytes too) *(Superseded at W3 by gap 102's measurement: 8,192 lines or 1,536 KiB, chunks of 4,096 lines or 768 KiB; README "Stage 5 D9 W3".)* | `mkLogReq?` | `tooManyLines` |
| a line | ≤ 65,536 chars; nesting ≤ 64 | `readLine` | warnings `lineTooLong`, `lineTooDeep` |
| a decimal's exponent | its digits are bounded by the line; its **value** is never used to build `10^e` unless `k = digits m ± e` lies in [−330, 330]; `m = 0` short-circuits to finite | `finiteF64` | `badField k` / `outOfRange k` |
| an instant | year ≤ 9999; `ns` per `Instant.wf` | `mkInstant?` | `badT`, `badTz` |
| an offset | `sec < 86,400` | `mkOffset?` | `badT`, `badTz` |
| tz transitions | ≤ 4,096, strictly increasing; key ≤ 128 chars | `mkTz?` | `badTz` |
| `U8` / `U32` fields | `< 256` / `< 2^32` | `U8.ofNat?` / `U32.ofNat?` | warning `badField` |
| `from`, `maxLine`, `headersFrom`, each `render` line | `< 2^40` | `mkLogReq?`, `mkWant?` | `badLogReq <field>` |
| `keepDays` | ≤ 31 | `mkReseal?` | `badLogReq keepDays` |
| `render` list | ≤ 4,096, each line inside the tail | `mkWant?` | `renderNotInTail` |
| `sealed` input | ≤ 62 records, each passing its record decoder | `mkSealedIn?` | `badLogReq sealed` |
| checkpoint `items` / `instOther` | ≤ 65,536 each | `readCkpt` | `badCkpt items` / `instOther` |
| checkpoint `window` | ≤ 4,096 records; per record `itemMin`, `doneIds`, `inst` ≤ 4,096 each | `readCkpt` | `badCkpt window` |
| checkpoint `named` | ≤ 16,384 | `readCkpt` | `badCkpt named` |
| checkpoint `openDays` | ≤ 4,096 records; per record `obs` ≤ 16,384, `demotions` ≤ 4,096, `headers` ≤ 65,536 | `readCkpt` | `badCkpt openDays` |
| checkpoint `wakes` / `sleptByDay` | ≤ 4,096 each | `readCkpt` | `badCkpt wakes` / `sleptByDay` |
| checkpoint `tagLast` | ≤ 25 known + 64 unknown; an unknown tag string ≤ 128 chars, longer ones only set `tagOverflow` | `TagLast.insert` | `badCkpt tagLast` |
| checkpoint `settled` | ≤ 1,024, each `> cut` | `readCkpt` | `badCkpt settled` |
| checkpoint `warnings` | ≤ 256 | `readCkpt` | `badCkpt warnings` |
| every string in a checkpoint or record | ≤ 65,536 chars | `readCkpt`, `readDayRecord`, `readWindowRecord` | `badCkpt <field>` |
| a day record / window record | as the checkpoint's per-record bounds | `readDayRecord`, `readWindowRecord` | `badCkpt <field>` |
| every numeral the `log` op emits | `< 2^53` | checked at emission | `counterOverflow <field>` (law 13) |
| capacity weights, levels, pairs, curves, day counts | §13.6 | §13.6 | §13.6 |

A kernel **emission** that would exceed a checkpoint bound (for example more than 65,536 distinct ids)
refuses `counterOverflow <field>` instead of writing a checkpoint its own reader would refuse. So
`readCkpt_emitCkpt` needs no extra hypothesis beyond `wf`.

---

## 11. What the kernel hands back, and the observations for Rust

### 11.1 Facts decoded into Rust's `Replay`, per verb scope

`kernel_log::decode_facts` builds the **reshaped** `tm_core::log::Replay` from Phase R (§12). Its fields
are §8.4's rows, filled through smart constructors, as `decode_report` already does.

**tm-core functions keep taking `&Replay`**, and their signatures do not change (D9-20, CRIT 4). The
host decides how much sealed history to merge in, by scope:

| scope | merges into `Replay` | verbs |
|---|---|---|
| `Hot` | the answer only (A, W, O) | every verb not listed below; TUI reloads; `auto_close` housekeeping; `tm close day <date>` for `date ≥ H` |
| `Dates(from, to)` | the answer, plus day records for `[from − 1, to + 1]` and window records for `[from, to]` | `tm close day <date>` for `date < H`; `tm log --since` (headers only) |
| `All` | the answer, plus every month's records | `tm review day` (`estimate_calibration` reads every duration), `tm review week` (`lounge_rate` reads every day), `tm review month`, `tm model` (the fit), `tm log --item` (headers only) |

- **The one-day margin** in `Dates`: a demotion or header whose wake-attributed day is `d` can have local
  date `d + 1`, and `day_review` buckets demotions by local date.
- **The merge is disjoint** by law 1. Records are taken only below the snapshot's `ledgerDay` and
  `horizon` (§9.8).
- `DayReplay::load()` divides `loadFifths` by 5 at display.
- **At S, `tm model --fit` runs `fit_replay` over the `All`-scope `Replay`**, so the fit sees every
  observation from the switch commit on (CRIT 4). F1 later replaces `fit_replay` with `fit_observations`,
  an optional cleanup that changes no value.

### 11.2 Observations (D9's hand-back to the fit)

- **`EnergyObs`** has: `line`, `t` (instant plus written offset), `day`, `pred : u8`, `rep : u8`, `hsw`
  (lexical), `loc`, `slept_min : Option<u32>`, `went : Option<u8>`, `id?`, `from_start`.
- **`DurationObs`** has: `line`, `t`, `day`, `id`, `ci : u8`, `tags`, `est_min`, `actual_min`, `went?`,
  `partial`.
- **Order.** Rust sorts by `line`, which gives the fork's `replay.energy` order exactly. A start's
  observation carries the start's line (`observations_are_in_file_order`).
- **`hsw`** is emitted lexically. The kernel re-emits the `JDec` it read, and Rust reads it with
  `serde_json`: same characters, same parser, same `f64`.
- **`slept_min`** is bound at emission from the final `sleptByDay`. For a sealed day it is final, because
  G3 refuses a later wake for that day.
- **Arrivals** are `DayFacts.{day, arrival, loc}`. `energy::arrivals_from_replay` keeps its time-of-day
  extraction in `cfg.tz` (D9-19).

### 11.3 Sealed records (what a finished day and a finished window date hand back, once)

- **A day record**, for `d < L`, holds:
  - `DayFacts`;
  - that day's energy and duration observations;
  - its demotions, with `t` and the written offset;
  - a header for **every** entry attributed to `d`, cancelled ones included, with its display text.
- **A window record**, for `d < H`, holds that date's item-day minutes, done ids and date-keyed instance
  records.

Both are written by the reseal that moves the horizon past them (§9.4), and loaded per §11.1's scope.

### 11.4 `tm log` and `tm undo`

**`tm log`**, in this order (CRIT 28):
1. **Digest.** `Ctx` checks the prefix digest in this process before anything else (§9.8).
2. **Select headers.** Rust builds the candidate headers from the snapshot: every day record's headers in
   scope, followed by the headers of the open days and the tail from the same call. It selects them
   exactly as `lifecycle.rs` `log` does:
   - `--item` keeps `id == key` and not cancelled (fork `iter_item`: the mask plus `primary_id`);
   - `--since` keeps `day ≥ from`;
   - `--tail` takes the last *n*, 20 by default.
3. **Read bytes.** For selected lines outside the tail, Rust reads their raw bytes by line number from
   the file whose prefix was just checked.
4. **Render.** A render-only call (`ckpt: null`, `reseal: null`, `want.render`) returns
   `[line, rendering, display]` for each. **The kernel parses and renders; it does not replay.**
5. **Print.**
   - `--json` emits each rendering's **own bytes**, verbatim — `serde_json::value::RawValue`, scoped to
     the renderer — so that it is byte-identical to today for every line the Rust writer wrote (T2).
     **The pretty-printing is re-emitted by the renderer**, because a `RawValue` is written into the
     enclosing document unformatted and would otherwise print each entry compact on one line.
     Hand-appended unknown lines with non-canonical numerals are P29. *(Corrected 2026-09-16, W-11,
     under **D22**: this bullet read "emits each rendering **parsed as a generic `serde_json::Value`**"
     and, in the same sentence, that it "is **byte-identical to today**" — and those two cannot both
     hold. This workspace's `serde_json` is built without `preserve_order`, so `Value`'s object is a
     `BTreeMap` and parsing **alphabetises every key**, where the writer emits `t` first; following the
     sentence literally moved `tm log --json` on **7 of 69** corpus invocations, every difference a key
     order and no value (W-9's measurement). `serde_json/preserve_order` was declined as changing
     `Value`'s ordering workspace-wide unmeasured, and alphabetising was declined as spending
     byte-identity in one of the few places the corpus test still catches a regression. README
     **gap 144**; AGENTS §4 **D22**.)*
   - The human line is the kernel's `display`, the tag, and the `k=v` pairs of that rendering **parsed as
     a `Value`** without `t` and `ev`. The parse stays on the *human* path deliberately: its alphabetical
     order is what `tm log` prints today, and `tm_log_is_byte_identical_on_the_corpus` pins it. Rust
     never parses a timestamp, so `parse_timestamp` is deleted at S (CRIT 20).
   - `total = facts.entryCount`.

A hand edit between two commands is caught at step 1 of the next command, so no header is rendered
against bytes it was not made from.

**`tm undo`:** §7.2.

---

## 12. The Rust side, file by file

| file | stays | changes, and when | deleted, and when |
|---|---|---|---|
| `tm-core/src/log.rs` | **The writer:** `Event` (`Serialize`, `name()`), `LogEntry::{new, to_json}`, `fmt_timestamp`, `hours_since_wake` (computes `hsw` when appending). **The decoded view:** `Replay` and its record structs, reshaped in Phase R | R1–R13 reshape accessors (§14.3). S: fields decoded from the kernel | **S:** `impl Deserialize for Event` with `Known` and `field_error`; `ts::deserialize`; `parse_timestamp`; `LogEntry::{parse, local, calendar_date}`; `LogWarning`; `UndoMask`, `undo_mask`; all of `Log` (`new`, `parse`, `parse_bytes`, `read`, `append`, `append_all`, `push`, `iter`, `effective`, `undo_target`, `compensating_undo`, `day_index`, `iter_day`, `iter_range`, `iter_item`, `replay`); `local_midnight`, `DayIndex`; `Block`, `Cut`, `Machine`, `replay_refs`; `parse_instance_status`, `stamp_from_key`; `Event::{primary_id, is_state_change}`; `Replay::{events_for, stamps}`. **R11 (per Q7):** the unread fields. ESTIMATE −1,750 lines |
| `tm-core/src/store.rs` | `FsStore::read_text`, `append_text`, `LOG_PATH` | R10: `append_text` to `LOG_PATH` writes `\n` first when the file is non-empty and does not end in one (G9) | — |
| `tm/src/cli/tz_table.rs` (new, B4) | the hourly probe, bisection to the second, the cache (§6.1) | — | — |
| `tm/src/cli/kernel_log.rs` (new, W3/S; ESTIMATE ≈ 1,050 lines) | the byte split, the UTF-8 test and `terminated`; the digest; `ckpt.json`, generations, manifest and collection; the reseal policy and back-off; genesis with exact pops and the memory cap; request build; `decode_facts` per scope; `headers`; `render`; the unwritable-cache fallback | — | — |
| `tm/src/cli/ctx.rs` | `append_event`, `append_entry` (the writer); `now`, `today` | R8: the `log` field and `read_log` go, and `Ctx::replay_of` becomes the chokepoint. R13: `Ctx::replay_with(scope)` wraps it per verb family (§11.1). S: its body becomes `kernel_log::replay(scope)` | R8: `Ctx.log` |
| `tm/src/cli/undo.rs` | `UndoStack`, `Recorder`'s snapshot and diff, `undo` | R6: physical line counts; `Replay::headers_from`; `UndoEntry.log_line` (absent in old stacks means none). S: from `kernel_log` | `log_len`, `new_events`' parse |
| `tm/src/cli/day.rs` | the verbs, `EnergyCtx`, the `now`/`state.break_` clamping | R1: `since_break_min` reads `DayFacts.since_break`. R2: `idle_min_since` reads `idle_marks`. R3: `idle` reads `last_effective` | the raw `effective` walks |
| `tm/src/cli/lifecycle.rs` | review verbs, `day_extras`, `model` | R5: `log` reads `Replay::view` rows. S: §11.4, with scopes per §11.1 | the raw `ctx.log` walks |
| `tm/src/cli/planning.rs` | everything reading `Replay` | L8: `days[].minutes_at_level` and `total` are display floors of exact units, with exact fields per Q4 | — |
| `tm-core/src/planner.rs` | everything reading `Replay` | R7: `PlanInput.log` deleted (no reader). **L8: the week-allocation loop (`capacity::reserve(std::slice::from_mut(day), take, c.ci)`) works in `u128` units over kernel capacities**, with a differential test against step 3's `reserveRest` (T16; gap 94) | `PlanInput.log` |
| `tm/src/tui/mod.rs`, `app.rs` | the watcher, reload via `Ctx::load`, every screen | R4: `idle_since` reads `DayFacts.last_t`; `AppData.log` and `App.log` go. S: an in-process checkpoint reused across reloads | `App.log` |
| `tm/src/tui/queue.rs`, `necessities.rs` | `done_minutes_map`, `waiting_state` | L8: the queue's `fits` reserve works in `u128` units (T16; gap 94) | — |
| `tm-core/src/review.rs` | **all of it:** presentation arithmetic (`gaps`, adherence, `wake_to_arrive_min`, `lounge_rate`, `mix_and_load`) | R9: `load()` over fifths. S: reads the `All`- or `Dates`-scoped `Replay` | — |
| `tm-core/src/energy.rs` | **the statistical layer:** `fit`, `shrunken_mean`, `observation_weight`, `compare`, `calibration`, `estimate_calibration`, `Posterior::*`, `EnergyObs::weight`, `DurationObs::ratio`, `arrivals_from_replay` | F1 (optional): `fit_observations` | F1: `fit_replay` |
| `tm-core/src/{recur,priority,capacity,horizon}.rs` | read the decoded `Replay` until their tranches | R3: `recur` reads `done_date_first`/`done_date_count` and `latest_named`. F2–F4: each decision fact's last Rust reader moves into a kernel function | with their tranches |
| `tm/src/cli/kernel_bridge.rs` | `apply`, `decode_report` | B4/W3: `refusal` learns the `log` names. L6: `decimal_pair`, and unit strings parsed to `u128` | — |
| **Tests** building a `Replay` or `Log` from text: 18 tm-core files (45 call sites) and 3 tm modules (`tui_common/mod.rs`, `tui_queue_common/mod.rs`, `tui_today_prompts.rs`) | their assertions | R12: every site calls `replay_of_text(text, tz)` (tm-core) or `app_with_log_text` (tm). S: the tm-core files move to `tm/tests/`, and the helpers call the kernel. `log_replay.rs` and `log_regressions.rs` run through it; `log_serde.rs` keeps writer tests only | R12: direct `Log::parse`/`Log::new` in tests |

**After S, the one-reader grep returns only the writer:**

```
grep -rn 'fn replay\b\|undo_mask\|DayIndex\|parse_bytes\|LogEntry::parse\|Log::parse\|Log::new\|Machine\b\|iter_day\|effective()\|parse_timestamp' \
  tm-core tm --include=*.rs
```

It covers `src/` and `tests/` of both crates, `horizon.rs` included (CRIT 31).

---

## 13. D10: the lookahead as an exact mixture, on step 3's EDF (`Lookahead.lean`, track L)

### 13.1 What exists and what this adds

**Step 3 landed as `fea3f81`.** Its `Capacity.lean` has:
- `Den`, `denOf?`, `DayCapacity {day, numAt : Fin 6 → Nat}`, `DayCapacity.minutesAt den l : Pos`,
  `DayCapacity.ofLevels`;
- `Deadline {need, ci, due}` and `Deadline.ofRemaining` (site R1);
- `availUntil`, `reserveRest`, `reserveOut`, `totalMin`, `sortDue`, `grantOf`, `edf (den : Den)`,
  `edfGrants`;
- `Grant.availQ`, `reservedQ`, `shortfallQ`, `Grant.hot`, `Grant.impossible`;
- `Lookahead` and `lookaheadOf? (den : Nat) days` (positive denominator, strictly ascending days);
- the three EDF goals, proved.

**This track adds one module**, `TmKernel/Lookahead.lean`. It imports `Capacity`, `Cal`, `Line`, `Plan`
and `Tree`, and goes in `TmKernel.lean` after `Capacity`. It **produces** the `List DayCapacity` that
`edf` consumes, and never restates `Capacity.lean`. The bin for a deadline is
`Priority.binOfScaledQ bins s rem (g.availQ capDenD)`, and `binOfScaledQ_congr` makes the choice of
denominator unobservable.

### 13.2 Weights and the mixture (step L1)

```lean
namespace Tm.Look
def capDen : Nat := 1000000000000000000                    -- 10^18: OWNER Q8's default (b)
def capDenD : Den := ⟨capDen, by decide⟩
abbrev Weight := { w : Nat // w ≤ capDen }                -- p = w / capDen (R10)
def mkWeight? (n d : Nat) : Except WErr Weight            -- badWeight (d = 0) | weightAboveOne (n > d) | weightPrecision (capDen % d ≠ 0)
abbrev Hist := Fin 6 → Nat                                 -- whole minutes per level, one location, one day
def mix (w : Weight) (lounge home : Hist) : Fin 6 → Nat := fun l => w.val * lounge l + (capDen - w.val) * home l
def ofHist (d : Nat) (h : Hist) : DayCapacity := ⟨d, fun l => capDen * h l⟩   -- day 0: pure, no mixture
```

**The host's reaction to a weight refusal** (CRIT 17). Under Q8 (b), `weightPrecision` fires only for a
weight with more than 18 decimal places, and `weightAboveOne`/`badWeight` only outside [0, 1] or for NaN.
`Model::load` checks through `decimal_pair` (§13.6) and fails every verb that computes capacity or
priority, naming the file and key: `model.json: p_lounge.Mon = 1.2 is outside [0, 1]`. Other verbs run.
The kernel's refusal is the authority, and the host check exists only to name the file.

**Proved in L1:**
- `mix_between_the_locations`, `mix_at_zero_is_home`, `mix_at_one_is_lounge`,
  `mix_denotes_the_weighted_sum`, `mix_atLeast_between_the_locations`;
- the rejection theorems `mkWeight?_zero_den`, `_above_one`, `_precision`, and the acceptance
  `mkWeight?_round2` (`9/10` gives `9·10^17`);
- `the_bin_does_not_see_capDen`: scaling every numerator and the denominator by `k > 0` leaves every
  `binOfScaledQ` unchanged. It is an instance of `binOfScaledQ_congr`, and it makes Q8's answer a
  one-line change;
- `edf_commutes_with_scaling`, a two-run law over step 3's `edf`, stated here and proved over
  `reserveRest`/`reserveOut` without editing `Capacity.lean`.

### 13.3 Pulled forward from stage 6 (steps L2–L4; OWNER Q2)

**E7, the window (L2, after B1).** Endpoints are UTC instants from B1:
- `arrival = instantOf z d (expectedArrival wd)`;
- `cap = instantOf z d windowCap`;
- walls from `wallsOn p d`, below.

Every endpoint is `instantOf` of a whole-minute local clock. The capacity path refuses a zone table
whose offset in force on any lookahead day is not a whole minute (`badTz subMinuteOffset`; no tzdb zone
has one after 1972, and T4 (d) checks). So minutes of UTC instants are exact, and E7 counts whole
minutes of real time, DST days included.

`wallsOn p d` covers every item whose status is not `.settled` and whose `Plan.effectiveShape` is
`Shape.interval s f`. It yields `(instantOf z s.day s.time − buffer, instantOf z f.day f.time)` covering
`d`, with `buffer` from `Field.viewBuffer`. It is indexed once per request, not per date.

```lean
/-- Specification only: never evaluated at run time (D9-21); decide witnesses use ≤ 1,440 minutes. -/
def wallOverlap (arrival stop : Nat) (walls : List (Nat × Nat)) : Nat :=      -- minutes of [arrival, stop) under ≥ 1 wall
  ((List.range (stop - arrival)).map (· + arrival)).countP (fun t => walls.any (fun w => decide (w.1 ≤ t ∧ t < w.2)))
def windowBase (arrival windowMin windowCap : Nat) : Nat := max arrival (min (arrival + windowMin) windowCap)
def windowEnd (arrival windowMin windowCap : Nat) (walls : List (Nat × Nat)) : Nat   -- the fork's walk: clip, sort, merge, extend (a foldl)
```

**Proved in L2:**
- **E7a** `the_window_end_solves_the_equation` and **E7b** `the_window_end_is_the_least_solution`;
- `the_window_end_is_not_the_least_solution_over_walls_wholly_inside`: arrival 420, window 480, cap
  1140, wall `(890, 950)`. `Goals.lean` STAGE 6's `wallsInside` equation has 900 as a solution; the
  fork, and `windowEnd`, give 960;
- the base-clamp refutation (arrival 20:00 after a 19:00 cap);
- the fork tests `budget_of_an_eight_hour_window`, `walls_extend_the_window` and
  `the_cap_bounds_the_window` as witnesses.

`Goals.lean` STAGE 6's `wallsInside` and E7a/E7b are **deleted and restated** in STAGE 5, with a README
note ("restated to the oracle's overlap semantics; refuted as written").

**Site R3 is reopened.** `windowMin = Arith.halfUpQ (60 · windowHours)`, and `Arith.lean`'s R3 row is
corrected. `budget = floorQ (60 · wh / blockMin · br)` on the exact pairs, equal to `budget_blocks`.

**The cut (L3).** The general `cut_slots_around`: free intervals over clipped, merged walls; `cutStretch`
on structural fuel `stop − start + 1`; rests and since-break included, so stage 6's `dayPlan` reuses it.
**Proved in L3:** `cutSlots_inside_the_window`, `cutSlots_avoid_the_walls`,
`cutSlots_short_block_is_at_least_min_last`, `cutSlots_fuel_is_enough`, and capacity.rs's documented
§4.3 cut as a witness.

**Energy and the limit (L4): hours since wake from seconds, site R11** (D10-11, CRIT 6).

The fork's chain is `Features::at` → `log::hours_since_wake` (`(secs / 36.0).round() / 100.0`, with
`secs = signed_duration_since(..).num_seconds()`) → `energy::bucket` (floor, clamped to `0..12`) and the
prior curve's range keys. Today's wake keeps its seconds (`Ctx::wake_time` returns `d.wake…time()`, and
a bare `tm wake` logs `now`). So whole minutes are not exact: wake 06:05:40 against a slot at 07:05:00
is 3,560 s, which rounds to 0.99 h and bucket 0, while minutes give 60 and bucket 1.

```lean
/-- Site R11: `(s / 36.0).round()` for whole seconds `s` — half away from zero. -/
def hsw100 (s : Int) : Int := if s < 0 then -(((-s).toNat + 18) / 36 : Nat) else ((s.toNat + 18) / 36 : Nat)
def bucket (h : Int) : Fin 12 := if h ≤ 0 then 0 else ⟨min 11 (h.toNat / 100), by omega⟩
/-- A prior range `from ≤ hours < to` with keys `num/den`, compared exactly. -/
def inRange (h : Int) (r : PriorRange) : Bool := r.fromNum * 100 ≤ h * r.fromDen && h * r.toDen < r.toNum * 100
def hswAt (wake slot : Cal.Instant) : Int := hsw100 (Cal.secondsBetween wake slot)
```

**Why these equal the fork's doubles.**
- `s / 36.0` is correctly rounded. A tie `s = 36k + 18` has an exact quotient `k + 0.5`, and a non-tie
  lies at least `1/36` from `k + 0.5`, far beyond an ulp for `|s| < 2^40`. So `round` sees the true
  side, and `hsw100` is its value.
- `bucket` floors `n / 100.0`, which is correctly rounded. For `|n| < 2^40` it never reaches the next
  integer, because `(100m − 1)/100` is `1/100` below `m`.
- Two range comparisons between `n/100` and a key `num/den` with `den ≤ 10^6` differ by at least
  `1/(100·den)` when unequal, which exceeds the ulp at these magnitudes, and are equal as doubles when
  equal as rationals. So `inRange` is exact against the fork's `f64` comparison, and LOOK's range-key
  exception is not needed.
- R10 bounds: prior keys `den ≤ 10^6`, `num ≤ 48·den` (§13.6).

**Inputs.** Future days use `instantOf z d (expectedWake wd)` from the model-then-config fallback, as
fork `wake_or_expected(None, weekday)` does. Today uses `wakeToday : Cal.Instant` with seconds, from
`state.wake` or the replay's day record. The host sends it as a stamp string that the kernel reads with
`parseStamp`.

`stepAt`, `priorLevel`, `learnedLevel`, `futureEnergy` (home cap included), `histOf`, `limitHist` and
`limitSlots` complete L4.

**Proved in L4:**
- `hsw100_is_round_half_away` (against the rational specification `|2·36·h − 2·s| ≤ 36`, ties away);
- `the_bucket_reads_seconds`: the 06:05:40 / 07:05:00 witness gives bucket 0;
- `limitSlots_is_limitHist` (via `List.mergeSort_perm` and `List.pairwise_mergeSort`);
- `futureEnergy_home_is_capped`;
- fork `prior_energy_lookup`'s 12 assertions and `predict_falls_back_to_the_prior`'s 4, each as a
  `decide` over literals.

### 13.4 The lookahead (step L5)

```lean
def maxLookaheadDays : Nat := 3660
structure Input where
  today : Nat; days : Nat; day0 : Hist
  weight : Cal.Weekday → Weight; arrival : Cal.Weekday → Clock
  wakeToday : Cal.Instant; expectedWake : Cal.Weekday → Clock
  curves : Curves; dayCfg : DayCfg; tz : Cal.Tz; walls : List (Nat × Nat)   -- indexed once
def mkInput? (…) : Except CapErr Input                    -- days ≤ maxLookaheadDays, else lookaheadTooLong (R10)
def pureDay (I : Input) (loc : Loc) (d : Nat) : Hist        -- window, cut, energise, limit
def lookahead (I : Input) : List DayCapacity :=             -- a foldl over the day range, then reverse (D9-21)
  ((List.range I.days).foldl (fun acc i =>
    let d := I.today + i
    (if i = 0 then ofHist d I.day0 else ⟨d, mix (I.weight (Cal.weekdayOf d)) (pureDay I .lounge d) (pureDay I .home d)⟩) :: acc) []).reverse
```

`List.range` over ≤ 3,660 is built by a tail-recursive loop in core (`List.range.loop`), so the
recursion rule holds. T0 runs `lookahead` with `days = 3,660` on a 2 MiB thread (§14.1).

**Proved in L5:**
- `lookahead_keeps_the_days`;
- `lookahead_is_a_lookahead`: `(lookaheadOf? capDen (lookahead I)).isSome`;
- `lookahead_at_a_certain_weight_is_the_pure_location`;
- `lookahead_between_the_locations`;
- `mixing_before_the_budget_is_not_the_expectation` (witness: budget 60, `L = {5:60, 4:60}`,
  `H = {3:120}`, `w = capDen / 2`);
- `mkInput?_refuses_too_many_days`;
- on a loaded plan (`Boundary.lean`): a Wednesday calendar wall 12:50–13:50 gives Wednesday's window end
  16:00, and the twin's capacity equals the fork value written out by hand. The plan literal is the
  smallest one with one wall (≤ 6 lines), and `loadPlan` is reached through its existing round-trip
  theorem, not unfolded under `decide` (CRIT 13).

**If the owner answers Q2 with (b)**, L2–L4 are skipped. `pureDay` becomes a request argument (two
`[u32;6]` per future day), recorded as a gap "future-day histograms are the host's", and L5's first two
theorems still hold.

### 13.5 Day 0 (interim, then derived in L9)

- **Interim, L1–L8.** `day0 : Hist` is a plain argument, filled by the host from `Ctx::today_slots` then
  `DayCapacity::from_slots`. It is one `[u32;6]`, recorded as gap 93. After the switch, `today_slots`
  reads kernel-decoded facts, so it stays correct through S.
- **L9, after S.** The kernel derives day 0 from:
  - today's window (the stored one or the formula), cut from `now`'s instant (a new wire stamp `at`,
    whose local date must equal `now`, else `nowDisagrees`);
  - the replay's `energy_on(today)` posterior, through `Arith.energyAfter`/`ramp` over minutes;
  - `wakeToday` in seconds through site R11;
  - the sleep shift at site **R10** (half away from zero on a signed value;
    `under_slept ⇔ slept · den < 60 · num`);
  - `allow_home`.

  Parity is against `Ctx::today_slots` exactly, not P1. The `day0` argument is deleted, and gap 93
  closes.

### 13.6 The wire for capacity, and the host's one encoder

```jsonc
"capacity": {
  "pLounge":  {"model": {"Mon": {"num": "9", "den": "10"}}, "config": {"Mon": {"num": "9", "den": "10"}, "…": "all 7"}},
  "arrival":  {"model": {"Mon": "07:10"}, "config": {"Mon": "07:00", "…": "all 7"}},
  "wake":     {"today": "2026-09-14T06:05:40-05:00", "model": {"Mon": "06:00"}, "config": {"Mon": "06:00", "…": "all 7"}},
  "energy":   {"lounge": [4,5,5,5,5,4,4,4,3,3,2,2], "home": [3,4,4,4,3,3,3,2,2,2,2,2]},     // exactly 12 each, each < 256
  "prior":    {"lounge": [{"from": {"num":0,"den":1}, "to": {"num":1,"den":1}, "level": 4}], "home": []},
  "homeMaxCi": 3,
  "day": {"breakMin": 20, "breakAfterBlocks": 2, "blockMin": 50, "minLastBlockMin": 30,
          "windowHours": {"num": 8, "den": 1}, "windowCap": "19:00", "budgetRatio": {"num": 75, "den": 100}},
  "priority": {"bins": [{"num":5,"den":10}, …], "safety": {"num":13,"den":10}, "defaultPriority": 3},   // gap 77's decoders, called at last
  "days": 7,
  "day0": [0, 0, 60, 120, 60, 0]                                            // until L9
}
// response
"lookahead": {"den": "1000000000000000000",
              "days": [{"day": "2026-09-15", "numAt": ["…", "…", "…", "…", "…", "…"]}, …],     // first min(days, 7); digit strings
              "grants": [{"id": "667", "avail": "…", "reserved": "…", "shortfall": "…", "bin": 1}, …]}   // numerators over den, digit strings
```

**R10 for the capacity section** (CRIT 14). Each bound has a smart constructor and a rejection theorem
in L6:

| value | bound | refusal |
|---|---|---|
| `pLounge` num/den | digit strings, `den ≥ 1`, `num ≤ den`, `capDen % den = 0` (≤ 18 places under Q8 (b)) | `badWeight`, `weightAboveOne`, `weightPrecision` |
| clocks (`arrival`, `wake` model/config, `windowCap`) | `HH:MM`, `< 24:00` | `badClock <key>` |
| `wake.today` | a stamp, local date `= now` or `now − 1` | `badWake` |
| `energy.*` | exactly 12 entries, each `< 256` | `badCurve <loc>` |
| `prior.*` | ≤ 64 ranges; keys `den ∈ [1, 10^6]`, `num ≤ 48·den`, `from < to`; level `≤ 5` | `badStep`, `badLevel` |
| `homeMaxCi` | `≤ 5` | `badCap homeMaxCi` |
| `breakMin`, `blockMin`, `minLastBlockMin` | `1..=1440` (`breakMin` may be 0) | `badDay <key>` |
| `breakAfterBlocks` | `≤ 64` | `badDay breakAfterBlocks` |
| `windowHours` | `den ∈ [1, 10^6]`, `0 < num ≤ 24·den` | `badDay windowHours` |
| `budgetRatio` | `den ∈ [1, 10^6]`, `num ≤ den` | `badDay budgetRatio` |
| `days` | `1..=3660` | `lookaheadTooLong` |
| `day0` | 6 entries, each `≤ 1440` | `badDay0` |
| `priority` | gap 77's decoders (`binsOfPairs?`, `safetyOf?`, `defaultPrioOf?`) | their names |
| zone offsets on lookahead days | whole minutes | `badTz subMinuteOffset` |

**Why unit counts are strings.** At `capDen = 10^18` one minute is `10^18` units, past 2^53 and past
`u64`. Strings keep R10's "every emitted numeral is below 2^53" true by construction, and the host
parses them into `u128`: 3,660 days × 1,440 minutes × 10^18 ≈ 5.3·10^24, far below 2^128.

**The host encoder** is `kernel_bridge::decimal_pair(x: f64, max_places: u32) -> Result<(String, String), CapErr>`.
It takes the shortest round-trip `Display` text, splits at the decimal point, and refuses NaN,
negatives and more places than allowed.
- It is **the only** way an `f64` reaches the kernel for capacity or priority (step 1's route).
- It is also checked when `Model` and `Config` load, so the verb names the file and key (§13.2).
- The kernel's refusal is the authority.
- T15 is its proptest.

### 13.7 Parity for D10 (step L7)

- **The twin.** Every weight is replaced by `if 2w ≥ capDen then capDen else 0`. Require
  `twin.numAt = capDen × fork lookahead.minutes_at_level`, day by day and level by level, modulo P26,
  P27 and P30. Priorities on the twin must equal fork `priority::compute`, modulo P2, P3, P7, P8 and
  P10–P12.
- **The real run** must satisfy `lookahead_between_the_locations` numerically against the twin's
  `pureDay` histograms (a harness-only export). Day 0 must be identical to the twin's.
- **Fixtures:** `kernel/corpus/plan-*` × `kernel/corpus/model.json` × generated wall layouts, including
  multi-day walls (Q6e is reproduced), DST-crossing walls (exact through B1) and wakes with seconds
  (exact through site R11).

### 13.8 Every consumer of `DayCapacity`, and what it holds after D10 (CRIT 5)

**The rule.** A floor may only ever *display*. Anything that decides placement, availability or a bin
holds exact units over `capDen`.

| consumer at `4748911` | what it does with capacities | after D10 | step |
|---|---|---|---|
| `capacity::lookahead` | produces them | **moves into the kernel** (`Look.lookahead`) | L5 |
| `priority::compute` (`capacity::reserve(&mut work[..n], take, c.ci)`), `floor_pass` | EDF reservation, availability, bins | **moves into the kernel** (step 3's `edf`, the stage-5 priority wiring; gaps 79–80) | L8, jointly with the priority wiring |
| `ctx.rs` `Ctx::priorities` | returns the caps with the priorities | passes the kernel's `lookahead.days` through as `u128` units with `den` | L8 |
| `planner.rs` week allocation (`take = left.min(day.at_least(c.ci))`, `capacity::reserve(std::slice::from_mut(day), take, c.ci)`) | places each candidate's remaining minutes on future days | **stays Rust until stage 6's planner.** It works in `u128` units: `take` in units is `min(left · capDen, atLeastUnits)`, and `planned_min` is shown as a floor. T16 tests it against `reserveRest`. Gap 94 records it as a second reserve | L8 |
| `planner.rs` `total` | `capacity.iter().map(DayCapacity::total).sum()` | `floor(Σ units / capDen)`, **the floor of the exact sum** | L8 |
| `planning.rs` `week` | emits `minutes_at_level` and `total` | display floors, each of its own exact value, plus exact fields per Q4 | L8 |
| `tui/app.rs` | holds the caps for display and the queue | `u128` units with `den` | L8 |
| `tui/queue.rs` (`fits += capacity::reserve(&mut caps, remaining, row.ci)`) | "does it fit" | **stays Rust** until stage 6's TUI tranche, in `u128` units; T16; gap 94 | L8 |

**T16 `rust_unit_reserve_is_the_kernels`** (proptest, 256 cases). Random `List DayCapacity` over
`capDen` and random `(need, ci, due)` sequences go through Rust's unit `reserve` and through the
kernel's `reserveRest`/`reserveOut` via a harness op. The remaining units and the grants must be
identical.

---

## 14. The build plan

### 14.0 Before any step

1. **Numbers.** Step 3 and its repair have landed. Gaps run to 81, cheats to 90 and parity entries to
   P12 (README "Stage 5 repair"). This plan's labels are therefore gaps **82–99**, cheats **91–118**
   and parity **P13–P31**. Before each commit, re-read the README's newest block. If the in-flight
   stage-5 core took numbers meanwhile, renumber *before* committing, never after (AGENTS §6.2, §6.4),
   and keep the label-to-number map in the README block.
2. **Sequencing against the in-flight core.** Steps that edit `Json.lean`, `Boundary.lean`,
   `Goals.lean`, `Check.lean` or `Negative.lean` start only after that work has committed, each in its
   own worktree. `Check.lean` is edited by one agent at a time (AGENTS §6.3).
3. **Memory.** Every `lake`, `lean`, `cargo` and `check.sh` run is capped with
   `systemd-run --user --scope -p MemoryMax=40G -p MemorySwapMax=0 --quiet`. Every probe, benchmark and
   generator run by a design or measurement step is capped at `MemoryMax=16G`.
4. **The `decide` budget** (AGENTS §5.10a and the memory lesson; CRIT 13):
   - every new `decide` or `rfl` witness is probed first in a scratch copy under
     `MemoryMax=8G timeout 120`;
   - a witness holds at most 8 `Entry` values, at most 2 zone transitions, and literals of at most 90
     characters. Instants are `Nat` literals, never parsed text;
   - an input of realistic size is **never** evaluated. It is an instance of a round-trip theorem
     (`readCkpt_emitCkpt`, `jparse_jemit`, `loadPlan`'s existing laws), used as a rewrite;
   - a probe that exceeds 8 GB or 120 s is split into per-arm lemmas. `native_decide` is never used;
   - per step: at most 20 new probed witnesses, and `check.sh`'s wall time may rise by at most 10%,
     measured and recorded in the README block. A step that needs more stops and says so.
5. **The recursion rule (D9-21).** Each step's README block lists every function it adds that recurses
   over a list the wire can make large, with its `foldl` form or its `@[csimp]` twin.
6. **Every step commits green:**
   - `check.sh` gives 7 `ok` lines;
   - `cargo test --workspace` passes with 0 failed; record the count;
   - the FFI suite passes;
   - `cli_latency.rs` is green;
   - the README gets a block with goals discharged, refuted and added, parity entries, behaviour rows,
     theorem counts and measured figures;
   - a step that adds a module adds its `import` line in `TmKernel.lean` in the same commit
     (`cat TmKernel.lean`; count the imports).
7. **Rules for goals.** A `Goals.lean` goal enters in the step whose definitions let it elaborate
   (provisional `def … := sorry` only where this document fixes the signature). It leaves when proved,
   appended to `Check.lean`. The burn-down rises only where a step says so.
8. **Owner answers gate steps**, as §4's "Blocks" lines say: Q2 before L2; Q3 and Q7 before W1; Q7
   before R11; Q8 before L6; Q4 before L8; Q9 (i) and (iii) before S. "Take the default" is an answer.

**Cost columns** are ESTIMATE: Lean definition lines / Lean proof lines / Rust lines / agent-days.

### 14.1 Phase A: prerequisites (kernel; the binary's behaviour changes only in named request error texts)

| step | files | what | proved in the step | acceptance | cost |
|---|---|---|---|---|---|
| **A1** gap 44 and the recursion rule | `Json.lean`, `Line.lean` (`splitDoc`) | accumulating twins `jarrAcc`, `jtailAcc`, `jobjAcc`, `jotailAcc`, `jemitTailAcc`, `jemitOTailAcc` and `splitDocAcc`, each behind `@[csimp]`, in the `junescapeTR` pattern; the rule D9-21 written into the README as a per-step checklist item | `jtail_eq_jtailAcc`, `jotail_eq_jotailAcc`, `jemitTail_eq_jemitTailAcc`, `jemitOTail_eq_jemitOTailAcc`, `splitDoc_eq_splitDocAcc` | **T0 (a)** `a_200000_element_array_reads_on_a_2mib_thread` (explicit `stack_size(2 << 20)`), for arrays of strings and of objects; gap 44 closed in the README | 150 / 800 / 40 / 3–4 |
| **A2** decimals, gaps 42 and 43 | `Json.lean`, `Boundary.lean` (new arms), `kernel_bridge.rs` tests | §5.1 | §5.1's table; the refutation and rename of `jparse_refuses_what_the_fragment_has_no_type_for` | FFI tests for `-0.5`, `1e5`, `007`, a request `-3`, a surrogate pair and a lone surrogate; behaviour rows; `the_response_call_emits_parses_back` re-proved | 150 / 900 / 60 / 4–5 |
| **A3** harness | `kernel/tm-kernel-ffi/examples/logbench.rs`, `tm/tests/support/loggen.rs` (a seeded port of `genlog.py`/`genlog80.py`) | prints wall ms and `VmHWM` for: (a) the wire parse on 1 mo, 6 mo, 1 y and 3 y at 40 and 61 events a day, as line arrays; (b) FNV-1a-64 over 6.9 MiB under the dev profile; (c) the hourly tz probe for Chicago; (d) RSS for a 1 MiB and a 4 MiB line array, which checks D9-12's memory cap | — | runs under `MemoryMax=16G`; the README quotes one measurement per number (AGENTS §5.11), replacing §18's MEASURED-by-a-design and ESTIMATE figures. **If (d) exceeds 256 MiB at 4 MiB, the resend cap in §9.7 is lowered before W3** | — / — / 400 / 1–2 |

### 14.2 Phase B: time and grammar (kernel; nothing in the binary calls it)

| step | files | what | goals (added → discharged) | acceptance | cost |
|---|---|---|---|---|---|
| **B1** time and zone | `Cal.lean` | §5.2 (with chrono's leap-second duration rule), §6.1 (kernel side), §6.3 `instantOf` | in-step: `offsetAt_reads_the_last_transition`, `instantOf_is_local_dt_on_an_unambiguous_time` (§15); §5.2's and §6.1's lists | check.sh; probes; cheats 91 (a transition applied one second early), 92 (an instant ordered by its written clock) | 330 / 850 / — / 4–5 |
| **B2** stamps | `Stamp.lean` (new; imports `Cal`, `Line`) | §5.3, `renderStamp`, `displayStamp` | in-step: `parseStamp_renderStamp`; the order witness | check.sh | 200 / 600 / — / 3–4 |
| **B3** events and lines | `Log.lean` (new; imports `Json`, `Stamp`); `Goals.lean` header fix (the stale `PlanCore.log` sentence) | §5.4–§5.6, `finiteF64` over every numeral, `renderLine` | adds `the_log_reads_what_it_renders`, `a_known_event_is_never_read_as_unknown`, `an_unknown_tag_is_never_a_warning`, `lineTooLong_bounds_every_string` → all discharged in B3; in-step: `an_out_of_range_numeral_warns_even_in_an_unknown_event`, the per-warning witnesses, the per-line corpus theorems | check.sh; cheats 93 (an unknown tag read as a warning), 94 (a known event with a bad field read as unknown), 106 (`finiteF64` applied only to `hsw`). **Before B3 freezes the grammar,** a throwaway Rust probe pins §5.4's numeric, duplicate-key and float-band rows against serde; it becomes T1's crafted set | 950 / 2,600 / 100 / 9–12 |
| **B4** the `log` op, grammar only | `Boundary.lean` (a new section, appended), `tz_table.rs` (hourly probe, §6.1), `kernel_bridge.rs` (refusal names), `tm/tests/kernel_log_grammar.rs` | `tz`; `log` with `ckpt: null`; the response's `lines`, `warnings`, `headers` (tag and id only), `render`; `mkLogReq?`, `mkTz?` rejection theorems | extends `the_response_shapes_emit_in_build_order` | **T1** `kernel_reads_the_corpus_logs_as_the_fork_point_did`: per line entry, warning class or blank, over the four corpus logs, `malformed.jsonl` and the crafted set (out-of-range numerals in unknown payloads, the `k ∈ [308, 310]` band, `-0`, `3.0`, repeated keys). **T2** `kernel_reads_what_the_rust_writer_writes`: proptest of 256 `Event`s through serde, then kernel `render`, byte-identical. **T3** `kernel_reads_every_timestamp_spelling_chrono_reads`, `:60` included. **T4** (a) and (b) in the suite; (c) and (d) `#[ignore]`d, run once here, results recorded (§6.4) | 250 / 300 / 600 / 4–5 |

### 14.3 Phase R: the Rust seams (Rust stays the only reader; interleaves with B, C, W)

Each step changes one consumer or one fact family.
- **Its equivalence test** compares the old function with the new one over the four corpus logs plus
  the generated 1-month log, and is deleted with the old function in the same commit.
- **Assertions** of existing suites do not change, except R9's display ties if any (P21).

| step | what | acceptance beyond both suites |
|---|---|---|
| **R-audit** | Re-grep **every accessor by name**: `done_items`, `is_done`, `last_done`, `done_dates` (every use, not only `.first()`/`.len()`), `ItemReplay.minutes`/`.blocks`, `done_minutes_map`, `block_minutes_on`, `block_minutes_on_day`, `instances_of`, `events_named`, `events_for`, `stamps`, `day(d)`, every iteration over `days`, `energy`, `durations`, `demotions`, `open_block`, `last_cut`, the open interruption, `days.keys().last`, `warnings`, `unknown`. For each call site record which dates it can ask for (today's periods, `≥ T − 16`, an explicit old date, all) and assign §11.1's scope. Record it in the README | the table committed. **A call site in `Hot` scope that can ask for a date below `H` blocks W1** until the family moves to the fuller form or the verb's scope changes |
| **R1** | `DayReplay.since_break` (last `break`'s `t + actual`, else first `start`); `day.rs` `since_break_min` reads it | `cli_day` |
| **R2** | `DayReplay.idle_marks` (the day's pause, interrupt, unpause, resume and break marks in file order); `idle_min_since` reads them | `cli_day` |
| **R3** | `Replay.last_effective_t` (last survivor in file order, any kind); `day.rs` `idle`. Accessor narrowing: `done_date_first`, `done_date_count` and `latest_named(name, id)` replace `done_dates(key)` and `events_named(name)` in `recur.rs`/`priority.rs` | `recur_*`, `priority_*` |
| **R4** | `DayReplay.last_t` (maximum `t` over survivors of the day, any kind); `app.rs` `idle_since`; `AppData.log` and `App.log` removed | `tui_*` |
| **R5** | `Replay::view` rows `(line, entry, day, cancelled, display)` and `entry_count`; `lifecycle.rs` `log` reads them and prints `display` instead of formatting `e.t` itself | `cli_lifecycle`; `tm log` human and `--json` output byte-identical on the corpus |
| **R6** | `Replay::headers_from(line)`; physical line counts in `Recorder`; `UndoEntry.log_line: Option<u64>` | `cli_undo`; new `a_malformed_line_does_not_shift_the_recorded_events` (P18) and `an_undo_stack_written_before_log_line_still_undoes` (CRIT 27) |
| **R7** | `PlanInput.log` deleted | planner suites |
| **R8** | `Ctx.log` and `read_log` removed. `Ctx::replay_of(store, cfg) -> Replay` is the only code that reads `LOG_PATH` | **one-reader grep** over `src/` **and** `tests/` of both crates, `horizon.rs` included: `grep -rn 'LOG_PATH\|Log::parse\|Log::new\|iter_day\|effective()\|day_index(\|undo_mask\|parse_timestamp' tm tm-core --include=*.rs` shows only the chokepoint, the writer, `log.rs` and the test files R12 will switch, listed by name (CRIT 31) |
| **R9** | `DayReplay.load` becomes `load_fifths` with `load()` | review suites; any `round1` tie recorded as P21 **here, in Rust, so the switch changes no display** |
| **R10** | torn-line repair before appending (G9) | new `an_append_after_a_torn_line_starts_a_new_line` (P19) |
| **R11** | per OWNER Q7: default (a) deletes the unread facts from `Replay` | `log_replay__three_days_replay.snap` updated in the same commit; nothing else changes (P22). **Blocked on Q7** |
| **R12** | the test chokepoints: 18 tm-core files (45 call sites) call `replay_of_text(text, tz)`; `tui_common/mod.rs`, `tui_queue_common/mod.rs` and `tui_today_prompts.rs` call `app_with_log_text` | test counts before and after recorded; R8's grep now lists no test file |
| **R13** | observations carry `line`; `Replay.energy`/`durations` sorted by it. `Ctx::replay_with(scope)` is introduced with §11.1's scopes. Before the switch every scope returns the full in-memory `Replay`, but each verb already asks for its scope, so S changes only the body | `energy_fit`, `review_*`; a test that each verb family asks for the scope §11.1 names |
| **R14** | **latency with history**: `cli_latency.rs` gains `a_verb_with_a_year_of_log_takes_well_under_a_second` (the history tree plus a 365-day `loggen` log at 61 events a day, fixed seed; `FIRST_VERB` 5 s, `LATER_VERB` 1 s), and an `#[ignore]`d 3-year variant whose numbers are recorded | green against the **Rust** reader; this is the switch's baseline |

**Phase R cost:** ≈ 550 Rust lines changed, ≈ 450 of tests, 8–10 agent-days.

### 14.4 Phase C: the kernel replay (kernel; test-only; T5 against the in-tree Rust)

**T5** is `tm/tests/kernel_replay_parity.rs`. It decodes the kernel's `facts` from a genesis call
without `reseal`, and compares them field by field with `Ctx::replay_of` over:
- the four corpus logs;
- the generated 1-month and 6-month logs;
- **256 generated sequences** mixing: undos (a silent-verb undo among them), out-of-order wakes, retro
  `break`/`idle`, interleaved housekeeping closes between a command and its undo, a partial `done`
  after `stop`, `extend`, and a `:60` stamp inside a block (CRIT 29);
- **the zone cases of §6.4** (CRIT 11), each as its own generator arm: a 01:30 wake on the fall-back day
  using the ambiguous hour twice; a wake after midnight under 24 hours after the previous one; events
  23–25 real hours after a wake across both transitions; a DST fold at midnight where consecutive dedup
  differs from earliest-per-date (in a zone that has one, e.g. a historical `America/Havana` or
  `Asia/Beirut` table); one day with written offsets `-05:00` then `+02:00`; `cfg.tz` different from
  the writer's `Local`;
- exceptions only from §17.

| step | files | what | goals (added → discharged) | T5 compares | cost |
|---|---|---|---|---|---|
| **C1** mask | `Replay.lean` (new; imports `Log`, `Arith`) | §7.1 with its fast twin | adds `survivors_snoc_event`, `survivors_snoc_undo`, `a_cancelled_event_is_never_revived`, `a_dangling_undo_dangles_in_every_extension` → discharged; in-step `survivors_eq_survivorsFast`; cheat 95 (an undo that does not cancel itself) | the cancelled line set | 200 / 1,200 / 150 / 4–5 |
| **C2** day index | `Replay.lean` | §6.2 | adds `dayOf_is_the_wake_date_within_a_day`, `a_wake_day_is_shorter_than_a_day`, `keptWakes_append_of_later` → discharged; cheat 96 (a 25-hour day) | every survivor's day | 150 / 750 / — / 3–4 |
| **C3** effects and block family | `Replay.lean` | §8.1–§8.2 for `start`, `pause`, `unpause`, `interrupt`, `resume`, `stop`, `done` (partial included), `extend`; `credit`; site R8 | adds `applyEffects_touches_only_named_keys`, `every_known_event_has_an_arm`, `credit_conserves_the_day_minutes` → discharged; site R8's pair; the rule witnesses, the partial-`done` pair and `an_extend_changes_only_the_bookkeeping` | block fields | 500 / 1,150 / — / 4–5 |
| **C4** completion family | `Replay.lean` | `routine`, `skip`, done sets, instances | adds `last_done_is_the_latest_by_instant`, `an_instance_is_its_last_record_in_file_order` → discharged; `instances_and_last_done_order_differently` | completion fields and replay warnings | 300 / 700 / — / 3–4 |
| **C5** day header and records family | `Replay.lean` | `wake`, `arrive`, `loc`, `plan`, `break`, `idle`, `energy`, `event`, `demote`, `drop`, `close`, `note`, `edit`, `move`, `readopt`, `unknown` | adds `energy_obs_slept_is_the_days_first_logged_sleep` → discharged; `the_first_leak_maximum_wins`, `a_demote_stamp_reads_the_week_or_date_key`, `idle_and_idle_since_read_different_orders` | day fields | 300 / 700 / — / 3–4 |
| **C6** facts emitter, observations, headers | `Replay.lean`, `Boundary.lean` (`facts`, full `headers` with `display`) | §8.4's view; `factsView`; `ask`; observations with lines; the `header` effect for every line; the seam facts (R1–R4) | adds `observations_are_in_file_order`, `every_dated_output_names_its_day_key` → discharged; cheat 105 (an observation keyed `global`) | **the entire `Replay`** | 270 / 600 / 100 / 3–4 |
| **C7** the undo law | `Replay.lean` | §7.3 | adds `undoing_a_command_replays_the_log_without_it`, `undo_of_a_silent_verb_cancels_an_older_event`, `undo_after_housekeeping_cancels_the_housekeeping` → discharged; cheat 107 (`undosFor` oldest first) | T5 gains 64 generated `(L, E, M)` triples: half meet `untouchedBy` and must satisfy the law; half violate it and must reproduce the fork's cancellation | 100 / 1,500 / 80 / 4–5 |

### 14.5 Phase W: windowing (kernel; test-only)

| step | files | what | goals (added → discharged) | acceptance | cost |
|---|---|---|---|---|---|
| **W1** types and codecs | `Seal.lean` (new; imports `Replay`) | `Header`, `DayRecord`, `WindowRecord`, `Ckpt`, `Meta`, `Resealed`, `Policy`, `Refusal`, `Seal.Q`; `emitCkpt`/`readCkpt`, `emitDayRecord`/`readDayRecord`, `emitWindowRecord`/`readWindowRecord`; `Ckpt.empty`, `ckptOf`, `sealable`, `horizonOf`, `dayRecordsBelow`/`Between`, `windowRecordsBelow`/`Between`, `answer`, `askAnswer`, `askMerged`. **Blocked on R-audit, Q3 and Q7** | **adds §15's W block: 16 goals** with provisional `resume`, `foldPoint`, `sealDay`, `reachFree`, `tagsClear`, `genesis` as `sorry` defs. **The burn-down rises by 16, a deliberate debt.** In-step: the three codec round trips | check.sh; cheat 97 (a view without `lastDone` still satisfies the partition law on its minimal witness: two `done` entries of one id on two days); cheat 98 (`readCkpt` defaulting a missing `ledgerDay` to 0) | 450 / 900 / — / 4–5 |
| **W2** seal, resume, the laws | `Seal.lean` | `resume` with G0–G4 and the `now` anchor; `foldPoint` (greatest valid cut, one pass); `sealDay`; `settled`; `futureFloor`; compaction to `H'`; record emission | discharges the 16 via §9.5's route; in-step: `resume_without_the_guards_is_not_replay`, `a_spurious_tag_refusal_exists`, `foldPoint_valid`, `foldPoint_greatest`, `dayOf_agrees_two_days_before`, `an_instant_before_the_stored_wakes_is_sealed`, `dayOf_with_no_folded_wake_reads_the_tail`, `the_unterminated_segment_is_never_folded`. **The laws' instances go through the codec round trips as rewrites and are never evaluated** (§14.0 item 4). **Stop condition:** if `resume_is_replay` or `resume_ok_iff` will not close, raise it to the owner (AGENTS §9.1). D5 forbids replacing a law with T6 | check.sh; cheats 99 (a resume accepting an unsettled undo whose target is folded), 100 (a ledger day that moves backwards), 101 (a reseal that leaves a folded-target undo out of `settled`, accepted afterwards), 102 (window compacted to `H + 1`), 103 (`F` not bounded by `now`), 104 (an unterminated last segment folded) | 600 / 4,600 / — / 14–17 |
| **W3** wire, genesis, files | `Boundary.lean` (`log`: `ckpt`, `from`, `lines`, `terminated`, `reseal`, `want`, `sealed`; refusals), `kernel_log.rs` | §9.6–§9.8, §10; the snapshot rule, generations and collection; back-off; genesis with exact pops and the 32,768-line / 4 MiB resend cap *(Superseded at W3 by gap 102's measurement: 8,192 lines or 1,536 KiB, chunks of 4,096 lines or 768 KiB; README "Stage 5 D9 W3".)*; the unwritable-cache fallback | in-step: `the_log_op_emits_only_numerals_below_2_53`; a rejection theorem per §10.4 row; extends the response-shape theorem | **T0 (b)** on a 2 MiB thread: genesis over a generated 200,000-line log (25 chunks) with facts and record emission; one call at exactly 32,768 lines; a reseal emitting ≥ 1,000 day records; a checkpoint at every §10.4 maximum through `readCkpt` (CRIT 10). **T6** `resume_equals_genesis_at_fifty_cuts` (6-month log, kernel against kernel). **T7** each refusal (`undoReach`, `wakeBehindCut`, `sealedDay`, `sealedWindow`, `nowBelowLedger`) followed by a fallback equal to genesis; `nowBelowLedger`'s answer is not persisted; `a_line_dated_next_year_changes_no_fact_about_today`. **T8** `genesis_in_chunks_equals_one_call`, with forced pops. **T10** cache mutation proptest: flip a prefix byte, truncate, append, a retro line, a far undo, a tz change, **finish a torn last line** (CRIT 8), **a concurrent reseal between reading `ckpt.json` and a month file** and **a deleted month file** (CRIT 7), an unwritable directory. After each, the next call equals a cold genesis | 150 / 400 / 900 / 7–9 |
| **W4** tree-map twin (gated) | `Replay.lean`, `Seal.lean` | `Std.TreeMap` fast twins of the item and window maps behind `@[csimp]`, proved equal to the list spec (the stage-4 `planWf` hardening pattern) | `items_eq_itemsFast`, … | **required** if W5's first run measures genesis above 1.5 s, or a hot call above 60 ms, at 3 y on lists | 250 / 900 / — / 4–6 |
| **W5** measurement gate | `logbench` | genesis total; hot call (checkpoint plus 3 days); reseal call; RSS; digest; **a 10-day stall** (a block left open); **a hand undo 30 days back** followed by 10 verbs (CRIT 19); **an undo stack pinning 14 days** | — | **Gate at 3 y and 61 events a day, dev profile:** hot call ≤ 60 ms including the digest, stalled or pinned; at most one checkpoint write per day during the stall; after the far undo, one rebuild and then hot calls again; genesis ≤ 1.5 s; per-call RSS ≤ 256 MiB. Otherwise W4, then §19's levers, before S | — / — / — / 1 |

### 14.6 S: the switch (one commit)

**Contents.**
1. `Ctx::replay_with`'s body becomes `kernel_log::replay(scope)`. `Recorder`, `tm log` (§11.4's order)
   and `tm model --fit` (the `All` scope) call `kernel_log`.
2. §12's deletions in `log.rs`, `parse_timestamp` included.
3. The consumer tests from R12 move to `tm/tests/` and call the kernel through `replay_of_text`.
4. **T5 is retargeted.** Its in-tree Rust side is gone, so its oracle becomes fork point `4748911`'s
   `log::replay`, through AGENTS §7.3's oracle scaffolding (moved off `main` as §8.3 requires).
   *(Done before S, 2026-09-16, W-11, under **D21**: this one line was a step of work, not a step of
   the commit — see README gap 146. The fork's answers are frozen into `tm/tests/fixtures/` and
   compared inside plain `cargo test --workspace`; the classes too large to freeze reach the fork
   through the `TM_ORACLE` arm, widened from 8 logs to **469 over 6 zones**. What is frozen and what
   is not is settled by D21 and stated in code by `t5_every_input_class_says_how_it_reaches_the_fork`.
   README **gaps 137, 147, 149** closed; residue **gap 150**.)*
5. `kernel_bridge::refusal` gains the `log` names; `TM_KERNEL_ID` from `tm-kernel-ffi/build.rs`.
6. `.gitignore` handling per Q3.
7. Per Q9's defaults: `tm check` lists log warnings, future-dated lines and a `reachTooFar` fault.

**Acceptance.**
- check.sh 7/7; `cargo test --workspace` green, count recorded and compared with R12's.
- **T9**, CLI tests:
  - `tm_undo_across_a_seal_restores_the_facts`;
  - `invalid_utf8_line_is_a_warning_and_tm_check_names_it`;
  - `deleting_the_replay_cache_changes_nothing` (run verbs, `rm -r .tm/cache/replay`, rerun, compare
    every `--json`);
  - `a_changed_tz_invalidates_the_checkpoint`;
  - `a_rewritten_log_prefix_invalidates_the_checkpoint`;
  - `a_line_dated_next_year_changes_nothing_about_today_and_tm_check_names_it`;
  - `a_now_before_the_ledger_is_answered_and_not_persisted`;
  - `an_unwritable_cache_rebuilds_in_memory_with_one_notice`;
  - `a_hand_undo_beyond_the_rebuild_bound_fails_by_name`;
  - `tm_log_is_byte_identical_on_the_corpus` (human and `--json`).
- **T12** `model_fit_is_the_fork_points_on_the_corpus`: `tm model --fit` on `energy-14d.jsonl` writes
  `model.json` byte-identical to fork `4748911`'s (CRIT 4: the fit sees every observation from this
  commit on).
- **T11**, latency: `cli_latency.rs` gains
  `a_verb_on_a_tree_with_three_years_of_log_takes_well_under_a_second`:

  | case | bound |
  |---|---|
  | first verb (genesis + automatic close + drop) | < 5 s |
  | later verb | < 1 s |
  | `--now` + 1 day (a reseal) | < 1 s |
  | after hand-appending an `undo` whose target is 30 days old (one rebuild) | < 5 s, and the next verb does **not** rebuild *(corrected 2026-09-16, S: on a three-year log this is **unreachable** — the pop that undo forces resends 9,039 lines, past gap 102's 8,192-line memory gate, so the answer is the named fault `reachTooFar` (D18 (iii), P31), and **the cap is never raised** (D18). `cli_latency.rs` measures both halves: the 30-day undo must fail by name inside the 5 s bound, and the rebuild bound is measured on an undo the gate can window. README **gap 180**.)* |
  | a routine logged for an instance 3 days old | < 1 s, no rebuild |
  | a block left open, then 10 successive `--now` days | each < 1 s; at most one checkpoint write per day |
  | `tm review week` (the `All` scope) | < 1 s |

  R14's 1-year test stays and is compared with its Rust baseline.
- **The §5.13 drive**, 30 minutes on a copy of a real `.tm/`:
  - `now`, `start`, `pause`, `done`, three `undo`s (one reaching behind the cut);
  - `review week` for this week and for three months ago;
  - `close day` on a **stale** tree, and `review day --date` for a date two months ago. *(Corrected
    2026-09-16, W-10: this item read "`close day` for a date two months ago", which **D1 makes
    unreachable by construction** — a close takes every day that has ended and files into the period
    containing `now` (the kernel's `closeTo`), so `tm close day --date <old>` is refused by name with
    `periodNotTaken`, which is the right refusal. README **gap 131**. The drive item that can be
    performed is the stale-tree close plus the dated **review** the refusal itself points at.)*
  - `model --fit`, `log --since 7d`, `log --item`;
  - the TUI through two reloads, with the CLI running a verb in between;
  - deleting the cache mid-session;
  - a UTF-8-broken line, then `tm check`.

**Why one commit is safe:** consumers read the same (reshaped) `Replay` through the scopes R13 already
wired; T5 proved field equality before the commit; the cache is derived, so a revert needs no data
migration.

**Cost:** — / — / +1,000 −1,750, tests moved / 6–8.

### 14.7 Phase F: after the switch

| step | what | acceptance | cost |
|---|---|---|---|
| **F1** (optional) | `energy::fit_observations` reads the `All`-scope observations directly; `fit_replay` deleted | T12 stays green; no value changes | — / — / 150 / 1–2 |
| **F2** | the recurrence family (`done_dates` first and count, `last_done`, instances, `latest_named`, `is_done`) read inside the kernel by the recurrence tranche; the Rust fields go with their last reader | that tranche's parity; grep shows no Rust reader | in that tranche |
| **F3** | priority rule inputs (`RuleIn.overdue`, `mandatory`, `pass`; `done_this_period` from W's window) computed in the kernel; `horizon::close_day`/`day_remaining`'s `block_minutes_on` moves into the kernel with the close tranche, reading a sealed window record for an old date (D9-13) | the priority wiring's parity; gaps 79–80 | in that tranche |
| **F4** | = L9 | §13.5 | in L9 |
| **F5** (optional, Q5) | the kernel emits the lines to append | `the_log_reads_what_it_renders` end to end | ≈ 1–1.5 weeks |

### 14.8 The D10 track

| step | depends on | files | goals (added → discharged) | acceptance | cost |
|---|---|---|---|---|---|
| **L1** mixture | — (step 3 landed) | `Lookahead.lean` (new) | §13.2's theorems, in-step; `edf_commutes_with_scaling` | check.sh; cheats 108 (swap `w` and `capDen − w`), 109 (accept `n > d`) | 150 / 500 / — / 2–3 |
| **L2** E7 | **B1**; Q2 | `Lookahead.lean`; `Goals.lean` (delete STAGE 6's `wallsInside`, `windowEnd`, E7a, E7b; add the restated E7a/E7b to STAGE 5 → discharged); `Arith.lean` (site R3 row) | E7a, E7b, the two refutations, three fork witnesses | check.sh; cheats 110 (walls wholly inside), 111 (no merge); AGENTS §8.3/§8.4 updated to move E7 | 170 / 650 / — / 4–5 |
| **L3** the cut | L2 | `Lookahead.lean` | the four `cutSlots_*` | cheats 112 (a stretch ending on a break), 113 (the short block dropped) | 130 / 450 / — / 3–4 |
| **L4** energy and limit | L1, **B1** | `Lookahead.lean`; `Arith.lean` (site R11 row) | `hsw100_is_round_half_away`, `the_bucket_reads_seconds`, `limitSlots_is_limitHist`, `futureEnergy_home_is_capped`, 16 fork witnesses | cheats 114 (no home cap), 115 (hours since wake from whole minutes), 116 (bucket without the clamp) | 200 / 550 / — / 4–5 |
| **L5** the lookahead | L2–L4 | `Lookahead.lean`, `Boundary.lean` (loaded-plan witness) | `lookahead_keeps_the_days`, `lookahead_is_a_lookahead`, `lookahead_at_a_certain_weight_is_the_pure_location`, `lookahead_between_the_locations`, `mixing_before_the_budget_is_not_the_expectation`, `mkInput?_refuses_too_many_days` | cheat 117 (mix before limit); **T0 (c)** `lookahead` with `days = 3,660` on a 2 MiB thread | 170 / 550 / — / 2–3 |
| **L6** the wire | L5; step 3's `edf`; gap 77's decoders; **Q8** | `Boundary.lean` (`capacity`, `lookahead`), `kernel_bridge.rs` (`decimal_pair`, `u128` unit strings) | one rejection theorem per §13.6 row; `the_capacity_section_reads_the_corpus_model` (a hand-shrunk `model.json` literal) | **T15** `decimal_pair` proptest; gap 77 closed | 150 / 400 / 300 / 3–5 |
| **L7** parity twin | L6 | oracle scaffolding (AGENTS §7.3) | — (a measurement); P1 refined and P26, P27, P30 recorded **before** the run | **T13** the twin equal to fork × `capDen`; the real run inside the bounds; wakes with seconds and DST walls included | — / — / 250 / 2–3 |
| **L8** wiring | L7; the priority wiring; **Q4** | `ctx.rs` `Ctx::priorities`, `planning.rs` `week`, `planner.rs` week allocation, `tui/queue.rs`, `tui/app.rs` | — | §13.8's table implemented; `cli_plan.rs`/`cli_json_matrix.rs` per Q4; **T16** `rust_unit_reserve_is_the_kernels`; **T14** latency with a `due:` three years out and one ten years out through the shipped binary (`LATER_VERB` holds) | 80 / 150 / 550 / 3–6 |
| **L9** day 0 in the kernel | **S** | `Lookahead.lean`, `Boundary.lean` (`at`), `Arith.lean` (site R10) | parity against `Ctx::today_slots`; site R10's `_withinOne`/`_mono` | cheat 118 (the posterior applied after the cap); gap 93 closed | 200 / 600 / −150 / 4–6 |

### 14.9 Cost, in one table (ESTIMATE; §19 lists what could move it)

| tranche | Lean definitions | Lean proofs | Rust (net) | agent-days |
|---|---:|---:|---:|---:|
| A (prerequisites) | 300 | 1,700 | +500 | 8–11 |
| B (time, grammar, wire) | 1,730 | 4,350 | +700 | 20–26 |
| R (Rust seams) | — | — | ≈ +550 changed, +450 tests | 8–10 |
| C (replay) | 1,820 | 6,600 | +330 | 24–31 |
| W (windowing) | 1,450 | 6,800 | +900 | 30–38 |
| S, F1 | — | — | +1,150 / −1,750 | 7–10 |
| **D9 total** | **≈ 5,300** | **≈ 19,450** | **≈ +4,580 / −1,750** | **≈ 97–126** |
| L (D10) | ≈ 1,250 | ≈ 3,850 | ≈ +950 | 27–40 |
| **D9 + D10** | **≈ 6,550** | **≈ 23,300** | **≈ +5,530 / −1,750** | **≈ 124–166** |

**What these numbers mean.**
- **Against the library.** The stage-4 audit counted 3,917 definition and 18,815 proof lines library-wide
  (AGENTS §4, D5's row). D9 and D10 add about 1.7 times the definitions and 1.2 times the proofs.
- **The ratio** is ≈ 3.6 : 1, below stage 4's 4.80 : 1, because many laws are per-arm `simp` and list
  lemmas. Under D5 it informs and stops nothing.
- **Agent-days** follow the input designs' unit. The stage-4 and stage-5 steps landed several a day, so
  compare lines, not calendar time.
- **About 2 weeks of L (L2–L4) is stage 6's** and comes off stage 6's price.
- **What the revision added** over the first draft (≈ +450 definition, ≈ +1,900 proof lines,
  ≈ +12–15 agent-days): the `now` anchor and future-line fence, sealed window records and the
  query-indexed laws, generation files, the resend cap and T0 (b), the housekeeping undo law, hours
  since wake from seconds, and exact unit reserves in Rust.
- Q1 asks the owner to confirm.

---

## 15. `Goals.lean` additions, as Lean signatures

**The rule.** Each group enters `Goals.lean` under `# STAGE 5` in the step named in its heading,
because only then do its names elaborate. It is deleted when proved and appended to `Check.lean`.
Groups marked *in-step* are stated and proved in the same step, so the burn-down does not move for
them. The file header's stale sentence ("`PlanCore.log` is `List String`", inv §7 item 7) is fixed
in B3.

All signatures assume `open Tm` inside the block. Types the W block names (`Log.Line`, `Seal.Q`,
`Seal.Resealed`, …) are real definitions from B3, C6 and W1; only the functions marked provisional are
`sorry`.

```lean
/-! ############################################################################
# STAGE 5 — D9: the kernel replays `.tm/log.jsonl`; D10: the lookahead mixture
Design: scratchpad `design/stage5-D9-D10-design.md` §5–§13.
############################################################################ -/

/-! ### B1 (in-step): the zone -/
theorem offsetAt_reads_the_last_transition (z : Cal.Tz) (t i : Cal.Instant) (o : Cal.Offset)
    (hmem : (i, o) ∈ z.val.trans) (hle : i.nanos ≤ t.nanos)
    (hnext : ∀ j o', (j, o') ∈ z.val.trans → i.nanos < j.nanos → t.nanos < j.nanos) :
    Cal.offsetAt z t = o
theorem instantOf_is_local_dt_on_an_unambiguous_time (z : Cal.Tz) (d : Nat) (c : Clock) (t : Cal.Instant)
    (hu : Cal.unambiguousAt z d c = true) (hns : t.ns = 0)
    (ht : Cal.localSec z t = d * 86400 + c.val * 60) :
    Cal.instantOf z d c = t

/-! ### B2 (in-step): stamps -/
theorem parseStamp_renderStamp (i : Cal.VInstant) (o : Cal.VOffset)
    (hns : i.val.ns = 0) (hmin : o.val.sec % 60 = 0) (hutc : o.val.sec = 0 → o.val.west = false) :
    Stamp.parseStamp (Stamp.renderStamp i o) = .ok (i, o)

/-! ### B3 (added, discharged in B3): the grammar -/
theorem the_log_reads_what_it_renders (e : Log.Entry) (h : e.canonical = true) :
    Log.readLine e.line (some (Log.renderLine e)) = .entry e
theorem a_known_event_is_never_read_as_unknown (n : Nat) (l : List Char) (e : Log.Entry)
    (h : Log.readLine n (some l) = .entry e) (hk : Log.isKnownTag (Log.tagIn l) = true) :
    e.ev.isUnknown = false
theorem an_unknown_tag_is_never_a_warning (n : Nat) (l : List Char) (w : Log.LWarn)
    (hshape : Log.isObjectWithStampAndTag l = true) (hu : Log.isKnownTag (Log.tagIn l) = false)
    (hlen : l.length ≤ Log.maxLineChars) (hdepth : Log.depthOf l ≤ Log.maxLineDepth)
    (hfin : Log.allNumeralsFinite l = true) :
    Log.readLine n (some l) ≠ .warn n w
theorem lineTooLong_bounds_every_string (n : Nat) (l : List Char) (e : Log.Entry)
    (h : Log.readLine n (some l) = .entry e) : ∀ s ∈ e.ev.strings, s.length ≤ Log.maxLineChars

/-! ### C1 (added, discharged in C1): the mask -/
theorem survivors_snoc_event (es : List Log.Entry) (e : Log.Entry) (h : e.ev.isUndo = false) :
    Replay.survivors (es ++ [e]) = Replay.survivors es ++ [e]
theorem survivors_snoc_undo (es : List Log.Entry) (e : Log.Entry) (of_ : List Char) (id : Option Log.Id)
    (h : e.ev = .undo of_ id) :
    Replay.survivors (es ++ [e]) = ((Replay.survivors es).reverse.eraseP (Replay.matches of_ id)).reverse
theorem a_cancelled_event_is_never_revived (es fs : List Log.Entry) (e : Log.Entry)
    (hl : Log.linesIncreasing (es ++ fs) = true) (he : e ∈ es) (hc : e ∉ Replay.survivors es) :
    e ∉ Replay.survivors (es ++ fs)
theorem a_dangling_undo_dangles_in_every_extension (es fs : List Log.Entry) (u : Log.Entry)
    (hl : Log.linesIncreasing (es ++ fs) = true) (hu : u ∈ es) (hd : Replay.dangles es u = true) :
    Replay.dangles (es ++ fs) u = true

/-! ### C2 (added, discharged in C2): the day index -/
theorem dayOf_is_the_wake_date_within_a_day (z : Cal.Tz) (kw : List Cal.Instant) (t w : Cal.Instant)
    (hw : Replay.lastWakeLe kw t = some w) (h24 : t.nanos < w.nanos + 86400 * 1000000000) :
    Replay.dayOf z kw t = Cal.localDate z w
theorem a_wake_day_is_shorter_than_a_day (z : Cal.Tz) (ws : List Cal.Instant) (t w : Cal.Instant)
    (hw : Replay.lastWakeLe (Replay.keptWakes z ws) t = some w)
    (hd : Replay.dayOf z (Replay.keptWakes z ws) t = Cal.localDate z w)
    (hne : Cal.localDate z t ≠ Cal.localDate z w) :
    t.nanos < w.nanos + 86400 * 1000000000
theorem keptWakes_append_of_later (z : Cal.Tz) (ws₁ ws₂ : List Cal.Instant)
    (h : ∀ a ∈ ws₁, ∀ b ∈ ws₂, a.nanos < b.nanos) :
    Replay.keptWakes z (ws₁ ++ ws₂)
      = Replay.keptWakes z ws₁ ++ Replay.keptFrom z (Replay.keptWakes z ws₁).getLast? ws₂

/-! ### C3–C6 (added and discharged in their steps): the machine -/
theorem applyEffects_touches_only_named_keys (st : Replay.State) (fx : List Replay.Effect) (k : Replay.Key)
    (h : k ∉ fx.map Replay.Effect.key) : (Replay.applyEffects st fx).valueAt k = st.valueAt k
/-- Every entry, whatever its kind, produces exactly one header effect (C3; CRIT 21). -/
theorem every_known_event_has_an_arm (z : Cal.Tz) (kw : List Cal.Instant) (slept : List (Nat × Nat))
    (st : Replay.State) (e : Log.Entry) :
    ((Replay.effects z kw slept st e).filter Replay.Effect.isHeader).length = 1
theorem credit_conserves_the_day_minutes (z : Cal.Tz) (es : List Log.Entry) (d : Nat) :
    Replay.sumByCi (Replay.replay z es) d + Replay.sumCiUnknown (Replay.replay z es) d
      = Replay.blockMin (Replay.replay z es) d
theorem last_done_is_the_latest_by_instant (z : Cal.Tz) (es : List Log.Entry) (i : Log.Id) :
    (Replay.replay z es).lastDone i = Replay.maxByInstant? (Replay.doneInstants z i (Replay.survivors es))
theorem an_instance_is_its_last_record_in_file_order (z : Cal.Tz) (es : List Log.Entry) (item inst : List Char) :
    (Replay.replay z es).instance item inst
      = (Replay.survivors es).reverse.findSome? (Replay.instRecordOf item inst)
theorem energy_obs_slept_is_the_days_first_logged_sleep (z : Cal.Tz) (es : List Log.Entry) (o : Replay.EnergyObs)
    (ho : o ∈ (Replay.replay z es).energy) (hfs : o.fromStart = false) :
    o.sleptMin = Replay.firstLoggedSleep z (Replay.survivors es) o.day
theorem observations_are_in_file_order (z : Cal.Tz) (es : List Log.Entry) :
    ((Replay.replay z es).energy.map (·.line)).Pairwise (· < ·) ∧
    ((Replay.replay z es).durations.map (·.line)).Pairwise (· < ·)
/-- C6; CRIT 9: an effect that carries a date names that date in its key, so G3/G3w see it. -/
theorem every_dated_output_names_its_day_key (z : Cal.Tz) (kw : List Cal.Instant) (slept : List (Nat × Nat))
    (st : Replay.State) (e : Log.Entry) (fx : Replay.Effect) (d : Nat)
    (hfx : fx ∈ Replay.effects z kw slept st e) (hd : fx.day? = some d) :
    fx.key.date? = some d

/-! ### C7 (added, discharged in C7): the undo law, with housekeeping in between -/
theorem undoing_a_command_replays_the_log_without_it (z : Cal.Tz) (L E M : List Log.Entry) (n : Nat) (t : Cal.VInstant)
    (hE : E.all (fun e => !e.ev.isUndo) = true) (hM : Replay.untouchedBy E M = true)
    (hl : Log.linesIncreasing (L ++ E ++ M ++ Replay.undosFor E n t) = true) :
    Replay.factsView (Replay.replay z (L ++ E ++ M ++ Replay.undosFor E n t))
      = Replay.factsView (Replay.replay z (L ++ M))
theorem undo_of_a_silent_verb_cancels_an_older_event :
    ∃ (L : List Log.Entry) (u : Log.Entry), u.ev = .undo "move".toList none ∧
      Replay.survivors (L ++ [u]) ≠ Replay.survivors L
theorem undo_after_housekeeping_cancels_the_housekeeping :
    ∃ (L E M : List Log.Entry) (n : Nat) (t : Cal.VInstant),
      E.all (fun e => !e.ev.isUndo) = true ∧ Replay.untouchedBy E M = false ∧
      Replay.survivors (L ++ E ++ M ++ Replay.undosFor E n t) ≠ Replay.survivors (L ++ M)

/-! ### W1 (added: the burn-down rises by 16) → discharged in W2: the window
`T₀` is the day a checkpoint was sealed at, `T` the request's day, `L` its ledger day.
`a`: folded lines; `r`: the unfolded lines known when it was sealed (a prefix of the tail `b`). -/
-- provisional, replaced by the real definitions in W2 (signatures fixed by this document)
def Seal.resume (z : Cal.Tz) (T : Nat) (k : Seal.Ckpt) (b : List Log.Line) (terminated : Bool)
    (p : Option Seal.Policy) : Except Seal.Refusal (Seal.Answer × Option Seal.Resealed) := sorry
def Seal.foldPoint (z : Cal.Tz) (T : Nat) (k : Seal.Ckpt) (b : List Log.Line) (terminated : Bool)
    (p : Seal.Policy) : Nat := sorry        -- how many tail lines are folded
def Seal.sealDay (z : Cal.Tz) (T : Nat) (k : Seal.Ckpt) (b : List Log.Line) (terminated : Bool)
    (p : Seal.Policy) : Nat := sorry        -- L'
def Seal.reachFree (z : Cal.Tz) (T₀ L : Nat) (a b : List Log.Line) : Bool := sorry
def Seal.tagsClear (z : Cal.Tz) (T₀ L : Nat) (a r b : List Log.Line) : Bool := sorry
def Seal.genesis (z : Cal.Tz) (T : Nat) (chunks : List (List Log.Line)) (terminated : Bool) (p : Seal.Policy) :
    Except Seal.Refusal (List Seal.DayRecord × List Seal.WindowRecord × Seal.Answer) := sorry

-- law 1: the partition, query by query (CRIT 3)
theorem the_answer_reads_the_replay (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) (q : Seal.Q)
    (hc : Log.contiguousFrom 1 ls = true) (hs : Seal.sealable z T₀ L ls [] = true)
    (hq : q.atOrAbove L (Seal.horizonOf L) = true) :
    Seal.askAnswer (Seal.answer (Seal.ckptOf z T₀ L ls [])) q = some (Replay.ask (Replay.replayDoc z ls) q)
theorem a_day_record_is_the_replays_day (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) (d : Nat) (q : Seal.DayQ)
    (hc : Log.contiguousFrom 1 ls = true) (hs : Seal.sealable z T₀ L ls [] = true) (hd : d < L) :
    Seal.askDayRecords (Seal.dayRecordsBelow z T₀ L ls) d q = Replay.ask (Replay.replayDoc z ls) (.day d q)
theorem a_window_record_is_the_replays_window (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) (d : Nat) (q : Seal.WinQ)
    (hc : Log.contiguousFrom 1 ls = true) (hs : Seal.sealable z T₀ L ls [] = true) (hd : d < Seal.horizonOf L) :
    Seal.askWindowRecords (Seal.windowRecordsBelow z T₀ L ls) d q = Replay.ask (Replay.replayDoc z ls) (.win d q)
theorem seal_partition_is_the_replay (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) (q : Seal.Q)
    (hc : Log.contiguousFrom 1 ls = true) (hs : Seal.sealable z T₀ L ls [] = true) :
    Seal.askMerged (Seal.dayRecordsBelow z T₀ L ls) (Seal.windowRecordsBelow z T₀ L ls)
      (Seal.answer (Seal.ckptOf z T₀ L ls [])) q = Replay.ask (Replay.replayDoc z ls) q

-- law 2: two-run, through the disk (AGENTS §5.9)
theorem resume_is_replay (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line) (term : Bool)
    (j : JVal) (k : Seal.Ckpt) (v : Seal.Answer)
    (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b) (hs : Seal.sealable z T₀ L a r = true)
    (hwire : jparse (jemit (Seal.emitCkpt (Seal.ckptOf z T₀ L a r))) = .ok j)
    (hk : Seal.readCkpt j = .ok k)
    (h : Seal.resume z T k b term none = .ok (v, none)) :
    v = Seal.answer (Seal.ckptOf z T₀ L (a ++ b) [])

-- law 3: the reseal's own answer is the same answer (CRIT 3)
theorem resume_answer_ignores_the_policy (z : Cal.Tz) (T : Nat) (k : Seal.Ckpt) (b : List Log.Line) (term : Bool)
    (p : Seal.Policy) (v : Seal.Answer) (x : Option Seal.Resealed)
    (h : Seal.resume z T k b term (some p) = .ok (v, x)) :
    Seal.resume z T k b term none = .ok (v, none)

-- law 4: two-run: what Rust stored is still true
theorem resume_keeps_the_sealed_records (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line) (term : Bool)
    (p : Option Seal.Policy) (x : Seal.Answer × Option Seal.Resealed)
    (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b) (hs : Seal.sealable z T₀ L a r = true)
    (h : Seal.resume z T (Seal.ckptOf z T₀ L a r) b term p = .ok x) :
    Seal.dayRecordsBelow z T₀ L (a ++ b) = Seal.dayRecordsBelow z T₀ L a ∧
    Seal.windowRecordsBelow z T₀ L (a ++ b) = Seal.windowRecordsBelow z T₀ L a

-- law 5: both directions (§5.8)
theorem resume_ok_iff (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line) (term : Bool) (p : Option Seal.Policy)
    (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b) (hs : Seal.sealable z T₀ L a r = true) :
    (Seal.resume z T (Seal.ckptOf z T₀ L a r) b term p).isOk
      = (decide (L ≤ T) && Seal.reachFree z T₀ L a b && Seal.tagsClear z T₀ L a r b)

-- law 6: two-run: a reseal is a seal, and never past now (CRIT 1)
theorem reseal_is_seal (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line) (term : Bool) (p : Seal.Policy)
    (v : Seal.Answer) (s : Seal.Resealed)
    (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b) (hs : Seal.sealable z T₀ L a r = true)
    (h : Seal.resume z T (Seal.ckptOf z T₀ L a r) b term (some p) = .ok (v, some s)) :
    let k  := Seal.ckptOf z T₀ L a r
    let j  := Seal.foldPoint z T k b term p
    let L' := Seal.sealDay z T k b term p
    L ≤ L' ∧ Seal.sealable z T L' (a ++ b.take j) (b.drop j) = true ∧
    s.ckpt = Seal.ckptOf z T L' (a ++ b.take j) (b.drop j) ∧
    s.days = Seal.dayRecordsBetween z T L L' (a ++ b.take j) ∧
    s.window = Seal.windowRecordsBetween z T (Seal.horizonOf L) (Seal.horizonOf L') (a ++ b.take j)
theorem a_reseal_never_seals_past_now (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line) (term : Bool)
    (p : Seal.Policy) (v : Seal.Answer) (s : Seal.Resealed)
    (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b) (hs : Seal.sealable z T₀ L a r = true)
    (h : Seal.resume z T (Seal.ckptOf z T₀ L a r) b term (some p) = .ok (v, some s)) :
    Seal.sealDay z T (Seal.ckptOf z T₀ L a r) b term p = L ∨
    Seal.sealDay z T (Seal.ckptOf z T₀ L a r) b term p + p.keepDays ≤ T
theorem an_accepted_resume_covers_now (z : Cal.Tz) (T : Nat) (k : Seal.Ckpt) (b : List Log.Line) (term : Bool)
    (p : Option Seal.Policy) (x : Seal.Answer × Option Seal.Resealed)
    (h : Seal.resume z T k b term p = .ok x) :
    k.ledgerDay ≤ T ∧ Seal.horizonOf k.ledgerDay ≤ Cal.monthStart T ∧
    Seal.horizonOf k.ledgerDay ≤ Cal.isoMonday T ∧ Seal.horizonOf k.ledgerDay ≤ T - 16

-- law 7: no loop
theorem a_resealed_checkpoint_accepts_its_own_suffix (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line)
    (term : Bool) (p : Seal.Policy) (v : Seal.Answer) (s : Seal.Resealed)
    (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b) (hs : Seal.sealable z T₀ L a r = true)
    (h : Seal.resume z T (Seal.ckptOf z T₀ L a r) b term (some p) = .ok (v, some s))
    (T' : Nat) (hT : T ≤ T') (term' : Bool) :
    (Seal.resume z T' s.ckpt (b.drop (Seal.foldPoint z T (Seal.ckptOf z T₀ L a r) b term p)) term' none).isOk = true

-- law 8: one code path
theorem resume_from_empty_is_replay (z : Cal.Tz) (T : Nat) (ls : List Log.Line) (term : Bool) (v : Seal.Answer)
    (hc : Log.contiguousFrom 1 ls = true) (h : Seal.resume z T (Seal.Ckpt.empty z) ls term none = .ok (v, none))
    (q : Seal.Q) :
    Seal.askMerged [] [] v q = Replay.ask (Replay.replayDoc z ls) q
theorem resume_from_empty_never_refuses_by_guard (z : Cal.Tz) (T : Nat) (ls : List Log.Line) (term : Bool)
    (p : Option Seal.Policy) (e : Seal.Refusal)
    (h : Seal.resume z T (Seal.Ckpt.empty z) ls term p = .error e) : e.isGuard = false

-- law 9: chunking and exact pops are invisible
theorem chunked_genesis_is_one_replay (z : Cal.Tz) (T : Nat) (chunks : List (List Log.Line)) (term : Bool)
    (p : Seal.Policy) (ds : List Seal.DayRecord) (ws : List Seal.WindowRecord) (v : Seal.Answer)
    (hc : Log.contiguousFrom 1 chunks.flatten = true)
    (h : Seal.genesis z T chunks term p = .ok (ds, ws, v)) (q : Seal.Q) :
    Seal.askMerged ds ws v q = Replay.ask (Replay.replayDoc z chunks.flatten) q

-- law 11: observations
theorem sealed_and_live_observations_are_the_replays (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line)
    (hc : Log.contiguousFrom 1 ls = true) (hs : Seal.sealable z T₀ L ls [] = true) :
    Replay.sortByLine ((Seal.dayRecordsBelow z T₀ L ls).flatMap (·.obs)
                       ++ (Seal.answer (Seal.ckptOf z T₀ L ls [])).obs)
      = (Replay.replayDoc z ls).obs

/-! ### W1 (in-step): law 10, the codecs -/
theorem readCkpt_emitCkpt (k : Seal.Ckpt) (h : k.wf = true) : Seal.readCkpt (Seal.emitCkpt k) = .ok k
theorem readDayRecord_emitDayRecord (d : Seal.DayRecord) (h : d.wf = true) :
    Seal.readDayRecord (Seal.emitDayRecord d) = .ok d
theorem readWindowRecord_emitWindowRecord (w : Seal.WindowRecord) (h : w.wf = true) :
    Seal.readWindowRecord (Seal.emitWindowRecord w) = .ok w

/-! ### W2 (in-step, beside the W1 block) -/
theorem resume_without_the_guards_is_not_replay :
    ∃ (z : Cal.Tz) (T₀ L : Nat) (a b : List Log.Line),
      Seal.resumeUnguarded z (Seal.ckptOf z T₀ L a []) b ≠ Seal.answer (Seal.ckptOf z T₀ L (a ++ b) [])
theorem a_spurious_tag_refusal_exists :
    ∃ (z : Cal.Tz) (T₀ L : Nat) (a b : List Log.Line),
      Seal.reachFree z T₀ L a b = true ∧ Seal.tagsClear z T₀ L a [] b = false
theorem the_unterminated_segment_is_never_folded (z : Cal.Tz) (T : Nat) (k : Seal.Ckpt) (b : List Log.Line)
    (p : Seal.Policy) : Seal.foldPoint z T k b false p < b.length ∨ b = []

/-! ### W3 (in-step): law 13, widths (CRIT 14) -/
theorem the_log_op_emits_only_numerals_below_2_53 (req out : JVal) (h : Boundary.logOp req = .ok out) :
    ∀ n ∈ JVal.numerals out, n < 2 ^ 53

/-! ### L1, L4, L5 (in-step): the mixture and the lookahead -/
theorem mix_between_the_locations (w : Look.Weight) (L H : Look.Hist) (l : Fin 6) :
    Look.capDen * min (L l) (H l) ≤ Look.mix w L H l ∧ Look.mix w L H l ≤ Look.capDen * max (L l) (H l)
theorem mix_denotes_the_weighted_sum {n d : Nat} {w : Look.Weight} (h : Look.mkWeight? n d = .ok w)
    (L H : Look.Hist) (l : Fin 6) :
    Look.mix w L H l * d = Look.capDen * (n * L l + (d - n) * H l)
theorem mixing_before_the_budget_is_not_the_expectation :
    ∃ (w : Look.Weight) (B : Nat) (L H : Look.Hist) (l : Fin 6),
      Look.mix w (Look.limitHist B L) (Look.limitHist B H) l ≠ Look.limitHist (B * Look.capDen) (Look.mix w L H) l
theorem the_bin_does_not_see_capDen (bins : List Arith.Q) (s : Arith.Pos) (rem a k : Nat) (hk : 0 < k) :
    binOfScaledQ bins s rem (Arith.mkPos (k * a) (k * Look.capDen) (by simp [Look.capDen]; omega))
      = binOfScaledQ bins s rem (Arith.mkPos a Look.capDen (by decide))
theorem edf_commutes_with_scaling (k : Nat) (hk : 0 < k) (den : Den) (caps : List DayCapacity) (ds : List Deadline) :
    edf ⟨k * den.val, Nat.mul_pos hk den.property⟩ (caps.map (Look.scaleDay k)) ds
      = (edf den caps ds).map (Look.scaleDay k)
theorem hsw100_is_round_half_away (s : Nat) :
    36 * (Look.hsw100 s).toNat ≤ s + 18 ∧ s + 18 < 36 * ((Look.hsw100 s).toNat + 1) ∧
    Look.hsw100 (-(s : Int)) = -(Look.hsw100 s)
theorem the_bucket_reads_seconds :                       -- wake 06:05:40, slot 07:05:00 (CRIT 6)
    Look.bucket (Look.hsw100 3560) = 0 ∧ Look.bucket (Look.hsw100 3600) = 1
theorem limitSlots_is_limitHist (budgetMin : Nat) (slots : List (Fin 6 × Look.Slot)) :
    Look.limitSlots budgetMin slots = Look.limitHist budgetMin (Look.histOf' slots)
theorem lookahead_keeps_the_days (I : Look.Input) : (Look.lookahead I).length = I.days
theorem lookahead_is_a_lookahead (I : Look.Input) : (lookaheadOf? Look.capDen (Look.lookahead I)).isSome = true
theorem lookahead_between_the_locations (I : Look.Input) (i : Nat) (c : DayCapacity) (l : Fin 6)
    (h : (Look.lookahead I)[i]? = some c) (hi : 0 < i) :
    Look.capDen * min (Look.pureDay I .lounge c.day l) (Look.pureDay I .home c.day l) ≤ c.numAt l ∧
    c.numAt l ≤ Look.capDen * max (Look.pureDay I .lounge c.day l) (Look.pureDay I .home c.day l)
theorem mkInput?_refuses_too_many_days (x : Look.InputIn) (h : Look.maxLookaheadDays < x.days) :
    Look.mkInput? x = .error .lookaheadTooLong

/-! ### L2 (moved from STAGE 6 and restated; added and discharged in L2): E7 -/
theorem the_window_end_solves_the_equation (a wm wc : Nat) (ws : List (Nat × Nat)) :
    Look.windowEnd a wm wc ws = Look.windowBase a wm wc + Look.wallOverlap a (Look.windowEnd a wm wc ws) ws
theorem the_window_end_is_the_least_solution (a wm wc m : Nat) (ws : List (Nat × Nat))
    (hm : m = Look.windowBase a wm wc + Look.wallOverlap a m ws) :
    Look.windowEnd a wm wc ws ≤ m
theorem the_window_end_is_not_the_least_solution_over_walls_wholly_inside :
    (900 = min (420 + 480) 1140 + Look.wallsInside 420 900 [(890, 950)]) ∧
    Look.windowEnd 420 480 1140 [(890, 950)] = 960
```

**Counts.**
- **Kept as debt:** 16 goals and 6 provisional definitions enter at W1 and leave at W2.
- **Transient:** B3, C1–C7 and L2 add ≈ 29 goals and discharge them in the same steps; they appear in
  `Goals.lean` only while their step is open.
- **In-step, never in `Goals.lean`:** the remaining ≈ 25 statements.

**What the W block's quantifiers say, in words** (for the README block, AGENTS §5.2):
- every law quantifies over **every** log `a ++ b`, every checkpoint `ckptOf` builds under `sealable`,
  every request day `T`, and every query `q` (law 1, 8, 9) — not over a witness;
- `sealable` is the only hypothesis on a checkpoint, and it is exactly what `reseal_is_seal` proves of
  the checkpoints `resume` builds, so no law is about checkpoints the code never makes;
- `resume_is_replay` crosses `emitCkpt`, `jemit`, `jparse` and `readCkpt`; the others speak of the
  in-memory checkpoint and inherit the disk through law 10.

---

## 16. `Negative.lean` cheats (append at the end; labels, renumbered at commit per §14.0)

| # | step | cheat | must fail because |
|---|---|---|---|
| 91 | B1 | a zone transition applied one second early | `offsetAt_reads_the_last_transition` |
| 92 | B1 | two stamps of one instant ordered by their written clocks | `stamp_order_is_the_instant_order` |
| 93 | B3 | `{"ev":"mood","level":3}` read as a warning | `an_unknown_tag_is_never_a_warning` |
| 94 | B3 | `est_min:"sixty"` on a known event read as `unknown` | `a_known_event_is_never_read_as_unknown` |
| 95 | C1 | an undo that does not cancel itself | `an_undo_never_survives` |
| 96 | C2 | a 25-hour wake day | `a_wake_day_is_shorter_than_a_day` |
| 97 | W1 | `view` without `lastDone` still satisfies the partition law on its minimal witness (two `done` entries of one id on two days, `L` between them) | `seal_partition_is_the_replay` (G-u) |
| 98 | W1 | `readCkpt` defaulting a missing `ledgerDay` to 0 | `readCkpt`'s field refusal |
| 99 | W2 | `resume` accepting an unsettled undo whose target is folded | `resume_ok_iff` |
| 100 | W2 | a reseal whose ledger day moves backwards | `reseal_is_seal`'s `L ≤ L'` |
| 101 | W2 | a reseal that leaves a folded-target undo out of `settled`, still accepted afterwards | `a_resealed_checkpoint_accepts_its_own_suffix` |
| 102 | W2 | the window compacted to `horizonOf L + 1` (CRIT 3) | `a_window_record_is_the_replays_window` |
| 103 | W2 | `F` computed from the log's latest day without the `T − keepDays` bound (CRIT 1) | `a_reseal_never_seals_past_now` |
| 104 | W2 | an unterminated last segment folded (CRIT 8) | `the_unterminated_segment_is_never_folded` |
| 105 | C6 | an observation effect keyed `global` instead of its day (CRIT 9) | `every_dated_output_names_its_day_key` |
| 106 | B3 | `finiteF64` applied only to `hsw` (CRIT 15) | `an_out_of_range_numeral_warns_even_in_an_unknown_event` |
| 107 | C7 | `undosFor` emitted oldest first | `undoing_a_command_replays_the_log_without_it` |
| 108 | L1 | `mix` with `w` and `capDen − w` swapped | `mix_at_zero_is_home` |
| 109 | L1 | `mkWeight?` accepting `n > d` | `mkWeight?_above_one` |
| 110 | L2 | walls counted only when wholly inside | `the_window_end_is_not_the_least_solution_over_walls_wholly_inside` |
| 111 | L2 | overlapping walls not merged | `the_window_end_solves_the_equation` |
| 112 | L3 | a stretch ending on a break | the documented §4.3 cut witness |
| 113 | L3 | the short last block dropped at `min_last` | `cutSlots_short_block_is_at_least_min_last` |
| 114 | L4 | no home cap | `futureEnergy_home_is_capped` |
| 115 | L4 | hours since wake from whole minutes (CRIT 6) | `the_bucket_reads_seconds` |
| 116 | L4 | the hours-since-wake bucket without its clamp to `0..11` | the `predict` witness |
| 117 | L5 | mixing before the budget limit | `mixing_before_the_budget_is_not_the_expectation` |
| 118 | L9 | the posterior applied after the home cap | the `today_slots` parity witness |

**Witnesses for the W cheats** are per cheat and minimal (CRIT 13): cheat 97 needs two `done` entries,
102 one `done` on `H`, 103 one line dated a year ahead, 104 one unterminated line, 99 and 101 one event
and one undo. None evaluates `emitCkpt` or `jparse`. They reach the disk laws through
`readCkpt_emitCkpt` and `jparse_jemit` as rewrites. Each is built from `Entry` values, not text, and
probed under §14.0 item 4.

---

## 17. The stage-5 parity exception list: D9 and D10 entries

These continue the README's P1–P12 (steps 1–3), and are recorded **before** the harness runs.

| # | site | the kernel | the fork point | authority | step |
|---|---|---|---|---|---|
| **P1 (refined)** | future-day capacity **and everything downstream**: each dated candidate's `avail`, `allocation`, `shortfall`, `u`, bin, `p`, HOT/IMPOSSIBLE class, the floor pass's availability, the week grid | `w·L + (capDen−w)·H` numerators over `capDen`, mixed after each location's budget limit | `capacity::lookahead`: lounge iff `p ≥ 0.5`; `u32` minutes; `f64` `u` | D10; checked through the threshold twin, with bounds on the real run | L7 |
| P13 | a log line that is not UTF-8 | a per-line `invalidUtf8` warning; the verb runs; `tm check` names the line (Q9) | `read_to_string` fails the whole command | G9 (PLAN §4); OWNER Q9 (i) | S |
| P14 | a line over 65,536 characters, or nested deeper than 64 | `lineTooLong` / `lineTooDeep` warning | parsed | R10; gap 44's per-nesting recursion | B3 |
| P15 | line and replay warning text | named constructors (`missingField slept_min`, `unknownInstanceStatus`) | serde's and `Replay.warnings`' free text | AGENTS §5.7 | B3, C4 |
| P16 | an instant outside [1900, 2200) | the table's edge offset | chrono-tz's value | §6.1 | B1 |
| P17 | minute and count sums above `2^32 − 1` | `Nat`; the Rust decoder refuses `minutesOverflow` by name | `saturating_add` | as P5 | C3 |
| P18 | `tm undo`'s recorded events after a malformed line | physical line numbers; the kernel's headers | `log_len` counts the line and `new_events` skips it, so they disagree | inv §0 defect | R6 |
| P19 | an append after a torn last line | starts a new line | the concatenation corrupts both lines | G9 | R10 |
| P20 | `tm log --json` bytes for lines the Rust writer wrote | the kernel's `renderLine`, whose target is byte identity (T2); any residue is listed here | serde re-serialisation | §11.4 | B4, S |
| P21 | `DayReplay.load` at display | exact fifths, divided once | an accumulated `f64` sum; `round1` can differ at a tie | site R9 | R9 |
| P22 | the unread facts of OWNER Q7 | not derived (default (a)) | computed, and shown nowhere | OWNER Q7 | R11 |
| P23 | timestamp edge spellings: fraction digits beyond 9, `:60`, spaces or padding in the fallback, `24:00`, year `0000` | T3's residue, decided against chrono | chrono | §5.3 | B2, B4 |
| P24 | numeric and duplicate-key edges at a known field (`-0`, `3.0` in a `u8`, a repeated key) | T1's residue, decided against serde | serde | §5.4 | B3, B4 |
| P25 | a numeral in serde's float band (`k ∈ [308, 310]`), anywhere in a line | exact `finiteF64` verdict; residue pinned by T1 | serde's fast-path "number out of range" | §5.4 | B3 |
| P26 | a weight or capacity decimal outside the exact domain: `p ∉ [0,1]`, NaN, more than 18 decimal places, a prior key with `den > 10^6`, a level ≥ 256, a curve not of 12 entries | refused by name (§13.6's table); the verb names the file and key | accepted (`p = 1.2` → lounge, NaN → home) | R10; OWNER Q8 | L6 |
| P27 | `window_hours × 60` not whole (e.g. `7.33` h) | `halfUpQ` on the exact pair; exact floor for the budget | `f64::round`; `f64` floor | site R3 reopened | L2 |
| P28 | **conditional**: a window or wall spanning a DST transition | civil minutes | real minutes via `local_dt` | recorded only if L2 lands before B1, and deleted when L2 moves onto `instantOf` | L2 |
| P29 | `tm log` (human and `--json`) of a **hand-appended unknown event** with a non-canonical numeral (`1.50`, `1e3`, `-0`, an integer above `u64`) | printed as written | re-serialised through `serde_json::Value` (`1.5`, `1000.0`, `-0.0`, a float) | CRIT 15; porting ryu's shortest-float printing for hand-written lines only is not worth its cost; OWNER Q9 (iv) | S |
| P30 | a `due:` more than 3,660 days ahead | the deadline sees the capacity of the first 3,660 days | the lookahead runs to the due date | R10; D10-13 | L6 |
| P31 | a hand-edited line that no rebuild can window within 32,768 lines or 4 MiB *(Superseded at W3 by gap 102's measurement: 8,192 lines or 1,536 KiB, chunks of 4,096 lines or 768 KiB; README "Stage 5 D9 W3".)* | the named fault `reachTooFar`; `tm check` reports it | the fork replays it | D9-12; OWNER Q9 (iii) | S |

**Exact by design, so not exceptions** (the harness must report zero differences):
- the undo mask, dangling undos and the housekeeping cancellation included;
- both first-wake rules;
- site R8's per-sub-segment floor;
- `last_done` by instant, and instances by file order;
- `hsw` (lexical);
- observation order (by source line);
- late-bound `slept`;
- day attribution in `cfg.tz` inside the span, leap seconds included;
- every fact about today, whatever the log's last line is dated (the `now` anchor);
- the multi-day wall quirk (Q6e);
- leading zeros refused, as serde does (gap 43 closed);
- surrogate pairs read (gap 42 closed);
- DST-day capacity (through B1);
- hours since wake from a wake with seconds (site R11);
- prior range keys with `den ≤ 10^6` (site R11; LOOK's range-key entry is not needed).

---

## 18. Latency budget math

### 18.1 The bases

| figure | value | provenance |
|---|---|---|
| kernel wire parse | **22 ms per MiB** of request, any shape | MEASURED by LAT on today's release `oneshot`, best of 7 |
| kernel RSS | **63 MiB per MiB** of request | MEASURED by LAT, same runs |
| gap 44 today | 14,941 array elements parse; 22,055 abort on a 2 MiB stack | MEASURED by LAT (objects and strings) |
| Rust today | parse plus replay ≈ 15 ms per MiB; **85–90 ms** per command at 3 y and 61 events a day | MEASURED by the inventory pass, dev profile (inv §4.3) |
| `cli_latency.rs` today | first verb **707 ms**; later verb **55.7–60.8 ms** (226 files, no log) | MEASURED at stage 5 step 2 (README) |
| a 3-year log at 61 events a day | 65,771 lines, 6.54 MiB; ≈ 8.2 MiB as JSON line strings | inv §4.2; LAT §1.1 (+20% escaping) |
| sizes in this design (ESTIMATE) | checkpoint 75–180 KB (900–3,000 ids); tail 20–30 KB normally, ≤ 90 KB with a 14-day undo pin; zone table 20 KB; sealed files ≈ 120 KB a month | §8.4, §9.6, §6.1 |
| step cost per event (ESTIMATE, unmeasured, no kernel replay exists) | 5 µs on tree maps; 40 µs on association lists at 3,000 ids | LAT §8.8 |
| FNV-1a-64 under `opt-level = 1` (ESTIMATE) | 1–2 ns per byte | typical byte-loop throughput; A3 measures |

**Every ESTIMATE is replaced by A3's and W5's committed measurements** before any number is quoted in
the README (AGENTS §5.11).

### 18.2 A hot call at 3 years (61 events a day)

| component | formula | low (900 ids, 3-day tail, tree map) | high (3,000 ids, 850-line pinned tail, lists) |
|---|---|---:|---:|
| request parse | 22 ms/MiB × (ckpt + tail + tz) | 0.12 MiB → 2.6 ms | 0.29 MiB → 6.4 ms |
| per-line `readLine` of the tail | 22 ms/MiB × tail | 0.4 ms | 2.0 ms |
| fold | tail lines × µs/event | 180 × 5 µs = 0.9 ms | 850 × 40 µs = 34 ms |
| facts emit | ≈ parse rate × facts | 1.4 ms | 3.7 ms |
| Rust decode (serde) | ≈ 5–10 ms/MiB | 0.5 ms | 2 ms |
| digest plus file read | 6.54 MiB × 1–2 ns/B + read | 9 ms | 19 ms |
| **total** | | **≈ 15 ms** | **≈ 67 ms** |

**Against the budget.**
- Today's later verb is ≈ 56 ms without a log, so with a 3-year log it becomes ≈ 71–123 ms, against
  `LATER_VERB` = 1 s.
- Today's Rust with the same log would be ≈ 140 ms.
- **W5's gate is ≤ 60 ms for the call.** The high case breaks it only on association lists with a
  maximal pinned tail, which is exactly W4's trigger.

### 18.3 A reseal (at most about daily)

- emitting the checkpoint: 75–180 KB, ≈ 1.6–4 ms;
- 1–3 days of day records and window records: ≈ 11 KB, < 1 ms;
- one read-modify-write of the current month file (≈ 120 KB of serde each way) and `ckpt.json`, both via
  temp file and rename: ≈ 3–8 ms.

Total: **+5–13 ms**. Under §9.6's back-off it happens at most once a day, plus whenever more than 512
foldable lines accumulate.

### 18.4 Genesis at 3 years (61 events a day, 9 chunks of ≤ 8,192 lines and ≤ 1 MiB)

| component | formula | tree map | lists |
|---|---|---:|---:|
| wire parse | 8.2 MiB × 22 ms/MiB | 180 ms | 180 ms |
| per-line `readLine` | 6.5 MiB × 22 ms/MiB | 145 ms | 145 ms |
| fold | 65,771 × µs/event | 330 ms | 2,630 ms |
| checkpoint parse and emit per chunk | 9 × 2 × 180 KB × 22 ms/MiB | 70 ms | 70 ms |
| records emit | 1,095 day and ≈ 1,065 window records ≈ 4.2 MiB | 90 ms | 90 ms |
| Rust decode and 36 month-file writes | | 60–120 ms | 60–120 ms |
| digest and read | | 20 ms | 20 ms |
| **total** | | **≈ 0.9–1.0 s** | **≈ 3.2–3.3 s** |

**`cli_latency.rs`'s first verb** is genesis plus the automatic close (707 ms today): ≈ 1.6–1.7 s on tree
maps, or ≈ 3.9–4.0 s on lists, against `FIRST_VERB` = 5 s. Lists leave too little margin on a busy
machine, **so W4 is required unless W5 measures genesis ≤ 1.5 s on lists.**

**Upgrades.** `TM_KERNEL_ID` changes with every kernel build, so the first command after an upgrade pays
this once (Q3, gap 99).

### 18.5 Memory (a swapless machine; CRIT 10)

| call | request | RSS (63 MiB per MiB) |
|---|---|---:|
| hot call | ≤ 0.3 MiB | ≤ 20 MiB |
| genesis chunk | ≤ 1 MiB of lines + checkpoint | ≤ 80 MiB |
| a refusal's resend | ≤ 4 MiB (32,768 lines) *(Superseded at W3 by gap 102's measurement: 8,192 lines or 1,536 KiB, chunks of 4,096 lines or 768 KiB; README "Stage 5 D9 W3".)* | ≤ 256 MiB |
| two processes rebuilding at once | | ≤ 520 MiB |

No call carries the whole log at any age. The first draft's worst case (≈ 520 MiB at 3 years,
≈ 1.7 GB at 10) is gone. A3 (d) checks the resend figure before W3.

### 18.6 Paths that read history (CRIT 4)

| verb | scope | what it loads at 3 y | ESTIMATE |
|---|---|---|---:|
| `tm review week`, `tm review day` | `All` (`lounge_rate` reads every day; `estimate_calibration` every duration) | 36 month files ≈ 4.3 MiB of serde | +40–80 ms |
| `tm review month`, `tm model --fit` | `All` | the same | +40–80 ms |
| `tm log --item X` | `All`, headers only | ≈ 1.6 MiB of headers, then a render call for the selected lines (≈ 300 × 104 B) | +15–25 ms |
| `tm log --since 7d` | `Dates` | open days plus ≤ 1 month file | +2–4 ms |
| `tm close day <date>` for `date < H` | `Dates` | ≤ 2 month files, and one kernel call carrying ≤ 62 records once the close tranche is in the kernel | ≈ +6–10 ms |
| today's `auto_close` housekeeping | `Hot` (dates `≥ T − 16 ≥ H`) | nothing | 0 |

`All` grows by ≈ +15–25 ms a year. The lever, if `review day` ever matters, is an all-time observations
file written at each reseal (the same records, indexed once); it is not needed at 3 years.

### 18.7 Stalls, far undos and pinned tails (CRIT 19)

- **A stall** (a block left open) holds `L` back, not `c`. Open days grow ≈ 2.5 KB a stalled day, so a
  30-day stall adds ≈ 75 KB to the checkpoint, ≈ +1.6 ms per call. §9.6's back-off keeps it to one
  checkpoint write a day.
- **A hand undo 30 days back** refuses once (G1), runs one genesis (≈ 1.0 s tree map, ≈ 3.3 s lists),
  and is `settled` from then on. No later call is pinned.
- **An undo stack pinning 14 days** (a light user's 50 commands) holds the cut at `maxLine`. The tail is
  ≤ 14 days of that user's lines, which is §18.2's high column. The 512-line reseal trigger counts only
  foldable lines, so a pinned tail does not reseal on every call.

### 18.8 D10's lookahead

The cost is `days × (walls that day + 2 × ~12 slots)`. ESTIMATE 50–200 µs of kernel work per day:
- 7 days: < 2 ms;
- a `due:` three years out (1,095 simulated days; the fork pays the same): 55–220 ms;
- the 3,660-day cap: 0.18–0.73 s.

T14 measures three and ten years through the shipped binary. The lever is a per-weekday memo for
wall-free days behind `@[csimp]`, exact. **It is required if T14 measures more than 300 ms at 3,660
days** (risk K22).

### 18.9 Growth per year of log (the trend the latency test guards)

| path | growth per year |
|---|---|
| hot call | +2.5–5 ms (digest); the checkpoint grows only with new ids (≈ 40 B each) |
| genesis | +0.3 s (tree map) / +1.1 s (lists) |
| sealed files on disk | +1.4 MiB |
| `All`-scope verbs | +15–25 ms |
| `Dates`-scope verbs | constant |

---

## 19. Risks

| # | risk | likelihood | effect | mitigation |
|---|---|---|---|---|
| K1 | the step's real cost per event is unknown (no kernel replay exists to measure) | medium | genesis misses `FIRST_VERB`'s margin | A3 measures early; the W5 gate; W4 tree-map twin; §18's formulas re-run on measurements |
| K2 | re-proving `JVal` over a sixth constructor in `Json.lean` (2,641 lines) and every exhaustive match in `Boundary.lean` (7,422 lines) | certain, bounded | A2 overruns | A2 budgeted at 900 proof lines; the `num`/`dec` split keeps readers' statements unchanged |
| K3 | chrono or serde edge acceptance differs from the port (padding-agnostic fallback, duplicate keys, `-0`, the float band) | high | a hand-edited line parses on one side and warns on the other | T1 and T3's crafted sets pinned **before** B3 freezes; residue only as P23–P25 |
| K4 | `resume_is_replay` or `resume_ok_iff` will not close | medium | W2 stalls | the effect-list shape (C3) and the W1–W4 lemma route; state W1's stack invariant as its own lemma first. **Under D5 a law that will not close is a stop condition raised to the owner (AGENTS §9.1), never replaced by T6** |
| K5 | a consumer reads a fact outside `view` (the law compiles and means less, AGENTS §5.2) | medium | a wrong answer after a reseal | R-audit by named accessor before W1; the query-indexed laws; the Rust struct has no field for an unlisted fact; cheats 97 and 102; T10 |
| K6 | a `decide` witness over `readLine`, a loaded plan or a checkpoint exhausts memory | medium | an OOM on a swapless machine | §14.0 item 4's budget: `Entry` values, ≤ 8 entries, literals ≤ 90 characters, round trips as rewrites, 8 GB-capped probes, per-arm split as the fallback |
| K7 | a hand-edited log reaches beyond the resend cap | low (hand edits only) | every verb but `tm check` fails by name until the line is moved | OWNER Q9 (iii); `reachTooFar` names the line; gap 95 |
| K8 | a stall holds the ledger day back | low | open days grow ≈ 2.5 KB a day; answers stay correct | back-off; `tm check` names stalls longer than 7 days (gap 88) |
| K9 | the per-call digest grows with the log | certain, slow | +2.5–5 ms a year | lever: a seal-time digest, which needs the owner because it changes when hand edits take effect (gap 96) |
| K10 | the hourly tz probe misses an A→B→A change inside one hour, or chrono and the table disagree | very low | wrong local dates on those days | T4 (a)–(d); the table's key includes the tzdb version; a quarter-hour probe for any zone T4 (d) flags |
| K11 | the CLI and the TUI write the cache concurrently | medium | a skipped reseal, or a mixed snapshot | generation-named immutable month files; one `ckpt.json` read per process; records filtered by that snapshot's `ledgerDay` and `horizon`; T10's concurrency mutations |
| K12 | the switch commit is too large to review | medium | a late defect | Phase R (with R13's scopes) reduces S to a body swap plus deletions; it is a revert unit |
| K13 | moving 18 test files and 3 test modules loses coverage silently | low | a regression passes | test counts recorded at R12 and after S; assertions byte-compared |
| K14 | the TUI's stage-6 budget of 5 ms per call: the checkpoint parse alone is ≈ 1.6–4 ms | medium | stage 6 misses its gate | in-process checkpoint reuse across reloads (same law); next lever, per-id pages selected by the ids in the request's documents (gap 97) |
| K15 | the in-flight stage-5 core edits `Json.lean`, `Boundary.lean` or `Goals.lean` while A1, A2, B4 or W3 are being written | high | rebase conflicts and renumbering | §14.0 items 1–2: those steps start only after it commits; numbers re-read before each commit |
| K16 | E7b over the minute-count spec is slow to prove | medium | L2 overruns | a merged-interval spec with a bridge lemma (LOOK); record which |
| K17 | lookahead latency on a far `due:` | low | `LATER_VERB` | T14 at 3 and 10 years; the per-weekday memo twin |
| K18 | `hsw` re-emission changes a lexeme (`1E+05` → `1e5`) | certain, harmless | none: the same double | T2 is byte identity on writer output only (ryu never writes `E+`); `hsw` equality is checked as a value in T5 |
| K19 | a proof agent narrows `view`, `sealable` or a guard to make a law close | medium | the law means less | AGENTS §3.1's "must not" rule; cheats 97–104; §15's quantifier paragraph copied into the README block |
| K20 | a new call path carries more than the resend cap (a future refactor) | low | an OOM with no swap | `tooManyLines` in the kernel; Rust's byte check; A3 (d)'s RSS figure; T0 (b) |
| K21 | every upgrade pays genesis once (≈ 1–4 s at 3 years) | certain | one slow command per upgrade | stated in the README and Q3; gap 99; a later lever is a kernel ID over `Seal`'s format only |
| K22 | the lookahead at its 3,660-day cap reaches 0.73 s | low | `LATER_VERB` on a far `due:` | T14; the memo twin required above 300 ms |
| K23 | an undo stack that pins 14 days on a light user keeps the tail long | medium | §18.2's high column on every call | the 14-day cap; W5's pinned case; W4 |

---

## 20. Gaps and behaviour rows to record

The numbers continue from 81. Each gap uses the README's four-part form: what, why not now, cost, when.

| gap | what | recorded at |
|---|---|---|
| 82 | two "first wake" rules (Q6a) | C2 |
| 83 | site R8, per-sub-segment minute truncation (Q6c) | C3 |
| 84 | a silent verb's compensating undo cancels an older event (Q6d) | C7 |
| 85 | a multi-day wall double-counts future capacity (Q6e) | L2 |
| 86 | an undo after housekeeping cancels the automatic close, because `close` has no id (Q6f) | C7 |
| 87 | two definitions of "today": calendar date in Rust, wake-attributed day in the replay (Q6g) | S |
| 88 | a stall holds the ledger day back; `tm check` names stalls longer than 7 days | W3 |
| 89 | the log writer is Rust; two definitions of one format guarded by T2 (Q5) | B4 |
| 90 | two zone evaluators, chrono for `today`/display and the table for attribution, until stage 6 moves `now` | B4 |
| 91 | `arrive.window` strings and `idle.attributed` are not validated (fork behaviour kept) | B3 |
| 92 | presentation over kernel facts stays Rust: `now`/`state.break_` clamping, review monitors, `arrivals_from_replay`'s time of day | S |
| 93 | day 0 of the lookahead is the host's histogram until L9 | L8 |
| 94 | Rust keeps two reserves over capacities (`planner.rs`'s week allocation, `tui/queue.rs`), in exact `u128` units and tested against the kernel by T16, until stage 6 | L8 |
| 95 | a hand-edited line beyond the resend cap is a named fault, not an answer (P31, K7) | W3 |
| 96 | hand-edit detection costs a full digest per call; the seal-time lever needs the owner (K9) | W3 |
| 97 | the checkpoint parse against the TUI's 5 ms budget (K14) | W5 |
| 98 | the lookahead is capped at 3,660 days (P30) | L6 |
| 99 | every kernel upgrade rebuilds the replay cache once; an unwritable cache rebuilds in memory once per process | S |

**Behaviour rows:**

| step | row |
|---|---|
| A2 | a request number that is not a `Nat` is refused by the field's reader, not as `bad json` |
| A2 | leading zeros refused (gap 43 closed) |
| A2 | a surrogate pair is read, and a lone surrogate still refused (gap 42 closed) |
| R6 | `tm undo` records by physical line (P18) |
| R10 | an append repairs a torn last line (P19) |
| S | an invalid-UTF-8 line is a warning, the verb runs, and `tm check` names it (P13, Q9) |
| S | `tm check` names future-dated lines (Q9 (ii)) and a `reachTooFar` fault (P31, Q9 (iii)) |
| S | `tm log` prints hand-appended unknown numerals as written (P29) |
| S | the replay cache under `.tm/cache/replay/`, and `tm init`'s `.gitignore` line (Q3) |
| B3 | `lineTooLong` / `lineTooDeep` warnings (P14) |
| L2 | `Arith.lean`'s site R3 row corrected (reopened as kernel half-up) |
| L6 | an out-of-domain `model.json` weight fails capacity verbs by file and key (P26, Q8) |
| L8 | capacity and priority `--json` fields per Q4, and the mixture visible in priorities and the week grid (P1) |

**AGENTS.md updates at S:**
- §2.4 gains the `tz`, `log` and `capacity` request and response shapes.
- §8.3's traps "the log has nowhere to live" and "time of day and tz are missing from the calendar" get
  their answers.
- §10.1's module map gains `Stamp`, `Log`, `Replay`, `Seal`, `Lookahead`.
- §8.3/§8.4 move E7 into stage 5 (at L2).
- §5.10a gains §14.0 item 4's per-step `decide` budget.

---

## 21. Critique responses

The completeness critique (`design/critique.md`) listed 3 blockers, 17 major and 12 minor items. Each row
says where the fix landed. "Different form" means the critique's fix was not taken as written, with the
reason.

| CRIT | severity | fixed in | how |
|---|---|---|---|
| 1 | blocker | §9.1, §9.3 G4, §9.4, §15 laws 6, `an_accepted_resume_covers_now`, cheat 103, D9-22, Q9 (ii) | **Different form, in part.** Taken: `T` required, `F = min (T − keepDays) (M − keepDays)`, `nowBelowLedger`, "never seals past now" as a law. Not taken: excluding a future line from condition (iii). A future-dated line is **folded and fenced** instead (its instant goes to `futureFloor`, a 2-day margin in G2), because excluding it from (iii) would let a later ordinary wake re-attribute it silently |
| 2 | blocker | §3.1 D9-10/D9-13, §8.4, §9.1 `H = min(month, week, L − 16)`, §9.2 `WindowRecord`, §11.1 `Dates` scope, R-audit | **Different form.** Neither option as written: `H` covers every auto-close date (`AUTO_CLOSE_CATCHUP = 16`), and explicitly old dates read sealed **window records**, exact by law 1. The kernel-reads-sealed-data exception is stated (D9-13) and put to the owner (Q3 (ii)). Refusing old-date closes was rejected as an unnecessary behaviour change |
| 3 | blocker | §9.5, §15 W block, cheat 102 | query-indexed laws for every A, O, W, DR and WR query; `resume_answer_ignores_the_policy`; `sealable` as the hypothesis on every checkpoint, proved of every checkpoint `resume` builds |
| 4 | major | §11.1, D9-20, R13, §14.6 T12, §18.6 | **Different form.** No `DaySource` trait: `Ctx::replay_with(scope)` merges sealed records into the same `Replay` per verb family, so no tm-core signature changes and there is one access path. The fit runs on the `All` scope from S, so there is no S/F1 gap. `review week` and `review day` are `All`, and §18.6 prices them |
| 5 | major | §13.8, D10-12, gap 94, T16 | every `DayCapacity` consumer tabled; placement and "fits" in `u128` units; floors only at display; `total = floor(Σ)` |
| 6 | major | §13.3, D10-11, site R11, §15 `the_bucket_reads_seconds`, cheat 115 | the fork's rounding ported exactly from seconds (the critique's first option). It also deletes LOOK's range-key exception |
| 7 | major | §9.8, §11.1, T10 | generation-named immutable month files, a manifest in `ckpt.json`, one snapshot per process, records filtered by that snapshot, no directory rename |
| 8 | major | D9-2, §9.4 (v), §9.8, §15 `the_unterminated_segment_is_never_folded`, cheat 104, T10 | as the critique proposed |
| 9 | major | §8.2 (`header` effect, `Effect.key` for `obs`), §9.3 G3, §15 `every_dated_output_names_its_day_key`, cheat 105 | as the critique's first option |
| 10 | major | D9-21, A1, §14.0 item 5, T0 (a)–(c), D9-12, §9.7, §18.5, A3 (d) | **Different form, in part.** Taken: the recursion rule, end-to-end T0, a memory-derived cap. Not taken: a chunked back-up, which can loop (§2.2). Exact pops plus a 32,768-line / 4 MiB resend cap with a named fault are used instead. T0 (b) runs genesis over 200,000 lines, not one 200,000-line call, because the per-call cap is 32,768 *(Superseded at W3 by gap 102's measurement: 8,192 lines or 1,536 KiB, chunks of 4,096 lines or 768 KiB; README "Stage 5 D9 W3".)* |
| 11 | major | §6.1 (hourly probe), §6.4 T4 (a)–(d), §14.4 T5 zone arms, §10.1 base `-06:00:00` | as the critique proposed; the sub-hour case is a stated assumption with two tests (§6.1) |
| 12 | major | §7.3, §15 C7, Q6(f), gap 86, T5 triples | as the critique proposed |
| 13 | major | §14.0 item 4, §5.5, §13.4, §16's witness paragraph, K6 | as the critique proposed, with a per-step probe count and wall-time bound |
| 14 | major | §5.1 (exponent as digits), §5.4 `finiteF64` bound, §10.4, §13.6 table, law 13, D10-13 | table completed. **Different form for capacity units:** they cross as digit strings, so the 2^53 bound holds by construction rather than by a proof about `avail`; `days ≤ 3,660` bounds everything else |
| 15 | major | §5.4, §5.5 step 7, cheat 106, P25, P29, Q9 (iv) | `finiteF64` over every numeral (the fork collects a `Map<String, Value>` first). **Different form for `tm log`:** serde's number normalisation is not ported; P29 records it, and Q9 (iv) tells the owner |
| 16 | major | OWNER Q7, P22, R11 | now an owner question, with cost |
| 17 | major | OWNER Q8, §13.2 (the host's reaction), P26 | now an owner question. The default (b) `capDen = 10^18` accepts every realistic hand edit, so a refusal needs more than 18 places or a value outside [0, 1] |
| 18 | major | OWNER Q9 (i), §5.5, §9.2 `warnings`, §14.6 T9 | now an owner question; the default makes `tm check` list them |
| 19 | major | D9-11 (`settled` removes the pin), D9-23 (back-off), §9.6, W5, T11, §18.7 | as the critique proposed, plus the pin removed at its source. A second trigger the critique did not name (a pinned undo stack re-firing the 512-line reseal) is fixed by counting only foldable lines |
| 20 | major | Q6(g), gap 87, §11.4 (`display`), §12, R5 | the "today" definition is an owner row, kept as a gap until stage 6 moves `now`; `parse_timestamp` is deleted at S because the kernel emits the display text |
| 21 | minor | §8.2, C3, `every_known_event_has_an_arm` | done |
| 22 | minor | §8.2 witnesses, C3 | done |
| 23 | minor | R-audit (named accessors), §8.4 (`events_for`, `stamps` have no caller) | done |
| 24 | minor | §8.4 `lastEffective`/`lastT`, R3, R4, `idle_and_idle_since_read_different_orders` | done |
| 25 | minor | §9.3 "the two edge cases of `wakes`" | done |
| 26 | minor | D9-24, §9.8, Q3, gap 99, K21 | done |
| 27 | minor | §7.2, §9.6, R6 | done. **Correction to the critique's premise:** the undo stack lives in `.tm/undo.json`, and `tm undo` never restores it |
| 28 | minor | §11.4 | done |
| 29 | minor | §5.2 `durationBetween`, T5 | done |
| 30 | minor | Q4 (a), D10-8, §13.8 | done |
| 31 | minor | R8, R12, §12 | done; recounted at `4748911` as 18 tm-core files with 45 call sites, plus 3 tm modules |
| 32 | minor | §0, Q1, §14.9 | harmonised: ≈ 6,550 definition and ≈ 23,300 proof lines, 124–166 agent-days |

**Items the critique found adequate** were re-read after the revision and still hold. The one-reader
invariant is now also stated for the fit (item 4) and the stamp reader (item 20).

---

## 22. Owner answers (2026-09-14)

The owner answered §4's nine questions on 2026-09-14. They are recorded as decisions D11–D18
(AGENTS §4, §10.5 rows 12–20; README "Stage 5 D9/D10: the owner's answers"). This section maps
each question to its answer and states what changes in the plan. The sections above are left as
written; where they disagree with this section, this section holds.

| question | answer | decision | differs from §4's recommendation? |
|---|---|---|---|
| Q1 price | (a) confirmed; D9 and D10 run as parallel tracks (§2.3) | **D11** | no |
| Q2 stage 6's pieces | (a) E7, the slot cut and future-day energy prediction are pulled into stage 5 as L2–L4 | **D12** | no |
| Q3 replay cache | (i) yes, (ii) yes: the kernel may read a sealed record back for an explicitly old date, (iii)(a) `tm init` excludes `.tm/cache/` from sync | **D13** | no |
| Q4 `--json` capacity | (a) integer floors, with `…_exact: {num, den}` beside each | **D15** | no |
| Q5 log writer | (b) the kernel writes log lines, in a new step right after S | **D16** | **yes** (recommended (a)) |
| Q6 fork quirks | the last column of Q6's table: (a), (c), (e) ported and fixed later; (b) kept; (d), (f) ported and fixed after the switch; (g) kept until stage 6 | (Q6) | no |
| Q7 unread fields | (b) ported: R11 keeps them, the kernel derives them into the sealed day records | **D14** | **yes** (recommended (a)) |
| Q8 `p_lounge` precision | (b) `capDen = 10^18`; more than 18 decimals or outside [0, 1] refused by name; `u128` units in Rust; digit strings on the wire | **D17** | no |
| Q9 damaged log | (i)(a) `tm check` warnings, exit code unchanged; (ii)(a) lines more than 2 days after `now` named as warnings; (iii)(a) a named fault beyond the rebuild bound, the memory cap never raised; (iv) serde's re-printing not ported (P29) | **D18** | no |

### 22.1 Consequences for §14's step plan

- **R11 (§14.3), under D14.** R11 no longer deletes the unread facts. It keeps them in Rust's
  `Replay`, so T5 compares them field by field. C3–C6 derive them in the kernel, W1's `DayRecord`
  carries them (not `Ckpt`), and P22 records a port, not a deletion. Q7's option-(b) estimate
  applies: ≈ 300 definition lines, ≈ 900 proof lines and witnesses, 4–6 agent-days; sealed records
  ≈ 15% larger.
- **A new step after S (§14.6), under D16.** Call it **S2, the kernel writer**. Appending verbs send
  typed events; the kernel renders the lines with B3's `renderLine` and returns them for Rust to
  append; `LogEntry::to_json` is deleted with its last caller. Acceptance: `the_log_reads_what_it_renders`
  end to end, T2's byte identity on every writable `Event`, both suites green. Estimate from Q5:
  ≈ 1–1.5 weeks. F5 (§14.7) is absorbed by it and is no longer optional.
- **L1 and L6 (§14.8), under D17.** `capDen = 10^18`. L1's weight constructor refuses a weight
  with more than 18 decimal places or outside [0, 1], with a rejection theorem (R10). L6 carries
  units as digit strings, and `kernel_bridge.rs` holds them as `u128`.
- **S (§14.6), under D18 and D13.** Item 7's defaults are the answer: `tm check` lists log warnings
  and future-dated lines as warnings with the exit code unchanged, and `reachTooFar` is a named
  fault. Item 6's `.gitignore` handling is Q3 (iii)(a).
- **L8 (§14.8), under D15.** `cli_plan.rs` and `cli_json_matrix.rs` gain the `…_exact: {num, den}`
  fields beside each integer floor.
- **L2–L4, under D12,** stay in stage 5 as planned; AGENTS §8.3/§8.4 move E7 when L2 lands.
- **§14.0 item 8's gates** are all open.
- **Parallel tracks, under D11.** D10 builds in its own worktree on branch `stage5-lookahead`.
  Shared files stay append-only under each step's banner, and the merge reconciles numbering
  (AGENTS §6.2–§6.5). While both tracks build, every run is capped at `MemoryMax=30G` (16G for
  benchmarks and generators), tighter than §14.0 item 3's 40G.
