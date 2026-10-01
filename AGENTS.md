# AGENTS.md — building the `tm` Lean kernel

You have been handed one stage of a rebuild. This is the working document for
building it. Read §1–§7 once, then your stage's section in §8, then §9.

`PLAN-lean-kernel.md` is a *decision* document — it argues that the rebuild is
worth funding. This document does not repeat it. Where you need the argument,
it is linked by section number.

**Precedence when documents disagree.** The Lean source is the truth. After
that, `kernel/README.md` is later than `PLAN-lean-kernel.md` — the plan has not
been rewritten as the kernel learned things, and several of its statements are
now stale in ways §10.2 lists by name. This document is the authority on
*process* only: rules, conventions, verification, stop conditions.

**Measurement date.** Every number here was re-measured on `rebuild-on-lean` at
`bf7cc63` on 2026-09-12, with a clean working tree, every build and test command
run under the memory cap §5.10a requires. (The previous stamp was `c8f3a38`,
2026-09-08; everything between — OpenCode's nine commits `0c3aaf7..9840ea8` and
the 2026-09-12 session `7f7d6d2..bf7cc63` — is recorded in `kernel/README.md`'s
2026-09-09 and 2026-09-12 blocks.) Every command shown was run, from the
directory the document names; paths are written for the original checkout,
`/Users/psixyzt/code/planner` — translate them to your clone's root. A figure
that is a snapshot of another commit says so where it appears. Re-measure before
quoting a number in a commit message; §10.4 says how.
*Stage 4's close (2026-09-13, `10bae51`):* §10.1's package table, §8.2's status
and §10.5 are re-measured there; numbers elsewhere in this document that cite
`bf7cc63` are that snapshot and say so.

**Nothing is in flight.** `git worktree list` shows the one checkout and no
other; the `stage-goals`, `orient-demotion` and `wire-fields` worktrees this
paragraph used to list belonged to the original machine and do not exist in this
clone. `git branch -a` shows `rebuild-on-lean` and its remote twin and nothing
else: **`main` is gone** — the owner discarded it on 2026-09-12 (`f386c56`,
§2.2). Stage 3 is closed out as far as its scope reaches (§8.1 says exactly
what that means, and what is still owed by name), and stage 4 is unblocked
(§10.5). *Since 2026-09-13 stage 4 is closed with its debts named (§8.2), and
stage 5 is blocked on two owner decisions: q3 / gap 22 (§10.5) and the
proof-to-definition stop condition, which fired (§9.1).* *Both were taken the same
day (D5, D6), and D6 landed at stage 4 final step 3: `@parent` is read off the line
and gap 22 is closed (README "Stage 4 final", step 3).* *Stage 4 closed for real at
stage 4 final step 4: B3 is refuted and renamed with §6.4's `max` law beside it, and
`Goals.lean`'s `# STAGE 4` holds no goal (burn-down 29, all stages 5–6; README "Stage 4
final, step 4").*

---

## 1. What the kernel is, and the one idea

`tm` is a Markdown-backed personal planner. The plan *is* the Markdown files;
there is no database behind them. The kernel is a pure Lean 4 package that
exposes exactly one symbol — `@[export tm_kernel_call] Tm.callExport : String →
String` — and Rust calls it through a hand-written C shim.

**The organising idea: item lines are not stored.**

A `Doc` holds prose only — headings, blanks, comments, front matter, generated
blocks — each line kept as verbatim bytes with a rank. Item lines are absent
from the document. They are *rendered* from the entity that owns them, and
`Store.get : Id → Option Entity` is a function. So "an id names one item" is not
an invariant anyone maintains; it is the type of the store. And `move` cannot
"append a line to a file", because there is no append.

That sentence is the whole answer to the bug class this rebuild exists to
remove. `horizon::move_line` calls `move_to`, which computes `to_path` and
appends the line without ever asking whether `to_path` already holds `key`.

**Five and six are both right, and they count different things.** Say which.

- **Five** is the harness's number and it is about *patched bugs*. Five
  duplicate-id bugs were patched separately over the project's history, and
  `invariant_exhaustive.rs` on `main` (discarded 2026-09-12, harness and all —
  the quotation is historical) says what the phrase "five code paths"
  turned out to mean: *"five entrances to one hole"*. The sweep's own evidence is
  that all 426 violations ended in a `move` (400) or a `readopt` (26) — the
  **two verbs** that reach `move_to`.
- **Six** is `PLAN-lean-kernel.md` §4.A's number and it is about *catalogued
  defects*: rows A1–A6, all verdict **U**. It is the five patched entrances plus
  A6, the hole itself — `tm move` never checking the destination — which was
  still open on `main` when the plan was written.

So: **six catalogued defects, five of them patched entrances, one hole, one
precondition.** Never write "six entrances"; the sixth row is not an entrance.

The measurement behind A6: 426 of 39,601 ordered depth-2 command pairs on the
committed 199-command alphabet, one of them reachable by a *single* command on a
fresh `tm init --example` tree. (Stage 0 landed that precondition on `main`, and
`main` has since been discarded with it: the restored Rust is the pre-stage-0
fork point `4748911`. What closes A6 in the shipped binary now is the kernel —
`move` and `readopt` run through it, and `tm move ^m2 month` on that tree is
refused `occupied` with nothing written, `d8e8d4d`. See §2.2 and §10.2.)

The finding cuts both ways, and the honest reading is in `PLAN-lean-kernel.md`
§6.1: a cheap proptest would have caught *this* class. The kernel is not sold as
"tm becomes verified" — §4's tally over 39 catalogued defects is 12
unrepresentable, 12 proof obligations, 2 fixed by single ownership, 4 partial,
**9 missed**, and the plan says out loud that quoting it as "verified" overstates
it by a factor of three. Write prose that matches that.

**Three tiers of enforcement, and choosing the tier is the load-bearing
decision.**

| tier | cost | what lives there |
|---|---|---|
| structural — the type forbids it | free, no proof | one entity per id (`Store.get : Id → Option Entity`); ≤1 live and ≤1 archive placement (`Core.archive : Option Tomb`); an item's horizon *is* its file (no `horizon` field); `Core.tags : TagSet`, a `Nodup` subtype; `Nat` does not overflow |
| decidable `wf : Core → Bool` + `Entity := { c // wf c = true }` | ~1 line per construction, unforgettable | the tombstone is in a different file from the live line |
| decidable `planWf`, re-established by `WfPlan.mapAt` on every post-state | one check per command | `docsWf`, `sitesInRange`, `pathsDistinct`, `demotionsOriented`, and `itemsWf` = `normalized && parentsTotal && parentsAcyclic && afterTotal && afterAcyclic && sectionsWf && shapesWf` |

A property in the right tier makes other proofs *available*. `normalized` (rank
distinctness) is what supplies the **strict** order that `sorted_ext_by_key`
needs, and that lemma is the step the whole plan-level round trip rests on.

**The plan's version of that row is not the kernel's — check before you quote
it.** `PLAN-lean-kernel.md` §3's structural row also lists "`moved`/`dropped` are
sets, not `Vec`+`dedup`", which is what earns E3/E4 their **U** verdict in §4.
Neither exists here: from `/Users/psixyzt/code/planner`,
`grep -rn 'moved\|dropped' kernel/TmKernel/TmKernel/` returns 31 lines at
`bf7cc63` (26 at `c8f3a38`), all of them `dropped` as a constructor — of
`Outcome` or `Glyph` — or prose. They are Rust
`state.json` fields (`diff()`'s moved list, `resume`'s dropped list) with no
kernel counterpart, so E3/E4 are verdicts the kernel has not yet cashed. The
rest of that row is real: `Core.tags : TagSet`, `Core.ci : Option (Fin 6)` and
`Core.prio : Option (Fin 4)` — the last two as *views* over the token vector,
which is the shape §5.3 settled on.

---

## 2. Start here

### 2.1 The one command

```bash
cd /Users/psixyzt/code/planner/kernel
systemd-run --user --scope -p MemoryMax=40G -p MemorySwapMax=0 --quiet ./check.sh
```

**Run it under a memory cap.** The prefix is the Linux form; on a machine with no
swap it is not optional, and it applies equally to `lake`, `lean` and
`cargo` run on their own — §5.10a says why (a `decide` exhausted 123 GB
twice). A command killed at the cap (exit 137 or 143) is a finding about a proof,
not a flaky run: never retry it uncapped. (The macOS machine the earlier stamps
were taken on has no `systemd-run`; there, cap by other means or keep every
`decide` small, §5.10a.)

**Every** check, exit 0 — and the number of them is written in exactly one
place, §7.1, on purpose. *(This paragraph said **seven** until the W-24 repair
step, **nine** until W-25 track A and **ten** until W-31, and so did §6.5 and
§7.1's heading: check 8 — the prose citations — landed at W-19, check 9 — every
new definition constant-folded — at W-20, check 10 — the parity register has one
home and no number is issued twice — at W-25, check 11 — no two names for one
definition — at W-30, and check 12 — a definition the compiler emits must be
REACHED — at W-31. **The number went stale here THREE times**, twice while the
paragraph beside it recorded that it had gone stale twice, because one fact was
written down in three paragraphs and a new check only ever reached one of them.
So the count has been taken out of this paragraph and out of §6.5's checklist
rather than corrected in both again: §5.11's rule is that a number lives where
it is measured, and this one is measured by counting the lines `check.sh`
prints.)* The wall time below is the seven-check stamp and is stale
with it: warm 1.1 s (four consecutive capped runs at
`bf7cc63`: 1.13, 1.11, 1.10, 1.10 s; `c8f3a38`'s were 1.15, 1.14, 1.11 s); at
nine it is ~8 s on the machine that measured it, and `check.sh`'s own check-9
comment carries that number. It is
the kernel's acceptance script, it is short, and you should read it before
claiming any of its checks — and since 2026-09-12 it is **not the whole
acceptance**: `cargo test --workspace` stands beside it (§7.5). Note it is `set -uo pipefail`
and **not** `-e`: **all of them** run regardless, so one failure does not hide
the others. §7 says what each one proves — checks 1–7 in §7.1, and checks 8
onward in their own scripts' headers and in `check.sh`'s comments above them.

The seventh is the one stages 3–6 care about most: it elaborates
`kernel/TmKernel/Goals.lean`, which holds the outstanding goals of stages 3–6 as
theorems with `sorry` proofs. Its number is a **burn-down** (§3.2), not a score.

### 2.2 Where things are

| path | what |
|---|---|
| `/Users/psixyzt/code/planner/PLAN-lean-kernel.md` | the decision document. §3 architecture, §4 defect-by-defect verdicts, §5 the stage table, §6 risks/open questions/stop conditions, §7 standing rules |
| `/Users/psixyzt/code/planner/tm-spec-v1.md` | the spec the kernel implements |
| `/Users/psixyzt/code/planner/kernel/README.md` | what is built, what is proved, and **one gap list, 1–51, in five places** (§6.4) |
| `/Users/psixyzt/code/planner/kernel/TmKernel/TmKernel/` | the ten modules (§10.1) |
| `/Users/psixyzt/code/planner/kernel/TmKernel/TmKernel.lean` | the root module: ten `import` lines and nothing else. **A module not listed here is not built** (§2.3) |
| `/Users/psixyzt/code/planner/kernel/TmKernel/Check.lean` | the axiom audit: `#print axioms`, one line per theorem |
| `/Users/psixyzt/code/planner/kernel/TmKernel/Negative.lean` | the cheats. **Must fail to compile** |
| `/Users/psixyzt/code/planner/kernel/TmKernel/Goals.lean` | stages 4–6 as 40 unproved statements (stage 3's section holds none any more). The one place a `sorry` may appear (§3.2) |
| `/Users/psixyzt/code/planner/kernel/totality.py` | the totality/boundary-discipline linter |
| `/Users/psixyzt/code/planner/kernel/corpus/` | 37 fixture Markdown files, copied verbatim from `main@557a3d2` (a commit this clone no longer holds); provenance in `corpus/PROVENANCE.md` |
| `/Users/psixyzt/code/planner/kernel/tm-kernel-ffi/` | the Rust bridge: `shim.c` 66, `build.rs` 69, `src/lib.rs` 57 lines; its own cargo workspace on purpose (the root `Cargo.toml` `exclude`s it), and a **path dependency** of `tm` |
| `/Users/psixyzt/code/planner/kernel/tm-kernel-ffi/examples/oracle/` | the differential oracle — **broken in this clone**: its scripts extract `main`, which no longer exists (§7.3) |
| `/Users/psixyzt/code/planner/kernel/tm-kernel-ffi/examples/oneshot.rs` | reads one request on stdin and prints the kernel's response; how the README's by-hand stack and cost measurements were taken |
| `/Users/psixyzt/code/planner/Cargo.toml`, `Cargo.lock`, `tm-core/` | the Rust workspace (members `tm-core`, `tm`), **restored** from the fork point `4748911` at `835d960`. `tm-core` is the fork-point library: the old grammar, planner, store and the harnesses `grammar_proptest.rs` and `planner_invariants.rs` |
| `/Users/psixyzt/code/planner/tm/` | the live CLI/TUI frontend. `tm/DORMANT.md` is **superseded** — it still calls the kernel rewiring "underway" and A6 open; the README's 2026-09-12 block is the record |
| `/Users/psixyzt/code/planner/tm/src/cli/kernel_bridge.rs` | the one choke point through which all seven kernel-backed verbs reach the kernel: read with the §1.3 guard, resolve horizon words and regions in the host, one request, write back only changed documents |

**`main` is discarded; the Rust is back, and part of it is the kernel's host.**
The owner ruled `main` obsolete on 2026-09-12 (`f386c56`): `git rev-parse main`
fails in this clone, and `origin` carries `rebuild-on-lean` alone. What survived
is the fork point, `4748911` — the parent of `6d9b1ba` "Remove the Rust kernel
in favour of the Lean one" — and the workspace was restored from it
(`git checkout 4748911 -- tm-core Cargo.toml Cargo.lock`, `835d960`). So the
sentence this section used to open with — "the branch has no Rust kernel" — is
false in the way that matters: `cargo test --workspace` builds and runs the whole
of `tm`, **and the `tm` binary calls the Lean kernel** for `move`, `drop`,
`demote`, `readopt`, `rank`, `add` and the keyed `edit` (`d8e8d4d`, `bd61f11`).
What is true is narrower: `tm-core`'s own lifecycle functions are still the
fork-point Rust, **pre-stage-0** (its `move_to` has no destination check), and
every verb the kernel does not yet back — `close`, `plan`, `review`, `recur`,
`check`, id-less lines — still runs on them.

The oracle is the fork point, not `main`, and the delta between them is stage
0's fix, as far as this repository can know:

```bash
cd /Users/psixyzt/code/planner
git show 4748911:tm-core/src/horizon.rs | grep -n 'fn move_to'
```

Cite the oracle **by function name, never by line number** — the plan's line
citations no longer resolve (§10.2).

### 2.3 The module map, in one line each

```
Cal ──▶ Grain ──▶ Text ──▶ Line ──▶ State ──▶ Plan ──▶ Cmd ──▶ Close ──▶ Report ──▶ Boundary
                   │                                                  ▲          ▲
                   └──▶ Json ─────────────────────────────────────────┼──────────┘
Arith ────────────────────────────────────────────────────────────────┘
```

Root import order (`cat TmKernel.lean`): `Arith Cal Grain Text Json Line Stamp Log Replay State
Plan Tree Priority Capacity Lookahead Fast Cmd Close Report Boundary` (`Replay` since stage 5 D9 step C1: it imports `Log` and `Arith`, and `Boundary` imports it for the `log` op's facts; `Log` since stage 5 D9 step B3: it imports `Json` and `Stamp`, and `Boundary` imports it since step B4 for the `log` op; `Stamp` since stage 5 D9 step B2: it imports `Cal` and `Line`, and `Log` imports it; `Tree` since stage 5 step 1: it imports `Plan`
only, and `Boundary` imports it for its loaded-plan witnesses; `Priority` since stage 5 step 2: it
imports `Plan` and `Arith`, and `Boundary` imports it likewise; `Capacity` since stage 5 step 3: it
imports `Priority` only, and `Boundary` imports it likewise; `Lookahead` since stage 5 D10 step L1: it imports `Capacity`, and `Cal` explicitly since step L2 (which `Capacity` already reached through `Priority` and `Plan`); `Boundary` imports it since step L5, for the loaded-plan witness). `Json` imports `Text` only; `Close` imports `Cmd`;
`Report` imports `Close` and `Arith` (stage 4 step 5 — the first consumer of
`Arith`); `Boundary` imports `Report` and `Json` (it imported `Cmd` before stage 4
step 2, and `Close` before step 5). **No module imports `Lean.Data.Json` any more** — the wire is the
kernel's own (§2.4).

- `Cal` — the calendar. Days since 0001-01-01, proleptic Gregorian. ISO weeks.
- `Grain` — the horizon order, all of it derived from `coarsen`.
- `Text` — tokens, numerals, list surgery, `freshId`, the structural `splitOn`/`joinWith`. A token carries its own separator.
- `Json` — the kernel-owned JSON fragment: `JVal`, `jescape`/`junescape`, `jemit`, the fuel-structural `jparse`, `jget`, and `jparse_jemit`. 3,726 lines (2,641 at stage 4's close; A2 widened `JVal` with `dec` for D9's log).
- `Line` — the item line and the whole of §4.1's field grammar, with the parse ⇒ wf bridges. 6,829 lines.
- `State` — entity versus observation. `Core`, `wf`, `Entity`, `render`.
- `Plan` — `Store`, `Doc`, `PlanCore`, `planWf`, `WfPlan`, and the comment rule (`commentAfter`).
- `Stamp` — the log's `"t"` field, namespace `Tm.LogStamp` (never `Tm.Stamp`: `Field.Stamp` is the `demoted:` stamp; write the names qualified and never `open LogStamp` beside `Field`): `parseStamp` (chrono 0.4.45's `parse_rfc3339`, then the fork's `%Y-%m-%dT%H:%M%:z` fallback; `StampErr`), `renderStamp` (`fmt_timestamp`), `displayStamp` (the `tm log` column), `stampBefore` (chrono's order: the instant's, never `nanos`), and `parseStamp_renderStamp`. Stage 5 D9 step B2.
- `Log` — the typed event grammar of `.tm/log.jsonl`, namespace `Tm.Log` (write `LogStamp` names qualified here too): `Event` (the 26 `define_events!` kinds and `unknown tag rest`), `Entry`, the field table `Kind.schema` with one reader `readF` and one writer `renderF` per serde field type, `readLine` (a `Verdict`: `blank`, an entry, or a named `LWarn`, in `Log::parse_bytes`' order), `renderLine` (`LogEntry::to_json`), `finiteF64` (serde_json's own "number out of range", applied to every numeral in the line), the small grammars `parseInstanceStatus`, `instDate?` and `stampFromKey`, and the goals `the_log_reads_what_it_renders`, `a_known_event_is_never_read_as_unknown`, `an_unknown_tag_is_never_a_warning` and `lineTooLong_bounds_every_string`. Stage 5 D9 step B3. **Since step S2 (D16) it also WRITES**: `emitEvent` reads the host's values with the reader's own `readArgs` and `emitLine` renders them with `renderLine`, so the log's format has one definition and not two held together by T2 — and `Event.primaryId` of a `close` is `period:key` since quirk Q6(f) (parity **P36**, gap 86).
- `Replay` — the kernel's replay of the log (design §7, §8; phase C), namespace `Tm.Replay`. Step C1: the undo mask as a left fold over a survivor stack (`matches`, written `«matches»` at its definition because `matches` is a keyword; `maskStep`, `survivors`, `dangles`), positions (`stackI`, `cancelledAt`, `cancelledLines`), `Log.linesIncreasing`, the goals `survivors_snoc_event`, `survivors_snoc_undo`, `a_cancelled_event_is_never_revived`, `a_dangling_undo_dangles_in_every_extension`, and the `@[csimp]` fast twins `survivorsFast`/`cancelledLinesFast` (per-tag and per-(tag, id) stacks of positions in `PosMap`, lazy deletion; `maskFast_inv` is the simulation). Stage 5 D9 step C1. Step C2: the day index, fork `DayIndex`, in chrono's order (`sortWakes`, `keptStep`/`dedupFrom`/`keptFrom`/`keptWakes`: consecutive dedup on the local date, not earliest per date; `lastWakeLe`, `dayOf` with chrono's `durationBetween` under 24 h; `dayIndexOf`, `entryDays` for every entry), quirk Q6(a)'s two first-wake rules (`keptWakeOn`, `firstLoggedWakeOn`, separated and bounded by `the_kept_wake_is_not_the_first_logged_wake` and `the_kept_wake_is_the_first_logged_wake_when_wakes_are_logged_in_order`), the goals `dayOf_is_the_wake_date_within_a_day`, `a_wake_day_is_shorter_than_a_day`, `keptWakes_append_of_later` restated in chrono's order (the design's nanosecond forms refuted by `…_by_nanos_is_refuted`), and the `@[csimp]` twins `sortWakesFast` (core `mergeSort`) and `entryDaysFast` (bisection, `lePoint`).
- `Seal` **and 57 `Seal*` proof modules — 58 files, 15,494 lines, 762 theorem declarations** — the
  window: a checkpoint plus sealed day and window records that answer exactly what replaying the whole
  log answers (design §9; phase W), namespace `Tm.Seal`. `Seal.lean` itself is the types and the disk
  codecs (`Header`, `DayRecord`, `WindowRecord`, `Ckpt`, `Meta`, `Resealed`, `Policy`, `Refusal`,
  `Seal.Q`; `emitCkpt`/`readCkpt` and the two record round trips; `sealable`, `horizonOf`,
  `dayRecordsBelow`/`Between`, `answer`, `askMerged`) — 1,839 lines and only 63 theorems, because the
  proofs live in the files beside it. Those are split because one file of this size does not elaborate
  in one pass, and each is named for what it proves: `SealLaw` the partition laws (1,409 lines, 110
  theorems), `SealLaw2A`–`SealLaw2F` law 2 through the codecs, `SealLaw4`/`SealLaw5A`/`SealLaw5B`,
  `SealLaw6*` the reseal at the cut, `SealLaw9*` genesis in chunks; `SealFoldPoint` the greatest valid
  cut that never folds an unterminated line; `SealGenesis` the chunked rebuild with exact pops;
  `SealResume`, `SealRestore` and `SealRun` the resume; `SealCut*` the cut machine; `SealIndex` the day
  index as lists; `SealRsDefs` the reseal's parts; `SealWire` what the `log` op carries across the wire;
  `SealTwin` the compiled twins W4 added. The remaining files hold the list lemmas those proofs rest
  on. **Every one of the 58 is imported** (the rule below is per file, not per group). Stage 5 D9
  phase W.
- `Tree` — §6.4's `remaining` (`remainingMin`, structural fuel, proved to be the one fixed point of its step) and §5.4's series head (`seriesHead`). Stage 5 step 1.
- `Priority` — §7.1's `k` (`rootK`, `Tree::root_priority`) and `p` (`prio`), the bin ladder at an exact rational availability (`binOfQ`, `binOfScaledQ`; D10), gap 27's loader check (`binsOf?`, `binsOfPairs?`), §7.2's rule table (`rowOf`, `rowTable`, `rawPrio`, `finalPrio`) and §7.4's hysteresis (`hysteresis`, `applyHysteresis`, `hysteresisDays`). Stage 5 step 2.
- `Capacity` — §7.3's EDF reservation pass over D10's exact capacity: `Den` (a positive denominator, `denOf?`), `DayCapacity` (a day and six level numerators, read over the pass's one `Den` by `minutesAt`), `Deadline`, `reserveRest`/`availUntil`, `sortDue`, `edf`/`edfGrants` and `Grant` (`avail`, `reserved`, `shortfall`, `hot`, `impossible`, `availQ`), and the lookahead's smart constructor `lookaheadOf?` (`Lookahead`, days ascending). The lookahead that produces the list is the D9/D10 tranche's. Stage 5 step 3. Since stage 5 D10 step L8 the compiled code runs proved `@[csimp]` twins (`edfGrantsGo_eq_edfGrantsGoFast`, `edfCaps_eq_edfCapsFast`, `reserveRest_eq_reserveRestFast` and four more; `NumSix` holds a reserved day's levels), linear in the days per deadline (gap 106).
- `Lookahead` — D10's exact mixture (design §13): `capDen = 10^18` (D17) and `capDenD`, `Weight` and its decoder `mkWeight?` (`WErr`: `badWeight`, `weightAboveOne`, `weightPrecision`), `Hist`, `mix`/`mixDay`/`ofHist`, the budget limit `limitHist` (mixing comes after it), the threshold twin `twin` (parity P1), and `scaleDay`/`scaleGrant` with `edf_commutes_with_scaling` (step L1). The day's window, E7, pulled from stage 6 by D12 (step L2): `windowEnd` (clip, sort, merge, extend; `@[csimp]` twin `windowEndFast`), `windowBase`, the specification `wallOverlap`, E7a/E7b (`the_window_end_solves_the_equation`, `the_window_end_is_the_least_solution`), sites R3 `windowMinOf` and R2 `budgetOf`, `windowOn` in UTC seconds through `Cal.instantOf`, and the plan's walls `wallIndex`/`wallsOn` (fork `Ctx::walls_on`, quirk (e) kept). The slot cut, pulled from stage 6 likewise (step L3): `freeIntervals` (fork `free_intervals`, specified in both directions by `freeIntervals_are_the_free_units`) and `cutSlots` (fork `cut_slots_around`: walls, rests and blocks since the last break; `Slot`, `Cut`, `CutCfg`), exact in whole UTC seconds, with the laws `cutSlots_inside_the_window`, `cutSlots_avoid_the_walls`, `cutSlots_short_block_is_at_least_min_last`, `cutSlots_fuel_is_enough`, `every_break_is_followed_by_a_slot`; `sortByStart` compiles as core's merge sort (`@[csimp]`). Energy and the budget limit, pulled from stage 6 likewise (step L4): site R11 `hsw100` (hours since wake in exact hundredths from chrono's whole seconds, `hswAt`) and `bucket`, the curves as data (`Curves`, `Step`, `stepAt`, `priorEnergy`, `priorLevel`, `learnedLevel`), `predictAt` (since step L9 `baseLevel` + `predictShift`, the shift subtracted **before** the `0..5` clamp as the fork does), the home cap `capForLocation`, `futureEnergy` and `energize` (fork `energize` under `Posterior::none`), `histOf'`, and `limitSlots` (fork `limit_to_budget`) with `limitSlots_is_limitHist` (equal to L1's `limitHist`; `@[csimp]` twin `limitSlotsFast`), so one location's future day is `dayHist`. Stage 6's `dayPlan` must reuse these. The lookahead (step L5): `InputIn` and its smart constructor `mkInput?` (`CapErr`: `lookaheadTooLong`, `weight wd e`, `badWake`, `nowDisagrees`; the model-then-config fallbacks and fork `Ctx::wake_time`'s wake fallback applied in the kernel), `Input`, `DayCfg`, a future day's wake `wakeInstantOf` (fork `local_dt` at second resolution; `Cal.instantOf` is its whole-minute instance), `dayCut`, `pureDay` (equal to `dayHist`), `dayOf` (a later day `mixDay` at its weekday's weight; `@[csimp]` twin `dayOfFast` holds each histogram as `Six`), `lookahead` (a `foldl` over the day range) with `lookahead_is_a_lookahead` and `lookahead_between_the_locations`, and `Input.twin` (`the_twin_forces_the_forks_location`). Every other bound the capacity wire carries (step L6): `mkDayCfg?` (`DayKey`), `mkStep?` (`StepErr`: `badStep`, `badLevel`), `curveOk`, `priorOk`, `energyOk`, `homeMaxOk`, `InputIn.boundsWf`, each with rejection theorems. The grants (step L8, kernel half): `Cand` (fork `Candidate`'s §7 inputs), gap 80's filter `Cand.enters`/`entering`, the served order `sortDueIx` (step 3's `sortDue` with positions; `servedGrants_are_the_pass`), `grantAt`, `binAt`, `CandOut`, `PClass`, and `priorities` (fork `priority::compute` without the floor pass), with `an_answer_carries_a_grant_iff_its_candidate_enters` and `a_hot_answer_is_zero`. The floor pass (step L8, host half; gap 79): `Floor` (the host's `left` and last date), `passLeft` (`passLeft_is_edf`), `FloorGrant`, `floorBin`, `withFloor` (the capacity left is a `Thunk`, forced once per request), `FloorOut` and `prioritiesWithFloors` (fork `priority::compute` whole), with `prioritiesWithFloors_without_floors`, `a_floor_reserves_nothing`, `the_pass_wins_over_a_floor` and `a_floor_answer_reads_what_the_pass_left`. **Day 0, derived (stage 6 step L9, README gap 93)**: `Today` (the `at` instant, `state.json`'s date/window/budget/arrival/location, `--allow-home`, and — through D24's seam — last night's `slept` and today's `reports`), `nowAgrees` (`nowDisagrees` at `mkInput?`), `Today.storedWindow`/`arrivalSec` (fork `Ctx::window`), `windowFrom` (`windowOn`'s definition, from an instant), `day0Window`, `day0Cut`, `curveKeyOf` (fork `curve_key`) and `capLoc`, the posterior `Report`/`latestBefore`/`PostCfg`/`weightAt`/`correctAt` (fork `Posterior`, site R5; the fork's `hours <= full_hours` test comes **before** its degenerate test and `weightAt` says so), the sleep debt `SleepCfg`/`underSlept`/`shiftOf` (site **R10**, `Arith.roundAway`), `todayEnergy`, `day0Slots`, `day0Hist` (fork `DayCapacity::from_slots`, **no budget limit**) and `day0Six`; `lookahead_day_zero_is_the_kernels`, `day0_slots_are_inside_the_window`, `day0_slots_avoid_the_walls`, `day0_after_the_window_is_empty`, and six witnesses ending in `day_zero_is_the_spec_day_energised`. Stage 5 D10 steps L1–L6 and L8, and stage 6 step L9.
- `Cmd` — `lift`, `Transform`, `Dest`, `WfPlan.mapAt`, `KErr`, the commands (`cmdMove cmdDrop cmdSetEst cmdDemote cmdReadopt cmdRank cmdEdit cmdUnset`, and `WfPlan.insertFresh` for `add`), the `EditVal` table.
- `Close` — §6.3's lifecycle as one fold at three grains: the `ClosePolicy` table and its bridges, `close`, the landing rank shift, `close_spec`, `autoClose`. On the wire since stage 4 step 5, as the `close` and `autoClose` ops.
- `Report` — what a close reports (the owner's D3): `CloseEntry`, `Report`, `closeReport`, `closeR`/`autoCloseR`, and the theorems tying each entry to the close's result. kernel/README.md, stage-4 step-5 block.
- `Boundary` — `String → String`: the request readers, `parseCmd`, the loader, `runLoad`/`run`, `respond`, `call`, `callExport`. Since stage 5 D9 step B4 `respond` runs `runWithLog`: the request's `tz` section (`readTz`, the zone table `tm/src/cli/tz_table.rs` probes, built only by `Cal.mkTz?`; **the one reader of `tz`** since the merge that closed gap 108) and `log` section (`readLogReq`, `mkLogReq?`, `logAnswer`: every line read by `Log.readLine`, its warnings by name, headers `[line, tag, id]`, renderings; since step C1 `want.facts`, answered as `facts.cancelled` for a tail from line 1, `Replay.cancelledLines`; since step C2 also `facts.days`, `[line, day]` for every entry, `Replay.entryDays` in the request's zone, which `LogReq.tz` carries from `zoneOf`), then `run`; a request with neither is `run`. Since stage 5 D10 step L6 the `capacity` section (`CapWire`, refusals `{"err":{"capacity":"<name> <key>"}}`; `CapWire.readTz` is `tzAbsent` or B4's `readTz`), `runCap`/`respondCap`/`callCap` (the `lookahead` response key, unit counts as digit strings), and `callExport`, which runs `callCap`: `runWithLog` on every request without `capacity` (`runCap_without_capacity_is_runWithEmit` since S2, `callExport_without_capacity_is_call`), and with it the `tz`/`log` sections first, then the documents, the capacity section and the commands, answering `docs`, `report`, `log`, `lookahead` (`runCap_answers_docs_report_log_lookahead`). Since stage 5 D10 step L8: the zone is read once (`zoneOf`, feeding `logSectionWith` and `readCapacityZ`; `the_zone_is_read_once_and_feeds_both_sections`), `runCap` answers through `runCapZ`, the optional `capacity.candidates` (`readCands`; `badCandidate <i> <key>`, `tooManyCandidates`) adds `lookahead.grants` (`grantJson`, `lookaheadJsonWith`), and a capacity request with commands is refused, `capacityWithCommands` (`runCap_refuses_commands_beside_capacity`, `an_answered_capacity_request_has_no_commands`). L8's host half: a candidate record's optional `floor` (`readFloor`, `badCandidate <i> floor`) and the floor answer's grant (`grantJsonF`, class `floor`; `grantJsonF_without_a_floor`); the binary's one encoder of this request is `tm/src/cli/kernel_capacity.rs`. Since stage 5 step **S2** (D16) the **`emit` section**: `{"emit":[{"at":[sec,ns,west,offSec],"ev":<tag>,"f":{…}}]}` in, the exact bytes to append out, through `Log.emitEvent`/`emitLine`; `runWithEmit` wraps `runWithLog`, so every theorem proved about `run` and the `log` section holds unchanged. Since stage 6 **W-13 track B** (D24) the **seam** is open: `logOpZ` answers a `LogAnswer` — the bytes `logOp` always answered, and the `Seal.Answer` they were rendered from (`LogReq.seamFacts`, `some` when the request resumed and asked for facts) — `logAnswerOf`/`readLogSection`/`logSectionWith` carry it, and `runCapZ` hands it to `readCapacityZ`, whose first consumer is `"wake": "log"` (`CapWire.WakeSrc`, `wakeClockOf`, `dayRecordOn`; refused `wakeWithoutLog` without a replay). `logOp` is kept as a **view** of `logOpZ`, so every law stated about it is unchanged (`the_capacity_section_reads_the_log_sections_own_replay`, `runCap_reads_the_capacity_section_against_its_own_log_answer`, `the_capacity_input_is_the_replays_wake`; README **gap 210 closed**). Since stage 6 **step L9** (gap 93 closed) the seam has its second consumer, **day 0**: the section gains `at` (a stamp through B2's one reader), `state` (`date`, `window`, `budget`, `arrival`, `loc`, `allowHome`), `posterior` (`fullHours`, `zeroHours`) and `sleep` (`shiftModel`, `shiftConfig`, `underHours` — the shifts **signed**), read by `readAt`, `readState`, `readPosterior`, `readSleep` through `boundedPos`/`signedOf` (`den ≤ 10^6`, value `≤ 10^6`, with rejection theorems), and `CapWire.todayFromLog` projects today's `DayRecord` into `Look.Today`. `day0` and `badDay0` are **gone**; the new refusals are `badAt`, `nowDisagrees`, `badState <key>`, `badPosterior <key>`, `badSleep <key>` and **`day0WithoutLog`** (a capacity request with no replay has no day 0 and is refused, never answered with an empty day). Phase F's F2/F3 spend the same seam.
- `Arith` — exact rational arithmetic. Its consumers are `Report` (minutes as an `Arith.Pos`) and, since stage 5 step 2, `Priority` (the ladder, `safety`, a rational availability).

**A new module is not built until it is imported.** `kernel/TmKernel/TmKernel.lean`
is **78** `import TmKernel.<Mod>` lines at stage 5's close (twenty at D9 step C1, nineteen at
D9 step B3, eighteen at D9 step B2, seventeen at D10 step L1, sixteen at step 3, fifteen at step 2,
fourteen at step 1) and nothing else — **58 of the 78 are the `Seal*` group**, and each of the 58 has
its own line: the group is a grouping in this document, never in `TmKernel.lean`; `lakefile.toml` names one
`lean_lib TmKernel` and no module list. So a `.lean` file dropped into
`TmKernel/TmKernel/` that nobody imports is **not compiled by check 1**, is not in
`libTmKernel_TmKernel.a`, and is therefore invisible to the Rust — while
`check.sh` still prints seven `ok`s. Stage 3 added one (`Json`, imported at
`c2ad8f6` in the same commit), stage 4 added `Close` and `Report` (each imported in the commit
that created it), and the remaining stages propose more (§8.3, §8.4). Add the `import` line in the same commit as the file:

```bash
cd /Users/psixyzt/code/planner/kernel/TmKernel && cat TmKernel.lean
```

`Goals.lean` is the deliberate exception — it is *not* imported, and §3.2 says
why that is what makes it safe.

**Read the module header docstrings.** They are written as arguments: each names
the alternative that was rejected and why. They are the best source in the
repository, better than the README.

### 2.4 The wire format today

Re-derived from `Boundary.lean` and `Json.lean` at `bf7cc63`.

**The wire is the kernel's own JSON, both ways.** `call` is `String.ofList ∘
jemit ∘ respond ∘ String.toList`: the request is read by `jparse` and every field
through `jget`, and every response byte is written by `jemit` (J5, `51f83a8` and
`b7f504d`). **`Lean.Json` does not touch the wire** — no kernel module imports
`Lean.Data.Json`, and `the_response_call_emits_parses_back` is the round trip at
the exported function. Four reading rules follow from owning it, each a named
refusal: a field key carried twice is refused `duplicateKey <k>` (only for a key
the kernel reads); a present `cmds` that is not an array is `array expected`
(absent `cmds` is a read with no commands); a number is a `Nat` — `-3`, `1.5`,
`1e3` are refused at parse; and a surrogate-pair escape is refused (gap 42),
while leading zeros are accepted (gap 43). Keys are emitted in **build order**,
not sorted (`the_response_shapes_emit_in_build_order`); both Rust readers look
keys up by name.

*Stage 5 D9 step B4 (2026-09-14; kernel/README.md "Stage 5 B4" is the record).* The request may
carry `tz` (`{"key","base":"±HH:MM:SS","then":[[instant, offset], …]}`) and `log`
(`{"ckpt":null,"from","lines":[string|null],"terminated","want":{"headersFrom","render"}}`); the
`ok` object then gains `log` after `report` (`lines`, `warnings`, `headers`, `render`), and the
section's refusals are `{"err":{"log":…}}` (`tzAbsent`, `badTz`, `tooManyLines`, `badLogReq`,
`renderNotInTail`). A request with neither key is read as before. String escapes are
**serde_json's** since B4 (`\b`, `\t`, `\f` short; other controls a lowercase quad).

*Stage 6 W-24 (2026-09-22; kernel/README.md "Stage 6 — W-24, track P" is the record).* The
request may carry a `plan` section — `{"bed":"HH:MM","priorities":[{"id","p"}],"segments":[…]}` —
and the `ok` object then gains `plan` **after** `lookahead`, carrying `rows` and nothing else:
one object per segment sent, with §4.3's nine cells (`time ci p mark title parent est actual
note`) plus `batchNames`, the member list the Rust fitter needs. A segment is
`{start,stop,kind,batch?,energy,item,planned,mult,flags,note}` on the kernel's absolute seconds
(from 0001-01-01, not the Unix epoch); `kind` is `kind_label`'s word, so `break` and `wind-down`
and not the Lean constructor names. The section's refusals are `{"err":{"plan":…}}` —
`badSegment <i> <key>`, `segmentRefused <i> inverted|pastTheHorizon`, `badPriority <i>`,
`tooManySegments`, `tooManyPriorities`, `rowsWithCommands` (a `plan` section on a request that
also edits the documents, gap 109's stance one section along), and `tzAbsent`/`blockMinAbsent`
for the two request-level values every cell needs. A request with no `plan` key is answered
exactly as before. The reader is `EmitWire.lean`, a new module importing `Boundary` and `Emit`,
which also carries the package's single `@[export]`.

```jsonc
// request
{"now":"2026-09-12","blockMin":50,     // both optional; required by close/autoClose (stage 4 step 5)
 "docs":[{"path":"week/2026-W37.md","grain":1,"ix":105695,
          "lines":["# Tasks","- [ ] 5 6b Finish the report ^m1"]}],
 "cmds":[{"op":"move","id":"m1","doc":0}]}
// doc: path, lines (every element a string); grain ∈ 0..2 (day week month) or
//      null/absent = no region; ix required when grain is present
// ops, ten:
//   move{id,doc}  drop{id}  est{id,min}  demote{id,doc,period,grain?}
//   readopt{id,doc}  rank{id,rank}  add{seed,doc,title}
//   edit{id,key,value}            // value "" is the unset form
//   close{grain}  autoClose{}     // grain 0..2; both read the request's now and blockMin
// demote's grain is a STRING: "d" stamps D<period>, anything else or absent W<period>
// rank is a raw document rank (a line index); add's id is the kernel's (freshId)
```

**The response has one `ok` shape and nine `err` shapes.** Quoting one of them
as if it were the taxonomy is how a host ends up with a `match` that falls
through. All ten, from `Boundary.lean`, keys in the order they are emitted:

```jsonc
{"ok":{"docs":[{"path":…,"lines":[…],"grain":…,"ix":…}],     // grain/ix only if the request declared a region
       "report":{"closes":[{"id":…,"grain":…,"did":…,"from":…,"to":…,"stamp":…,"min":{"num":…,"den":…}}]}}}
                                               // report on every ok (empty closes when nothing closed);
                                               // did: move|moveReopening|copy|carry; stamp/min may be null
{"err":"<free text>"}                          // jsonErr: see below
{"err":{"kernel":"<name>"}}                    // see below
{"err":{"dupId":{"key":…,"a":{"path":…,"line":…},"b":{"path":…,"line":…}}}}       // D32, W-16
{"err":{"notADemotion":{"key":…,"a":{…},"b":{…}}}}          // key: a store key, NOT an `^id` token —
{"err":{"ambiguousDemotion":{"key":…,"a":{…},"b":{…}}}}     // since D31 it may be a title the kernel
                                               // derived.  a/b are the two colliding lines, 0-based
                                               // like badLine, ordered by path then line (spotPair),
                                               // NOT by the order the request listed its documents
{"err":{"duplicatePath":"<path>"}}
{"err":{"badLine":{"path":…,"line":…,"why":…}}}   // why is repr of a PErr: notAnItem|badState|noId|manyIds
{"err":{"unterminatedComment":{"path":…,"line":…}}}   // line = the opener's 0-based index (a4ccd9c)
{"err":{"itemCheck":"<fault>"}}                // firstItemFault, 7 values: rankCollision danglingParent
                                               // parentCycle danglingDep depCycle sectionDiscipline fileKindShape
```

`"kernel"` carries **thirteen** strings, and twelve of them are `KErr`, from
`kerrName` — `noTarget` and `noSection` (a close with no destination file or
section, kernel/README.md gap 56) reach the wire since stage 4 step 5, beside: `occupied`, `noSuchId`, `notDemoted`, **`alreadyDemoted`**,
`badHorizon`, `badItem` (an `add` whose post-state fails `itemsWf`),
`tabbedLine` and `keyAbsent` (the edit path), `danglingDep` and `depCycle` (an
`after:` edit, renamed out of `badHorizon` by `nameEditFault`). The eleventh,
`siteOutOfRange`, is emitted directly by `loadPlan` and has no `KErr`
constructor. `alreadyDemoted` is the one most often left out — §6.3 gives an item
**one** archive record, so a second `demote` is refused rather than overwriting a
standing tombstone. Note that `danglingDep`/`depCycle` appear under **both**
`kernel` (a command) and `itemCheck` (the loader): a host must not match on the
string alone.

The free-text `err` is not one thing either. It carries: `bad json: <JErr>` (the
parser's thirteen names, `jerrText`); `property not found: <k>`, `String
expected`, `Natural number expected`, `array expected`, `object expected`,
`duplicateKey <k>`, `grain <n> out of range (0..2)`, `unknown op <op>`; `add`'s
five title refusals `titleNewline titleTab titleId titleBlank titleEdge`;
the edit's `unknownKey <k>`, `keyNotWired <k>` (only `demoted` today, by policy)
and `badValue <k>`; and the request clock's four (stage 4 step 5): `nowAbsent`
and `blockMinAbsent` (a close op in a request without one), `badNow` and
`badBlockMin` (present and malformed, refused whatever the commands). The host (`kernel_bridge::refusal`) maps these names to
`detail.refusal`. Re-derive the list rather than trusting this block:

```bash
cd /Users/psixyzt/code/planner/kernel/TmKernel/TmKernel
grep -n '"err"\|"kernel"\|jsonErr\|lerrJson\|throw\|kerrName' Boundary.lean
grep -n 'def jget' -A 8 Json.lean
```

*Stage 4 step 5 (2026-09-12) added `now` and `blockMin` to the request and
`report` to the response; the paragraph below is the pre-step-5 record, kept for
its history — the full shape of record is kernel/README.md's stage-4 step-5
block.*  There is **no `now`, no `log`, no `cfg`, no `model`, no `seed`** in the request,
and **no `events`, no `report`, no `repairs`** in the response. Stages 4–6 need
all of them; §8 says which stage adds what — and §8.2 gives `report` the shape it
does not yet have (the owner has since decided what it carries, §10.5 q8, but no
code exists). Stage 3's scope listed `now` for itself (§8.1 item 5) and did not
add it; it is owed to stage 4 by name. `report` has no code today: `grep -rn '"report"\|Report'
kernel/TmKernel/TmKernel/` returns nothing, so there is no JSON key, no type and
no constructor for it anywhere in the kernel.

---

## 3. Hard rules

Every one of these is checked by `check.sh` or by an audit. None is a matter of
taste.

| # | rule | checked by |
|---|---|---|
| R1 | No `sorry` in any module of the library or in `Check.lean`/`Negative.lean` — not even temporarily on a branch you intend to fix. **`Goals.lean` is the single named exemption and the only place a `sorry` may appear** (§3.2) | `totality.py`, which exempts by filename, not by pattern; the axiom audit fails on `sorryAx` |
| R2 | No new `axiom` declarations. The only axioms the package may reach are `propext`, `Quot.sound`, `Classical.choice` | `totality.py` bans the KEYWORD (W-27's repair step), and `Check.lean` prints every theorem's axiom set. Until W-27 the second was the whole rule and an UNUSED axiom reaches no `#print axioms` line at all: driven in a clone, `axiom w27PlantH : Nat` in `Emit.lean` built, left check 2 silent and check 3 at ok |
| R3 | No `native_decide`. It discharges a goal by trusting the compiler and the linked C, which is exactly the layer the kernel exists to distrust. `decide` is the workhorse; give it budget instead (§5.10) | `totality.py` |
| R4 | No `partial def`, no `unsafe`, no `opaque`, no `@[implemented_by]`, no `panic!`, no `!`-accessors (`.get!`, `xs[i]!`) | `totality.py`, all of it — and **the scanner under the rules, since the W-27 repair step**: the rules were applied per LINE to text a `line.split("--")[0]` had already cut, so `partial` + newline + `def` and a `--` or `/-` inside a STRING LITERAL each left it silent on a real plant that built. It strips comments with a scan that knows what a string is, and matches over the whole file. The `!`-accessors are matched as a CLASS — a `!` that ends a name — and not as the two examples this row gives, which is what `.head!`, `.getLast!`, `.back!`, `.tail!`, `.set!` and `.toNat!` walked through for six stages. `unsafe`, `opaque` and `@[implemented_by]` said **"audit items"** here and the audit existed nowhere in `check.sh` and was never once performed; they are mechanised. Driven: nine plants, each `rc=0` before and named after. **AND THE ROW IS NOT THE RULE — THE RULE IS THREE RESIDUES** (W-29 track A): an ATTRIBUTE is in `ALLOWED_ATTRS` whichever of Lean's two spellings applies it (`@[..]`, and the `attribute [..] name` command, which W-28's residue did not read — driven, `rc=0` on an `extern` plant that built); a `set_option` names one of the four options in `ALLOWED_OPTIONS`, because `debug.skipKernelTC` turns the kernel typechecker off and nothing here looked at an option — driven, `rc=0`; and a word that begins a column-zero line is one of the 22 in `ALLOWED_COMMANDS`, which is what `partial_fixpoint` — a definition Lean never had to justify the recursion of — walked through, driven `rc=0` on a plant that built. The spellings this row names keep their own rows for the message they print, and `partial` is matched as a STEM |
| R5 | No `.toOption`. `Except` all the way through the boundary | `totality.py` |
| R6 | No Mathlib. Core toolchain only (`Fin`, `Nat`, `Option`, `Except`, `Subtype`, `List`, `omega`, `decide`, `simp`, `Lean.Data.Json`) | absence from `lakefile.toml`; and needing it is a **stop condition**, not a decision you take (§9) |
| R7 | No new dependencies of any kind, Lean or Rust | `lake-manifest.json`, `Cargo.toml` |
| R8 | Do not touch `kernel/TmKernel/lean-toolchain` (`leanprover/lean4:v4.33.1`). `lake update` once moved a pinned v4.33.1 to v4.34.0-rc2 unasked and cost two link failures with a misleading error | review |
| R9 | Nothing but `String` crosses the FFI. No `lean_object*` escapes the shim | `nm` on the archive; the shim is 66 lines and stays that way |
| R10 | Every bounded type gets a `Fin`/`Subtype`, a smart constructor its decoder actually uses, and a rejection theorem. Every integer crossing gets a stated width | `Negative.lean` cheats; audit |
| R11 | A field's setter is not exported without its `view ∘ set = id` proof | audit; `Negative.lean` CHEAT 5 |
| R12 | `Negative.lean` must fail to compile | `check.sh` check 4, which inverts the exit code |

`totality.py` takes **one or more directories** and scans each **recursively**,
pruning build directories by a property (`leanfiles.lean_files`). *(This
paragraph said "one level deep, non-recursively" for six stages after the W-21
and W-22 repair steps made it recursive — the process authority describing a
checker it had stopped describing. Corrected at W-27 track X, beside the R4 row
above.)* `check.sh` passes **two**:

```bash
cd <repo>/kernel && python3 totality.py TmKernel/TmKernel TmKernel
```

So the library *and* the package root are scanned, which means `Check.lean` and
`Negative.lean` are covered too. Only the Rust is outside it — and `Goals.lean`,
which is exempted **by filename** (`EXEMPT = {"Goals.lean"}` in `totality.py`),
not by a loosened pattern. That is what makes the exemption reviewable: it is one
line in a diff, and a `sorry` added to any other file is still a check-2 failure.
The exemption is doing real work: the directory it scans contains a file with
fifty-six `sorry`s in it and the scan is clean.

```bash
cd /Users/psixyzt/code/planner/kernel
python3 totality.py TmKernel        # exit 0 — the root: Check, Negative, Goals
grep -c 'sorry' TmKernel/Goals.lean # 56 at bf7cc63 — 40 goals plus the provisional defs and prose (70 at c8f3a38)
```

### 3.1 What to do when a proof will not close

In this order. Every one of these is a normal outcome; none is a failure.

1. **Move the property to a cheaper tier.** Most "hard" proofs are hard because
   the property is being defended at the wrong level. `no_two_lines_of_one_id_in_one_path`
   is free because the store is a function; a version that quantified over
   commands would have needed a proof per command. Ask: can the type forbid it?
   Can a decidable check on the post-state establish it?
2. **Put the missing fact into `planWf` instead of proving it.** Sorted-list
   extensionality with `≤` is false; the fix was not a cleverer proof, it was
   adding rank distinctness to `planWf` so the order became strict.
3. **State the law and refute it.** Several of tm's stated laws are false as
   written. A refutation is a deliverable of equal weight — `move_last_wins_refuted_globally`,
   `move_back_at_a_fresh_rank_is_not_the_inverse`,
   `floor_and_respect_are_incompatible`, `monthOfWeekByToday_is_not_stable`.
   A kernel that stayed silent about a false law would be repeating the mistake.
4. **State the law, prove it on a subdomain, and name the subdomain in the
   theorem's own name.** `move_last_wins` holds at entity level and is refuted at
   plan level; both are theorems and the pair is the honest statement.
5. **Keep the Rust proptest, state the law in Lean, and prove it last or
   never** — the recorded recommendation for L24 (tail-drop) and L25 (stability).
   "A kernel that proves 25 of 27 laws and property-tests 2 is not compromised —
   but decide that deliberately now rather than discover it in month six."
6. **Cut the scope and record the gap by name** (§9.2).

What you must **not** do: weaken the predicate so the obligation goes through.
`rfl` offered for a `Bool = true` obligation fails with an *application type
mismatch*: the argument `rfl` has type `?m.7 = ?m.7`, and the expected type is
the `wf … = true` it was supposed to discharge. (`Negative.lean:21`, run today —
the metavariable number is elaborator state and will differ; do not grep for it.)
That message is the guardrail working. The wrong reaction is to make the
guardrail weaker; the right one is to satisfy it or to say you could not.

### 3.2 The one `sorry` exemption, and the burn-down

`kernel/TmKernel/Goals.lean` holds every remaining obligation of stages 3–6 that
*can* be written down, as a Lean `theorem` whose statement elaborates against the
real kernel and whose proof is `sorry`. **40 at `bf7cc63`** (52 at `c8f3a38`;
stage 3's twelve are all gone — discharged, refuted, or renamed to a narrowing,
each recorded in the README), grouped by stage inside the file, with provisional
`def … := sorry` signatures only where the spec settles the signature.
*It is **0** since W-39 (2026-09-30): track K refuted the last six stage-6 goals as
written and proved each law beside it, and every stage's section of the file is empty
(README "Stage 6 — W-39 track K"; gap 3553). The figures in this section are the history.*
*It is **1** again since the W-39 repair (2026-09-30): `plan_places_no_demanding_block_after_wind_down`'s
refutation stood on the kernel's window running past the night over a multi-day wall, which the repair made
the fork planner's (README gaps 3556 and 3713), so the refutation fell and the goal came back, unproved.*

Three properties make it safe, and all three are checked:

1. **Nothing imports it.** `TmKernel.lean` does not and no module does, so its
   `sorry`s cannot reach a proved theorem. Check 3 — the axiom audit — is what
   *enforces* that: a `sorryAx` in `Check.lean` means `Goals.lean` leaked.
2. **`totality.py` exempts it by filename**, not by pattern (§3's R1 row).
3. **It elaborates on its own**, and check 7 fails on an *error*. The `sorry`
   warnings are the point; an error is not.

**What a statement that only typechecks buys.** It is guaranteed to be
well-formed and to name real definitions. A goal nobody can state precisely is a
goal nobody has understood, and finding that out now costs a session rather than
a stage. It has already paid: writing these found that spec §8.3's "monotone
rank" cannot be stated over spec §7's `p` until stage 5 exists, and that B3 —
`close_week_folds_a_dropped_child_into_its_parent` — cannot *fire* until gap
22's `Core.parent` decision is taken, which makes that a visible precondition of
stage 4 rather than a surprise inside it. *(Taken as D6; B3 then fired and was
refuted as additive — `close_week_does_not_add_a_dropped_child_to_its_parent`, with
`close_week_folds_dropped_children_by_max` beside it — at stage 4 final step 4.)*

**The count is a burn-down, not a score.** To discharge a goal:

1. prove it in the module it belongs to — `Cmd.lean` for a command law,
   `Plan.lean` for a plan-level one, and so on;
2. append its name to `Check.lean` under your own banner (§6.3), so the axiom
   audit covers it;
3. **delete it from `Goals.lean`.** The number check 7 prints drops.

Removing a provisional `def … := sorry` is the same move: it is replaced by the
real definition in the real module. A goal that turns out **false** is a finding
of equal weight (§3.1 item 3) — rename it to the negation, prove that, and record
it. Five were flagged as expected refutations or expected narrowings at their
doc comments, and three of them have gone exactly that way:
`move_has_an_inverse_command` (L22) was refuted as `move_has_no_inverse_command`
(`378fdf9`); `joining_lines_is_injective` as `joining_lines_is_not_injective_char`
(`a6dcc96`); and `the_json_edge_round_trips` was narrowed, as its doc comment
licensed, to `the_response_call_emits_parses_back` (`b7f504d`). The two still
standing are `close_week_and_close_month_commute` (L17) and
`lifecycle_commands_commute` (L27) — *both refuted at stage 4 step 3, as
`close_week_and_close_month_do_not_commute` and `lifecycle_commands_do_not_commute`.*

**The number rises only when a new debt is deliberately admitted**, and that is a
thing worth noticing in a diff. It is not progress; it is a decision. Say in your
handover which goals you added and why they could not be discharged.

A goal deleted without a proof is the worst thing you can do to this file: check 7
goes *down* and nothing is true. §9.2 lists it with the other disguised gaps.

---

## 4. Settled — do not relitigate

Each of these was decided by hitting the alternative. If you disagree, you are
arguing with a decision, not an oversight. Changing one is a plan-tier decision
that needs the user's assent, not an agent's judgment.

| decision | why, in one line |
|---|---|
| Item lines are rendered, never stored | there is then no append for a precondition to be missing from — the entire bug class |
| `Store.get : Id → Option Entity` | makes "an id names one item" a *function*, and makes four pieces of Rust reconciliation machinery deletable |
| `Bool` predicate on a plain record + `Subtype`, never a dependent proof field | a proof field whose type mentions a field breaks `{c with …}`; it was tried and broke in eight places |
| Three tiers, with the tier chosen deliberately per property | the structural tier deletes machinery; the wrong tier costs a proof per command forever |
| `WfPlan.mapAt` re-runs the whole of `planWf` on every post-state | the check cannot be forgotten by a command nobody has written yet |
| A relocating command takes a `Dest p`, whose second field is a proof and whose only constructor is `resolveDest` | `move ^m1 7` on a one-document plan once deleted the item and returned `ok`; a `Nat` off the wire cannot supply the proof |
| Nothing but `String` crosses the FFI; the C shim is permanent | the FFI spike SIGSEGV'd in 3 of 5 runs sharing one `lean_object*` across 8 threads; `lean.h`'s host API is `static inline`, so `bindgen` cannot help |
| The parser and serializer live *in* the kernel | adding a command is one case in `parseCmd` and one in `applyAll`; nothing is marshalled |
| The kernel is total | a Lean panic prints a C backtrace, returns `Inhabited.default`, and gives the host **exit code 0** — a silent wrong answer, which is the failure class this exists to remove. `lean_set_exit_on_panic(true)` is no better: `exit(1)` with no unwind leaves a ratatui terminal in raw mode |
| No `Float`, no fixed point, no `Rat`; every ratio is a pair and every comparison cross-multiplies | Lean 4.33.1 has 421 `Float` constants, 69 theorems, and **zero** about `+ * / ≤ <`. `Rat` normalises by `gcd` on every operation and cannot represent `⟨n,0⟩ = ∞`, which §7.1 requires |
| The statistical layer stays in Rust | the kernel consumes a fitted model as data; it never fits one. `exp(−age/decay)` is outside the kernel entirely — the one transcendental has no soundness theorem worth proving |
| `Id := List Char`, not `String` | in this Lean, `String` is `ByteArray`-backed and the `List Char` round trip is not a core theorem; the proofs stay off UTF-8 |
| `Day := Nat`, no `Int`, origin 0001-01-01 | nothing before year 1 is representable, which is what makes `ofDay` total |
| `Store` is an interface (`get`/`dom`/`domSpec`/`domNodup`), not a concrete map | `Std.HashMap` internals are opaque to `decide` and `rfl`; a fast checker and a provable checker may be two artifacts, and the proofs live on the interface |
| Six `Status` cases, not five | a lone `[-]` is a *state*: `close month` carries a `# Demoted` copy forward without touching its partner, which may be in a file the host never hands over |
| The week→month tie-break is `monthOfIsoWeek` (the civil month of the week's Thursday) | total, and a function of the week alone; "the month of today" is refuted by `monthOfWeekByToday_is_not_stable` |
| `close day` targets the week containing *now* (`closeTo`), not the week the closed day belonged to; the stamp stays `demoted:D<dd>` | the owner drove stale trees (D1, 2026-09-12): the closed day's own week double-stamped a skipped weekend off Monday's plan, deleted a child whose parent was in the closing week, and stranded a close more than 16 days late in a sealed file |
| **D5** (2026-09-13): §9.1's proof : definition brake is overridden — relational (two-run) laws keep being proved, L24/L25 included; a two-run theorem a change breaks is re-proved in that step, never downgraded to a property test or deleted, and a step whose re-proof will not close is not done | the owner priced the ratio (4.52 : 1 at `c9ef6f0`) against losing the laws that caught stage 4's defects; README "Stage 4 final". *Re-measured at stage 4 final step 4 (B3, the stage's last goal), same script: **4.80 : 1** (18,815 : 3,917), 9.36 : 1 in `Close.lean`, 6.22 : 1 in `Report.lean`.* **Re-measured again at stage 5's close, same script, over the 78 modules: 4.03 : 1** (42,506 proof : 10,543 definition lines; net 3.97 : 1 with witnesses and fixtures removed, 3.00 : 1 counting each declaration's doc comment with it — taken at the stage's closing commit, after the switch, S2 and Q6(f); it read 4.06 : 1 / 42,426 : 10,451 at `b344185`, before S2 added `emitEvent`'s definitions and theorems). It **fell** while the library grew 2.3×, and the arithmetic says why: what stages 5's D9/D10 tranche added is **23,611 proof : 6,534 definition lines = 3.61 : 1**, against the design's own estimate of "≈ 3.6 : 1, below stage 4's 4.80 : 1" (`kernel/design/stage5/stage5-D9-D10-design.md` §14.9) — the tranche landed on its predicted ratio and pulled the average down. Per module the spread is wide and worth reading before quoting the average: `Close.lean` 10.10 : 1, the `Seal*` group **5.74 : 1** (10,471 : 1,824), `Lookahead.lean` 3.99 : 1, `Replay.lean` 3.32 : 1, `Log.lean` 1.86 : 1 (a field table is definition; it rose from 1.81 with S2), and `Seal.lean` **alone** 0.22 : 1 (216 proof to 983 definition lines — it holds the types and the codecs, and its proofs live in the 57 modules beside it). Under D5 it informs and stops nothing |
| **D6** (2026-09-13): parents are on, strictly — `@parent` is a view over the token vector, not a stored slot; a dangling link refuses the whole tree (`danglingParent`), a cycle refuses (`parentCycle`); the corpus harness loads whole trees only | one reader per field (§5.3), and a refusal by name over the old Rust's check-only `@ghost`; stricter than the Rust, chosen knowingly (gap 22, §10.5 q3) |
| **D7** (2026-09-13): at a week close a past-due dated `persist` line (a point's or interval's default) moves to `backlog.md # Overdue`, staying `[ ]` — pulled forward from stage 5 | spec §6.3's week row and §5.3; §4.3's own example week (`^d1`) otherwise refuses its automatic close (gap 55) |
| **D8** (2026-09-13): a not-yet-due dated line unfinished at a week close is demoted like any other and keeps its `due:`; the month rule "an outcome carries no date" covers outcomes, not `# Demoted` records — a deliberate owner narrowing of `shapesWf` | spec §6.3 calls `# Demoted` records work items, and fork-point `check.rs` has no date rule for month items (gap 55) |
| **D9** (2026-09-14): the Lean kernel replays `.tm/log.jsonl`, all of it — requests carry the log's events; the kernel derives every replay fact (minutes and blocks per item and per day, last completion, completion dates, routine instance status, undo masking, lost minutes) and hands energy and duration observations back to Rust, which keeps **only** the statistical fit (plan §3.6); the old Rust `log::replay` stops being a source of decision facts | one reader, and it is proved (§5.3); `move_has_no_inverse_command` already made replay the only correct `tm undo`. §10.5 q4; README "Stage 5 step 1" |
| **D10** (2026-09-14): future-day capacity is an **exact weighted mixture** — expected minutes at each energy level = `p_lounge · lounge + (1 − p_lounge) · home`, carried as exact numerator/denominator pairs through the EDF pass with nothing rounded; this deliberately disagrees with fork-point `capacity::lookahead` (lounge iff `p ≥ 0.5`) and is on stage 5's parity exception list | no unstated rounding reaches stage 6 (R7, gap 26); a threshold throws away the weight §8.4 states. §10.5 q5; README "Stage 5 step 1" |
| **D11** (2026-09-14): the D9/D10 design's price is confirmed (design Q1), and D9 and D10 run as **parallel tracks** — D9 on `rebuild-on-lean`, D10 (L1–L9) on `stage5-lookahead` | option (a) of `kernel/design/stage5/stage5-D9-D10-design.md` §4 Q1; no narrowing lever taken. README "Stage 5 D9/D10: the owner's answers" |
| **D12** (2026-09-14): stage 6's window (E7), slot cut and future-day energy prediction (home cap, budget limit) are **pulled into stage 5** as L2–L4; the kernel computes both location histograms | one reader of walls; Rust's comment-blind wall parser (gap 45) never decides capacity. Design Q2 (a) |
| **D13** (2026-09-14): `.tm/cache/replay/` is allowed as persistence of kernel output; the kernel may read a sealed record back for an explicitly old date; `tm init` excludes `.tm/cache/` from sync | the cache is derived and rebuildable (T9); a sealed record is trusted as the checkpoint is, and law 1 proves it equals the replay's. Design Q3 (i), (ii), (iii)(a) |
| **D14** (2026-09-14): the ≈ 13 unread fork `Replay` fields are **ported, not deleted** — R11 keeps them, the kernel derives them into the sealed day records | D9 says "derives every replay fact"; restoring them after the switch would need a port plus a rebuild of every sealed record. Design Q7 (b), against its recommendation |
| **D15** (2026-09-14): `--json` capacity fields stay **integer floors**, each with `<field>_exact: {num, den}` beside it; `total` is `floor(Σ exact)` | no breaking change for readers, and the exact value is visible. Design Q4 (a); governs L8 |
| **D16** (2026-09-14): the **kernel writes log lines** — appending verbs send typed events and the kernel returns the lines, in a new step right after the switch S | one definition of the line format, not two held together by T2. Design Q5 (b), against its recommendation |
| **D17** (2026-09-14): **`capDen = 10^18`**; a weight with more than 18 decimals, or outside [0, 1], is refused by name; Rust holds units as `u128`, and units cross the wire as digit strings | keeps the fork's acceptance of hand-edited `p_lounge` with no rounding anywhere. Design Q8 (b); governs L1, L6 |
| **D18** (2026-09-14): `tm check` lists malformed log lines and lines dated more than 2 days after `now` as **warnings** (exit code unchanged); a hand edit beyond the rebuild bound is a **named fault**; the memory cap is never raised. Q6's seven fork quirks take the design's recommended dispositions | a corrupt line must not go from fatal to invisible, and raising the cap risks an OOM on a swapless machine. Design Q9 (i)(a), (ii)(a), (iii)(a); Q6's last column |
| **D19** (2026-09-16): **S stays all-or-nothing** — the switch is ONE commit in which every verb begins reading through the kernel at once; it is made to fit by landing everything separable BEFORE it (the eight missing T9 tests, T12, T11's seven latency rows, the per-verb call counts, gaps 134-136 and 138), each green against the unswitched binary, so the switch commit itself is the body swap plus §12's deletion and nothing else | the owner priced a third dedicated run against weakening the gate. §14.6's rule protects against a **half-switched binary** (some verbs on the kernel, some on Rust), which only the body swap can cause; the acceptance instruments and the mechanical fixes cannot, so moving them out of the commit costs no safety and is what makes the remaining commit session-sized. Two agents (W-6, W-7) refused S correctly as oversized; the gate is kept and the work is re-shaped around it, never the reverse |
| **D20** (2026-09-16): **`tm break` validates its arguments in both arms** — `tm break zzzz` is refused by name whether or not a break is already running; the running-break arm parses before it acts, and the arguments do NOT retime a running break (gap 138) | the verb was two verbs and only one of them validated: with a break running, `tm break zzzz --where bed` exited 0, ended the break and discarded both arguments. That is §5.13's failure class exactly — a plausible keystroke that neither works nor says so. Refusing is the smallest change, adds no capability, writes no new log bytes, and needs no parity entry; retiming was considered and declined as a new feature |
| **D21** (2026-09-16): **the fork retarget comes BEFORE S, and S still stays whole** — T1-T3 and T5 are re-anchored to fork point 4748911 (gaps 137, 147, 149) as their own preparation step; only then does S land as one commit with the body swap and §12's deletion | gap 146: §14.6 item 3 points `tm/tests/support/replay.rs`'s `replay_of_text` at the kernel, and the instant it does, T5's 20 tests and the door suite's 15 become **kernel-vs-kernel self-comparisons** — still passing, proving nothing, on the least reviewable commit of the stage (README gap 16's lesson, AGENTS §9.2's worst disguised gap). The retarget is owed either way, so the only real choice was ordering, and the owner put the instrument before the change it must watch. D19 is unchanged: S is still ONE commit. *Campaign's own call inside this, revisable: gap 147 freezes ONE representative generated month rather than every generated class, because a digest would have to normalise P21 out and so hide the one thing P21 exists to watch* |
| **D22** (2026-09-16): **`tm log --json` keeps byte-identity with the fork, via `RawValue` scoped to the renderer** — design §11.4 step 5 is corrected to say what is buildable | gap 144, the first design sentence this campaign found **unimplementable as written**: it demanded the output be both a generic `serde_json::Value` and byte-identical to the fork, but without `preserve_order` Value is a `BTreeMap` and alphabetises keys where the fork writes `t` first; following it literally moved `tm log --json` on 7 of 69 invocations. `RawValue` keeps the order with a one-function blast radius; `serde_json/preserve_order` was declined as changing Value ordering workspace-wide unmeasured, and alphabetising was declined as costing byte-identity in one of the few places the corpus test still catches a regression. Pretty-printing must be re-emitted explicitly and verified |
| **D23** (2026-09-16): **`tm-oracle` gains a per-log-entry `parse-entry` mode** so T1-T3 keep a differential oracle after §12 deletes the in-tree parser | gap 148, which nobody had costed: T1-T3 test serde's and chrono's per-line acceptance against the parser §12 removes, and the oracle's existing `parse` reads item lines, not log entries. Retiring the parse half was declined (the acceptance edges would stop being compared against anything) and freezing fixtures was declined (expectations go static and cannot follow a legitimate grammar change). Inert without `TM_ORACLE`, like the rest |
| **D24** (2026-09-16): **L9's day 0 gets its facts by opening the seam INSIDE the kernel**, not by couriering them back through the capacity request — the kernel's own `log` answer feeds the capacity section | gap 210: the kernel answers a request's `log` and `capacity` sections independently — `logOp`'s `Seal.Run` answer is consumed by `logBody` and discarded, and `readCapacityZ` has no argument a replay could arrive through. The courier route was genuinely available post-switch (since the host now DECODES those facts from the kernel rather than computing them, it would be a second wire representation, not a second reader or definition) and was DECLINED: the seam is a signature change through `logOp`, `logAnswerOf`, `logSectionWith` and `runCapZ` whose laws are re-proved over their new shapes — never weakened (D5) — and **design §14.7's F2 and F3 need the same seam, so three steps pay for it once** and day 0's facts never cross the wire twice. Priced at ~200 definition / 600 proof lines, −150 Rust, 4–6 agent-days |
| **D25** (2026-09-16): **stage 6 (the planner) is the next stage**, and the seam, L9, F2 and F3 fold into it as one shared piece of work rather than three separate ones | stage 5 is closed at `c627148`: the kernel is the binary's only reader (`2b26be3`) and only writer (`47a0443`) of the log. All 13 remaining `Goals.lean` goals are stage 6's, so it is the only stage carrying outstanding proof obligations. The performance levers (gaps 121, 122, 123, 126, 127, 143) stay open and unstarted: genesis is the only cost that grows with log length (first verb ~2.15–2.48 s on a three-year log against a 5 s bound) and nothing is failing, so they buy headroom rather than fix a defect. Stage 5's residue gaps stay named in §8.3 |
| **D26** (2026-09-17, stage-6 design Q1): **stage 6 runs as TWO PARALLEL TRACKS** — K (the seam, L9, F2, F3-rule) on a worktree, P (the planner's eight steps) on `rebuild-on-lean` | D11's shape, which carried stage 5; they collide only in `Boundary.lean` and the three append-only files. The owner was shown the design's estimate — ~5,360 definition / ~21,350 proof Lean lines, Rust +950/−5,400, **121–167 agent-days** against §8.4's "3–4 wk" — and the fact that the same estimating method priced D9+D10 within 0.3% and 1.3% of actual, and chose the parallel shape over narrowing. K1 (the seam) and K2 (L9) already landed |
| **D27** (2026-09-17, Q2): **the KERNEL collects the planning candidates** — `Cand` is derived from the `PlanCore` the request already loads plus the run D24's seam exposes; the host stops sending them | gap 113: since L8 the capacity request carried a candidate list whose facts were the host's, so `remaining`, `ci`, `due`, `overdue`, `mandatory`, `hot`, `window`, `wall` and `optional` each had TWO readers — the duplication the log switch spent twelve runs removing. This kills gaps 113, 114 and 116 outright. Costs K3 (F2) and K4 (F3-rule) before P4 plus a larger request: ~+650 definition, +1,700 proof, −500 Rust, 11–15 agent-days, most of it owed anyway. The cheap option was declined because a what-if replan or a TUI minute-tick **cannot re-derive facts it did not compute**, so 114 and 116 would have stayed open by construction rather than by choice |
| **D28** (2026-09-17, Q3 — stage 6's largest): **L26's eleven single-run laws are PROVED, not checked-and-refused.** `dayPlan_ok : ∀ r, planOk r (dayPlan r) = true` is proved as a fold induction carrying eleven invariants through all eight planner steps; `dayPlan` keeps its total signature and does NOT become `dayPlan?` | ~4,500 proof lines and 22–30 agent-days, about a quarter of the stage, after which each of the eleven discharges in one line and leaves the burn-down honestly. The named-refusal route was declined on two grounds: it would give the kernel power to REFUSE to plan a day (a user-visible behaviour change), and the eleven laws would stop asserting the planner is correct and start asserting only that it is checked. The two are mutually exclusive — a gate behind a proved lift is "a check no input can fail", §9.2's own disguised-gap list |
| **D29** (2026-09-17, Q4): **`plan_tail_drop` is RESTATED with the Active item erased**, not restricted — `∃ n, (assignedOf (dayPlan r')).erase a = ((assignedOf (dayPlan r)).erase a).take n`, shipped with `plan_tail_drop_as_stage_6_wrote_it_is_refuted` and its witness | the goal as written is FALSE against the fork: §8.2 choice 5b reserves the running block before the budget is consulted, so shrinking the budget can drop items ranking ahead of the Active item while it stays, and the result is not a prefix. The restated form is what §8.3 actually says ("Active item excepted"). Restricting to requests with no Active block was declined as **§5.2's failure mode exactly** — a precondition that excludes the interesting case, since a running block is the normal state of a working day. This is the campaign's refute-and-rename protocol (§3.2) |
| **D30** (2026-09-17, Q5–Q8): **the stage-6 design's remaining four recommendations are taken as CAMPAIGN CALLS, revisable by the owner at any time** — (Q5) the one-renderer acceptance means *one row renderer whose output every surface prints*, so `render_now_with` stops formatting and starts selecting, with no user-visible change; (Q6) **the kernel emits `Row` CELLS and one Rust function pads** — `emit::render_row` becomes the only padder and G6's East-Asian width table stays where the terminal is; (Q7) **§9's facts and its consequence replan are the kernel's, the prompt UI and its timers stay Rust**, which closes gap 114; (Q8) the §9.1 5 ms TUI trigger is **measured at P5 with the fallback pre-authorised** (the TUI replans on reload), and P5 adds the missing instrument — a T-row for a 500-item replan through the FFI — so the trigger has a number before it can fire | each has one defensible option and the alternatives are self-defeating: Q5's literal reading is unsatisfiable without dropping the TUI's width parameter; Q6(b) moves ~120 lines of Unicode ranges into Lean with no theorem worth proving, against `Id := List Char`'s whole purpose; Q7(a) puts the kernel inside ratatui and Q7(c) leaves §8.3's invariants unstatable; Q8(c) is against §4's settled "nothing but String crosses the FFI". Recorded as the campaign's calls, NOT the owner's, and revisable without relitigation |
| **D31** (2026-09-17, gap 301): **the item grammar is widened so a state-box-less, id-less line is representable in `PlanCore`** — the box and a title-derived key land in ONE commit (D19), on track K as K3a, before K3b's recurrence family; D27 stands unchanged and waits for it | D27 was chosen priced at 11–15 agent-days with this prerequisite invisible. W-14 measured it: `Line.lean`'s `parseBody` requires `- [<glyph>]`, but spec §4.1 has routines.md and optional.md deliberately omit the box, so every line of those two files is `PErr.notAnItem` and loads as PROSE with no entity in `PlanCore.store` — on plan-basic, **10 of 28 candidates are keyed by title with no `^id`**. Deriving a field for the 18 that have ids and leaving the host to compute it for the other 10 would be a second reader on a subset, the exact class D27 exists to end. Relaxing the box ALONE was DRIVEN, not inferred: every routines line becomes `PErr.noId` and the whole plan is refused. Blast radius measured at **270 declarations — 145 theorems (3.6% of the audit), 117 defs, 6 structures — across ten files** (Line.lean 135, Boundary.lean 32, State.lean 25, Cmd.lean 24, Plan.lean 17, Close.lean 15, Negative.lean 9, Tree.lean 6, Text.lean 5, Report.lean 2); the 145 are **re-proved, never weakened** (D5). §14.7's K column (970 / 2,750 / −600 / 17–24 days) prices the recurrence FACTS and not the grammar, so it is re-added before K3 is scheduled. Reversing D27 and changing the plan format were both offered and declined — the format change would land the cost on the owner's own hand-edited Markdown, and §4.1 omits the box deliberately because a routine recurs rather than being checked off |
| **D32** (2026-09-17, gaps 475+476): **a title-key collision keeps REFUSING, and is made findable** — `LErr.dupId`, `.notADemotion` and `.ambiguousDemotion` are widened to carry BOTH placements' `path`/`line` so the message names the two colliding lines, and **`tm check` is given sight of a kernel load refusal** | D31's grammar made title-keyed lines real entities, so two lines with one title now collide. DRIVEN by the main session at `8c3b6dc`: duplicating any inbox note, or two `sleep` routines, makes `tm plan`/`now`/`review day`/`tm drop` exit 1 while **`tm check` prints "no problems" and exits 0** — fatal everywhere, findable nowhere. Tolerating-and-warning (the D18 shape) and disambiguating by occurrence were both declined: the first plans with one of two lines and silently drops a legitimately-distinct routine, the second makes a key unstable across edits so an undo or a close record can quietly point at a different line. The widening is the `Look.WallIx` move — widen and prove the old one-`Id` view is `.map Placement.id` of the new — and is a WIRE change under D19: `lerrJson` and its build-order theorems, `pairedEntity`/`buildEntity`, §2.4's wire table, the bridge decoder and the FFI corpus move together. **Campaign call inside this, revisable: a tree the kernel refuses is an ERROR in `tm check`, not a warning** — every other verb already fails on it, and `tm check` is wired into the pre-commit hook of every generated plan, where catching it is the point |
| **D33** (2026-09-17, gap 477): **when a verb puts a state box on a title-keyed line, it also writes the `^id`** | `tm drop <routine title>` wrote a boxed id-less line, which D31's grammar refuses by cheat 174 — so dropping a routine bricked every kernel-backed verb on that tree (pre-existing, verified byte-identical at `d2c0aa6`). This follows D31's own principle rather than bending it: a boxed line is a tracked item, and a tracked item needs an id that survives the user editing its title. The alternatives were declined — keying a boxed id-less line by its title retires cheat 174 and has the kernel invent ids for lines the user marked as tracked, so a title edit silently orphans the item's history; refusing the drop leaves `tm drop` unusable on routines, a regression against the fork rather than a port of it. The cost accepted: a `^id` token appears in the user's Markdown that they did not type, which is honest about what just happened to that line |
| **D34** (2026-09-18, gap 500): **D27 is DOWNSTREAM of the planner, not upstream — the planner is finished first (P4–P8, then R3), and D27 follows.** The design's K3/K4-before-P4 ordering is reversed | W-16 found the concrete reason D27 had been refused twice: `Ctx::priorities` hands its `Vec<Candidate>` to `tm-core/src/planner.rs` via `PlanInput::with_ranking`, and **`Candidate` has THIRTY fields of which D27's nine are a slice** — the shipped planner also reads `title`, `planned_min`, `multiplier`, `scope`, `floor`, `cap`, `state`, `blocked_by`, `waiting`, `loc`, `splittable`, `wall_today`, `instance`, `root_order`, `own_order` and `tags`, none of which the kernel can supply until `dayPlan` replaces the eight steps. So `collect_candidates` dies with `planner.rs` at **R3 and not before**, and the only copy D27 can delete is `cand_json`'s nine JSON keys. Moving all thirty was declined as building a wire explicitly to tear out; splitting `Candidate` was declined because the split line would be drawn through a struct about to be deleted. **P4 is NOT blocked by this** — it consumes the candidates as they arrive on the wire today; D27 changes where they come from, not what they are. Cost accepted: gaps 113, 114, 116 and 301's item 1 stay open for several more runs, and **gap 577 records that the host's nine facts are pinned only by a copy test — inverting one leaves the whole suite green while `tm plan` visibly re-ranks** |
| **D35** (2026-09-18, gap 584): **every host-only write path asks the kernel whether the tree still loads** — `lifecycle::kernel_problems` is lifted out of `tm check` into one shared gate | DRIVEN, not reasoned: `tm edit ^d1 'title=…'` takes the host-only path (a typed non-key edit, gap 41), rewrites the file and exits **0**, while `tm plan` exits 1 and `tm check` exits 2 on that same tree — so a user can keep editing a tree every read-verb refuses. The cheap alternative was driven and found UNSOUND: `closing::auto_close` runs only when a period has ended, so on a tree where nothing is due the verb holds no refusal at all and the collision produced no warning whatever. Gating only "corrupting" paths was declined as needing a rule for which edits are inert — a rule to maintain and to be wrong about. **The cost is a whole-tree kernel load per write on `tm edit`'s commonest branches and it MUST be measured against T11's `tm drop` row (127–132 ms, the one reliable baseline) before it lands**; if it does not fit, that is a finding to report, not a bound to raise (D18) |
| **D36** (2026-09-18, gap 686): **check.sh's check 5 guards ALL SEVEN of `tm-kernel-ffi/tests/stack.rs`**, and the **+59% built-tree cost is accepted deliberately as a one-time coverage payment** | those seven tests ran in NEITHER check.sh nor `cargo test --workspace` — including **T17, the replan instrument D30(Q8)'s TUI decision now rests on** *(named T12 when D36 was written; renamed at W-18 track A — T12 and T14 were both taken, README gap 688)*. Measured: +2.23 s on check.sh's 3.79 s. The repair step refused to spend the 10%-per-step rule quietly and reported it instead, which is the behaviour the rule exists to produce. **The rule stops CREEP accumulating step by step; a single declared payment for coverage is a different thing, and recording it as such keeps the rule meaningful rather than bent.** ~6 s absolute is trivial. Guarding T17 alone (+8.7%) was declined as leaving six tests guarded by nothing; moving tm-kernel-ffi into the workspace was declined as double-running checks 5 and 6 and moving the test-count figure every ledger block quotes, which is structural and not a repair |
| **D37** (2026-09-18, gap 687): **`tm check --fix-ids` records an undo entry** — `lifecycle::check` gains a `Recorder::start` and joins the undo-recorder table | it writes item ids into the user's own source lines and, driven on a SOUND tree, exits 0 while `tm undo` then answers "nothing to undo". The principle already holds everywhere else in tm: **if a verb changes your files, you can take it back** — and a verb that edits lines the user wrote is precisely where reversibility matters most. Recording the exemption as deliberate was declined: it leaves one write verb behaving unlike every other, and a user who did not want those ids with no way back |
| **D38** (2026-09-18, D30(Q8)'s trigger FIRED): **the TUI replans on RELOAD, not on a tick** — the pre-authorised fallback is now in force | the measurement D30(Q8) required landed at W-17 as T17 in `stack.rs` (T12 as written; gap 688): a 500-candidate replan through the FFI costs **20.89–21.30 ms against §9.1's 5 ms tick budget** (and 47–125 ms at opt-level 0 with a 2,000-line tree). The 0.8 ms figure behind the original budget was taken at the FFI spike and never against this kernel, which is why D30(Q8) made the measurement a precondition. No decision is re-opened: D30(Q8) pre-authorised exactly this fallback, and the number is now on record rather than assumed. Smaller shapes do fit — a 40-line tree with 50 candidates is 2.51–2.65 ms at opt-level 1 — so the trigger is about scale, not about the kernel being the wrong shape |
| **D39** (2026-09-18, gap 779) — **CAMPAIGN CALL, revisable: check.sh gains a check 8 that resolves backticked snake_case identifiers in `kernel/TmKernel/**.lean` AND `kernel/README.md` against the declaration set**, with a DECLARED allow-list for fork-function and config-key names | **this is the campaign's most persistent defect class and the fifth consecutive run has shipped an instance**: no existing check reads a doc comment, so a citation of a deleted or renamed theorem is invisible to the gate, and the independent auditors have had to find each one by hand. The sweep is already measured — 166 unresolved identifiers in Lean of which **ZERO were defects**, so the allow-list IS the work, and the README half is where the one real dangling referent actually lived. Taken as a campaign call rather than an owner question on D36's precedent (the owner paid +59% of check.sh's wall for coverage of seven unguarded tests, and that guard caught a real regression on its first run); revisable without relitigation. It is a change to what "green" means, so under D19 it lands as its own commit, and gap 703's measurement — that checks 3 and 4 are already spending the 10%-per-step budget — must be re-measured with it |
| **D40** (2026-09-19) — **check.sh gains a check 9: every definition a step ADDS is mutated — body replaced by a constant, one at a time — and the step must show something FAILING for each**, with the transcript in its block | **the campaign's leading defect class, found three times by hand and never by a gate**: W-17's P4 sort key (halves swapped, 1,342 tests green), W-18's nine candidate facts (invert one, suite green, `tm plan` visibly re-ranks), W-19's `Planner.Ranked.gatherable` (`:= true` and 168 build targets, every theorem, all 19 witnesses and check.sh 8/8 stay green). Scoped to NEW definitions so the cost is bounded by the step's own size rather than by 4,665 theorems, and because the moment a definition is introduced is when its distinguishing witness is cheapest to write. A full sweep of the existing kernel was declined as producing a backlog rather than preventing new instances; relying on the auditors was declined because they sample rather than sweep, and nobody knows how many shipped instances already exist. **Follows check 8's shape exactly: a gate whose first job is to be seen failing** |
| **D41** (2026-09-19, gaps 880/881) — **check 8 widens to camelCase identifiers and to AGENTS.md; it does NOT sweep `kernel/design/**`** | D39 wrote check 8's scope and the repair step correctly refused to widen it unasked. Both blind spots were measured instead: resolving **snake_case only** let a live stale emitRefused report green and hid **31 eligibleAt citations** — a name W-19's own gap 809 declares nonexistent, so had they been snake_case the gate would have failed at 31 sites. Widening to AGENTS.md costs three exemptions or three repairs; **`kernel/design/**` would cost 144 and would be wrong**, because the design is a historical record that deliberately names things the repo no longer has. The 31 are real defects and are repaired, not exempted |
| **D42** (2026-09-19, gap 993): **`.tm/state.json` becomes a DERIVABLE CACHE, rebuilt from the log when missing or stale, exactly as `.tm/cache/replay` is under D13** — with the symmetric acceptance test "deleting the runtime state changes nothing" added to T9 | DRIVEN by the main session at `e588fc5`: with `^d1` running, `rm .tm/state.json` leaves `tm now` saying "nothing running" and `tm check` saying "no problems" at exit 0, while `.tm/log.jsonl` still holds the `start` line — and the README's own reproduction is worse still: **in the same tree `tm plan` renders `^p1` with ▶ while `tm done` and `tm stop` both answer "nothing is running" at exit 1.** The log already records a `start` with no matching `stop`, so the running block is derivable from the one reader the kernel owns (D9). **This removes a second source of truth rather than teaching a checker to police it, which is the decision the whole rebuild is named after.** Teaching `tm check` to report the disagreement was declined as leaving two authorities that can still diverge between checks; deferring to R1 was declined because a silent data-disagreement would ship meanwhile, and it is exactly the class §5.13's drives exist to surface. **The step must say which of §9's fields are genuinely derivable and which are host-only** — `last_plan_hash` and `interrupt` may not be, and an honest split is worth more than a forced one |
| **D43** (2026-09-20, gaps 1007/1089): **P8 unifies the two padders on `emit.rs`'s East-Asian table — `emit::render_row` becomes genuinely the only padder and the TUI calls it — and the resulting display change is ACCEPTED** | D30(Q6) bought "one row renderer whose output every surface prints", and gap 1089 found that premise was already false: `tm/src/tui/queue.rs` has its own width/truncate/pad measuring with **ratatui's unicode-width** while `emit.rs` uses its own **East-Asian table**, so the two can disagree on CJK and emoji. **Two width tables that can disagree is the same two-sources-of-truth defect as D42's `.tm/state.json`, in pixels rather than data** — and single ownership of the bytes is exactly what kills G1. Columns containing wide characters may shift by a cell in the TUI: that needs a **behaviour row** and **the grep guard that stops a second padder reappearing** (gap 1007 owed that guard and never got it). Unifying on ratatui's measurement instead was declined because the fork's own output is the East-Asian table's, so the corpus round trip and the fork comparand would both move; leaving two padders was declined because it leaves D30(Q6)'s "only padder" untrue and G1 alive |
| **D44** (2026-09-21, gap 1198): **`emit.rs`'s width table collapses ZWJ sequences and skin-tone modifiers to their base width**, hand-rolled inside the existing table — **no new dependency** | the table measured such a sequence at 4–6 columns where a terminal draws 2, so a title carrying one rendered visibly short. Pre-existing in `emit.rs`, **but D43 made that table authoritative for the TUI, which previously used ratatui's unicode-width — so for the TUI this is a regression D43 introduced, not an inherited quirk.** Because D43 made the table single-source, one fix corrects the day file, `--json`, `tm now` and the TUI at once. It **diverges from fork 4748911 for emoji widths and therefore needs a PARITY ENTRY** recorded the way P17 and P21 were. Recording it as a kept quirk beside Q6's seven was declined because it would leave the TUI rendering worse than before D43; adding a unicode-segmentation crate was declined because it would be **the first new external dependency since the rebuild began** and the hard rule has held for six stages |
| **D45** (2026-09-21, gap 1202): **the LAST `tm arrive` of a day wins** — D42's rebuild-from-log is corrected to agree with the cache, not the other way round | the replay cache held the last arrival while the log derivation took the first, so `arrival`, `window` and `budget` shifted across a cache deletion — **the exact invariant D42 was bought to establish**. The last arrival is also the more defensible reading: if you arrive home, go out and arrive again, the day's window and budget should re-anchor to when you actually settled, and **`tm arrive`'s own semantics already treat a later arrival as re-anchoring — so the derivation follows the verb rather than the reverse.** No shipped behaviour changes. `tm arrive` and D42's table must now be shown to agree, and §5.3 says that agreement has one definition, not two |
| **D46** (2026-09-22, gap 1316): **the `.proptest-regressions` files stay TRACKED, and a new seed line in one is a FINDING — never a dirty tree to revert.** The acceptance rule gains a sentence: **"cargo test --workspace 0 failed" from a single run is a PROBABILISTIC claim, and a block must say how many runs it made** | an auditor ran the suite THREE times instead of once and one run failed: a fresh proptest seed found a **real pre-existing bug** — removing a `ci:0` token from a line where it is followed by two spaces merges a bare word back into the title with its original whitespace, so `set_state_with_ci` does not round-trip (`tm-core/tests/grammar_proptest.rs:277`, minimal input `("- 0 A A ci:0  a @A @a", false)`). Its own conclusion is the point: **"the mandated acceptance line is a probabilistic claim; W-23 held it by luck"** — every green figure this campaign has quoted came from one run. Tracking the seed makes a bug found once a deterministic regression test forever, which is the same move as check 8 and check 9: **turn what an auditor found by hand into something the gate remembers.** Untracking was declined (a bug drawn once is forgotten by the next run); pinning the seed was declined (the test stops exploring and loses the capability that produced this finding) |
| **D47** (2026-09-22, gap 1317): **a column-zero item line inside an `<!-- -->` comment is PROSE — the HOST is corrected to agree with the kernel's `Plan.lean`**, with a parity entry | two readers disagreed about what an HTML comment is: such a line was an ITEM to `tm-core`'s fork-point parser and prose to the kernel. **If you comment something out, every reader should agree it is gone** — treating it as live is the silent wrong answer this rebuild exists to remove. The repair refused to take it alone because the host is also the D21/D22 comparand, so this changes what "is an item" means for `check`, `plan`, `move`, `close` and the round-trip corpus; it **measured the blast radius before leaving it: ZERO instances in `kernel/corpus/**`, `tm/tests/**` or `tm-core/tests/**`**, because `tm init`'s own comment blocks indent their examples by four spaces, so only a hand-written line reaches it. It diverges from fork 4748911 and needs a parity entry recorded the way P17, P21 and D44's P37 were |
| **D48** (2026-09-23, gap 1431): **the planner's wire moves into R2; R3 becomes PURELY the deletion** — §14.5's graph is corrected | doing R2 found a **CYCLE**: aiming `planner_invariants.rs` at the kernel needs `dayPlan` reachable through the FFI, but that wire was assigned to R3 and R3 depends on R2. W-24's `EmitWire.lean` deliberately carries ROWS, not the planner's inputs and outputs, because the shipped binary still plans with the fork's code — asking the kernel for "the day the binary renders" would compare two different days. **Priced exactly:** four request fields are on no wire (`state`, `routines`, `overrides`, `prio.batchMaxMin`) plus a response `plan` key (day, window, budgetBlocks, segments, diagnostics, priorities, hash); everything else is already wired. **Each new value REUSES an existing bound** — `Planner.maxCands`, `CapWire.maxCandId`, `Look.maxPlanMinutes` — and note gap 1330: `CapWire.maxCandidates` is already `Planner.maxCands` under a second name. **Keeping the wire in R3 was declined on this campaign's own evidence: the stage-5 switch was its one all-or-nothing commit and it took four runs and three honest refusals to land, which is why D19 exists.** The window where both can plan is instrumented, not unguarded — comparing them is the property test's whole job. Same class as D34 |
| **D49** (2026-09-23, gap 1430): **`tm edit` has ONE writer, and it is the kernel's** | DRIVEN on the shipped binary: editing one key versus two changes **three independent things** — the alias (`cap=3h/d` writes `max:3h/d` alone, `cap:3h/d` combined), the rendering (`est=2b` writes `est:120m` alone, `est:2b` combined) and **the slot** (on a line with no `est:` key, combined it writes `2b` as a LEADING estimate, a different position in the line grammar). Two writers exist: **the kernel's, which has a theorem, and a host path, which has a written comment.** This is **D16's principle applied to the edit path** — the kernel defines the format — and **§5.3's rule against two definitions of one thing**; where they disagree, **the proved side wins over the commented side.** These are hand-edited files, so it needs a behaviour row for whichever spelling moves and a corpus round-trip re-check. Keeping the fork's spelling as a quirk was declined because it makes a diff depend on how many keys were passed to one verb, permanently and by decision |
| **D50** (2026-09-23, gap 1790): **a COMPOSITION step (P9) lands before R3** — `assignFold`'s rows join `dayRows` so the kernel answers a WHOLE day; only then does R3 delete `tm-core/src/planner.rs` with its last caller | gap 1790 recorded R3's precondition as undecided and the code settles it: **`dayRows` is `stepOneSegs ++ dayRoutineSegs ++ reservationSegs ++ optionalRows ++ restRows` — walls, routines, the reserved running block, optionals and rest, and NO ASSIGNED WORK BLOCKS.** `assignFold`/`dayAssigned` are built and proved (`assignFold_ok` carries the energy filter, `loc_ok` and the wind-down rule) and referenced 17 and 5 times inside `Planner.lean`, **but their rows never reach the day the kernel answers with.** Each P step landed its RULE and its laws; **the rules were never composed into the day.** Meanwhile the shipped binary plans assigned blocks through **32 `planner::` sites across 9 files**, `cli/planning.rs` — the `tm plan` verb — among them. So §14.4's "deleted with its last caller" is unreachable until the kernel's day is whole. **Expect P9 to cost more than the composition itself:** the assigned rows meet the fork's for the first time and `planner_invariants` will disagree — which is the point, and D46 says keep each disagreement rather than smooth it away. **It also likely moves the burn-down, which has sat at 9 for seven runs because several L26 goals are about a `dayPlan` that does not assign.** Narrowing R3 to the comparand was declined (it contradicts §14.4's own text and leaves gaps 113/114/116 open indefinitely); splitting `planner.rs` was declined as adopting §5.3's two-definitions condition by construction |
| **D51** (2026-09-25, gap 2130): **check.sh gains a REACHABILITY gate (check 12), stated as a PROPERTY over all definitions with today's unreachable set grandfathered into a DATED exemption file that may only SHRINK** | an auditor built the instrument nothing in this tree had — a call-graph walk over the emitted C in `.lake/build/ir` rooted at `tm_kernel_call` — and its conclusion is the campaign's sharpest structural finding: **"a definition can be pinned by a theorem (check 9 PINNED), unique (check 11 ok), audited (check 3 ok), cited (check 8 ok) and still be called by nothing — `Tm.remainingMin` is all five."** **Every instrument in the repository reads the SOURCE or the THEOREM SET; reachability is a property of the emitted call graph, so no gate could see it.** Three findings live in that blind spot: D50's `assignFold` (found by hand after eight audit runs, referenced 17 times inside its own module while reaching nothing), gap 501's `Recur.lean` (found by hand), and **`Tree.lean` — 10 definitions and 37 theorems — which nobody had found.** The rule is a property (*not used solely within proofs ⇒ reachable*) because **a bare count would be the list-shaped answer this campaign has now got wrong nine times**; the 2,092-of-11,945 grandfathered set is W-27's shape — **an enumeration you must join to be EXEMPT, not to be COVERED** — and the ratchet makes it shrink as modules are wired. Scoping to check 9's roster was declined because **the gate would not have found the finding that motivated it**; recording without a gate was declined because the auditors sample rather than sweep, so the true count is unknown |
| **D52** (2026-09-25, gap 2129) — **CAMPAIGN CALL, revisable: `Tree.lean` is BUILT AHEAD OF ITS CALLER, and the caller is D27.** It is recorded, not wired and not deleted | §6.4's `remaining` and §5.4's series head reach no answer a caller sees — `lp_TmKernel_Tm_remainingMin` occurs exactly twice in the emitted IR, its prototype and its own body, with no `___boxed` wrapper and no call site, and every reference outside `Tree.lean` is inside a THEOREM in `Boundary.lean` (a witness, not a caller). The shipped remaining-minutes number still comes from the Rust side. **But `remaining` is the FIRST of D27's nine candidate fields**, so this module was built for a caller that D34 puts downstream of R3 — it is early, not dead. Wiring it now would be **deriving a candidate fact in the kernel, which D34 forbids**; deleting 10 definitions and 37 proved theorems that D27 will need would be waste. **It gets a gap of its own with this reason, which is what gap 2129 says was missing — "no gap carries it"** — and it is a declared entry in D51's exemption file, due to leave when D27 lands |
| **D53** (2026-09-25, gap 2362): **THE DIFFERENTIAL ARM COMPARES AGAINST THE FORK AS THE SHIPPED BINARY RUNS IT — kernel-ranked — and never against a configuration the binary cannot build** | the owner's call was *compare the fork as it is, unmodified*: D21/D22/D23's comparand is fork 4748911 and the arm must not normalise away a divergence class. **The question was put to the owner with the facts backwards, and the code settles it the other way.** `with_ranking(cands, kernel_prios)` is not a normalisation of the fork — it **is** the shipped wiring: `planning::build_ranked` (`tm/src/cli/planning.rs:156`) calls `ctx.priorities()` which calls `kernel_capacity::rank` (`tm/src/cli/ctx.rs:1521`) and feeds the result to `planner::plan` at `:167`; the TUI reaches the same call through `tm/src/tui/mod.rs:176`, and every shipped `planner::plan` site is fed those priorities. **So the fork's OWN-§7 day is the artificial one — no shipped path builds it.** It also differs only because **P1 and P41, two ALREADY-REGISTERED divergences**, put a different `p` into step 5, so asserting against it re-counts them as a third. Applied to the facts, the owner's principle ENDORSES the arm as W-32 left it. **The fork's own §7 priority pass is therefore shipped code reached by no shipped path** — gap 2229's shape on the fork side — and R3 deletes it; it is not given a test |
| **D54** (2026-09-25, gap 2362): **P42 STANDS, its row corrected to the measurement; the parity register gains NO withdrawal mechanism** | P42 was issued for gap 2224 asserting *fork quirk*, and W-32 measured the stated reason FALSE — both planners defer the row at step 2 and both run a step 6 (`Planner.PlanReq.deferOne`/`deferWalk`/`deferFold`, composed into `dayRows` since `0d52a4d`). Against the shipped comparand it is **0 of 292 and 0 of 306** over two 272-case runs. **The number is kept anyway**: `parity.txt`'s issuance line is append-only and `parity.py` requires P1..Pmax contiguous, so a `hole P42` line would contradict a line that cannot be deleted — and a withdrawal mechanism is a way to make a disagreement go away, which is exactly what **D46** forbids elsewhere. The row states the measurement and marks the old reason false; nothing is hidden, and a reader who counts 42 finds the 42nd explaining itself. **Holing it and subsuming it into a ranking number were both declined as more mechanism than the finding earns** |
| **D55** (2026-09-25, gap 2510): **an impossible item is owed "everything available" PER ITS OWN GRANT (§7.3)** — when two impossible items contend and §7.3's EDF pass leaves the second `avail 0`, the planner dropping it is CORRECT; `PlanCheck.impossibleKept` is restated to read the grant (*an eligible impossible item WITH availability is assigned*) and `hnoimp` comes OFF all five lifts | W-33 wrote `Diagnostics.impossible` and the check it feeds failed for the first time, at `PlannerWit.theTwoImpossibleRequest`: two HOT items due today, each owing 100,000 minutes, on a 240-minute day; the EDF pass gives the first every minute and the second none, and step 5 gives the first every slot. The spec says it two ways — §7.3 (`tm-spec-v1.md:497`) *"IMPOSSIBLE items are still scheduled with everything available"* and §8.3 (`:575`) *"impossible never dropped"* — and the fork does exactly what the kernel does (its step 5 never consults impossibility; `planner.rs:2160` is the diagnostics pass), so this is shipped behaviour, not a kernel defect. Both items stay NAMED in the `impossible` banner with their shortfalls, so neither vanishes from what the user sees. **Declined:** sharing the day among impossible items (a planner behaviour change, a new divergence from the fork, and arguably worse for both deadlines); leaving `hnoimp` on the lifts indefinitely |
| **D56** (2026-09-25, gap 2572): **`tm edit est=` on a line with a LEADING estimate and no `est:` token REWRITES THE LEADING ESTIMATE IN PLACE, unit kept** (`30b` → `20b`) — one estimate per line, as the pre-switch fork did | driven by W-33's auditor: `tm edit ^x3 est=20b` on `- [ ] 2 30b Big migration … ^x3` appended `est:1200m`, leaving two estimates on one line; the row's estimate cell prefers the leading one (`est_original`, `tm-core/src/emit.rs:577`), so the row showed **30b** while the planner used **1,200 min**, and `tm check` said "no problems" — §5.3's founding bug (*"`est:` and the leading estimate were two syntactic slots for one field"*) in a new form. **This refines D49, it does not reverse it**: the kernel stays the one writer of `tm edit`; D49 settled who writes, and never examined a line that already carries a leading estimate. `the_edit_path_writes_what_the_field_path_reads` is re-proved over the leading slot. **Declined:** keeping the append and registering a parity number (the row and the planner would keep disagreeing on one line); refusing the edit (the commonest estimate edit would fail) |
| **D57** (2026-09-26, gap 2740): **the three §9 behaviours the fork gets wrong are FIXED IN THE KERNEL BEFORE R3, each a registered divergence from fork 4748911 (next free parity number) with a behaviour row** — so the user sees them at the R3 switch | driven by W-34's auditor on the shipped (fork) planner, and ported unchanged by the kernel: (1) **a running break is invisible** — `tm now` says "nothing running" and `tm plan` schedules over it with no Break row; fork `planner::plan` reads no `runtime.break_`, and the kernel decodes it (`RuntimeIn.brk`) and reads it nowhere (one of gap 2734's five unread inputs); (2) **in overtime the header says "94m of 60m" while the current row is the NEXT item**; (3) **a block running across a wall is drawn across it and `tm now` names the wall current**. Spec §9 treats a Break as a RUNNING state (its idle prompt fires only when *"no Block, Break, Routine, or Wall [is] running"*; *"Break overran → next block starts now; tail drops"*), and §8.2 choice 5b reserves the running block, so (1) and (2) contradict the spec. **(3) is the least specified**: the step proposes its reading — §9's Interruption row (*"ad-hoc Wall … Active block paused"*) is the nearest rule — and records it as a campaign call the owner may revise. **The owner chose this over the campaign's recommendation** (fix after R3, keeping R3 a like-for-like swap): the fixes land in the kernel first, so the R3 switch ships them together with the body swap. Keeping the fork's behaviour as quirks was declined |
| **D58** (2026-09-26, gap 2680): **the TUI's overtime what-if gets the extended item's recomputed candidate facts FROM THE HOST** — at R3 the host computes the override-grown `remaining_min`/`planned_min`/`need_min` and sends them, and the kernel's `overtimeDiff` consumes them | fork `PlanOverrides::apply` recomputes the extended candidate's facts, so its step 5 gives the running group more commitment; the kernel's what-if reads the running estimate and never `extra_min`, and its `→ drops:` differs on 6–8 of ~273 generated days a run. Recomputing `planned_min` in the kernel (`Arith.plannedMin`, §8.5's `est × multiplier`) would DERIVE A CANDIDATE FACT, which **D34** places after R3 (D27) — while the host already computes every candidate fact today, so sending the grown ones is the same reader, not a second one. This is the route W-34's repair registered as **P44** (*"at R3 the host must send the override-grown candidate facts"*). Accepting the divergence as a parity number was declined |
| **D59** (2026-09-27, gap 2800): **on a day whose budget is SPENT, dropping an impossible item is CORRECT** — §8.3's "impossible never dropped" is restated as *never dropped while the day's budget can still be spent*, and the five lifts are proved WITHOUT `hnoimp` against that statement | W-35 built D55 and found it cannot take `hnoimp` off: §7.3's grant is a CAPACITY reading (free slots) and the day's BUDGET is not in it, so on an ordinary day with the budget used up (six blocks done) an impossible item still holds availability in its grant while step 5 — rightly — places nothing more. The budget is the user's own limit on the day, so the planner obeying it is not a defect. **Declined:** making day 0's grant net of the remaining budget (as future days already are) — a §7.3 change, a new divergence from fork 4748911, and a shift in every item's priority bins, for a case the restated law already answers |
| **D60** (2026-09-27, gap 2801): **priority-0 ties among IMPOSSIBLE items are broken by DUE DATE, not line order** — so step 5 serves them in the order §7.3's pass computed their grants; a planner change and a registered divergence from fork 4748911 (next free parity number) with a behaviour row | every impossible item is HOT (`p = 0`), and §7.4's key `(p, root line, own line)` therefore orders them by their position in the file, while the EDF pass that computes the grants orders by due date. `PlannerWit.theReversedTwoImpossibleRequest` is the witness: with the earlier-due item lower in the file, its grant holds the day's minutes and step 5 hands every slot to the other item, so the item the grant favoured is dropped — the fork does the same. **Declined:** keeping line order and accepting the drop |
| **D61** (2026-09-27, gaps 2805, 2932): **a calendar wall that starts while a block is running STOPS THE TIMER** — the pause is logged at the wall's start, as §9's Interruption row logs one, so `tm now`'s worked minutes, `tm done`'s `actual_min` and the drawn history all exclude the meeting; a registered divergence with a behaviour row | D57 (3) made a wall on `now` pause the running block, but only as a STATE of the day at `now`: the log recorded no pause, so once the meeting ended a replan drew the stretch across it again, and the host's worked minutes counted the meeting as work (driven: `56m of 30m` over a 17:10–17:50 call). The owner accepted the costs named when asked: the kernel's log now carries an entry the user did not type, and a user who skipped the meeting and kept working is undercounted until they correct it. **Declined:** keeping the pause a view of `now` only |
| **D62** (2026-09-27, gaps 2926, 2928): **D56's one-estimate rule reaches `tm extend`, `tm stop` and `tm done --partial`**, and every writer puts the value **as typed** (`2h` + `est=90m` → `90m`) | driven by W-35's auditor: those three verbs still write an `est:` token beside a leading estimate (`… 30m … est:1b ^a1`), the two-estimates-on-one-line defect D56 removed from `tm edit` — and a later `est=` edit then leaves the stale leading `30m`. "Unit kept" in D56's row was ambiguous; the implementation wrote the value as typed, which is what fork `ItemLine::set_leading_est` does, and the owner confirmed that reading. `tm/tests/cli_day.rs`'s `extend_adds_a_block_to_the_estimate` pins the fork's behaviour and changes WITH a behaviour row — a deliberate behaviour change, never a silent re-bless. **Declined:** converting to the line's unit (lossy and awkward: `2h` + 90 minutes); leaving the three verbs as the fork had them |
| **D63** (2026-09-28, gaps 3001, 3003): **among priority-0 items, IMPOSSIBLE items come first — by due date, as D60 orders them — and the other HOT items follow in file order**; §8.3's monotone-rank check reads the planner's own order, so a pair D60 orders by date is not a rank violation | D60 ordered only impossible ties by date, and leaving the other `p = 0` items in line order is not a total order (two impossible items and one other form a cycle), so step 5 needed one. Of the orders that keep D60, this is the narrowest, and it is the one under which a `p = 0` item §7.3 served later never takes a slot an impossible item's grant was given today. **Cost accepted:** a HOT, not-impossible item written above an impossible one is served after it (P51's census counts every day this moves). **Declined:** every `p = 0` item by due date (it changes every HOT tie, a wider divergence from fork 4748911 than D60 asked for); impossible items last (the other HOT items could take the very slots D60 set out to protect) |
| **D64** (2026-09-28, gaps 3133, 3138): **a frozen fork comparand may be re-blessed under a STANDING RULE** — a line may be recomputed when (a) a REGISTERED parity number changes the fork's day on it, or (b) it describes a world the shipped binary cannot build; the shipped fork's day is kept beside it by value, and every changed line is named in the README block of the step that changes it. W-36 land's D60 rewrite of the planner-classes comparand (9 of 38 `day` lines, P51) is ratified under (a); the ten interrupted classes are re-drawn under (b), with the interrupt LOGGED as the binary logs it | once R3 deletes the fork's planner the frozen file IS the fork, so a divergence the owner chose has to be expressible in it, and a comparand line describing a day nothing ships compares nothing (the ten interrupted classes set the interrupt in `state.json` only, which D42's rebuild-from-log erases). §7.3's "rewriting a committed differential fixture is a decision and never a repair" still governs everything outside (a) and (b), and a re-bless that is neither comes back to the owner. **Declined:** ratifying case by case (this rule is the shape every future case takes); checking D60 as a reordering of an unrewritten day (on the reversed day a DIFFERENT item holds the slots, which no reordering can express) |
| **D65** (2026-09-28, gaps 3044, 3141, 3142): **a meeting that paused the running block is drawn as the WALL ALONE, and the pause is SAID when it is logged** — the verb whose housekeeping logs D61's pause prints one line naming the block and the wall (`paused ^t4 for Standup 12:50–13:50`) and writes the day file's journal line a typed `tm pause` writes; `tm plan`'s `paused` lost row over the meeting goes, so the plan and `tm review day` agree. A registered divergence from fork 4748911 (next free parity number) with a behaviour row | D61's pause is written by housekeeping, not typed, and the owner accepted that a skipped meeting is undercounted until the user corrects it: a correction nobody is told they need is the silent-wrong-answer class, so the notice is what makes it findable (and `tm pause` resuming inside a meeting stays the correction). One span drawn as lost by `tm plan` and counted 0 by `tm review day` is two readings of one fact (§5.3). **Declined:** fixing the drawing with no notice; keeping the lost row and aligning only the review |
| **D66** (2026-09-28) — **CAMPAIGN CALLS, revisable by the owner at any time:** (gap 3000) **`PlanCheck.impossibleKept`'s eligibility is the spec's own step-5 filter** — `tm-spec-v1.md` §8.2 step 5's "pick the first eligible candidate": state, dependencies satisfied, not waiting, location, `ci` within the slot's energy, the cap not exhausted, and contiguous free slots for an item that is not splittable (§5.1 says a waiting item "never take[s] slots") — evaluated against the day's slots BEFORE step 5 assigns anything, so a drop caused by lower-ranked work still fails the check, and `hnoimp` comes off the five lifts as D59 asked; (gap 3047) on a line carrying a tab `tm stop` and `tm done --partial` END THE BLOCK and warn that the estimate was not written, while `tm extend`, whose whole job is the estimate, keeps refusing; (gap 3048) `tm pause` inside a meeting keeps resuming — it is the correction for a skipped meeting — and its message names the meeting; (gaps 3002, 3005) "owed today" and P52's re-ranked what-if stand | gap 3000's two routes were exempting `[?]` alone or reading step 5's whole filter, and the first is not enough: an atomic item that fits no contiguous slot fails the check as well (the atomic witness). The spec already lists the filters, so this is its reading, not a restatement, and D59's instruction was that the lifts carry no `hnoimp`. A stop that fails because a secondary write cannot be made leaves the timer running, which is worse than the estimate going unwritten; an extend that cannot write is nothing |
| **D67** (2026-09-29, gap 3160): **step 5 stays greedy, and a dropped owed impossible item is SAID** — when the walk hands the only unbroken run an atomic impossible item fits to an item ranked before it, the item is not placed, stays in the `impossible` banner with its shortfall, and the day NAMES why it found no place (no run left); §8.3's "impossible never dropped" is read as **an owed impossible item is placed or named with its reason**, and `PlanCheck.impossibleKept` checks that statement | `PlannerWit.step_five_drops_an_owed_impossible_item_its_filter_admitted_before_the_walk` is shipped behaviour — the fork's step 5 is the same greedy walk and never reads a grant — made visible only by D66's faithful filter. Saying it keeps the planner the fork's and keeps the law about what the USER sees rather than about the algorithm. **Declined:** a look-ahead that reserves an atomic impossible item's run (a new planner behaviour and a divergence from fork 4748911, hard to state with several such items); restating the law over the walk's own state ("never dropped while step 5 could still place it"), which comes close to restating the algorithm and tells the user nothing |
| **D68** (2026-09-29, gap 3344): **a typed `tm pause` is NOT lost time** — `tm plan` draws it as a pause (`paused 10m`), not as `lost`, and `tm review day` keeps counting as lost only what an interruption's `resume` logs; a registered divergence from fork 4748911 (its `past_segments` draws a Pause as a Lost row) with a behaviour row | the spec's "lost" is interruption time: §9's Interruption row logs `lost=` on resume, and the status line and day review report that figure. One span read two ways by two surfaces is §5.3; the reading that matches the spec is the review's. **Declined:** counting typed pauses as lost (it changes every review's number against the spec); keeping the two readings |
| **D69** (2026-09-29) — **CAMPAIGN CALLS, revisable by the owner at any time:** (gap 3244) D65's "the wall alone" reaches `tm review week`'s heat grid, so a meeting's pause is styled as the wall there too, under P56's behaviour row; (gap 3283) `tm start` during an open interruption records the block as paused, which is what D42's rebuild from the log derives — the cache follows the log, never the reverse; (gap 3323) a routine's or optional's line with no `ci` reads the spec's file-kind default — `tm-spec-v1.md` §4.3: `routines.md` "`ci` defaults to 1", `optional.md` `ci:0` — in the kernel's plan view as it already does on the wire, so the planner and its checks read one `ci`; (gap 3345) the kernel's loader refuses, by name, a leading estimate past the host's width (R10), and `tm check` names that line, as D32 does for a collision | each follows a rule already settled: D65's "one span, one reading" on a third surface; D42's "the log is the truth and `.tm/state.json` its cache"; the spec's own default, where the kernel's plan view read 3 while the wire read 1 or 0 — two readers of one fact (§5.3) in which the wire's reading was the spec's; R10 and D32 for a bound the host already enforces |
| **D70** (2026-09-30, gap 3532): **D64(a) is widened by an INTRODUCTION clause, ratified** — a frozen comparand line may GAIN (never change) the answer for a registered parity number whose comparand did not exist when the line was frozen; the shipped fork day stays by value and the line is named, as for any D64 re-bless. The six `p45` break lines W-38 track H added under it stand | a registered number whose rule the comparand had not computed when a line was frozen could otherwise license nothing on that line, so every new departure would reach no existing frozen day; adds-only keeps the fork's day untouched, and the gate enforces it on eight plants. **Declined:** moving the six answers off the lines and checking P45 from its rule alone |
| **D71** (2026-09-30, gap 3430): **`tm pause` while an interruption is open is REFUSED BY NAME** — the timer is already stopped by the interruption, and the message points to `tm resume`, as `tm interrupt` already refuses a second interruption | a toggle inside an interruption wrote a cached `active.paused` that D42's rebuild from the log contradicts, so deleting `.tm/state.json` changed the answer; refusing leaves the log and the cache nothing to disagree about. **Declined:** logging the mark and keeping the block paused until `tm resume` (a keystroke that is recorded and does nothing) |
| **D72** (2026-09-30, gap 3533): **before R3 the planner keeps BOTH kinds of fork comparison** — a seeded batch of generated days is frozen with the shipped fork's answers by value and compared in plain `cargo test --workspace`, and `tm-oracle` gains a `plan` mode that runs fork 4748911's planner out of the tree, so fresh proptest draws keep meeting the fork under `TM_ORACLE`, inert without it — D23's shape, for the planner | `planner_invariants`' hash arm is today the only differential that explores fresh draws (≈283 a run), and R3 deletes the planner it runs; a fixed list alone finds nothing in a world no frozen line holds, which is D46's reason for fresh draws. **Declined:** the frozen batch alone (the comparison stops exploring); keeping `planner.rs` in the test tree (contradicts D50, R3 deletes it) |
| **D73** (2026-09-30, gap 3523) — **CAMPAIGN CALL, revisable by the owner at any time:** D67's naming covers every owed impossible item the day does not place, including one step 5's filter admits NOWHERE (a location mismatch, say) — it is named `noSlotAdmits` (`not placed: no slot admits it`) | W-38's critic counted 42 owed impossible items on 36 of the frozen days that had neither a row nor a reason, because D67 as first built named only drops the walk caused; D67's law is "placed or named with its reason", and an item no slot admits is not placed. `PlanCheck.every_listed_impossible_item_is_placed_or_named` holds with no hypothesis |
| **D74** (2026-09-30, gap 3546): **§7.5's batches join only items CONSECUTIVE in the served order** — a bucket closes where the next ranked candidate cannot join it (another location, an atomic item, the running block), so the split never serves a lower-ranked sibling ahead of a higher-ranked one; §8.3's monotone rank then holds of the candidate order, and the check reads it there. A planner change and a registered divergence from fork 4748911 (next free parity number) with a behaviour row | `PlannerWit.theOneBlockSplitRequest`: §7.4 ranks `^t3 ^t1 ^t2`, the fork's `build_groups` keys `{^t3, ^t2}` by its least member and serves it first, and `^t1` — ranked ahead of `^t2`, same `p`, same `ci`, fitting every slot — gets nothing, so `PlanCheck.monotoneInRank` and `batchDoesNotReachPast` fail on the planner's own output. **Cost accepted:** an occasional batch the fork would have formed is not formed. **Declined:** keeping the fork's split and restating the rank check over the served groups (the law would describe the algorithm, D67's declined shape) |
| **D75** (2026-09-30, gap 3715): **`tm done` (and every verb that logs worked minutes) reads the block's start INSTANT from the log's own `start` line**, so a block finished after local midnight logs its real worked minutes, not `actual_min: 0`; a registered divergence from fork 4748911 (which puts the stored `HH:MM` start on today's date) with a behaviour row | a wrong fact written into the log is the silent-wrong-answer class, and this one feeds the duration fit a zero for every block done across midnight. The log already holds the instant; `.tm/state.json`'s `HH:MM` is its cache (D42). **Declined:** keeping the fork's zero as a quirk |
| **D76** (2026-09-30, gap 3725): **`tm wake` while a block is still running is REFUSED BY NAME** — it names the block and its start and says to stop or finish it first; nothing is written | `tm wake` cleared `active` in `.tm/state.json` while the log held nothing that ended the block, so the next verb's reconcile (D42) resurrected it — a verb that did not do what it said. Ending the block at the wake would write a duration nobody stated (the night counted as work); refusing invents nothing and leaves the user to say how the block ended, as D71 does for a pause inside an interruption. **Declined:** ending the block at the wake; leaving it running across the wake |
| **D77** (2026-09-30) — **CAMPAIGN CALLS, revisable by the owner at any time:** (gap 3620) a pause crossing local midnight is cut by EACH calendar day's own walls, so a meeting that spans midnight while a block runs is drawn as the wall on both days of the week grid (P63 restated); (gap 3714) the restated rank and HOT laws are stated over what a user can observe — the candidate order and step 5's filter before the walk — never over step 5's own state (D67's declined shape), and L25 covers a replan after a logged verb (a day record that EXTENDS the earlier one by lines after `now`), not only an unchanged record; (gaps 3480, 3666) a RUNNING break resets the cut's break counter exactly as the same break will once it is logged, so the day does not change at the instant a break ends (P45's reading made one); (gap 3580) the step-5-to-7 witness families stay on the stored-arrival afternoon, since the logged-arrival fallback is run by the 19 re-derived day-level witnesses and both Rust suites | each is §5.3's one-span-one-reading or D67's rule that a law describes what the user sees: D65/D69's "the wall alone" on the second day of a midnight meeting; laws restated over the walk's internals would discharge a goal by describing the algorithm; a break counter that reads a running break one way and the same break logged another moves the plan with no time passing; and re-deriving the afternoon families dissolves their subjects (measured) without adding coverage the day-level witnesses lack |
| **D78** (2026-10-01, gaps 2874 input 1, 3952): **a running block whose logged start is AFTER `now` is planned FROM `now`, with no minutes worked — as fork 4748911 plans it** — not refused | since W-40's repair the planner's starts come from the LOG (D75's instant), so a start after `now` arises only when the clock is behind the log: a `--now` in the past, a clock that jumped, or two machines syncing one plan directory with clocks a few seconds apart. Refusing would stop `tm plan`, `tm now` and the TUI on exactly that skew; the fork's reading is harmless there. The clamp W-40's repair withdrew was a silent wrong answer only because it composed with the cache's `HH:MM` placed on today's date, a reading D75 and the repair removed. **Declined:** refusing by name |
| **D79** (2026-10-01, gap 3823): **`tm stop` and `tm done` (with `--partial`) take an END TIME — `--at HH:MM` — and log that instant**, so a block forgotten overnight ends when it ended and the night is not counted as worked; D76's refusal of `tm wake` names it | D76 refused `tm wake` over a running block and said to stop or finish it first, but both verbs ended the block NOW, and since D75 they count from the log's start, so the night counted as worked (driven: `stopped ^t4 after 483m`). An end the user states is a fact the log can hold (D75's clock), not a duration invented. **Declined:** naming the workaround (`tm undo` the start, or edit the log by hand) without a flag |
| **D80** (2026-10-01, gaps 3780, 3785, 1984): **the planner request REFUSES BY NAME the two requests fork 4748911 can never produce** — a day whose evening runs past the calendar's last second (the kernel's `Planner.clampSec` would otherwise squeeze the rows onto it), and a candidate whose `ci` on the wire disagrees with the `ci` the kernel reads in the plan file (`PlanCheck.candsAgree`); with both refused, `plan_places_no_demanding_block_after_wind_down` is to be proved AS WRITTEN over the requests the decoder accepts | the goal is proved wherever the window ends inside the night and wherever the wire agrees; its only falsifying requests are these two, and W-39's rule forbids discharging it by a refutation that stands on the kernel's own clamp. A disagreeing `ci` has not been seen on any of 341 measured days; refusing it makes a future disagreement LOUD and findable (D32's shape) instead of a plan built on the host's number. **Declined:** leaving the goal open with its two exceptions recorded |
| **D81** (2026-10-01) — **CAMPAIGN CALLS, revisable by the owner at any time:** (gap 3820) a break running across local midnight starts at the LATEST instant at or before `now` whose clock is the stored `HH:MM` — D75's rule where the log holds no instant (a running break has no log line) — read at every site that places it, with a parity number; (gap 3824) `tm wake` also refuses BY NAME over an open interruption or a running break, D76's rule for every running state a wake would clear; (gap 3860) a TUI left open past midnight plans the day `tm plan` would plan at that instant (the kernel's reading, registered); (gap 3861) before the day's first `tm arrive` the day is planned as `tm plan` plans it today — the home curve, location `any` — and day 0's capacity follows that one reading (a registered change to the fork's lounge assumption there); (gap 3902) the kernel's bounds on a running block's estimate and a running break's length widen to the host's width, `Look.maxPlanMinutes`, as the fork plans both; (gap 3903) `tm break --where <unknown place>` is refused by name from one host table of places (D20's shape); (gap 3743) a small queue item may still ride in a HOT item's §7.5 batch; (gaps 3827, 3959) the week grid's rows stay wake-to-wake as the spec's day bar draws them (§12), with the per-day cut kept; (gap 3790) an `arrive` stamped after `now` stays the day's arrival, as the fork reads it; (gap 3953) check 12's exemption file becomes strictly shrink-only, as D51 says; (gap 3958) P67 gets its own flag and transformation, and the six lines carry it under D70; (gaps 3866, 3963) the TUI's in-memory worlds are frozen as class lines — the TUI is the shipped binary | each follows a settled rule: D75 and D76 one field on; §5.3's one reading (the TUI agreeing with the CLI at one instant, and day 0's capacity agreeing with the planner); R3 as a swap that keeps `tm plan`'s visible day; D20's argument validation; §7.5 batching takes no slot from the HOT item, it fills minutes of a block a higher-ranked item already holds; the spec's own wake-to-wake rows; D51's letter; and attributing every comparand change to the number that caused it |
| Behaviour changes are recorded next to the rule they replace, with a theorem separating them — never taken silently | *"this is a bug" vs "this is an undocumented deliberate choice" is a judgment reading cannot settle* |

---

## 5. Lessons — the rule, and the failure it prevents

A rule with its reason survives. A rule without one gets argued with. These are
in the order they cost time.

### 5.1 `Bool` + `Subtype`. Never a dependent proof field inside a record.

**Prevents:** a proof field whose type mentions a field being updated makes
`{e with live := t}` stop elaborating. The `firstprinciples` spike used
`archive_elsewhere : ∀ r, archive = some r → r ≠ live` and the next module
**failed to compile in eight places**. The cost of the fix is goal sharpness and
nothing else.

**The payoff is measured, but not by the widening the plan forecast.**
`PLAN-lean-kernel.md` §5 lists "scaling `Core` from five fields to the real
`Item`'s twenty-two" as remaining stage-1 work, and it **did not happen and will
not**: `Core` still has five fields (`live`, `archive`, `status`, `line`,
`parent` — `sed -n '/^structure Core/,/^$/p' State.lean`), because §5.3's fix
made the item fields *views over the token vector* instead of record fields. What
was measured is the theorem getting **stronger**: `wf_ignores_the_item_fields`
was a thirteen-binder statement listing the fields it was safe to set, and is now
two binders covering `line` and `parent` — *"every field there is, because there
is only one left to set"* — still `rfl`. `Negative.lean` CHEAT 1 and CHEAT 2 hold
the line.

### 5.2 A theorem can compile and mean nothing.

**Prevents:** `every_transform_preserves_the_invariant` took three arguments —
`f`, `p`, `_h` — and used none of them. It was
`no_two_lines_of_one_id_in_one_file` wearing a name that promised a closure
property it did not state. It was **withdrawn, not patched**, and `Cmd.lean`'s
header still ends with the sentence: *"An earlier version of this module claimed
the first bullet for all three, in a theorem whose command argument was unused.
It is withdrawn."*

Non-vacuity is a *separate* check from correctness, and the package carries
purpose-built witnesses for it: `demo_wf` / `demo_line_bytes`,
`the_round_trip_is_not_vacuous`, and on the Rust side
`the_harness_can_see_a_rewrite`. The cautionary case is `shapeWfFor .calendar` —
a clause **no line the boundary could construct could satisfy**, invisible for a
whole stage, found by running the corpus and not by reading.

### 5.3 Two definitions of one concept is the bug.

**Prevents the defect class the rebuild is named after.** Two instances, same
shape:

- Rust: `est:` and the leading estimate were two syntactic slots for one field,
  so `tm edit est=` reported success and changed nothing.
- Lean, stage 2: §4.1's value types lived in `Line.lean`'s `Field` namespace and
  `State.lean` carried its **own** re-encoded copies. A parsed `at:` never
  reached `Core.shape`, so `shapeWfFor DocKind.calendar` was **unsatisfiable, not
  merely unsatisfied** — every calendar line in the fixture corpus was refused
  with `itemCheck: fileKindShape`, §4.3's own `at:2026-09-07T12:50/13:50`
  included. A correct grammar and a correct invariant together refused the spec's
  own examples.

**The fix was deletion, not a bridge.** The copies went; the fields became views
over the token vector, and `the_fields_are_the_line` says two `Core`s with the
same line have the same fields — there is nothing left for a second reader to
disagree with. The corpus went 26/37 → 33/37.

Two symptoms to recognise a stored slot by: `demote` appended its `demoted:`
stamp to a slot beside the line while `renderCore` prints *the line*, so the
stamp reached no file at all (and §6.3's month review cuts on "≥ 2 stamps"); and
a lone `[-]` was rejected outright.

**CHECKED BY `kernel/twins.py`, check 11, since W-30 track A.** This rule was
enforced by hand sweeps until then, and the last hand sweep reported "seventeen
groups, all seventeen accounted for" while five character-identical `def` pairs
were in none of them. The gate keys every `def` on its signature and its body
WITH its string literals and demands a property for each group that survives:
the definition is nullary (a named value, not a rule), or the compiler emits
different code for the two **and the export REACHES one of them** (which is what
the `@[csimp]` fast/slow shells are FOR — their sources are identical and their
compiled callees are not). The second half of that second property was written
here and never checked until the W-30 repair, and two of the five groups it
exempted had no caller at all to deoptimise (gap 2126); both twins were deleted
rather than exempted. Anything else is named. It found one live duplicate on its first run and the blind spots
it keeps are in its own header and in README gaps 2093-2094.

**AND SINCE W-33 TRACK A IT HAS A SECOND KEY (README gap 2418), because the exact key
cannot see a GENERALISATION.** A definition that is another's body with a literal turned
into a parameter was never a twin under it, and W-32's repair found four such in one module
(`PlannerWit.pCand`, `pCandDue`, `pCandSmall`, `bCand`) with check 11 green — a LIST where
the rule is a CLASS, inside the gate named after this section. The second key puts two
`def`s in one group when their result types and bodies are identical once every parameter
and every literal is a hole (a constructor over holes is a literal, and constructors are
what the library and the pinned `Init/Prelude.lean` DECLARE — `leanfiles.constructors`,
the one scanner check 8 also reads). Every group that is not an exact-key group climbs a
ladder: E3 a fixture value; ALPHA, two names for one body once parameters are renamed,
which FAILS unless E2 answers — its first catch was `closeTo`/`targetContaining`; E5 a
wrapper, one head over holes; E4 wire-named, the members differing only in a string, a
character or a nullary constructor. What no rung answers must carry a SENTENCE in
`kernel/twins-exempt.txt`: `ONE CONCEPT`, naming the carrier and an EXIT, or `NOT ONE
CONCEPT`, saying why — dated either way, W-27's shape. A group with no sentence fails; a
sentence whose group dissolved fails as STALE; a ONE CONCEPT verdict at HEAD cannot be
rewritten NOT ONE CONCEPT. Measured at `8702132`: 60 generalisation groups, 16 of them
adjudged, 9 of those owed. What the second key cannot see is in `twins.py`'s header: a
generalisation across a delta step or a structure eta (gap 2417's family is two groups
there and one definition), a closed term that is not a literal, a renamed body-local binder.

**Two live exceptions, both recorded rather than hidden.** `parent` is still a
stored slot and is always `none` (gap 22). And two readers of `est:`
still coexist on the command path (gap 4), which the README labels *"a
live S2"* — by its own accounting the kernel contains one instance of the class
it exists to remove. Do not inherit either silently.

*Status at `bf7cc63`: one exception left.* Gap 4 is **closed** (`7af7f1a`):
`Cmd.setEstE` writes through the field setter, and
`the_command_path_writes_what_the_field_path_reads` — generalised by the edit
widening to `the_edit_path_writes_what_the_field_path_reads`, over every wired
key — is the theorem. `parent` (gap 22) is the one that stands. *Status at stage 4
final step 3: none stands.* `parent` is a view since the owner's D6 —
`Core.parent c := Field.parentRef c.line`, and `the_fields_are_the_line` gains its
conjunct — and gap 22 is closed. The one reader is also the fast one: a `@[csimp]`
twin skips the classification for a line with no `@` word
(`parentRef_eq_parentRefFast`). A new instance
of the class, recorded rather than hidden, is between the kernel and the host:
`tm-core`'s fork-point parser is comment-blind while the kernel reads a comment
as prose (gap 45), so two readers of one file disagree about a commented item.

### 5.4 The boundary is where the holes are.

**Prevents under-budgeting.** Stage 1's core was right and its edge was not: an
audit took the package from 799 lines to 2,981, and the repair was *almost
entirely boundary code and its proofs*. Carry the cost signal, not the numbers —
the ten modules are 20,902 lines at `bf7cc63`, 23,724 with the root module,
`Check.lean`, `Negative.lean` and `Goals.lean` (§10.1). (At `c8f3a38`: nine
modules, 14,674 and 17,129.) Stage 3 bore the lesson out again: most of its
growth is `Json.lean` (2,641 lines) and `Boundary.lean` (1,939 → 3,909), the
edge.

The same lesson at the theorem level: **is the theorem about the code the FFI
actually runs?** A `[-]` line failed to survive a read with no commands at all
while the package already had a line round-trip theorem — because
`serialize_parse` is stated about the glyph *the parser returned*, and the
pipeline throws that glyph away and asks `glyphAt` for a new one. The theorems
that catch it are stated about the entity the loader builds. Later, `run` was
refactored to call `loadPlan` specifically so the theorem is about the code the
FFI runs and not a copy of it.

### 5.5 Derive, but not always. Tabulate where a different answer is merely different.

**Prevents both failure modes.** Derive where a wrong answer is *wrong*:
§6.3's three close rows are one operation at three grains, and row 3 is the
**fixed point** — `coarsen_month : coarsen month = month := rfl`, not a special
case. §5.3's default `on_miss` derives from one sentence with all four rows `rfl`.
The 53-week rule derives.

Tabulate where the data is arbitrary, and keep the table compile-checked:
§7.1's ladder is **four** edges — the implicit `hotEdge = 1` (`u ≥ 1` is HOT, off
the configurable list) followed by §16's `defaultBins = [1/2, 1/4, 1/10]`. The
first three halve; the fourth breaks the pattern at `1/10` instead of `1/8`. So
the generator you would write from first principles, `log2Bins = [1/2, 1/4, 1/8]`,
gives a different bin at `u = 11/100`, and
`log2_ladder_disagrees_at_eleven_percent : binOf log2Bins 11 100 ≠ binOf
defaultBins 11 100 := by decide` is the theorem saying so. Likewise
`Cal.cumBefore`'s thirteen-entry month table and §4.1's field table: humans type
those, so they are data, and everything derived from them is `decide`d
exhaustively (731 days, 416 month/day pairs).

The one datum in the calendar that is a fact about the world rather than
arithmetic is the **phase** of the seven-day cycle. It enters through
`weekdayOf`'s definition and is cross-checked at 1970-01-01, 2000-01-01 and
2026-09-07.

### 5.6 The loader never picks between two readings.

**The sharpest lesson in the repository.** An inverse can fail by having **no**
value, and it can fail by having **two**.

`demote` renders `[-]` at both sites, so for the two-line form *both*
orientations of the pair are entities that render exactly those two lines.
`pairedEntity` tried one order, then the other, and took the first that worked —
so which line was the tombstone was decided by **the order the host listed its
documents in**. Reproduced through the FFI: the same two files and the same
`drop`, documents swapped, marked the *other* file. `Boundary.lean`'s header
promised the loader returns an `LErr` and *"never picks a nearby state"*, which
was true of the no-value case and said nothing about the two-value case, and
`paired_placement_renders_back` had been honest about it — its conclusion was a
*disjunction* over the two orientations — and nobody read it that way.

**The fix is the pattern to copy: make the choice part of what a plan is, not
something inferred.** Read the header now: it states the promise as **two**
clauses, one per failure mode, *"because a weaker version of it was false here"*.
`Doc` carries `Option Region`; `horizonPrecedes` is the order and
`horizonPrecedes_asymm` is why an inversion has exactly one answer;
`demotionsOriented` joined `planWf`; `orientPair_comm` and
`pairedEntity_order_independent` say the loader is a function of the pair and not
of its order; and a pair the documents genuinely do not order is
`LErr.ambiguousDemotion`, **by name**.

Landed since, at `8eea3d6`: `orientPair` is **lexicographic** — the `[-]` line is
the tombstone, and horizon order is consulted only when both lines are `[-]`
(`sed -n '/^def orientPair/,/^$/p' Boundary.lean`). The box decides first,
because §6.3's sanctioned pre-close pair is `[-]`/`[ ]`.

Same discipline, on dead code: seven definitions were **deleted** rather than
wired in, because *"wiring a toy calendar into the command path would be a worse
lie than the dead code was"* (`Cmd.lean`, the `resolveHorizon` note). Note that
sentence's premise has since moved — `Cal.lean` landed and `Grain.index` is real
— but its conclusion has not: horizon-name resolution still stays with the host
(gap 10, §8.1).

### 5.7 Every diagnostic is named, and rejection is real.

**Prevents silent reclassification.** A line that *looked* like an item and did
not parse used to be quietly kept as prose. Only `PErr.notAnItem` counts as prose
now; `scanLines` runs before anything is built. A refusal you can name is a
finding; a refusal you cannot is data loss.

### 5.8 Both directions of a check get a theorem.

*A check nothing can fail is decoration. A check a legitimate command fails is a
trapdoor.* It bites: `mapAt_rejects_unoriented`,
`demote_into_a_horizon_that_does_not_follow_is_rejected`, `self_parent_is_rejected`,
`self_dep_is_rejected`. It does not over-bite: `mapAt_ok_of_inRange`,
`cmdMove_succeeds`, `applyCmd_move_succeeds`. Any new command in stages 4–6 owes
one of each.

### 5.9 Does the theorem quantify over what reaches the disk?

**Prevents:** `Site.doc` is a list *index*. Two documents at different indices
could carry one `path`, so a `demote` put two `^m1` lines into one file **with
every stated theorem still true**. Path injectivity joined `planWf` and the claim
was restated: `no_two_lines_of_one_id_in_one_file` →
`no_two_lines_of_one_id_in_one_path`. Ask it of every new invariant: is the thing
I quantified over the thing the user has?

### 5.10 A Lean panic does not propagate — and `decide` has a budget.

A panic returns `Inhabited.default` with **exit code 0**. That is why
`totality.py` exists, why `.toOption` is banned alongside it (it is how the FFI
spike silently turned `est: -3` into `est: null`, reproducing tm's own
estimate-loss bug inside the boundary code of a verified kernel), and why stage 3
owed the host a fault probe — landed at `dd89bc6` as a constructed probe
(`TM_KERNEL_FAULT_PROBE`) whose tests assert the host's reaction:
`the_panic_probe_faults_loudly_and_writes_nothing`.

`decide` is the workhorse and it runs out. `set_option maxRecDepth` is live in
`Cal.lean` (20000 file-scoped, with `maxHeartbeats 1000000`), `Line.lean` (20000
from its line 5904 to the end of the file), `Boundary.lean` (40000, three scoped
uses), `State.lean` (8000, four scoped uses), `Json.lean` (4000 file-scoped) and
`Negative.lean` (10000). The
`Negative.lean` one carries its reason and it is a review point in itself:
*"Only so the failures below are the type errors they claim to be, and not an
elaborator budget running out first."* A negative test that fails for the wrong
reason still "passes".

Related: `digitsOf` is structural with `n` as its own fuel **deliberately**. A
well-founded definition (`n / 10 < n`) is also total but does not reduce in the
kernel, so `decide` could not evaluate anything that renders a number — and every
theorem pinning down what the kernel *writes* is exactly such a statement. Copy
that trick when you need a reducing recursion. `Json.lean`'s `jparse` copies it
one level up: fuel derived from the input's length (`2 * length + 2`), so small
witnesses reduce, and `jparse_never_runs_out` proves the fuel never refuses a
real input.

### 5.10a `decide`'s budget is heartbeats, and heartbeats are not memory.

*The rule.* Treat the memory a `decide` or `rfl` evaluation can take as
**unbounded**. Byte-level `decide` witnesses over a parser or renderer run stay
**small**, spelled as `List Char` literals; a realistic-size input is an
**instance of the round-trip theorem, not an evaluation** (decide `jemit v =
bytes`, then `jparse bytes = .ok v` is `jparse_jemit`); never reach for
`decide +kernel` on a large computation — it removes the one budget there is;
and on any machine without swap, run `lake`, `lean`, `cargo` and `check.sh`
under a memory cap, so that a blowup kills the command and not the machine. On
Linux:

```bash
systemd-run --user --scope -p MemoryMax=40G -p MemorySwapMax=0 --quiet <cmd>
```

Before committing a new `decide`/`rfl` witness over a computation, probe it in a
scratch copy under a tighter cap (8 GB and `timeout 120` is what stage 3 used).
A command killed at the cap (exit 137/143) is a **finding about that proof**:
shrink the input or derive the fact from a proved theorem; never retry uncapped,
and never answer a heartbeat timeout by raising `maxHeartbeats` — the timeout
was the same bomb, with a budget.

*The failure it prevents.* During stage 3's J-route (2026-09-12) a decided
witness running the kernel's JSON parser over an ~85-character request string
consumed **all 123 GB** of the build machine, which has no swap, and the OOM
killer ended the agent session and the owner's terminal — **twice**. Measured
afterwards under caps (README, "The memory-bomb finding"): `{"a":1 "b":2}` passed
an 8 GB cap in 15 s without any timeout; `{"a" 1}` did stop, at the
200000-heartbeat `whnf` limit, at ~2 GB; and the same parser over a 92-byte
request spelled as a `List Char` literal decides by `rfl` in ~0.5 s at ~520 MB —
the cost was the string literal's decoding re-forced inside the parser run.
Precisely what the budget is: `maxHeartbeats` counts allocations, not bytes, and
the elaborator's `whnf` is where the measured timeout came from; v4.33.1 does
pass `maxHeartbeats` to kernel checking (`addDeclCore` in the toolchain's
`Lean/Environment.lean`), so do not read this lesson as "the kernel has no
limit" — read it as "no limit is in bytes, and none stopped the measured runs".
The rule does not depend on which layer ran out.

### 5.11 Quote one measurement per number, from the committed harness.

**Prevents:** the plan once cited 164 violating depth-2 sequences from a spike's
141-command alphabet while the harness that ships measures 426 of 39,601 on a
199-command alphabet. Nine sites were reconciled in one commit, because *"two
numbers for one measurement is how a decision document loses trust."* If you
quote 426, quote the alphabet with it.

**Corollary, from watching it rot three times: cite theorem names and function
names, not line numbers, and paraphrase a compiler transcript rather than pasting
one.** A `Negative.lean` error transcript was refreshed against a real run and
was stale again within a stage; §3.1's and §5.6's quotations were both re-checked
against the source at `c8f3a38` and both had drifted — one in its metavariable
number, one in its tense. Where this document quotes a docstring it now says
which file the sentence is in, so the next reader can diff it in one command.

### 5.12 Record what you did not do, by name, and what it costs.

Five audits have run on this package. Between them they caught a vacuous
theorem, four boundary holes, a silent orientation choice, a missing field
wiring, and a test that could not fail. **Every one was found because the
previous agent wrote its gaps down.** The register to imitate is the README's own
gap 16: *"a checker that no input can fail is a checker whose bite is a proof and
not a test, and that is worth writing down."*

### 5.13 Each stage ends with 30 minutes of driving the shipped binary.

Eleven of 39 catalogued defects came from that and from nothing else, and all
four integration bugs did. No kernel proof reaches them. Since `835d960` there is
a binary on this branch again, and stage 3's own drives earned their keep: the
bare-`tm init` tree that no kernel-backed verb could load, the bridge's phantom
blank line and lost final newline (`e5d38b8`), and gap 45's two readers were all
found by driving it, not by a proof. The human's 30-minute drive of the stage-3
binary is still owed (§8.1), and so is the stage-4 binary's — `tm close` and the
automatic close on a real stale tree (§8.2) — **and, since 2026-09-16, the
stage-5 binary's**, whose list is design §14.6's own.

**Why no agent has done these, and no agent can.** Half of every drive list is
the TUI, and `tm tui` exits by name when stdout is not a tty
(`tm/src/tui/mod.rs:92`: *"tm tui needs a terminal (stdout is not a tty) — every
verb of §13 also works on its own"*). Stage 5's list asks specifically for "the
TUI through two reloads, with the CLI running a verb in between", which is
exactly the integration surface no proof reaches (README **gap 182**). An agent
can run the CLI half and has. *(This paragraph said an agent "cannot run" the
TUI half, and that was FALSE — README gap **3527**, the W-38 repair: `tm tui`
refuses a non-tty, not an agent. `script -qfc "stty cols 120 rows 40; tm --dir
<tree> --now <t> tui" tui.raw` gives it a pty, and a small terminal emulator
over `tui.raw` renders the frame — the W-38 auditor drew D68's `paused` row and
D65's meeting that way, and the repair re-drew it. What stays human is the part
the pty cannot give: with `--now` fixed the TUI's clock does not advance, so
"two reloads with a CLI verb in between" is only partly meaningful, and taste.
Say which part a drive covered rather than calling a partial drive a drive.)*
Two recorded questions wait on the
stage-5 drive: **gap 131** (a close cannot be aimed at an older period) and
**gap 139** (`--now` at an earlier instant rolls `.tm/state.json` back).

---

## 6. How to work

### 6.1 Worktrees

Agents work in git worktrees off `rebuild-on-lean`, one branch each, and own
**disjoint files**. To see what exists:

```bash
cd /Users/psixyzt/code/planner && git worktree list
```

They live under `/Users/psixyzt/code/planner/.claude/worktrees/<name>`, which is
gitignored. Your checkout is stable while others work; do not rebase onto a
branch that has not landed. (At `bf7cc63` this clone has no worktrees: stage 3's
2026-09-12 steps ran sequentially on `rebuild-on-lean` itself.)

Before you write anything, name in your handover the files you own.

**"Disjoint files" is about the library modules, not about the four shared
files.** Every stage's *Modules touched* list ends with `Check.lean` and
`Negative.lean`, and every stage owes `kernel/README.md` a block and `Goals.lean`
a deletion — so if "own disjoint files" meant those too, no two stages could ever
run in parallel and every stage would be blocked on the previous one. It does
not. Those four are **append-only by convention**, and the conventions are the
whole point of §6.2, §6.3, §6.4 and §3.2:

| file | how to share it |
|---|---|
| `Negative.lean` | append at the end under your own banner, from a number nobody has used (§6.2) |
| `Check.lean` | append under your own end-of-file banner, or record the omission by name (§6.3) |
| `kernel/README.md` | append a block under an HTML comment banner; number gaps from what is free (§6.4) |
| `Goals.lean` | **delete** the goals you discharged; do not rewrite anyone else's (§3.2) |

The rule for everything else stands: if your stage needs a **library module**
another agent is editing, say so and stop rather than editing it. `Boundary.lean`
and `Plan.lean` are the two most likely collisions, because three of the four
remaining stages touch both.

### 6.2 `Negative.lean` — append at the end, never renumber

New cheats go at the **END** of the file, under a delimited banner that says why
the block exists. Never edit or renumber an existing block. **The merge
renumbers.**

Earned by: three stage-one branches each appended cheats starting at 9, so the
file carried three CHEAT 9s.

**The renumber is outstanding at HEAD.** Measured at `bf7cc63`: the file is 592
lines (510 at `c8f3a38`), 59 `/- CHEAT` banners run to `CHEAT 49`, `CHEAT 27`,
`28`, `29` and `30` each still appear **twice as banners**, and there is a
letter-labelled block `CHEAT A`–`F`. (36, 37 and 38 look duplicated to a naive
grep; they are not — `CHEAT 7`'s withdrawal note cites them.) The README's cheat
table lists only the first set of 27–30 while README gaps cite the second set by
the same numbers. Stage 3 took 43–49, each under its own end-of-file banner.
**Start from a number nobody has used — 50 today — say which numbers you took in
your handover, and do not assume the renumber was done.**
*Done for the banners since the W-1 audit repair (2026-09-14, README "Stage 5 W-1
audit repair"): the second 27–30 (the parser block) are 122–125, and `grep -o '^/- CHEAT
[0-9A-Z]*' Negative.lean | sort | uniq -d` prints nothing. The letter block A–F and the
design's unused reserved numbers (93–107, 118) remain; a new cheat still starts above
the highest number in the checkout — 125 after the repair.*

```bash
cd /Users/psixyzt/code/planner/kernel/TmKernel
grep -n '^/- CHEAT' Negative.lean | tail -5
```

### 6.3 `Check.lean` — do not edit it in parallel

`Check.lean` is the one file every branch would otherwise touch: it is a flat
list of `#print axioms` lines, so two branches adding modules conflict on the
same region every time. Three parallel stage-one branches hit exactly this, none
could extend it, **and the audit covered 119 of 445 theorems while the README
implied it covered the kernel**.

So: append under your own end-of-file banner, **or** record the omission by name
in your README block. One of the two, explicitly. Current practice is visible in
the file — it carries sixteen `APPENDED …` banners at `bf7cc63` (three at
`c8f3a38`).

**This rule was broken once, and the count could not see it.** Step L9
(`5ab24bf`) declared **35** theorems and appended **26** audit lines, did neither
of the two things above for the other nine, and its README block said the
opposite twice ("every one with an audit line"). Both numbers rose, so nothing
looked wrong. **`check.sh` check 3 now runs the reconciliation below itself** and
fails, naming the theorems, when a declared theorem has no audit line — so the
manual step is now guarded rather than merely documented.

**The check that makes this safe**, because the append step is manual and has
demonstrably lost names:

```bash
cd /Users/psixyzt/code/planner/kernel/TmKernel
grep -c '^#print axioms' Check.lean                                     # 4971 (3993 at e7b816c, 1299 at bf7cc63, 1006 at c8f3a38)
grep '^#print axioms' Check.lean | awk '{print $3}' | sort -u | wc -l   # 4971
grep -hcE '^(@\[[^]]*\][[:space:]]*)?theorem ' TmKernel/*.lean | awk '{s+=$1} END {print s}'   # 4969
```

**These told an inconsistent story and were repaired at `e7b816c`; the trap that
produced it has not gone away.** `#print axioms` accepts **any** constant — a
`def`, a `structure`, an `abbrev` — and prints a normal-looking line, so a name
whose final dotted segment was dropped audits the *type* and cheerfully reports
"does not depend on any axioms". That is how 21 theorems came to be unaudited
while the count looked healthy.

**Re-measured 2026-09-16 at W-13's audit repair (3946 at stage 5's close, 3934 at
W-10, 1299 before that).** The audit numbers agree at **3993** over the **78**
modules, against **3992** declarations — and the one entry of difference is now
in the *harmless* direction only. Re-derive by diffing the two **multisets** —
declared short names against audited last segments — not the two `sort -u`
counts, which cannot see a name declared in two namespaces:

```bash
cd kernel   # not kernel/TmKernel: the one roster lives beside the package
python3 leanfiles.py --theorems TmKernel | sed 's/.*\.//' | sort > /tmp/decl
grep '^#print axioms' TmKernel/Check.lean | awk '{print $3}' | sed 's/.*\.//' | sort > /tmp/aud
comm -23 /tmp/decl /tmp/aud   # MUST BE EMPTY — check 3 fails if it is not
comm -13 /tmp/decl /tmp/aud   # `WfPlan` and `effectiveScope` — the two `def`s below
```

**The first line used to be a `grep` over `TmKernel/*.lean` and re-deriving that
way is how this reconciliation gets a wrong answer.** Four repairs have moved
the roster since: the walk went recursive (W-21), the prune list became a
property (W-22), the library ROOT module joined it (W-23, gap 1314), and the
declaration SHAPE stopped being a list of prefixes — attributes, `private`,
`nonrec`, indentation, and finally the line anchor itself, so that
`set_option … in theorem` counts (W-27, W-28). `leanfiles.py --theorems` is the
one roster `check.sh` uses; re-deriving it by hand re-derives the hole.

- 4971 audit lines, 4971 **distinct** names: no name is audited twice.
- Every theorem declared in the 84 modules is audited, and `comm -23` is now
  **empty** — that is the direction `check.sh` check 3 enforces. `^theorem`
  alone misses the declared `@[simp] theorem`s, which is why the grep allowed an
  attribute prefix — and allowing prefixes one at a time is the pattern W-28
  replaced with a keyword-token rule; see `leanfiles.THEOREM`.
- **The `whose` off-by-one is gone.** The third number used to count one prose
  line — `Cmd.lean`'s header contained *"theorem whose command argument was
  unused"* at column 0 — so the two off-by-ones cancelled and the three counts
  looked equal while the diff was non-trivial. That comment is reflowed
  (`Cmd.lean:29-33`, which says why), so the third number is now **4969 real
  declarations** with nothing to subtract. Distinct short names are fewer still,
  because **24** short names are declared in more than one namespace; that is why
  the reconciliation is a multiset diff and not a count comparison. *(This bullet
  read "3790 … 144" from W-10 until stage 5's close, and neither figure
  reproduces by the pipeline above — a reminder that §5.11 applies to this file
  too.)* *(W-39 repair, re-measured by that pipeline: **27** short names are declared
  in more than one namespace, not 24 — README gap 3723.)*
- **Plus TWO non-theorems** in the audit: `Tm.WfPlan` at `Check.lean:472` and
  `Tm.effectiveScope` at `Check.lean:5038`, both `def`s, are still audited. This
  bullet read *"Plus one non-theorem"* and named only the first from `e7b816c`
  until W-24's land step, while `Tm.effectiveScope` had been audited since
  `f2225ec` — so the pattern the repair removed **did** breed, once, and the
  sentence warning against it could not see it. It is why check 3's
  reconciliation is **one-directional**: auditing more than the theorems is not
  a defect, and that is exactly why nothing counts them. Leave them or delete
  them deliberately. *(W-39 repair, re-measured by `comm -13` above: **EIGHT** definitions are
  audited, not two — the two named here and six of `PlanCheck`'s, `candPlanView`,
  `candWireView`, `candsAgree`, `AssignedRowsPay`, `FoldRowsAdmitNothing` and
  `UnfilledAnchored`. The count went stale here a second time by the pattern
  this bullet records the first time of; README gap 3723.)*
- The file carries **92** `APPENDED …` banners (66 at stage 5's close, 65 at `5ab24bf`, sixteen at `bf7cc63`). *(W-39 repair: `grep -c APPENDED Check.lean` prints **123**.)*

So the honest sentence is *"every theorem in the 84 modules is audited, and the
audit names two definitions as well"* (**eight**, and more than 84 modules, at the W-39 repair — gap 3723) — not *"every theorem"* with nothing after
it. (It read "the ten modules" until 2026-09-16 and "the 78 modules … one
definition" until W-24's land step; ten was stage one's count, and one was a
count of the definitions somebody had looked for rather than of the ones there.) `check.sh` reports the audit size by grepping its own output, so its printed
number is the audit's, not the package's.

### 6.4 `kernel/README.md` — append a block, and keep the gap list a single sequence

Same convention: append your stage's material as a block under an HTML comment
banner, and number your gaps from whatever is free.

**There is now one gap list, 1–51, and "gap N" means exactly one paragraph.** It
lives in five places, because the material does: gaps 1–23 under "What this does
not cover", 24–29 in the `Arith.lean` block, 30–36 in the acceptance-evidence
block, 37–39 in the 2026-09-09 stage-3 block, and 40–51 as bold-headed
`**Gap N …**` paragraphs inside the 2026-09-12 stage-3 block (42–51 in §9.2's
numbered four-part form; 40 and 41 in prose). The first three carry a header line saying where in
the sequence they sit; the later two say it in their banners and closing
"new gaps start at" sentences.

Until `c8f3a38` these were three lists each starting from its own number — 1–23,
12–17 and 18–24 — so 12–17 and 18–23 each named **two** different gaps, and four
cross-references landed in the wrong one. That is fixed. **Number your new gaps
from 52 (37 at `c8f3a38`) and keep one sequence**; if you cannot, say in your
banner which range is yours and fix it at the merge (§6.5).

### 6.5 What a merge owes

1. Renumber `Negative.lean`'s cheats into one sequence and update the README's
   cheat table to match. (Outstanding at `c8f3a38`, and still at `bf7cc63`; §6.2.)
2. Keep the README's gap numbering one sequence, and fix any cross-reference the
   merge moved. (Done at `c8f3a38`; §6.4.)
3. Append every branch's new theorem names to `Check.lean` — then run the three
   counts in §6.3 and confirm every new name prints its own line and none
   collapsed to its namespace root.
4. Delete from `Goals.lean` every goal the branches discharged, and check that
   check 7's number went **down** by exactly that many (§3.2).
5. Confirm every new module is imported in `TmKernel/TmKernel.lean` (§2.3).
6. Run `check.sh`, capped (§2.1). **Every** check, exit 0 — and
   `cargo test --workspace` green beside it (§7.5). *(This line said "seven"
   until the W-24 repair step, "nine" until W-25 track A and "ten" until W-31,
   while checks 8-13 landed at W-19, W-20, W-25, W-30, W-31 and W-33. It no
   longer carries the number: §7.1 does, once, and README gap 2148 is why.)*
7. **Reconcile the PARITY register, the way item 1 reconciles the cheats.** A
   parity entry is a recorded divergence from the fork (D21/D22), and the
   register has no single home and no gate — README **gap 226** said so when
   **P32 was issued twice**, and **P38 was issued twice** at W-24 for exactly
   the same reason (README gap **1417**): gap 402's block took P38, four later
   blocks wrote "P38 still free", and W-24 track A believed the later ones.
   This checklist is where the merge could have caught it and did not, because
   it reconciled everything except this. The reconciliation is:

   ```bash
   cd /Users/psixyzt/code/planner/kernel
   grep -noE '\*\*Parity P[0-9]+ taken\*\*|^\| \*\*P[0-9]+\*\* \|' README.md
   ```

   Every number it prints must appear **once**. It is a command and not a
   check, and the reason is written down rather than left to be rediscovered: a
   `P<n>` in this repository is also a stage-6 **step** name (P1–P5, and track P
   itself), so a regex over `P<n>` cannot tell an issuance from a step
   reference, and the two idioms above are the only ones a block has ever used
   to *issue* one. A block that issues a parity entry in a third spelling is
   invisible to it. **The gate this wants** is a canonical issuance line that
   every block must carry, checked for uniqueness — which is a convention to
   impose on future blocks, not something that can be retrofitted over 53,000
   lines of ledger.

   **BUILT AT W-25 TRACK A as check 10, and the retrofit was not the hard
   part.** `kernel/parity.txt` is the index — one row per number, naming the
   file and **line** where the entry is recorded — and `kernel/parity.py`
   re-resolves every anchor with no build. **This item is therefore a command
   that fails**, not a command that prints:

   ```bash
   cd /Users/psixyzt/code/planner/kernel && python3 parity.py
   ```

   The canonical issuance line, at column zero, is

   ```
   **Parity P<n> taken**: <what diverges, and from what>
   ```

   and `parity.py` prints the next free number rather than leaving it to be read
   off whichever sentence a step happens to find — which is how both duplicates
   happened. **Three things the command above could not see, each measured at
   W-25:** it required the register row to be **bold** and the first twelve
   (`| P1 |`–`| P12 |`) are not, so twelve of the thirty-nine numbers in use were
   invisible to the reconciliation written to find them; it counted the P38
   issuance **quoted inside backticks** by the W-24 block that repaired P38, so
   it reported the duplicate on the repaired tree; and it read `README.md`
   alone, while P13, P22, P28, P29 and P31 live only in design §17's table and
   **P36 lives only in a comment in `Replay.lean`**. Gap 1417 concluded that 17
   numbers were "not locatable mechanically"; all 39 are located and anchored,
   and what was missing was a list of where to look.

---

## 7. How to verify your own work before an audit does

### 7.1 The seven checks this section documents — and `check.sh` runs FOURTEEN

**This heading said "the seven checks" while `check.sh` ran nine**, and the
number is repaired here rather than the section: checks **8** (the prose
citations, W-19, owner D39/D41), **9** (every new definition constant-folded,
W-20, owner D40), **10** (the parity register, W-25), **11** (§5.3: no two
names for one definition, W-30 track A; a second key for a GENERALISATION
since W-33 track A), **12** (a definition the compiler emits must be REACHED
from `tm_kernel_call`, W-31 track A, owner D51) and **13** (a field the
planner wire emits must have a WRITER the day builder reaches, W-33 track A,
README gap 2403) are specified by their own scripts' headers —
`kernel/citations.py`, `kernel/mutate.py`, `kernel/parity.py`,
`kernel/twins.py`, `kernel/reach.py` and `kernel/fields.py` — and by
`check.sh`'s comments above each, which are long and are the specification.
The exemptions are `kernel/reach-exempt.txt` (check 12), `kernel/twins-exempt.txt`
(check 11's second key, one dated sentence per adjudged group) and
`kernel/fields-exempt.txt` (check 13, one dated line per unwritten field with
its EXIT); each may only shrink, and each is W-27's shape — an enumeration you
join to be EXEMPT, not to be COVERED. Since the W-33 repair each file is held
against ITSELF AT HEAD in both directions (README gaps 2560, 2563, 2564): check
12 answers three measured classes by `CLASS` line and module rather than by name
(a definition reached only through a declared unsent request section; a
`mutate.WITNESS_MODULES` leaf; since the W-35 repair, a definition of a declared
`CLASS proof` module that no auditable module imports — `PlanCheck.lean`, README
gap 2923), check 11 refuses a NEW `NOT ONE CONCEPT` line,
and check 13 refuses a new line for a field the structure already had. The call graph checks 8, 11, 12 and 13
read is `kernel/callgraph.py`, which none of them owns.

**Since the W-34 repair (README gaps 2730-2734):** check **14** (`kernel/replay.py`)
replays every library module through the pinned toolchain's `leanchecker`, so the
environment check 3 audits is one the KERNEL checked — a `theorem (1 : Nat) = 2`
added through the run_tac tactic with `debug.skipKernelTC` passed checks 1–13 and is refused
here; check 2 refuses an `import` of anything but the kernel's own modules (the
route that plant took) and a `decide +kernel` outside `kernel/kernel-decide-exempt.txt`
(§5.10a, may only shrink); and check 13 gained an INPUT half — every field the
planner request decodes must be READ by a definition `Planner.dayPlan` reaches, or be
a dated line of `kernel/inputs-exempt.txt` with an EXIT (may only shrink). What is
written out below is checks 1–7. Do not read
"seven" here as the size of the acceptance; §2.1 and §6.5 carry that number and
both said "seven" too until the W-24 repair step.

Run them together with `kernel/check.sh`. Each also runs alone. **Every command
in this section runs under the memory cap** — prefix it with
`systemd-run --user --scope -p MemoryMax=40G -p MemorySwapMax=0 --quiet` on
Linux (§2.1, §5.10a); the bare forms below are what goes after the prefix.

**1 — the kernel builds, including the linkable archive.**

```bash
cd /Users/psixyzt/code/planner/kernel/TmKernel && ~/.elan/bin/lake build TmKernel:static
```

Proves only that a proof that does not compile is not a proof. The `:static`
facet matters: plain `lake build` produces `.olean` + C IR but not the archive
Rust links (`.lake/build/lib/libTmKernel_TmKernel.a`, 3,704,386 bytes at
`bf7cc63`; 1,759,720 at `c8f3a38`). The build emits `linter.unusedSimpArgs`
hints; they are warnings.

**It proves nothing about a module nobody imports.** `lake` builds the `TmKernel`
library, which is `TmKernel/TmKernel.lean`'s ten imports; an unimported file in
that directory is not compiled and this check still says `ok` (§2.3).

**2 — totality and boundary discipline.**

```bash
cd /Users/psixyzt/code/planner/kernel && python3 totality.py TmKernel/TmKernel TmKernel
```

Proves the kernel cannot answer wrongly *and silently* through a panic, and that
the boundary cannot swallow an error into a `none`. Exit 0 is clean. **Two
directories**: the library and the package root, so `Check.lean` and
`Negative.lean` are scanned too, and `Goals.lean` is exempt by filename (§3).

**3 — the axiom audit.**

```bash
cd /Users/psixyzt/code/planner/kernel/TmKernel && ~/.elan/bin/lake env lean Check.lean
```

Proves no audited theorem depends on `sorryAx` — transitively, so a `sorry`
anywhere under an audited theorem surfaces. This is also what keeps check 7 safe:
a `sorryAx` here means `Goals.lean` leaked into something proved (§3.2).

**It now proves coverage too** (W-13's audit repair). Three ways the audit can
rot, all three of them caught here:
- a `#print axioms` naming a renamed constant elaborates to `unknown constant`,
  prints no `axioms` line and used to leave the check green — **any error Lean
  reports for `Check.lean` now fails it**, and the first three are printed;
- a theorem **declared and never audited** used to be invisible, because the
  printed number is the audit's size and not the package's — the check now runs
  §6.3's multiset reconciliation (`comm -23` of declared short names against
  audited last segments), fails when it is non-empty, and **names** up to five of
  the missing theorems;
- auditing a `def` is *not* failed, deliberately: `Tm.WfPlan` is audited on
  purpose (§6.3), so the reconciliation is one-directional.

Step L9 added 35 declarations and 26 audit lines and this check said `ok` at
3984. That is the case the reconciliation exists for; §6.3 has the history.

**4 — `Negative.lean` MUST fail to compile.**

```bash
cd /Users/psixyzt/code/planner/kernel/TmKernel
LEAN_PATH=.lake/build/lib/lean ~/.elan/bin/lean Negative.lean    # exit 1
```

The only check that tests the type system rather than a theorem. `check.sh`
inverts the sense: if this ever compiles, the build fails.

**5 — Rust calls the kernel and gets the right answers.**

```bash
cd /Users/psixyzt/code/planner/kernel/tm-kernel-ffi && cargo test --quiet --test kernel --test stack
```

**93 tests at stage 6 W-18** — `kernel.rs` 86 and `stack.rs` 7 — through
`Rust → C shim → Lean` (57 at `bf7cc63`, 26 at `c8f3a38`; the command read
`--test kernel` alone until the owner's **D36**, §4). Proves
the export is reachable and the wire format is what both sides think it is —
and, since J5, it is the main evidence for the one agreement no theorem can
state: that serde_json reads what `jemit` writes and writes what `jparse` reads.

`--test stack` is D36's declared coverage payment (README gap 686): those seven
tests ran in **neither** this script nor `cargo test --workspace`, and they cost
**2.23 s** on a **3.8 s** built-tree wall. `check.sh` now says the count the way
checks 3, 6 and 7 say theirs, so a test that stops running is visible.

**6 — the corpus round trip.**

```bash
cd /Users/psixyzt/code/planner/kernel/tm-kernel-ffi && cargo test --quiet --test corpus -- --nocapture
```

6 tests; prints the per-file table and a `CORPUS:` score line. It was written as
the only check covering the two steps no theorem reached: splitting a file's
bytes into lines and back, and the JSON escaping on both sides of the FFI. Both
kernel halves are theorems now — `a_file_splits_into_the_lines_it_was_joined_from_char`
over `Tm.splitOn`, and `jparse_jemit` / `the_response_call_emits_parses_back` for
the JSON — so what this check still uniquely covers is the **host's** half: the
harness's `split('\n')` and its hand-written JSON codec agreeing with the kernel's
over every corpus file.

**Its two assertions are different in kind and both matter.**
`no_file_is_silently_rewritten` is **absolute** — a document the kernel *accepts*
and hands back with different bytes is data loss, and there is no baseline for
it. `corpus_round_trip` is a **ratchet** against `corpus/round-trip.expected`: a
file recorded `ok` that stops round-tripping fails, a file that starts
round-tripping does not, because the grammar is still being extended, and the
total `ok` count may not fall. The baseline is regenerated by setting
`TM_CORPUS_BLESS=1` for that test run — `corpus_round_trip` calls `bless` when it
sees it — which **rewrites a committed file**, so treat it as an edit under
review, not a test invocation, and never rebless downward.

The two targets are 57 + 6 = 63 tests at `bf7cc63` (26 + 6 = 32 at `c8f3a38`).

**Whole trees only, since the owner's D6 (stage 4 final step 3).** A parent is read
off its line, and a link to an id the request does not carry refuses the whole
tree (`itemCheck: danglingParent`); a `week/*.md` or `backlog.md` naming a month
outcome therefore cannot load on its own, and the owner accepted that the harness
changes with it. Each plan is loaded **once**, and a `file` row is **that file
inside its plan's whole-tree load**: `ok` when the plan loads and the file comes
back byte for byte, `differs` when the plan loads and the file changed (still the
absolute failure — `no_file_is_silently_rewritten` is unchanged), `reject` carrying
the plan's refusal when the plan does not load. A file is never loaded alone. **The
score moved 33/37 → 29/37 and means something different:** until D6 four of
`plan-conflicts/`'s nine files (`inbox`, `month`, `optional`, `routines`) scored
`ok` on their own while their plan was refused; inside the plan's load they are
refused with it. No file outside `plan-conflicts/` changed, and the whole-plan
score stays 4/5. `corpus/round-trip.expected` was reblessed **for that
redefinition and nothing else**. For a refused plan the `--nocapture` report now
peels its refusals from the whole tree one at a time — the fewest item lines that
still reproduce each named refusal, removed with the lines that name them so no
`danglingParent` is manufactured — and `plan-conflicts` reports nine, the `@ghost`
parent's `danglingParent` and the ouroboros' `parentCycle` among them
(`the_conflicts_plan_refuses_its_parent_defects_by_name`). 8 tests in the corpus
target, 67 in the kernel target, at stage 4 final step 3.

**7 — the outstanding goals of stages 3–6 elaborate.**

```bash
cd /Users/psixyzt/code/planner/kernel/TmKernel
LEAN_PATH=.lake/build/lib/lean ~/.elan/bin/lean Goals.lean        # exit 0, sorry warnings
grep -c '^theorem ' Goals.lean                                    # 40 at bf7cc63 (52 at c8f3a38)
```

`Goals.lean` states every remaining obligation of stages 3–6 that can be written
down as a theorem against the real kernel, with a `sorry` proof. **A statement
that typechecks is guaranteed to be well-formed and to name real definitions**,
so a goal nobody can state is visible now rather than in stage 6. The check fails
on an *error*; the `sorry` warnings are the point, and `check.sh` filters
`declaration uses 'sorry'` out of the failure dump for exactly that reason.

**Its count is a burn-down, not a score.** 40 at `bf7cc63`, 0/11/14/15 across
stages 3/4/5/6 (52 at `c8f3a38`, 12/11/14/15). A stage that discharges a goal moves the theorem into its real
module and deletes it here, and the number drops; it rises only when a new debt
is deliberately admitted. §3.2 is the procedure, and it is the check stages 3–6
should watch most closely — checks 1–6 say the kernel is still sound, check 7
says how much of the rebuild is left.

Nothing imports `Goals.lean`, so its `sorry`s cannot reach a proved theorem, and
check 3 is what enforces that.

### 7.2 The corpus is evidence, not a test suite to satisfy

`kernel/corpus/` is 37 Markdown files across five plan trees, copied verbatim
from `main@557a3d2`. `plan-conflicts/` is **deliberately malformed** — a
duplicate id, two ids on one line, a bad priority, an odd token, an unknown key,
a repeated `due:`, an out-of-range `ci:`, a dangling `after:`, a `@ghost` parent,
cycles, a calendar entry with no time, a day-file item outside `# Pinned`.
`corpus/PROVENANCE.md` enumerates them.

**A refusal in `plan-conflicts/` is the fixture doing its job. A refusal anywhere
else is a finding.** Do not "fix" a corpus refusal without reading PROVENANCE.

The score at `bf7cc63` is `33/37 files and 4/5 whole plans`, printed by check 6 —
unchanged since `c8f3a38` through all of stage 3.
All four failing files are `plan-conflicts/`, and each refusal names a defect
`PROVENANCE.md` lists as deliberate: `dupId: a1`, `itemCheck: fileKindShape`,
`itemCheck: sectionDiscipline`, `badLine: manyIds`.

*Since D6 (stage 4 final step 3) the score is `29/37 files and 4/5 whole plans`:
a file is scored inside its plan's whole-tree load (§7.1, check 6), so all nine of
`plan-conflicts/`'s files carry that plan's refusal, and the four that scored `ok`
alone no longer do. The per-file refusals above are still reproduced — by name,
with each of the plan's other deliberate defects — in the report's whole-tree
peel.*

The whole-plan number is the one carrying information, and it moved: `1/5 → 4/5`
when the demotion model landed at `8eea3d6`. `plan-basic`, `plan-home-day` and
`plan-travel-day` were refused as `splitLine: m2`; `LErr.splitLine` is now
**deleted**, because the tombstone carries its own bytes and there is nothing
left for it to refuse. The fifth plan is `plan-conflicts`, which exists to be
refused. Do not quote `1/5`, and do not look for `splitLine` — it is gone.

### 7.3 The differential oracle (not in `check.sh`)

**Repaired and retargeted at the S attempt** (2026-09-15; README "the S
attempt"). `build-oracle.sh` used to run `git archive main`, and `main` was
discarded on 2026-09-12 (§2.2), so it failed before it built anything. It now
extracts the fork point `4748911`, stamps the scratch tree with the ref it holds
so a tree left by the old script is re-extracted rather than silently reused, and
every "no disagreement" it prints is against the fork-point grammar, whose delta
to `main@557a3d2` is stage 0's fix. The numbers below are re-measured against the
fork point; the old `main`-side pair (126 of 138, 481 of 2,048) is **superseded
and must not be quoted**.

```bash
cd /Users/psixyzt/code/planner/kernel/tm-kernel-ffi
./examples/oracle/run-oracle.sh <scratch-dir> [cases-per-seed] [seeds]
```

It extracts the fork point into a scratch directory, builds a small binary
against the shipped `tm-core::grammar` and `tm-core::log`, and runs both
implementations over two input sets: the corpus's own item lines, and the fork
point's own `grammar_proptest` generator over several seeds. It writes nothing
inside the repository. It is deliberately **not** a seventh check, because it
needs a Rust build of the fork point outside the repo, which is the wrong
dependency for an acceptance script that must run on this branch alone.

It prints the denominator for every comparison, so "no disagreement" is never
confused with "never ran". Four things are comparable through a `String → String`
boundary: is it an item line; does each side hand the line back unchanged; what
id does each read; does `tm edit est=` produce the same line. Title, `ci`,
priority, parent, tags, shape, recurrence, budget, `loc:`, `buffer:` and the
flags are **not** compared, because the kernel keeps those tokens verbatim and
has no answer to differ from (gap 35).

**A fifth thing became comparable at the S attempt:** `tm-oracle replay <tz>`
reads whole log texts and prints what the fork's `log::replay` derives from each,
as JSON. That is **T5's oracle at the switch** (design §14.6 item 4), which
deletes the in-tree Rust reader T5 compares against today. The fork's `Replay`
and this branch's serialise 20 and 22 keys, differing only by this branch's
`seams` and `last_effective_t`, with all 19 nested record structs field-identical
on the same `chrono`/`chrono-tz`, so the comparison is key for key over the whole
structure. It is driven from `tm/tests/kernel_replay_parity.rs`, which holds the
log corpus, not from `run-oracle.sh`.

**The fork's answers are also frozen, and that arm is not `#[ignore]`d**
(2026-09-16, W-11; design §14.6 item 4, README gaps 137/146/147/149). Taking the
oracle's answers once and committing them to `tm/tests/fixtures/` puts a
*differential* inside plain `cargo test --workspace`, which is what guards a
commit — an arm that runs only when someone builds the fork point does not.
`tm/tests/support/fork.rs` is the one place that reads them back, shared by
`kernel_replay_parity.rs` and `kernel_log_door.rs`; **20 T5 inputs and 16 scoped
door reads** are compared against them, key for key. Freezing is not weakening:
a frozen expectation is the fork's own bytes, blessed by
`the_frozen_fork_answers_are_reblessed_from_the_oracle` (inert without **both**
`TM_ORACLE` and `TM_FORK_BLESS`, because rewriting a committed differential
fixture is a decision and never a repair, §7.2). Values, never a digest: a digest
would have to normalise parity **P21** out, and that hides the one thing P21
exists to watch (**D21**).

**A third input set landed at stage 5's close**, and it is stage 5's own plan
acceptance (§8.3): `tm-oracle replay` and the new `tm-oracle fit` read whole log
texts, and `tm/tests/kernel_replay_parity.rs`'s
`stage5_parity_the_kernel_replays_and_fits_as_the_fork_point_does` compares them
with the kernel's facts — the whole `Replay` key for key, and the `Model`
`tm model --fit` writes from it (design §14.6's T12). It is `#[ignore]`d and inert
without `TM_ORACLE`, so `cargo test --workspace` never needs the fork build;
`run-oracle.sh` sets it and runs it as input set 3. **Widened at W-11** from the
8 corpus-and-month logs to every input class T5 covers — the generated half-year,
the 256 generated sequences and the 192 undo-triple logs as well — grouped by
zone so each zone costs one subprocess rather than one a log: **469 logs over 6
zones, 8,442 `Replay` keys, 469 entry counts, 8 fitted models, 195,243 scalar
values; 24 sightings of parity P21 and no other disagreement** (was 8 logs,
144 keys, 16,772 values, 4 P21).

**A fourth input set landed on 2026-09-16 (W-11), under owner decision D23**
(README gap 148): `tm-oracle parse-entry` reads **one log line per line of
stdin** and prints what the fork's `Log::parse_bytes` says about that single
segment — accepted (with the entry as the fork's own `to_json`, its tag, id,
`tm log` column, and the instant as `epoch`/`nanos`/`offset`), refused (with
serde's or chrono's message verbatim), or blank. A segment that is not UTF-8
cannot be a JSON string, so it may be given as a **JSON array of byte values**
instead; that is how the crafted set's torn-write lines reach the fork. This is
**T1-T3's oracle at the switch**: their comparand until W-11 was the in-tree
`Log::parse_bytes`, `LogEntry::parse` and `parse_timestamp`, which design §12
deletes, so all three would otherwise have had to be retargeted inside the
switch commit. The verdicts are frozen into
`tm/tests/fixtures/fork-4748911-log-lines.jsonl` — **11 sources, 8,273 per-line
verdicts and 7 whole-file readings, 1,946,886 bytes**, byte-reproducible on a
re-bless — so the comparison runs in plain `cargo test --workspace`, and the
`TM_ORACLE` arms are the re-bless and the one assertion bytes on disk cannot
make: **1,375** kernel renderings handed back to the fork and read to the same
entry. Measured at the retarget, unchanged from the pre-retarget figures against
the in-tree reader: **T1 636 lines, 553 entries (533 byte-identical), 66
warnings, 9 blank, 8 residue; T3 4,601 spellings, 822 read (42 leap seconds),
3,765 refused by both, 14 P23 residue; the generated month 3,036 lines over 24
event kinds.**

**Provenance is not freshness: rebuild the binary before you trust a scratch
tree** (W-11's audit repair; README gap 196). `build-oracle.sh` stamps the
scratch tree with the ref it extracted, and that stamp says nothing about when
the **binary** beside it was built. W-11's audit did exactly what this section
asks — diffed the extracted `tm-core/src/log.rs` and `tm/src/cli/ctx.rs` against
`git show 4748911:` and found them identical — and the binary it then ran
predated D23, had no `parse-entry`, and failed both grammar arms with the empty
message `the fork oracle failed: ` (that oracle printed its usage banner on
stdout, and only stderr was quoted). One re-run of `build-oracle.sh` fixed it.
The tests no longer let that happen silently: `fork_oracle` in
`kernel_log_grammar.rs` and `kernel_replay_parity.rs` reads the binary's own
usage banner and **refuses an oracle that lacks the mode by name**, and a failed
call quotes the exit code and *both* streams. A leftover binary is still the
right thing to reuse — just re-run the script first; it is a no-op when the tree
and the sources already match.

**Re-run AFTER the switch, at stage 5's closing commit (2026-09-16), with `512 4`
and a REBUILT oracle** — this is stage 5's plan acceptance (§8.3) and the run to
quote: **138 corpus lines compared, 77 with nothing to report; 2,048 generated
lines compared, 470 with nothing to report** — both **byte-for-byte** the
`017ead3` and stage-5-close figures, so the grammar surface did not move while
the in-tree reader was deleted, the writer was replaced by the kernel's (S2) and
quirk Q6(f) was fixed. Set 3: **469 logs over 6 zones, 8,442 `Replay` keys, 285
`tm event` name sets, 469 entry counts, 7 refused-line lists, 8 fitted models,
195,243 scalar values; 24 sightings of parity P21 — each checked to display the
same `round1` load and `load_blocks` — and no other disagreement.** Set 4:
**1,375** kernel renderings read back to the fork's own entry.

**The `events` key set joined the comparison at the close (README gap 225).** The
fork serialises 20 `Replay` keys and the frozen comparison covers 18; `warnings`
is P15, and `events` had been left out because the kernel keeps only the latest
record per `(name, id?)`. Its doc comment said T5's `latest_named` queries
compared it — **true until S, and false the moment the in-tree reader those
queries used was deleted**, which turned the whole `named` family from compared
into merely counted with nothing saying so. `fork::compare_event_names` now
compares the half both sides share, the key set, which is the half
`priority::collect_candidates` actually reads, and it was shown to fail against a
deliberately corrupted kernel answer before being trusted.

*Run at the stage's first close (`b344185`, before the switch), superseded by the
run above:* 138 / 77 and 2,048 / 470; set 3 **8 logs, 144 `Replay` keys, 8 entry
counts, 8 fitted models, 16,772 scalar values; 4 P21 sightings.*

Run at `017ead3` with `512 4`, byte-identical across runs: **138 corpus lines
compared, 77 with nothing to report; 2,048 generated lines compared, 470 with
nothing to report.** These are deterministic for a fixed seed count — they move
when the *kernel* or the *oracle target* moves, not between runs. They fell from
the `main`-side 126/481 when the target became the fork point, which is the
retarget and not a regression: the largest single corpus row is
`itemCheck/danglingParent` at 55. The rows are not a partition — 61 of the 138
corpus lines have something to report against the old side's 12, so 49 are new,
and because a line may disagree in more than one comparison the corpus rows sum
to 199. The README's `129`/`479` were taken before the demotion model changed;
that is the whole point of §5.11.

### 7.4 The self-check an audit will apply to your theorem statements

Go through this before you claim anything.

1. **Is every binder used?** A theorem with an ignored argument is a different
   theorem wearing a better name. §5.2.
2. **Is every hypothesis satisfiable?** Exhibit a witness if it is not obvious. A
   precondition nothing satisfies makes the conclusion vacuous, and it stayed
   invisible for a whole stage once.
3. **Does the name match the statement?** A theorem's name is checked by nobody.
4. **Are both directions covered?** The check can be discharged, and the check
   bites. §5.8.
5. **Is it about the code the FFI runs, or a copy of it?** §5.4.
6. **Does it quantify over what reaches the disk?** §5.9.
7. **If it is a missing precondition, is it one of the four disguises?** The
   destination already holds this id; the destination is not a file at all; the
   inverse has *two* values, resolved by argument order; the inverse has *no*
   value where the code assumed one.
8. **Is the new theorem in `Check.lean`, or the omission recorded?** §6.3.
9. **If you discharged a goal, is it deleted from `Goals.lean`** — and if you
   added a module, is it imported in `TmKernel/TmKernel.lean`? §3.2 and §2.3.
   Both failures are silent: check 7 stays flat, check 1 stays green.
10. **Does every `Negative.lean` block still fail for its stated reason?** Not
   just "the file failed". Look for a block failing on a `maxRecDepth`/heartbeat
   budget instead of its type error; a block that has *started* to compile, which
   means a guard was weakened; and a cheat whose comment no longer describes what
   the kernel does. Note that at least one cheat fails as
   `error(lean.unknownIdentifier)`, which a naive `grep 'error:'` misses.
11. **Did you re-measure every number you wrote down?** §5.11.
12. **Is every new `decide`/`rfl` witness small, and was it probed under a
   cap?** §5.10a.

### 7.5 Two suites are acceptance now, because the Rust calls the kernel

Until stage 3, `check.sh` was the whole acceptance: the only Rust on the branch
was `kernel/tm-kernel-ffi`, and checks 5 and 6 already ran it. **That is no longer
true.** Since `d8e8d4d` the shipped `tm` binary calls the kernel for seven verbs
through `tm/src/cli/kernel_bridge.rs`, so a kernel change can break the product
while all seven checks stay green — a renamed refusal the bridge maps by name, a
reordered response key a test splits on, a wire field the host sends that the
kernel now refuses. And a host change can break the kernel's contract without
touching Lean. So before **any** commit that touches the kernel or the Rust, both
of these, capped, from their own directories:

```bash
cd /Users/psixyzt/code/planner/kernel
systemd-run --user --scope -p MemoryMax=40G -p MemorySwapMax=0 --quiet ./check.sh
#   seven ok lines, exit 0
cd /Users/psixyzt/code/planner
systemd-run --user --scope -p MemoryMax=40G -p MemorySwapMax=0 --quiet cargo test --workspace
#   1,309 passed / 0 failed / 9 ignored across 78 result lines at stage 5's close
#   (984 / 0 / 0 across 64 test binaries at bf7cc63, 4.9 s warm)
```

They do not overlap: the root workspace `exclude`s `kernel/tm-kernel-ffi`, so
`cargo test --workspace` does **not** run the FFI crate's own **101** tests
(63 at `bf7cc63`), and `check.sh` does not run the CLI, TUI,
`tm-core` or proptest
suites. **Since the owner's D36 (stage 6 W-18) checks 5 and 6 run all 101** —
`kernel` 86, `stack` 7, `corpus` 8. Until then they ran 94 of them and the
seven of `stack.rs` were run by nothing automatic, which this sentence said the
opposite of for four runs (README gap 686). The FFI crate's `build.rs` re-drives `lake` when any file under
`TmKernel/` changes, and `tm` depends on that crate, so the workspace run also
rebuilds the kernel it links (`tm/build.rs` only adds the toolchain `lib/` rpath). A green
`check.sh` with the workspace unrun is half an acceptance; say which half in
the commit if it is all you have.

**"0 failed" from ONE run is a probabilistic claim, so say how many runs you
made** (owner **D46**, 2026-09-22; README gaps 1316 and 1360). Four of the
workspace's suites are `proptest`s, and a `proptest` draws fresh cases from the
clock on every run: the number above is *this* run's verdict on *these* draws,
not a property. An auditor ran the suite three times instead of once at W-23's
close, **one of the three failed**, and the fresh seed had found a real
pre-existing round-trip bug in `ItemLine::set_state_with_ci` that six stages of
single runs had never drawn. So the acceptance line a block quotes now names its
denominator — "1,397 passed / 0 failed across 81 binaries, **three runs**" — and
a step that made one run says one. Three is the working minimum for a commit
that touches parsing, editing, the planner or the log reader; one is enough for
a documentation-only commit, said out loud.

**A new line in a `.proptest-regressions` file is a FINDING to report and fix —
never a dirty tree to revert** (same decision). Those files are **tracked**, and
proptest appends the failing seed to the one beside the test. So a red run hands
you a modified tracked file through no edit of your own, and the reflex that
keeps a tree clean — `git checkout --` on the "unexpected" modification — throws
away the only cheap evidence the bug exists. Commit the new seed with the fix:
that turns a case drawn once into a case that runs every time, which is the same
move as check 8's allow-list and check 9's roster — **the gate remembers what an
auditor found by hand.** If the seed is genuinely not reproducible against the
fixed code, say so and delete it deliberately, in the commit message; do not
revert it silently.

---

## 8. The remaining stages

The plan's stage table is `PLAN-lean-kernel.md` §5. Its acceptance criteria are
quoted below; the corrections and traps are what this document adds.

Four facts cut across all four stages.

**Your stage already owns a set of named goals.** `Goals.lean` groups its 40
statements (52 at `c8f3a38`) by stage under `# STAGE n` banners, and each stage section below lists
its own. Read them before you read the plan's prose: they are the same
obligations, already stated precisely enough to elaborate. Discharging one is
§3.2's three-step move, and check 7's number is how the stage is measured.

**A new module must be imported into `kernel/TmKernel/TmKernel.lean`.** Stages 4,
5 and 6 each propose one. Unimported, it is not built, not in the archive, not
reachable from Rust — and `check.sh` still prints seven `ok`s (§2.3).

**Any new command pays `WfPlan.mapAt`.** It re-runs the whole of `planWf` by
computation on the post-state, so it cannot be forgotten. Every new command owes
a "this command can discharge it" theorem (`cmdMove_succeeds` is the model) and a
"the check bites" theorem (`mapAt_rejects_unoriented` is the model).

**Relational versus single-run is the cost line.** A property over one run of a
function is a decidable check on the output plus a `lift` — cheap, and the whole
point of the `Subtype` tier. A property comparing *two* runs is a real induction
over a greedy fold. Classify every law you are given before you start.

---

### 8.1 Stage 3 — the boundary and the first kernel-backed verbs

> **Plan acceptance.** `cargo build` from clean drives lake and links; the seven
> verbs `move`/`demote`/`readopt`/`drop`/`edit`/`rank`/`add` kernel-backed; full
> suite green; panic probe returns `KernelFault`, not exit 0. Cost: 1 wk.
> Worth alone: half the lifecycle verbs are structurally sound in the shipped
> binary; the id class is dead in production.

**Status at `bf7cc63` (2026-09-12): stage 3's scope is landed, its twelve goals
are gone from `Goals.lean`, and a named list is still owed.** The honest one-line
reading of the plan acceptance: the seven verbs are kernel-backed in the shipped
binary and the id class is dead there (`tm move ^m2 month` on a fresh `tm init
--example` tree is refused `occupied`, nothing written — `d8e8d4d`); the fault
probe returns a named `kernelFault`, never exit 0 (`dd89bc6`); both suites are
green (§7.5); and `cargo build -p tm` into an empty target directory built and
linked in 18.1 s at `bf7cc63` with the Lean archive already built — a from-clean
`lake` build was not re-measured. What the acceptance does **not** yet cover is
listed under "Still owed", below, and it is not small.

**Scope, concretely — what each item became.** Each item's heading follows the
original's; the text after it is what became of it (the original text is in `git show
3d2959b:AGENTS.md`).

1. **Restore the Rust workspace first.** *Landed, `835d960`* — not from `main`,
   which the owner discarded (`f386c56`), but from the in-clone fork point:
   `git checkout 4748911 -- tm-core Cargo.toml Cargo.lock`. Zero portability
   fixes; 943 tests passed at the restore. The restored `tm-core` is pre-stage-0.
2. **Two verbs did not exist in Lean at all.** *Both landed.* `rank`: `cmdRank`,
   L20a/L20b proved (`1d4fc14`), both §5.8 directions
   (`rank_onto_a_taken_rank_is_refused`, `cmdRank_succeeds`, `d0aced9`); the host
   compiles a position into a rotation of raw ranks (`bd61f11`). `add`: `freshId`
   with L21 proved by pigeonhole, not a retry loop (`dcf35dc`), the verb
   (`9840ea8`), `cmdAdd_succeeds` (`d0aced9`). The seed landed as a **per-`add`
   wire field**, not PLAN §3.4's request-level `Seed`/`Repair` round trip —
   `Repair` still does not exist anywhere. `add`'s command-shaped `itemsWf` bite
   has no Lean theorem (README, `1a85e25`).
3. **`edit` was one keyed field of eighteen.** *Now seventeen of eighteen on the
   kernel's edit path*: nine at `a2e0dc2` (`est dur buffer pref on-miss
   after-done min max ci`), eight more at `bf7cc63` once their parse ⇒ wf bridges
   were proved (`due at win every on-event after loc waiting`). The eighteenth,
   `demoted`, is excluded **by policy** (`keyNotWired demoted`, CHEAT 45). The
   host routes only the first nine — gap 48.
4. **Horizon *names*.** *Decided: resolved in Rust.* `kernel_bridge.rs` maps
   words to paths and generates each document's `grain`/`ix` from the kernel's
   own numbering (`regions_are_the_kernels_numbers`: 2026-W37 is `(1, 105695)`).
   The kernel still believes whatever region it is sent (gap 10).
5. **Schema.** *The seven verbs' fields landed* (§2.4). **`now` was not added** —
   owed to stage 4, which needs it first.
6. **Panic layers 2 and 3.** *Landed, `dd89bc6`*: the stderr `dup2` while the TUI
   owns the screen, fault-versus-refusal at the verb seam with the terminal
   restored, and the constructed probe `TM_KERNEL_FAULT_PROBE`.
7. **The four integration-bug countermeasures.** *Three landed, `f4d0ec5`*:
   `cli_conformance.rs` (`--help` versus runtime, 38 pages), `cli_json_matrix.rs`
   (34 verbs × four legs), `tui_screen_router.rs` (runtime half; the compile-time
   half already stood). The fourth, the one-renderer test, belongs to **stage 6**
   by PLAN §4's own row.

Beyond the scope list, stage 3 also made the JSON edge the kernel's own (J0–J6,
`c2ad8f6`..`b7f504d`, a new module, `Json.lean`), taught the loader that an HTML
comment is prose (`a4ccd9c`, `LErr.unterminatedComment`), and fixed the bridge's
newline handling (`e5d38b8`).

**Spec sections.** §13 (CLI), §12 (TUI wiring only), §4.1/§4.3 as far as the
loader already reads, §6.3's `move`/`readopt`/`demote`/`drop` rows, §17.2.

**Modules touched, as it turned out.** `Boundary.lean` (dispatch, `ReqCmd`,
`parseCmd`, `run`, `respond`, schema), `Cmd.lean` (`rank`, `add`'s
`insertFresh`, the keyed `edit`), `Plan.lean` (`normalized` preservation, the
comment rule), `Line.lean` (the parse ⇒ wf bridges), `Text.lean` (`freshId`,
`joinWith_splitOn`), **one new module, `Json.lean`** (imported at `c2ad8f6`, §2.3),
`Check.lean`, `Negative.lean` and `Goals.lean` by the conventions, all of
`kernel/tm-kernel-ffi/`, and the restored `tm-core/` and `tm/` (the bridge, the
CLI tests, the templates).

**Depends on.** Stage 1's `WfPlan`/`mapAt`/`resolveDest`/`Dest`; stage 2's parser
and `loadPlan`. Nothing in stage 4 blocks it.

**Acceptance, as it now stands.** The plan's clauses are measured by the two
suites of §7.5 (both capped): `check.sh` 7/7 and `cargo test --workspace` green,
with the panic probe and the seven verbs' refusal-by-name tests inside the
latter. Plus, unchanged: check 6 must not regress, and
`corpus/round-trip.expected` must move forward and never be reblessed downward.
(The one authorised exception: D6's redefinition of a `file` row as the file
inside its plan's whole-tree load, stage 4 final step 3 — §7.1, check 6.)
The Rust half is no longer owed; the items under "Still owed" below are.

**Goals this stage owned — all twelve gone from `Goals.lean`, each by a named
route, plus the two provisional signatures replaced** (`cmdRank`, `freshId`):
`add_assigns_a_fresh_id` (L21) proved, `dcf35dc`; `rank_is_idempotent` and
`rank_preserves_the_order_of_the_others` proved, `1d4fc14`;
`move_has_an_inverse_command` (L22) **refuted** as `move_has_no_inverse_command`,
`378fdf9`; `the_json_edge_round_trips` **narrowed**, as its doc comment licensed,
to `the_response_call_emits_parses_back`, `b7f504d` (the original was stated over
`Lean.Json`'s `partial def`s and could be neither proved nor refuted);
`the_char_edge_round_trips` proved, `d61fece`;
a_file_splits_into_the_lines_it_was_joined_from restated over the kernel's own
`Tm.splitOn` and proved as `a_file_splits_into_the_lines_it_was_joined_from_char`
(`Text.lean`, audited in `Check.lean`), and `joining_lines_is_injective`
**refuted** as `joining_lines_is_not_injective_char`, both `a6dcc96`;
`the_loader_builds_sites_in_range` and `the_loader_builds_oriented_demotions`
proved, `9812dd9`; `the_loader_builds_a_normalized_plan` proved, `6f32f41`;
`the_command_path_writes_what_the_field_path_reads` proved, `7af7f1a`. Where a
statement was restated rather than proved as written, the README block says why
by name; the host-agreement obligations those restatements leave (Rust's
`split('\n')` and serde_json agreeing with the kernel) are **evidence** — the FFI,
corpus and CLI suites — never a theorem.

**Still owed from stage 3, by name** — each recorded in `kernel/README.md`:

- **Gap 48** — the host's `KERNEL_EDIT_KEYS` (`tm/src/cli/items.rs`) does not
  route the eight newly wired keys; `tm edit ^id due=…` still runs the fork-point
  Rust. The next host step, with **gap 50** (every other plan-tier edit refusal
  is still `badHorizon`) beside it.
- **Gap 51** — `∀ v : EditVal, wordWf v.rendered = true` is proved for `loc`,
  `est`, `ci` only; the edit's re-read is evidence for the rest. Priced as stage
  3's closing theorem.
- **Gap 49** (the edit is narrower than the loader in two named places), **gap
  41** (unset of `est`/`ci` clears the key slot only), **gaps 42 and 43**
  (surrogate pairs refused, leading zeros accepted), **gap 47** (a `planWf`
  conjunct no wire input can fail) — decisions recorded, no stage named as
  owing work unless a host or a user needs it.
- **Gap 44** — `jparse`'s and `jemit`'s per-element recursion has no runtime
  twin; the ~21 500-element bound on a 2 MiB stack is the one `splitDoc` already
  had, but a request with that many *documents* newly aborts.
- **Gap 45** — `tm-core`'s parser is comment-blind, so `tm check`/`tm plan` and
  the kernel disagree about a column-0 item inside `<!-- -->`; **gap 46** — the
  comment rule's narrow edges (generated-block interiors, indentation).
- **`now` in the request** — stage 3's item 5; stage 4 adds it.
- **The oracle** — `examples/oracle/` still extracts `main`; it must move to
  `4748911` (§7.3).
- **The depth-3 sweep** — `invariant_exhaustive.rs` lived only on `main` and was
  discarded with it; §9.1's most consequential gate now needs a harness rebuilt,
  not merely run.
- **The human's 30-minute drive** of the stage-3 binary (§5.13).
- **Housekeeping writes precede a kernel refusal** — on a stale tree the
  fork-point day-close catch-up writes before the command's own kernel call is
  refused; stage 4 territory, recorded not fixed. *Status (stage 4 step 6): the
  automatic close is one kernel call and writes nothing when refused; its
  successful writes still precede the verb's own call.*
- **Two newline conventions** — the bridge normalizes rewritten files to a final
  newline, legacy writers do not; retires as stages 4 and 6 and gap 5 retire the
  legacy writers.
- **The `Negative.lean` renumber** (§6.2, §6.5) and **`tm/DORMANT.md`**, whose
  text still says the rewiring is "underway".

**Named traps — kept, each with its status at `bf7cc63`.**

- **The old blocker is gone; read the new one.** Until `8eea3d6` three of five
  fixture trees failed to load whole with `splitLine: m2`, and this trap said so.
  That landed: `Core.archive` is a `Tomb` carrying its own bytes, so a pair whose
  two lines **legitimately differ** renders; `orientPair` is lexicographic — the
  `[-]` line is the tombstone and horizon order is the tie-break only when both
  are `[-]` — and `LErr.splitLine` is deleted. The corpus went `1/5` → `4/5`.
  A binary kernel-backed for the lifecycle verbs can now load a real tree.
  *Status: closed before this stage began, and confirmed by the shipped binary
  loading real trees.*
- **What that opened, and it is stage 3's to decide: the kernel asks only whether
  the box is `[-]`** (gap 31). `tree.rs`'s `is_archive_copy` also constrains
  *where* a `[-]` may be an archive copy — a week file, or a `month/…# Demoted`
  section, and nowhere else. So a `[-]` in `backlog.md` paired with a `[ ]` in a
  week file loads here as a demotion and is a **duplicate id** to `tm`. Nothing
  in the corpus is in that state and no kernel command can reach it, but
  `planWf` is supposed to be no weaker than `tm check` and on this predicate it
  is. Closing it needs a placement's *section* to reach the plan tier. It is a
  behaviour change, so it is recorded rather than taken — and stage 3 is where a
  real host starts sending real trees. *Status: **open**, not decided this
  stage; §10.5 q9 carries it to the human.*
- **A tombstone's bytes are checked by the parser and by nothing else** (gap 31,
  second half). `itemsWf`'s field-derived conjuncts all read `Core.line`, so
  `- [-] 1 1b T after:^m1 ^m1` is `itemCheck: depCycle` standing alone and `ok`
  as the archive half of a pair. That matches `tree.rs`, which walks `n.primary`
  only, and it is the behaviour you want for a frozen record — but know it before
  a user reports it. *Status: open, unchanged.*
- **`tm undo` must replay the log.** L4b is refuted by
  `move_back_at_a_fresh_rank_is_not_the_inverse`: the wire form carries a
  document, not a rank, and the rank is generated fresh. An undo built as "apply
  the inverse command" is wrong by a compiled theorem. *Status: now general —
  `move_has_no_inverse_command` (`378fdf9`) refutes every inverse over all seven
  command shapes. Which side replays the log is still §10.5 q4.*
- **The response must carry each document's region back.** A host that drops
  `grain`/`ix` on the way back makes its own next request unloadable
  (`ambiguousDemotion`). The FFI test
  `the_response_carries_each_documents_horizon` guards it. *Status: closed
  host-side, `d8e8d4d` — the bridge keeps every returned region on `BridgeDoc`,
  checks it against what it declared, and refuses to write on a mismatch.*
- **Nothing ties a `Doc`'s declared region to its path** (gap 10). A
  host may send `{"path":"week/2026-W37.md","grain":1,"ix":35}` and the kernel
  believes it, while the true ISO week ordinal of 2026-W37 is 105695 — and the
  FFI fixtures do exactly this. The gap names it "the obvious place for the next
  boundary bug", and stage 3 is where the host starts generating those numbers
  for real. *Status: mitigated, not closed — the host generates the kernel's own
  numbers and a compiled test pins them (`regions_are_the_kernels_numbers`), but
  the kernel still checks nothing.*
- **A panic probe needs something that can panic.** The kernel is total by CI, so
  there is no reachable panic. The probe must be constructed — a deliberately
  faulting build, or a shim-level injection returning a non-JSON string — and it
  must test the *host's* reaction, not the kernel's. *Status: closed, `dd89bc6` —
  `the_panic_probe_faults_loudly_and_writes_nothing` and
  `a_kernel_fault_propagates_and_a_refusal_stays_a_message`.*
- **Two `est` readers sit on exactly the command path** (gap 4).
  `Core.est` is the field-level `viewRemainingDur`; `Cmd.setEstE` and the
  boundary's `est` go through the stage-one `Nat` reader `viewRemaining`, which
  does not read `NhMm` or `Nd`. This is the S2 shape, in the code stage 3 ships.
  *Status: closed, `7af7f1a` — `the_command_path_writes_what_the_field_path_reads`.*
- **A tab is not a separator, and neither is a second space**
  (gap 32). `Text.isSp c := c == ' '`. Measured: 1,049 of 2,048
  generated lines are silently prose to the kernel. And it already reaches a
  shipped operation — on a line with a tab before a repeated `est:`,
  `tm edit est=45m` writes the *first* `est:` in the Rust (documented: first
  occurrence wins) and the *second* in the kernel, because the kernel cannot see
  the first. **The kernel is on the wrong side of the bug the rebuild exists to
  make impossible, in the same operation.** Do not ship kernel-backed `edit`
  without fixing this or refusing tabbed lines loudly. *Status: the edit hazard is
  closed by refusal, `a2e0dc2` — every edit-path command refuses a tabbed line as
  `tabbedLine` (`edit_of_a_tabbed_line_is_refused`,
  `the_tab_guard_is_not_vacuous`); `add` refuses a tab in a title. Gap 32 itself
  (`isSp`) stays open and plan-tier.*
- **Every `^`-leading word is an id** (gap 33). A bare `^` names
  the empty id; `^%` names `%`; a corpus line is refused as `manyIds` where the
  shipped parser reads `q7`. *Status: open, unchanged.*
- **Routines and optional items are invisible** (gap 5). §4.1 says
  `routines.md` and `optional.md` omit the state box; `parseItem` requires
  `- [<glyph>]`, so those lines are prose. The seven verbs cannot address them.
  Fixing it needs a `RawItem` that records whether the box was there — a type
  change across `State`/`Plan`/`Cmd`/`Boundary`. *Status: open; the host keeps
  every id-less line on the old Rust path, by name.*
- **`Id`'s shape is a human decision** (gap 13, plan §6.2 q2). §3.1 says
  4 chars of `[a-z0-9]`; the Rust enforces nothing; the spec's own fixtures ship
  `^O1`. The recorded resolution is *weaken the spec, not tighten the data* — but
  only a human can tell that case from the case where the type is right.
  *Status: **decided** by the owner, 2026-09-12 (§10.5 q2): ids stay digits, and
  spec §3.1's width sentence is weakened.*
- **The JSON/string edge is the only unproved step on the text path**
  (gap 12; gap 34 measures it and does not close it).
  A request line containing a literal newline round trips as one line in the
  kernel and becomes two on disk, and nothing notices. *Status: both kernel
  halves are theorems — the split at the char level (`a6dcc96`) and the JSON edge
  (`b7f504d`, with `Lean.Json` off the wire). What remains is host agreement,
  evidenced, and gap 12's live remainder: the kernel still accepts a doc line
  carrying a literal newline (the bridge never sends one — it splits on `'\n'` —
  and `add` refuses one in a title).*
- **The depth-3 sweep in the stop condition does not exist and may not be
  affordable.** `invariant_exhaustive.rs` has depth 1 (199 commands) and depth 2
  (39,601 pairs, `#[ignore]`d at ~10 minutes). Depth 3 over the same alphabet is
  7,880,599 triples — ~199× the depth-2 work, order tens of hours. This is the
  most consequential decision gate in the whole plan (§9.1) and it is gated on a
  harness nobody has costed. Narrow the alphabet, or state a different gate.
  *Status: worse — the harness itself was discarded with `main`; it must be
  rebuilt before it can be costed.*

**Inherited debt, re-sorted.** Closed during stage 3: gaps 4, 13 (by decision),
14 (the shipped binary calls the kernel), 16, and the kernel halves of 12 and 34;
37–39 were blockers or pricings of those and are superseded by name in the
README. Still open and inherited by later stages: 5, 6, 7, 9, 10, 12's newline
remainder, 15, 17, 31, 32, 33, 34's host half, 35, 36 (the oracle, now broken),
and the stage's own 40–51 as their paragraphs price them.

---

### 8.2 Stage 4 — `close`, `autoClose`, `ClosePolicy`; L16–L19

> **Plan acceptance.** Close idempotent at library *and* CLI level; a 3-month-stale
> tree catches up losing nothing; the two behaviour changes landed with assent.
> Cost: 2–3 wk. Worth alone: §6.3 becomes one operation at three grains;
> F1–F4 and F6 covered.

**Status at stage 4's close (2026-09-13, `10bae51` plus the closing docs commit).**
All four scope items are landed and the stage is closed with debts, by name.
*What landed, by step:* (2, `50f11e3`) `Close.lean` — `ClosePolicy` tabulated by
`Grain`, `close` as one fold into `closeTo g now`, `close_spec`;
`close_day_stamps_a_day_stamp` discharged. (3, `b605bfe`) `close_is_idempotent`
(L16) as stated; L17 and L27 refuted and renamed
(`close_week_and_close_month_do_not_commute`, `lifecycle_commands_do_not_commute`).
(4, `41792e8`) `autoClose` is each grain's close once, coarsest last; L19a and L19b
as stated, L19c refuted (`autoClose_leaves_lines_in_periods_it_passes`) beside
`autoClose_strands_no_unfinished_line`. (5, `d7487b2`) `Report.lean` — D3's
per-item list under `ok.report.closes`, tied to the close by `closeReport_ids` and
`closeReport_agrees_with_close`; `now` and `blockMin` on the wire. (6, `5557713`)
`tm close` and the automatic close are kernel-backed (`tm/src/cli/closing.rs`);
`AUTO_CLOSE_CATCHUP = 16` is deleted. (7, `210daad`) the last three over-strong
goals refuted and renamed, each with its narrowed law
(`close_leaves_no_line_it_would_take`, `close_never_demotes_a_wall_but_may_carry_it`,
`close_rewrites_a_line_only_by_stamping_it`, `close_keeps_every_remaining_estimate`).
(8, `ea08382`) gap 59 closed — `close_keeps_source_order`. (9, `10bae51`) gap 20's
remainder — the `demote` verb files into `# Demoted` through the close's landing;
new gap 60. Ten of the stage's eleven goals are gone from `Goals.lean`, each with a
proof of its statement or of its negation; burn-down 40 → **30**.

*What the acceptance measures, clause by clause:* "close idempotent at library
level" is `close_is_idempotent` on `WfPlan`; "at CLI level" is
`closing_twice_changes_zero_bytes_the_second_time` through the built binary
(`tm/tests/cli_close_kernel.rs`); "a 3-month-stale tree catches up losing
nothing" is `autoClose_catches_up_in_one_step` in general, decided on a loaded
plan (`the_stale_tree_catches_up_in_one_call`), pushed through `String → String`
(`a_three_month_stale_tree_catches_up_in_one_call_and_reports_each_line`) and
through the binary (`a_three_month_stale_tree_catches_up_losing_nothing`, 1005
minutes before and after); "the two behaviour changes landed with assent" is one
change, D1, taken by the owner after driving stale trees. *What it does not
measure:* §4.3's own example week still refuses its week close (gaps 53, 55); a
close writes no `est:` (gap 54); the human's 30-minute drive (§5.13) has not
happened.

*What remains, by name:* B3 `close_week_folds_a_dropped_child_into_its_parent`
(waits on §10.5 q3 / gap 22, the owner's) *— superseded: refuted and renamed at stage 4
final step 4, below*; gaps 52 (deferred, no consumer), 53, 54
(stage 5), 55 (stage 5 and an owner decision), 56 (kernel half: gap 10), 57
(gap 10), 58 (stage 5's `cfg`), 60 (q9, the owner's), 61 (the host's old id
generator), 62 (a kernel call over a history-sized tree takes about a minute —
the automatic close's gate is load-bearing) and 63 (`tm check` does not name a
line a close would take); §6.3's overdue routing (stage 5) and F3 (stage 6); the
human drive. *Repaired after the close* (README "Stage 4 repair"): the automatic
close's gate was `state.closed` alone, so a tree the fork-point binary had stamped
current kept its stranded lines; it is now `closing::due` — behind, or no kernel
sweep yet (`state.closed.swept`, which the fork-point binary drops on write).
**The proof-to-definition ratio is measured, and the §9.1 stop condition fires:**
4.49 : 1 over the library, 6.43 : 1 in `Close.lean`, 5.63 : 1 in `Report.lean`,
4.56 : 1 over everything stage 4 added — the owner decides before stage 5 whether
to stop proving relational laws. Method, script and every figure: README
"Stage 4 closed".

**Status after the owner's decisions (2026-09-13, D5–D8; README "Stage 4 final").**
Stage 4 is reopened for one goal and one gap. **B3 is unblocked:** D6 turns parents
on, so `close_week_folds_a_dropped_child_into_its_parent` can fire; under spec §6.4
its additive statement double-counts and is expected to be refuted and renamed, with
fork-point `horizon.rs`'s `max(remaining(parent), Σ dropped children's own
remaining)` proved beside it. **Gap 55's two halves are decided:** the past-due half
by D7 (a move to `backlog.md # Overdue`, pulled forward from stage 5, the week row's
`overdue := .stage5OnMiss` made real), the not-yet-due half by D8 (demoted like any
unfinished line, `due:` kept; `shapesWf`'s month rule covers outcomes only). D5
means each landing re-proves the two-run laws it breaks (L16, the L19 theorems,
`close_keeps_source_order`, the report agreement) in the same step.

**Gap 55 closed (stage 4 final, step 2; README "Stage 4 final, step 2").**  The week
row's fourth action moves a past-due `persist` line to `backlog.md # Overdue`, box,
bytes and tombstone kept, under the heading (`close_week_moves_a_past_due_persist_line_to_the_backlog`,
`close_lands_every_overdue_line_under_overdue`); a not-yet-due one is demoted keeping its
`due:` (`close_week_demotes_a_not_yet_due_line_keeping_its_date`) over D8's
`demotedRecordPlacement`.  The host hands over `backlog.md` with `# Overdue` appended
when absent (gap 56's overdue half, closed).  L16, `close_keeps_source_order`, the L19
theorems, the report agreement and `move_has_no_inverse_command` are re-proved with
their statements unchanged.  §4.3's literal tree closes on its first command a week
after its week.  Stage 4 has B3 left, and B3 waits on D6. *(Superseded: D6 landed at
step 3, B3 at step 4 — next paragraph.)*

**B3 closed; stage 4 at zero (stage 4 final step 4, 2026-09-13; README "Stage 4 final,
step 4").**  §6.3's week row now drops an unfinished child of a line it files from the
same week file: `[~]` in place (the fork point deleted the line; the kernel removes no
entity, `close_dom`), no stamp, no record, no event, and its own remaining floors the
nearest filed ancestor's record by §6.4's `max` — the table's `children := .dropIntoParent`
(`closePolicy_drops_children_only_at_week`).  The additive goal is refuted exactly as
stated (`close_week_does_not_add_a_dropped_child_to_its_parent`: a `6b` milestone with a
dropped `1b` subtask carries 300 minutes, not 350); beside it
`close_week_folds_dropped_children_by_max`, both directions
(`close_week_lifts_a_parent_its_dropped_children_outweigh`,
`close_week_keeps_a_parent_that_covers_its_dropped_children`), the child's side
(`close_week_drops_a_child_with_its_parent`,
`close_week_keeps_a_dropped_childs_remaining_in_its_parents_record`), non-vacuity, cheats
62–66, FFI `a_week_close_folds_dropped_children_on_the_wire` and CLI
`a_week_close_folds_dropped_tasks_into_their_milestone_by_max`.  The fold needs the block
length, so `close g now bm` and `autoClose now bm`.  The report has nine dispositions
(`dropIntoParent`, `copyFolding`, `copyMergingFolding` added).  **Two-run laws (D5):**
`close_is_idempotent`, the L19 theorems, the commute refutations,
`move_has_no_inverse_command` and `close_spec` keep their statements but for `bm` (and, in
`stepSkel`, the fold's argument); the report agreement is extended over the three new
dispositions; **`close_keeps_source_order` and `_iff` gained one hypothesis**, `hfold` (the
two lines agree on whether the fold drops them), because the statement as it stood is false
under §6.3's child rule — a dropped child and its filed parent, taken by one action from one
file, end in different files — and that is proved
(`a_dropped_child_and_its_filed_parent_part_ways`).  Twelve single-run names were retired,
each refuted where it is not a helper and restated beside its narrowing.  New gaps: 72 (a
dropped child's record is not carried by the month close), 73 (no §6.4 rollup or
`MIN_REMAINING_MIN` under the fold; `dur:`-only children count 0), 74 (a wall's prep children
are demoted, not carried with the wall — the step-2 scope-out gap 22 closed without taking).
Burn-down **29** (stage 4: 0).  Proof : definition **4.80 : 1**.

**Scope, concretely.**

1. **One fold, three grains.** Fold over
   `{ i ∈ dom | the live site is in a region of grain g that is Closed at now }`,
   applying `demoteEst` into `closeTo g now`, subject to `ClosePolicy g`.
2. **`ClosePolicy`, a typed table indexed by `Grain`** — §6.3's residue:
   copy-vs-move disposition, the `backlog.md#Overdue` target, child folding,
   stamp accrual, exemptions. This is a **tabulate**, not a derive (§5.5), with a
   compile-checked bridge.
3. **`autoClose` collapses to one step per grain, coarsest last.** Because
   `closeTo` targets *now* rather than the successor, the Rust's 16-period
   iteration disappears and F1 becomes a `none`-vs-`some` case in one place.
4. **`now : Day` must enter the request.** §10.2's `closed` map stays Rust's.

**Spec sections.** §6.3 (all three rows), §6.2 (candidate set, and the "outcome
with estimate" warning), §4.2 (`# Demoted`, `# Pinned`), §6.4's child-folding
clause, §10.2, §5.3 in part.

**Modules touched.** `Grain.lean` (already has `closeTo`, `Closed`,
`targetContaining`, `horizonPrecedes`), `Cal.lean`, a new `Close.lean` or an
extension of `Cmd.lean`, `Plan.lean` (the fold; `ClosePolicy`; the `sectionsWf`
interaction), `Boundary.lean` (`now`, the close ops, the report), `Check.lean`,
`Negative.lean`, `Goals.lean`.

**If you take the `Close.lean` option, add `import TmKernel.Close` to
`kernel/TmKernel/TmKernel.lean` in the same commit** — after `Plan.lean` and
before `Cmd.lean` if `Cmd` consumes it. Without the import the file is not
compiled, is not in `libTmKernel_TmKernel.a`, and `close` is unreachable from
Rust while all seven checks stay green (§2.3).

**Goals this stage owns** — 11 in `Goals.lean` under `# STAGE 4`, plus the
provisional `close` and `autoClose` signatures: `close_is_idempotent` (L16),
`close_leaves_no_live_line_in_a_closed_region`,
`close_week_and_close_month_commute` (L17, **expected refutation**),
`autoClose_is_each_grain_once`, `autoClose_catches_up_in_one_step`,
`autoClose_runs_every_period_it_passes`, `close_never_demotes_a_wall`,
`close_writes_every_estimate_through_demoteEst`, `close_day_stamps_a_day_stamp`,
`close_week_folds_a_dropped_child_into_its_parent` (B3), and
`lifecycle_commands_commute` (L27, expected refutation). B3 **cannot fire** until
gap 22's `Core.parent` decision is taken — that is a precondition of this stage,
not a discovery inside it. *All eleven are gone at stage 4 final step 4; B3 was the
last, refuted and renamed (above).*

**`report` needs a shape before you write one.** §2.4: the response has no
`report` key, no type and no constructor anywhere in the kernel, and both this
stage and stage 6 list it as a deliverable. Whatever shape it takes must satisfy
four rules this document already enforces, so settle it here rather than letting
stage 6 inherit an accident:

1. it is a value under `ok`, beside `docs` — a host that gets `err` gets no
   report;
2. every field is a bounded type with a smart constructor its decoder uses (R10),
   because `Diagnostics` is nine families and `Segment` eleven variants by
   stage 6 and forgetting it on one type silently reopens the hole;
3. every entry is **named** the way `LErr` and `firstItemFault` are (§5.7) — a
   refusal you can name is a finding;
4. it emits integer numerator/denominator pairs and never divides (§8.4).

It is open question 8 in §10.5, because "what a close reports" is a product
decision, not a proof. *Answered 2026-09-12 (§10.5 q8): a per-item list — id,
disposition, destination, stamp, minutes as integer numerator/denominator — not
counts only, and not stage 6's full diagnostics surface yet.* The four rules
above still govern its shape. **Landed:** `Report.lean`, `d7487b2` (`closeReport_ids`,
`closeReport_agrees_with_close`).

**Depends on.** Stage 1, all built and compiled: `coarsen_month = rfl`,
`closeTo_target_is_open`, `demotion_target_follows_the_closed_region`,
`horizonPrecedes_asymm`, `demoteEst` with `demoteEst_conserves` /
`demoteEst_respects_user`, and `Field.Stamp` knowing `W37` from `D07`. Depends on
stage 3 only to *ship*, not to prove.

**Acceptance, and how to satisfy it on this branch.** The plan's acceptance is
*"close idempotent at library **and CLI** level; a 3-month-stale tree catches up
losing nothing; the two behaviour changes landed with assent"*. Two of those
three clauses need a binary. When this was written the branch had none; since
`835d960` it has one (§2.2), so the split below is now a sequencing, not a
blocker. Do not let it become an excuse:

- **Library level, here, now.** `close_is_idempotent` on `WfPlan` is the L16
  goal. The stale-tree clause becomes a corpus-shaped fixture pushed through the
  `String → String` boundary by a `tm-kernel-ffi` test — the same instrument as
  check 6 — asserting the item count and the summed `est:` are unchanged.
- **CLI level.** The restore this clause waited on has landed (from `4748911`,
  not `main`, §8.1), so the CLI clause is owed **in this stage**, through the
  bridge, against a stale fixture tree — and until `close` is kernel-backed the
  fork-point Rust close still runs as housekeeping ahead of every command (§8.1's
  "Still owed"). Do not restate the library result as the CLI one.
  *Status (step 6): landed — `close` is kernel-backed and the CLI clause is
  tested through the built binary (`tm/tests/cli_close_kernel.rs`).*
- **The behaviour changes need a human**, and the plan's instruction is literal:
  construct a stale tree and close it before deciding. *Done 2026-09-12*: the
  owner drove stale trees with the restored binary and decided (a); (b) turned
  out not to be a behaviour change at all — see the first trap and §10.5 q1.

Plus the corpus ratchet, plus 30 minutes driving whatever binary exists (§5.13).

**Named traps.**

- **One close behaviour change, decided; the second one never existed.**
  PLAN §3.2 and §6.2 q1 named two, both read off line citations and not observed
  by running the binary. **(a) `close day`'s target is decided** (D1, 2026-09-12,
  after the owner drove stale trees with the restored binary): the week
  containing *now* — the kernel's `closeTo day now` — not the week the closed day
  belonged to (`targetContaining`, fork-point `horizon::close_day`). The stamp
  stays `demoted:D<dd>`, and `AUTO_CLOSE_CATCHUP = 16`'s period-by-period
  iteration collapses to one step per grain. The generalised statements are
  compiled — `impl_rule_disagrees_iff` and
  `containing_targets_a_closed_region_iff` say the two rules differ, and the
  Rust's target is already closed, **exactly when the coarser period rolled over
  in between** — so this is a fact about closing late, not one witness.
  **(b), "week→month is the Thursday's month, not the month of today", is not a
  behaviour change and is withdrawn:** fork-point `horizon::close_week` files its
  `# Demoted` copy into `YearMonth::from_date(cx.today())`, which **is**
  `closeTo week now` (checked by `decide` on four dates, stage 4 step 1), and
  `closeTo week now` is even `rfl`-equal to `monthOfWeekByToday w now` — one
  month in two roles, right as a close destination and wrong as a name.
  `monthOfIsoWeek` / `monthOfWeek` is a naming tie-break with **no consumer**,
  and `Grain.closeTo_week_is_not_monthOfWeek` keeps the roles apart. Do not
  reopen (b) as a close-rule change. The residual, smaller question — *which
  month file a week's `# Demoted` record belongs in* — has no consumer either and
  is **deferred out of stage 4** by name (README stage-4 block). Repaired at
  stage 4 step 1: this bullet, §10.5 q1, `Cal.lean`'s header; the README
  supersedes its own cheat row 24 and tie-break section by name.
  **Closed:** D1 recorded at `d615bd1`, built at `50f11e3` (`close` targets
  `closeTo` at every grain), shipped at `5557713`; `Goals.lean`'s `# STAGE 4`
  header reads "two" as one since the stage's closing docs commit.
- **If assent is refused, L16 may not be provable.** The idempotence argument is:
  after the fold, no entity's live site is in a closed region of grain `g`, so
  the second run folds over the empty set — which is `closeTo_target_is_open`.
  With `targetContaining`, the fold's own output can be back in scope and the
  proof does not go through. Record it as a stop point, not a surprise.
  *Status: assent was given for (a) (D1), so the `closeTo` argument is the one
  L16 gets.* *Proved at step 3. For one grain the old rule would have broken it
  at month only; at day and week it breaks across grains (L19b) — README
  stage-4 step-3 block, read off the definitions.*
  **Closed:** `close_is_idempotent`, `b605bfe`.
- **L17 is an expected refutation, and a refutation is a deliverable.**
  `close week ∘ close month` is not expected to commute. *Refuted at step 3 —
  through rank in the shared `# Demoted`, not through one close seeing the
  other's output, which D1 rules out.*
  **Closed:** `close_week_and_close_month_do_not_commute`, `b605bfe`.
- **Four stage-4 goals are stated stronger than §6.3 allows**, and the repair is
  refute-and-rename (§3.2), never a weakened predicate:
  `close_leaves_no_live_line_in_a_closed_region` and
  `autoClose_runs_every_period_it_passes` quantify over settled, recurring and
  wall lines §6.3 leaves in place; `close_writes_every_estimate_through_demoteEst`
  equates the whole line and so forbids the `demoted:` stamp;
  `close_never_demotes_a_wall` forbids the carry fork-point `close_week` performs.
  Priced, with L17's and L27's expectations, in the README's stage-4 block.
  *All four refuted and renamed: `autoClose_runs_every_period_it_passes` at step
  4, the other three at step 7 (README "Stage 4 step 7"), each on a loaded plan
  with its narrowed law beside it.*
  **Closed:** `41792e8` and `210daad`.
- **`demote` must learn to target a *section*** (gap 20). §6.3 files the
  copy into `month/<current>#Demoted`; today `demote` lands it at `freshRank`.
  This changes `demote`, its `normalized`-preservation lemma, and `sectionsWf`.
  §6.2's "outcome with an estimate is a `tm check` warning" is unimplementable
  until then, because the two-line demotion form this kernel writes would trip it.
  *Status (step 2): landed for `close`'s week row (a rank shift makes room in
  `# Demoted`); the `demote` wire verb still lands at `freshRank`, `sectionsWf`
  is unchanged (§10.5 q9), and the warning still needs `parent` (gap 22).*
  **Closed for both writers:** the close's week row at `50f11e3`, the `demote`
  verb at `10bae51` (`demoteSpot_is_the_week_close_landing`). Still open, by
  name: `sectionsWf` does not demand a `[-]` sit under `# Demoted` (q9, gap 60),
  and the §6.2 warning waits on gap 22.
- **Stage 4 *is* the code that writes the legitimately-differing pair**
  (gap 31). The named fix is a second `RawItem` on `Core` for the
  tombstone, set by `demote` and cleared by `readopt`, with `renderCore` reading
  it at the archive site — and `orientPair` needs a glyph clause, with
  `demotionsOriented` changing alongside it because it is part of `planWf`.
  *Status (step 2): subsumed — that `RawItem` is `Tomb.line`; `close` writes the
  differing pair through `demote`, and neither `orientPair` nor
  `demotionsOriented` changed.*
  **Closed:** subsumed at `50f11e3`.
- **Backlog orientation is fine, and here is why.** `horizonPrecedes (some _)
  none = true`, so every bounded region precedes backlog: a close that files
  overdue work into `backlog.md#Overdue` leaves the tombstone (in the week)
  legitimately preceding the live line (in backlog). `demotionsOriented` will not
  refuse it. Worth knowing because the opposite is the natural guess.
  *Not exercised at stage 4:* no close files into backlog yet, because the
  overdue routing is scoped out to stage 5 (next trap).
- **Two rows of §6.3 need things stage 5 owns.** "Dated items past due with
  `persist` → `backlog.md#Overdue`" needs `due:` evaluation and §5.3's `on_miss`;
  "unfinished children are dropped, their remaining folded into the parent's
  `est:`" needs §6.4 rollups, which need `parent`, which is always `none`. Either
  pull them forward or scope them out **by name** in the README.
  *Status (step 2): scoped out, and visible in the table itself — the week row's
  `overdue := .stage5OnMiss` and `children := .gap22Parent`.*
  **Open by name at the stage's close:** stage 5 (`on_miss`) and gap 22 (B3).
  *Stage 4 final: the overdue row landed at step 2 (D7) and `parent` at step 3
  (D6, gap 22 closed; the column is `children := .childFoldB3`). B3's fold is what
  is left.* **Closed at step 4:** `children := .dropIntoParent`, the fold by `max`
  (`close_week_folds_dropped_children_by_max`). Still open by name: fork-point
  `close_week`'s carrying of a wall's prep children (gap 74) and the overdue route's
  effective shape (gap 68) — both need `closeAct` to read the tree.
- **F3 is missed until stage 6.** `close day` replacing a written review with
  `review pending` needs generated-block ownership. Stage 4 covers F1, F2, F4, F6
  — do not claim §6.3 complete.
  **Still open:** F3 is stage 6's. F6 is covered only in part: a close loses
  no estimate (`close_keeps_every_remaining_estimate`, `210daad`), but writes no
  `est:` = remaining (gap 54, stage 5).
- **Recurring items and calendar intervals are never demoted** (§6.3's last
  paragraph). That is a `ClosePolicy` exemption.
  **Closed:** `closePolicy_exemptions` (`50f11e3`) and
  `close_never_demotes_a_wall_but_may_carry_it` (`210daad`), which covers
  recurring lines as well as walls.
- **`demote` is deliberately not idempotent**, because the month review's cut
  list is "≥ 2 stamps" and stamps accumulate on purpose. The stamp must reach the
  file — see §5.3 for the bug where it did not.
  **Closed:** `close_day_stamps_a_day_stamp` (`50f11e3`) and
  `close_rewrites_a_line_only_by_stamping_it`; within one catch-up,
  `autoClose_stamps_each_line_at_most_once` (`41792e8`).
- **Two idempotences must not be conflated.** §6.3's "runs automatically on the
  first command after the period ends (idempotent; recorded in `state.json`)" is
  a Rust fact about a `closed` map. L16's `close g` idempotence is a fact about
  the fold on `WfPlan`. Only the second is a kernel theorem.
  **Kept apart:** L16 is `close_is_idempotent` (`b605bfe`); the Rust half is the
  binary test `closing_twice_changes_zero_bytes_the_second_time` (`5557713`), a
  test and not a theorem.

**Inherited debt.** Gaps 2, 3, 16, 17, 20, 22, 31. *At the stage's close:* 20
closed for both writers (`50f11e3`, `10bae51`), its `sectionsWf` half now gap 60;
31 subsumed (`50f11e3`); 22 still the owner's (q3).

**One thing stage 4 owes stage 5.** Measure the proof-to-definition ratio at the
end of this stage and write it in the README. It is a stop-condition trigger
(§9.1) and stage 5 needs it before it starts.
**Measured at stage 4's close, and the trigger FIRES** (README "Stage 4 closed",
with the script): proof : definition is **4.49 : 1** over the twelve library
modules (4.44 : 1 with decided witnesses and their fixture data taken out of both
sides), **6.43 : 1** in `Close.lean`, **5.63 : 1** in `Report.lean`, and
**4.56 : 1** over every line stage 4 added. It was already **4.48 : 1** when stage
4 opened (`a8bb800`), so the plan's 1.09 : 1 had not described the kernel for some
time. §9.1's action is not an agent's to take quietly: the owner decides, before
stage 5 starts, whether stage 5 stops proving relational laws and keeps decidable
checkers plus the existing proptests.
*Taken 2026-09-13 (D5): keep proving. Re-measured at stage 4 final step 4:
**4.80 : 1** (18,815 : 3,917), 9.36 : 1 in `Close.lean`, 6.22 : 1 in `Report.lean`
— recorded, gating nothing (§9.1).*

---

### 8.3 Stage 5 — `recur`, rollups, `priority`, `capacity`, exact arithmetic

> **Plan acceptance.** Parity harness: kernel vs Rust over the fixture corpus
> agrees except at the six stated rounding sites. Cost: 3–4 wk. Worth alone:
> floats leave the decision path; D1/D2 and E7 covered.

**Scope, concretely.**

1. **Recurrence.** One denotation `Log → Instant → Option Occurrence`, with all
   four `Recur` constructors kept as **syntax** — a function is not
   serialisable, not `DecidableEq`, and not writable in a Markdown line, and §0
   says the Markdown is the database. The yield is one classification theorem
   (`calendar_is_history_independent` vs `afterDone_is_history_dependent`) and D1
   as a postcondition on instance selection.
2. **Rollups (§6.4).** `remaining`, `done_minutes`, `progress` as integer
   numerator/denominator pairs — **the kernel emits numerator and denominator;
   Rust divides.** Plus the prep derivation: children of an Interval with no
   shape become `Point{due: parent.start}`.
3. **Priority (§7).** `k = root_priority`, `need = remaining × safety`, the EDF
   pass with reservations, the bin ladder, §7.2's rule table, hysteresis,
   batching.
4. **Capacity lookahead (§8.4).** `minutes_at_level : [u32; 6]` per day. *Under D10 a level holds an exact rational: stage 5 step 3's `DayCapacity`
   (`Capacity.lean`) holds numerators over one positive denominator (`Den`), and the EDF pass
   consumes a list of them. The lookahead that produces the list is the D9/D10 tranche's.*
5. **Consume `Arith.lean`.** It exists — 1,079 lines, 90 theorem declarations at
   `c8f3a38` — and **nothing consumes it**: the only `import TmKernel.Arith` in
   the package is the root module's. `needMin` (R1, ceiling), `budgetBlocks` (R2, floor),
   `plannedMin` (R4, half-up) and `energyAfter` (R5, half-up then clamp to 0..5)
   are the four entry points §7 and §8 will call.

**Spec sections.** §5.1–5.5, §6.4, §7.1–7.5, §8.4, §8.5's *correction* only (the
fit stays Rust), §16 (config), §10.1 (log replay), §10.2.

**Modules touched.** `Arith.lean` (consumers), `Cal.lean` (time of day, tz),
`Line.lean`, `Plan.lean` (series head, rollups, `parent`), new `Recur.lean` /
`Tree.lean` / `Priority.lean` / `Capacity.lean`, `Boundary.lean` (log, cfg,
model, now), `Check.lean`, `Negative.lean`, `Goals.lean`.

**This stage adds up to four modules; every one of them needs an
`import TmKernel.<Mod>` line in `kernel/TmKernel/TmKernel.lean`, in dependency
order** (§2.3). It is the stage most likely to lose one, because it adds the most
files at once and none of the seven checks will tell you. `cat TmKernel.lean` at
the end of the stage and count.

**Goals this stage owns** — 14 in `Goals.lean` under `# STAGE 5`, plus
provisional `remainingMin`, `seriesHead`, `prio`, `hysteresis`, `DayCapacity`,
`Deadline` and `edf`: `remaining_is_the_est_key_when_set`,
`remaining_falls_back_to_the_leading_estimate`, `remaining_sums_the_children`,
`the_series_head_is_not_settled`, `the_series_head_ranks_first`,
`prio_of_hot_is_zero`, `prio_is_clamped`, `prio_is_antitone_in_utilisation`,
`hysteresis_improves_by_at_most_one_bin`, `hysteresis_worsens_freely`,
`hysteresis_never_delays_hot`, `edf_keeps_the_days`, `edf_only_spends_capacity`,
`edf_reserves_only_before_the_deadline`. Note what is **not** there and why —
`Goals.lean`'s header lists D1/D2 (no `LogEvent` exists), D2's epoch (a spec
gap), R7 (a decision, not an obligation), and the parity harness (a measurement).
Read that list before deciding your stage is bigger than it is.

*Status at stage 5 step 3 (2026-09-14, README "Stage 5 step 3"). None of the fourteen
stands in `Goals.lean`, and stage 5's burn-down is 0. Step 1 proved two §5.4 goals as stated
and refuted the three §6.4 rows as written, proving the narrowed law beside each. Step 2
proved `prio`'s three and `hysteresis`'s three as stated. Step 3 proved the three `edf`
goals in `Capacity.lean`. They were restated over D10's rational minutes, which is a
generalisation, not a weakening: `edf_only_spends_numerators` is the provisional `Nat`
statement verbatim at every denominator. The provisional `DayCapacity`, `Deadline` and
`edf` are real. Step 3 also proved two-run laws (D5):
`edf_more_capacity_never_raises_a_shortfall` and
`edf_a_later_deadline_takes_nothing_from_an_earlier_one`.*

*Status 2026-09-14 (README "Stage 5 D9/D10: the owner's answers"). Stage 5's remaining work
follows `kernel/design/stage5/stage5-D9-D10-design.md` §14 (the step plan; §14.0 holds the rules
before any step), as amended by the owner's answers D11–D18 in its §22. D9 (phases A, B, R, C, W,
the switch S, the kernel-writer step D16 adds after S, and F) runs on `rebuild-on-lean`; D10
(L1–L9, with stage 6's E7, slot cut and energy prediction pulled in as L2–L4 under D12) runs in
parallel on `stage5-lookahead` (D11).*

**STAGE 5 IS CLOSED (2026-09-16, README "Stage 5 closed — the kernel reads and writes the
log"). The switch is made.** Since `2b26be3` the Lean kernel is the shipped binary's **only
reader** of `.tm/log.jsonl`, and since `47a0443` the **only writer** of its lines (D16). This
paragraph said "the switch is not made" from 2026-09-15 through four runs that correctly
refused S; the sentence is false now and it is gone. What landed, by phase:

| phase | what landed | commits |
|---|---|---|
| **A** prerequisites | gap 44's accumulating twins, `JVal`'s exact decimal (gaps 42, 43), the `logbench` harness | `b2ad4ba`, `013ed83`, `c2ebb8f` |
| **B** time and grammar | `Cal`'s instants and the zone table, `Stamp`, `Log`'s 26-kind event grammar, the `log` op | `c73e032`, `d202829`, `85f586d`, `a8f3022` |
| **R** Rust seams | fourteen steps; `Ctx::replay_of` became the one reader of `LOG_PATH`, every verb asks for its §11.1 scope, R14's Rust latency baseline | `1fe59c6` … `a9cbeda` (15 commits) |
| **C** the kernel replay | the undo mask, the day index, the block, completion and day-record families, the whole fact view, the undo law | `ae3a3cc`, `1e55211`, `5cc3831`, `c5689f8`, `f50886d`, `69bd90f`, `8fe6d80` |
| **W** windowing | `Seal.lean` and 57 proof modules: **all sixteen window laws**, the codecs, genesis in chunks, the measured gate | `45e8133` … `72576ec`, `017ead3` |
| **L** (D10) | the exact mixture, E7's window, the slot cut, future energy, the lookahead, its wire, the parity twin, the grants and floor pass — **L1–L8; L9 did not land** | `319919c` … `23b06e2` |
| **F1** | the fit reads the kernel's observations; `fit_replay` deleted | `983a8be` |
| **preparation for S** (D19, D21, D22, D23) | the eight missing T9s and T12, T11's seven latency rows, the per-verb call counts, gaps 134-136 and 138/D20, R12's consumer tests moved, and the whole instrument re-anchored **outside** the tree to fork point `4748911` (gaps 137, 146, 147, 148, 149) | `022317d` … `1b416e8`, `ab455cf`, `07b525e` |
| **S, the switch** | `Ctx::replay_with` → `kernel_log::replay_scoped`; `Ctx::replay_of` gone; §12's deletion (`tm-core/src/log.rs` 3,609 → 1,806 lines); D18's defaults wired; the one-reader grep 125 → **41** | **`2b26be3`** |
| **S-after** | `tm check` names a stalled ledger day (gap 119); a bare `tm log` at three years measured at 232.9 ms, so gap 129's narrowing is **not needed** | `cae3695` |
| **S2** (D16) | the kernel returns the exact bytes to append — `Log.emitEvent`/`emitLine`, the `emit` wire section, `Ctx::append_entry`; the log's format has **one** definition (gap 130) | `47a0443` |
| **Q6(f)** | a `close` carries `period:key` as its primary id, so undoing your own close no longer cancels the automatic one (gap 86); parity **P36** | `760ead6` |
| **the close** | the parity harness re-run *after* the switch through a rebuilt oracle; gap 225 closed; the ratio, §10.1 and §2.3 re-measured | this commit |

**What the acceptance measured**, re-run **after** the switch (2026-09-16) through an oracle
rebuilt under §7.3's freshness rule. Every denominator is recorded; none is omitted:
- **the whole `Replay` and the fit against fork point `4748911`** (input set 3): **469 logs over
  6 zones** — 8 frozen (the seven corpus logs and a generated month) and 461 in the classes too
  large to freeze — **8,442 `Replay` keys** (18 of the fork's 20 per log), **285 `tm event` name
  sets**, **469 entry counts**, 7 refused-line lists, **8 fitted models**, **195,243 scalar
  values**. Disagreements: **49**, every one `days.<date>.load`, every one **parity P21** (the
  kernel's exact fifths against the fork's accumulated `f64`), every one checked to display the
  same `round1` load and `load_blocks`. **Nothing else differs**, and `tm model --fit` agrees on
  all 8 fitted logs — design §14.6's T12, against the fork rather than a saved file. *(This
  number was **24** at stage 5's close and the undercount was the harness's, not the kernel's:
  both sides of every comparison were decoded by a `serde_json` without `float_roundtrip`, which
  reads the fork's own `187.60000000000002` back as `187.6` — the very double the kernel
  produces. W-12 turned the feature on, re-blessed the two frozen fixtures from a fresh oracle
  (8 leaves, every one a `days.<date>.load`) and re-ran this census: README **gap 235**. The
  denominator did not move.)*
- **inside plain `cargo test --workspace`, with no fork build** (D21): T5's frozen arms compare
  **20 inputs / 360 keys / 17,291 scalar values / 4 event-name sets** and the door **16
  `All`-scope reads / 288 keys / 32,976 values / 6 event-name sets**; 458 further inputs reach
  the fork only under `TM_ORACLE` (**gap 150**) and 2 door inputs are counted **skipped**, never
  as agreement. Their **P21** sightings are **4 + 8 + 0** (corpus, generated month, zone cases)
  and **24** (door) — **12 + 24**, where stage 5's close counted **4 + 8** for the same inputs,
  for the parser reason above.
- **the grammar** (input sets 1 and 2): 138 corpus lines, 77 with nothing to report; 2,048
  generated lines, 470 with nothing to report — **byte-for-byte the `017ead3` and stage-5-close
  figures**, so the grammar surface did not move while the reader was deleted, the writer
  replaced and a quirk fixed. Per line (input set 4, D23): 8,273 frozen verdicts and **1,375**
  kernel renderings read back to the fork's own entry.
- **the lookahead, priority, hysteresis and EDF** are measured by the committed T13
  (`kernel_lookahead_parity.rs`) and T16 (`kernel_unit_reserve.rs`): **92 windows, 552 future
  days, 482 candidates** (312 entering the pass, 6 held by hysteresis, 132 floors) and **256**
  proptest cases, with **0** disagreements outside **P1** (25 candidates), **P2** (3), **P3**
  (131) and **P27** (31 fork days). Those compare against the **in-tree** `tm_core::capacity` and
  `tm_core::priority`, and that is a fork-point comparison, **re-verified at the close rather
  than carried**: `capacity.rs` is purely additive since `4748911` (198 added, **0 removed**);
  `priority.rs` is 27 added / 6 removed, and its non-additive edits are **three**, not one — the
  `use` line gaining `Exact`, `is_impossible` reading the exact shortfall (P1-refined's own
  downstream), and `collect_candidates`' `events` source moving to `Replay::event_names()` at
  step X1. *(That last one is what README **gap 225** was about, and it is why the hole
  mattered: this sentence used to say "`priority.rs`'s only non-additive edit is
  `is_impossible`".)*
- **`remaining`, the rollup and the series head are NOT measured, because they are not reachable**:
  the kernel has no wire op that answers them, and a candidate's `remaining` is a **host-supplied**
  field of the capacity request (README gap 113). `Tree.remainingMin` and `Tree.seriesHead` are
  proved and witnessed inside the kernel and reach no response key. The denominator is **0**, said
  out loud rather than reported as agreement.

**What remains, by name** — and "closed" does not mean nothing is owed:
1. **Step L9 (README gap 93) did not land in stage 5, and has LANDED in stage 6.** Day 0 of the
   lookahead was the host's histogram at stage 5's close. Its blocker was **gap 210**, a seam
   inside the kernel — `runCapZ` answered a request's `log` and `capacity` sections independently,
   so the capacity path could not read the replay the same call just ran. Gap 210 closed at stage
   6 W-13 track B (D24), and **L9 closed at stage 6 W-13 step L9**: the kernel derives day 0 from
   its own replay (`Look.day0Hist`, site **R10**, the `at`/`state`/`posterior`/`sleep` keys), the
   `day0` argument and its `badDay0` refusal are gone, `Ctx::window` and `Ctx::today_slots` are
   deleted from the binary, and `kernel_lookahead_parity.rs` is **re-aimed**: it compares the
   kernel's day 0 against the fork's `Ctx::today_slots` exactly, over 92 day-0 comparisons with
   0 disagreements. Phase F's **F2** and **F3** still want the same seam, which is now paid for.
2. **The §5.13 human drives** of the stage-3, stage-4 **and stage-5** binaries. **No agent can
   perform them** *(partly false — an agent CAN drive the TUI through a pty, §5.13, README gap
   3527)*: `tm tui` refuses a non-tty by name (`tm/src/tui/mod.rs:92`) and design
   §14.6's stage-5 list asks for the TUI through two reloads with a CLI verb in between
   (README **gap 182**). Two items on that list are owner questions the drive is meant to
   settle: **gap 131** and **gap 139**.
3. **Open gaps**, the corrected list: **94**, **98**, **113**, **114**, **116**,
   **132**, **133**, **139**, **143**, **150**, **151**, **152**, **160**, **170**, **180**,
   **181**, **182**, **190**, **200**, **201**, **226** (**210** closed at stage 6 W-13 track B;
   **93** closed at stage 6 W-13 step L9, with **261**).
   Performance levers: **121,
   122, 123, 126, 127** (and 143). Quirks kept by owner answer Q6: **85** (e), **87** (g),
   **118** (b). Kept by owner decision rather than open: **120**'s remainder (D18 — a hand edit
   no rebuild can window is a named fault, and the memory cap is never raised).
   *Gaps 140, 141, 142 and 145 were cleared by S and are named closed in the README's closing
   block — four runs of "still open" lists had carried them by mistake.*
   *And this list, billed as corrected, was itself five short (W-12, README **gap 236**):
   **94, 98, 113, 114** and **116** are opened in the README and named closed nowhere in it —
   the five the README's own closing block calls **stage 6's inheritance** (`94` two reserves
   still Rust, `98` the 3,660-day lookahead clamp, `113` the candidates' facts are the host's,
   `114`/`116` the what-if and TUI replans ranking by the previous load's priorities). **113 was
   cited as a live constraint two bullets above this one** while being absent from it, and 98,
   114 and 116 appeared nowhere in this file at all. The README's line 19519 groups **107** with
   114 and 116 as stage 6's; 107 is closed (README "Gaps 107 and 80 — closed") and does not
   belong on any open list.*
4. **Phase F's F2 and F3** belong to stage 6's recurrence and priority tranches.

*The dated paragraphs below are the working record of how the switch was reached, kept because
each says what it closed and on what evidence. **None of them is a work list any more** — items
1–4 above are what is owed.*

*Measured 2026-09-16 (README, "W-9: the switch was built and measured, and it did not land").* The
body swap is **built and green** — `Ctx::replay_with` onto `kernel_log::replay_scoped`, and with it
`Ctx::log_tail_of`, `Ctx::entries_at`, the undo recorder and `tm log` — and it was measured end to
end against the unswitched binary before being reverted: **T5 20/20 and the door suite 15/15 pass
against the shipped switched path**, T12 passes, **8 of 10 T9s** pass (the unwritable-cache one with
its `#[ignore]` removed), **131 of 138** captured outputs are byte-identical, and the three-year
later verb is **faster** — 141.8 ms against track B's pre-switch 278.6 ms. So S's blocker is **not**
item 1, and **not** the size of §12's deletion: it is **gap 146** — the moment
`tm/tests/support/replay.rs`'s `replay_of_text` calls the kernel, T5's 20 tests and the door suite's
15 become **self-comparisons**, passing while proving nothing (§9.2's worst disguised gap) on the
least reviewable commit of the stage. Retargeting them to the fork oracle (**gap 137**) should be
**its own preparation step before S**, exactly as D19 did for T9/T12, T11 and R12. Two new decisions
belong inside S: **gap 144** (`tm log --json` cannot be both key-ordered and pretty-printed as design
§11.4 step 5 prescribes — `serde_json` here has no `preserve_order`, so parsing to `Value`
alphabetises the keys) and **gap 145** (`tm check` does not survive a `reachTooFar` log, which is
D18 (iii)'s "every verb **except** `tm check`" half).

*Partly closed 2026-09-16 (W-10; README, "the comparand that survives the deletion").* **Gap 146's
blocker is answered for the corpus class, and its own figure was wrong.** `tm/tests/fixtures/`
now carries **fork point 4748911's own answers, frozen** — 7 corpus logs, 146,868 bytes, blessed
through AGENTS §7.3's oracle by an `#[ignore]`d test and byte-reproducible on a re-bless — and
`t5_the_corpus_logs_replay_as_the_frozen_fork_point_does` compares the kernel against them inside
`cargo test --workspace`: **126 `Replay` keys, 7,189 scalar values, 7 entry counts, 7 refused-line
lists, 1 parity P21 sighting whose displays are equal, 0 other disagreements.** It names neither
`replay_of_text` nor `entries_of_text`, so §12's deletion **cannot** turn it into a
self-comparison — which is the whole of what gap 146 asked for. **The "door suite's 15" in gap 146
is a miscount**: the binary's 15 is 10 door tests plus the 5 `kernel_log::tests::*` unit tests the
`#[path]` include pulls in, and only **7 of the 15** name a chokepoint function §12 deletes. What
remains of the retarget is **gaps 147-149**: T5's *generated* classes (1mo/6mo, 256 sequences, the
zone cases, 64 triples) are still compared against the in-tree reader (**147**), T1-T3's grammar
comparand is `Log::parse_bytes`/`LogEntry::parse`/`parse_timestamp` themselves (**148**), and the
door suite's 7 exposed tests are unretargeted (**149**).

*Gap 148 closed 2026-09-16 (W-11, track B; README "the grammar differential that
survives the deletion").* **T1-T3 no longer name a function design §12 deletes.**
`tm-oracle` gained the per-log-entry `parse-entry` mode D23 called for (§7.3's
fourth input set), and `tm/tests/kernel_log_grammar.rs`'s **11** direct sites on
`Log::parse_bytes`/`LogEntry::parse`/`parse_timestamp` are now **0** — the parse
half reads fork point 4748911's frozen per-line verdicts, and the writer half
(`LogEntry::{new, to_json}`, `Event`, `EVENT_NAMES`, `hours_since_wake`) never
needed an oracle because §12 **keeps** it, which is why **T2 is untouched**.
Every acceptance edge the tests covered is preserved, with the denominators
unchanged (§7.3), and the sweep gained the fork's whole-file reading of each
corpus log as a cross-check. §12's one-reader grep falls **125 → 123**: eleven
code sites went, and **nine doc-comment lines still name the deleted functions in
prose**, which is why the count does not fall by eleven.

*Gaps 137, 146, 147 and 149 closed 2026-09-16 (W-11, track A; README "the
instrument is anchored outside the tree"), and re-verified at the W-11 merge.*
**The retarget is finished: nothing on this list is now compared against the
reader §12 deletes.** T5's default comparand is the fork (`fork_arm` is asked
before the in-tree reader, and an input with no frozen answer is counted as
**skipped**, never passed over); one representative generated month and §6.4's
twelve zone cases are frozen by value under **D21**
(`fork-4748911-classes-replay.jsonl`, 212,349 B); and the door suite's exposed
tests now compare against the frozen fork, the kernel's own `All` scope, a
hand-written expectation, or the log's own bytes — none against a §12-deleted
chokepoint. **Proved by simulating the deletion, not asserted:** with the reader
made unreachable both suites still build, run and compare (T5 20 inputs / 360
`Replay` keys / 17,291 scalar values; the door 16 reads / 288 keys / 32,976
values), and with one kernel answer corrupted they fail by name against fork
point 4748911 — T5 on all three frozen arms, the door at **14 passed / 2
failed**. Residue: **gap 150** (458 inputs reach the fork only under
`TM_ORACLE`), **gap 152** (the fork's `Replay` cannot answer for `rows`), and
**gap 151** (§12's deletion list reaches past the reader, to be settled at S).

*Closed 2026-09-16, on the `w8-facts` track (README, "the three findings that would have made a
naive switch wrong").* **Gaps 134, 135 and 136 are no longer on this list.** `tm check` is wired to
the kernel's read-only line sweep, so it names every unreadable line and not just the last chunk's
(**134**); `decode_facts` keeps the two all-time done-date numbers the kernel already sends
(`Seal.ItemAgg.doneFirst`/`doneCount`), which is what the **135** audit found missing — without them
`tm plan`'s `every:Nd` phase anchor and the ordinal recurrences' pending number are computed at
`Hot` from a *suffix* of the completion dates; and `tm log`'s `total` is the log's all-time entry
count rather than the row count of the scope it asked for (**136**). All three are green against the
**unswitched** binary under D19, and each is pinned by a test that was shown to fail without its
fix. **T11's seven latency
rows and the per-verb kernel-call count are no longer on this list either**: they landed on
2026-09-16 on the `w8-latency` track, merged to `rebuild-on-lean` the same day, as
`tm/tests/cli_latency.rs`'s T11 and `tm/tests/kernel_call_counts.rs`, both green against the
**unswitched** binary. That track also closed **gap 138** (D20) and opened **gaps 140-141** (139-140
on its own branch; renumbered at the merge, AGENTS §6.5, because track A took 139 the same day).
**The eight remaining T9 CLI tests and T12 are no longer on this list**: they landed under D19 as
`tm/tests/cli_switch_acceptance.rs`, six T9s and T12 green against the **unswitched** binary and
two `#[ignore]`d with their full post-switch bodies (README, "the T9/T12 step"). S's acceptance for
those two is to delete the attribute, not to write the test.
Then **S2** (**gap 130**, D16's kernel writer, with quirk
Q6(f) = **gap 86**), then **L9** (**gap 93**, day 0). Phase F's F2 and F3 belong to the recurrence
and priority tranches. Performance and unbuilt-test debt: **gaps 121, 122, 123, 126, 127**. Quirks
kept by decision: **85** (e), **87** (g), **118** (b). And the **§5.13 human drives** of the stage-3,
stage-4 and stage-5 binaries are still owed.

**"Eight T9 tests" — and the three counts this ledger gave for one number.** Design §14.6 lists
**ten** T9 names. Two of them exist and pass, both in `tm/tests/cli_check_log.rs` and both landed
with D18 (i) and (ii) at `022317d`: `invalid_utf8_line_is_a_warning_and_tm_check_names_it` and
`a_line_dated_next_year_changes_nothing_about_today_and_tm_check_names_it`. **Eight remain**, and
that is the figure to quote. This paragraph said "nine" from the stage's close until 2026-09-15;
`kernel/README.md`'s X1 block says "seven"; its S block says "eight" and is the one that is right.
The older README blocks are append-only history (§6.4) and are not rewritten — §10.2's table
carries the correction for anyone quoting them.

*Closed 2026-09-16 (D19).* **All ten T9 names now exist**, and so does T12. The eight that were
missing are in `tm/tests/cli_switch_acceptance.rs`; **six pass against the unswitched binary**, and
**two are `#[ignore]`d** because the code they name has no caller until S —
`an_unwritable_cache_rebuilds_in_memory_with_one_notice` (nothing in `tm/src` calls
`kernel_log::unwritable_notice`) and `a_hand_undo_beyond_the_rebuild_bound_fails_by_name`
(`ReachTooFar` has no call site; **gap 120 part 3**). The figure to quote from here is
"ten exist, two ignored until S". That step also took **gap 139** (`--now` at an instant before the
stored runtime day rolls `.tm/state.json` back), which is a question for the §5.13 drive, not S's.

*Item 3 closed 2026-09-16 (D19).* **Design §14.6 item 3 — R12's consumer tests — is landed**, before
the switch and green against the unswitched binary: **23** test files and the two shared modules
(`planner_common/`, `review_common/`) moved from `tm-core/tests/` to `tm/tests/` with their **49**
insta snapshots, whose bodies are byte-identical — only insta's `source:` header line changed, and
that was verified blob by blob, not asserted. What item 3 still owes S is **only the chokepoint's
one-line body swap**: `tm/tests/support/replay.rs`'s `replay_of_text` calling the kernel instead of
`Log::parse(..).replay(..)`. No caller changes. Measured while both readers still existed — the
whole point of landing this before S — over the moved suites' own **308 distinct (text, zone)
pairs**: the kernel door and the Rust reader agree **exactly**, with one refusal, which is the
recorded parity exception **P17** (**gap 142**).

*Gaps 119 and 129 closed 2026-09-16 (W-11, S-after; README "a stalled ledger day has a
name").* Both were **unreachable before S and reachable the moment it landed**, which is why
three runs had correctly left them. **Gap 119**: `tm check` now names a stall in D18's warning
family (`check::LOG_STALL`, `log-stall`), at the line the stall began on, with the ledger day it
holds and the verb that clears it. The obvious rule was a trapdoor and the tests say so — a lag
test ("the ledger day is more than 7 days behind `now`") fires on **healthy** trees, because
§9.4 folds only to `min(T, M) - keepDays` and so `L` trails the log's own last activity:
measured over two trees identical but for the open block, the unstalled one ran **12 days**
behind while the stalled one pinned at its block's day forever. The cause is named, not the lag.
**Gap 129**: measured, not narrowed, on exactly the condition the gap wrote for itself — a bare
`tm log` over three years (66,169 lines) is **232.9 ms**, inside `LATER_VERB`, so `All` stays and
the two-step narrowing is not built. The three-year behavioural test gap 117 could not carry
landed with it. Residue: **gap 190**, design §9.4's third stall cause (a `stop` never followed by
a `start`) is invisible to the host — it lives in the kernel's `Replay.Machine.lastCut` and
reaches no response key, and a stopped tree with a 23-day ledger lag still reports `no problems`.

**Depends on.** `Cal.lean` and `Arith.lean` (both built), §4.1's field grammar
(built), stage 4 for `close`, and — a hard dependency — the `parent` decision.

**The blocking decision, which must be taken before stage 5 starts.** `parent` is
the one **spec** §3.1 field still *stored* rather than viewed, and it is always
`none`.
`Field.parentRef` reads `@O2` off the line today; wiring it would make
`parentsTotal` — a **load precondition**, not `tm check`'s `@ghost` *report* —
refuse every `week/*.md` and `backlog.md` in the fixture corpus with
`danglingParent`. The consequence is stated in gap 22: **spec** §3.2's
`effectiveShape` prep rule, `effectiveCi` inheritance and `rootPrio` are **proved
and cannot fire on anything the boundary builds**. §6.4 rollups, §7.1's
`k = root_priority`, tag inheritance and prep-due derivation all need it. Derive
the field and demote `parentsTotal` to a report, or keep it stored and have no
hierarchy — a plan-tier decision nobody has taken. *Taken 2026-09-13 (D6: derive
it, and keep `parentsTotal` a load precondition) and landed at stage 4 final step
3: the prep rule, `effectiveCi` and `rootPrio` fire on loaded plans
(`the_prep_rule_fires_on_a_loaded_plan`, `effectiveCi_inherits_on_a_loaded_plan`,
`rootPrio_reads_the_root_on_a_loaded_plan`). The close's overdue route does not
yet read the effective shape (README gap 68).*

**Acceptance.** The parity harness. **Its exception list is longer than the six
rounding sites**; extend the existing oracle scaffolding rather than writing a
new one — after first moving it off `main`, which no longer exists, to the fork
point `4748911` (§7.3). Stage 5's parity is therefore against the fork-point
Rust. *Done at the stage's close: the scaffolding was retargeted (`89ead46`) and
extended with a third input set and a `fit` mode, then a fourth (D23's
`parse-entry`); the exception list runs to **P36**.* **Re-run AFTER the switch
on 2026-09-16 through a rebuilt oracle**, which is the run that counts: over
**469 logs / 8,442 `Replay` keys / 195,243 scalar values / 8 fitted models**, the
measured disagreement is **P21 alone**, **24** sightings, none of them reaching a
display; over the capacity surface it is **P1, P2, P3 and P27** and nothing else.
The numbers and every denominator — including the one that is **zero** — are in
the status block above and in `kernel/README.md`'s closing block.

**Named traps.**

- **Config decimals have exactly one safe route.** §16 ships `bins = [0.5, 0.25,
  0.1]`, `safety = 1.3`, `budget_ratio = 0.75`, `plan_ratio = 0.8`,
  `p_lounge = 0.9`, `under_hours = 7.0`. `Arith`'s only decoder is
  `ofPair? (n d : Nat) : Option Pos`. `Lean.JsonNumber` is
  `{mantissa : Int, exponent : Nat}` — an exact decimal — so `0.75` arrives as
  `75 / 10^2` with no `Float` anywhere. Use that route, or have Rust send num/den
  pairs. What must not happen is a `Float` appearing "to read the config".
  *Stale route, as of `b7f504d`:* `Lean.Json` is off the wire, and the kernel's
  own `JVal.num` is a `Nat` — `jparse` refuses `0.75` at parse
  (`jparse_refuses_what_the_fragment_has_no_type_for`). So the `JsonNumber`
  route is gone; the remaining routes are Rust sending numerator/denominator
  pairs as two `Nat`s, or widening `JVal` with an exact decimal constructor —
  **visibly, in a diff**, with its escaping/numeral round trip extended so
  `jparse_jemit` still holds. The last sentence stands unchanged. *Route chosen at
  stage 5 step 1 (README "Stage 5 step 1"): Rust sends each configured rational as a
  numerator/denominator pair of `Nat`s, decoded by `Arith.ofPair?` (a zero denominator
  refused); `JVal` is not widened. The wiring step inherits this.* *Stage 5 A2
  (D9 track, design §5.1): `JVal` **is** now widened, with `dec` holding an exact
  lexical `JDec`, for D9's log; `jparse_jemit` still holds unconditionally. The config
  route above is unchanged, because every wire reader wants `num` and refuses a `dec` by
  its own name (`a_request_number_that_is_not_a_nat_is_refused_by_its_reader`).*
- **`binsWf` and `descending` are two decidable checks a loader should run**
  (gap 27). `ladder_eq_rungs` needs the edges sorted;
  `rungs_antitone` does not. A misconfigured `priority.bins` still produces a
  well-defined antitone bin that is **not** §7.1's ladder, and there is no
  `planWf` clause rejecting it, because config validation lives at the boundary. *Stage 5 step 2: `Priority.lean`'s `binsOk` / `binsOf?` / `binsOfPairs?` are the
  smart constructor (pairs through `ofPair?`), with `Bins.ladder_eq_rungs` for what the check
  buys and `a_misconfigured_ladder_is_antitone_but_not_the_ladder` for what it refuses; the
  loader call waits for the config wiring (README gap 77).*
- **`0/0` is a decided disagreement, not a rounding site** (gap 25).
  §7.1 says "capacity 0 → `u = ∞`" with no exception for zero need, so
  `utilGe 0 0 e = true` and an item with nothing left to do and no capacity comes
  out **HOT**. An `f64` implementation gets `NaN`, every comparison is false, and
  it falls into the *lowest* bin. Both are defensible. **The parity harness will
  report this and it is not one of the six stated sites** — add it to the
  exception list *before* running, or acceptance fails for a reason already
  decided. *Stated at stage 5 step 2 over a rational availability as
  `zero_need_on_zero_capacity_is_hot` (parity entry P2). The fork point's mechanism is
  `priority::utilization`'s `need 0 → 0.0`, which `bin_of` puts in the lowest bin, not a
  `NaN` (README "Stage 5 step 2").*
- **R1 is a systematic disagreement, not a rare one.** §3.5 changes `need_min`
  from `round(rem × 1.3)` to **ceiling**, because a margin rounded down stops
  being a margin. The Rust computes it twice — `priority.rs:349` in
  `safety_minutes` and `planner.rs:323` inline — and both must move together or
  the harness sees two different Rust answers for one rule.
  `rounding_the_need_changes_the_bin` is why the ordering path uses
  `utilScaledGe` and never `needMin`. *Stage 5 step 2: the ordering path is
  `binOfScaledQ`, which is `utilScaledGe`'s ladder on whole minutes
  (`binOfScaledQ_on_whole_minutes`) and takes a rational availability; the exact scaled
  need in the bin is parity entry P7.*
- **R7 is open and it is the planner's to decide** (gap 26). §8.4
  mixes lounge and home capacity by `p_lounge`, a rational weight over two
  integer minute counts. Whether the planner floors per level, per day, or
  carries the pair exact into the EDF pass is undecided. Decide it here and state
  it, or stage 6 inherits an unstated rounding. *Taken 2026-09-14 (D10): exact, carried
  as numerator/denominator pairs through the EDF pass, nothing rounded; fork-point
  `capacity::lookahead`'s `p ≥ 0.5` threshold is a parity exception.* *Stage 5 step 3: the EDF pass takes capacity as numerators over one positive
  denominator (`Den`), so it grows no numerator/denominator pairs and rounds nothing.
  `flooring_the_capacity_changes_the_verdict` shows why a floor per level is wrong: it turns
  a HOT item IMPOSSIBLE.*
- **The log has nowhere to live.** `PlanCore` is `{docs, store}` — there is no
  `log` field, against the plan's three-field sketch. Instance status comes from
  the log (`done inst=…`, `skip inst=…`), and so do `done_minutes`,
  `blocks_done` and lost minutes. §3.6 keeps the *statistical* layer in Rust —
  but `log::replay` is not statistics. **Decide which side replays, and say so.**
  *Taken 2026-09-14 (D9): the kernel replays all of it and hands the energy and duration
  observations back to Rust's fit. Until the D9/D10 tranche lands, every log-derived
  input is a plain argument of the kernel function that reads it, never a Rust summary
  format.*
- **Hysteresis is a second relational-ish law and it is not in L1..L27.** §7.4:
  `p` may improve by at most one bin per day relative to yesterday's stored `p`,
  unless the new value is 0. It makes today's priorities depend on yesterday's
  output. Name it and place it in a tier before writing it. *Named and placed at stage 5 step 2 (`Priority.lean`'s module
  doc): a function law of two numbers whose `yesterday` is the host's `state.json` input
  (`Fin 8`, `yesterdayOf?`), with the day-over-day reading proved over `hysteresisDays`
  under the host's contract that today's `p` is stored as tomorrow's yesterday.*
- **Time of day and tz are missing from the calendar, not from the grammar**
  (gap 10). `Line.lean` already has `Clock = Fin 1440`, `DT{day,time}`
  with `DT.abs` in minutes, and `Moment` — so the values parse. What is missing is
  clock arithmetic in `Cal.lean` and the zone.
- **`omega` does not see through the `Day` abbreviation** when `Day` is the type
  argument of `=` or `≤`. That is why `Day` appears only in *parameter* positions
  in `Cal.lean` and every day-valued **result** is typed `Nat`. Getting it wrong
  costs an hour diagnosing "omega could not prove the goal" on arithmetically
  trivial statements, and stage 5 writes a lot of day arithmetic.
- **Two known spec gaps, recorded not papered over.** `every:Nd` has no epoch and
  ordinal-keyed recurrences take the pending ordinal from the wrong place — a
  spec gap, not a theorem. And `every:week` / `every:Nw` is used by §4.3's own
  routines example while §3.1's `Rule` has no constructor for it (gap 9).
- **E7 is `~U`, not U.** `window_and_budget` solved a fixed point by iterating;
  totality forces a termination argument *or* a bound. Forcing a decision point
  is not the same as making the right decision.
  *Moved into stage 5 by the owner's D12 and proved at D10 step L2 (README "Stage 5 D10 L2"):
  `Look.windowEnd` is the fork's clip-sort-merge-extend walk, and it is the least solution of
  `end = max(arrival, min(arrival + window, cap)) + overlap(arrival, end, walls)`
  (`the_window_end_solves_the_equation`, `the_window_end_is_the_least_solution`). Both STAGE 6
  goals were false as written (walls wholly inside, an unclamped base) and are restated under
  their names; the refutations are `the_window_end_is_not_the_least_solution_as_stage_6_wrote_it`
  and `the_window_end_does_not_solve_the_equation_as_stage_6_wrote_it`.*
- **Series head has no home** (gap 18). `seriesOf` derives the
  `## series:<name>` a placement sits in; §5.4's head rule and the implied
  `after:` a series section carries are planner concepts. *The head got a home at
  stage 5 step 1: `Tree.lean`'s `seriesHead`, per document (README "Stage 5 step 1",
  difference (s1)). The implied `after:` (fork-point `Tree::implied_dep`) is still
  unbuilt, README gap 75.*
- **This is where the proof-to-definition ratio is expected to blow up**, and the
  3:1 stop condition fires here on the measurement taken at the end of stage 4.
  The `1.09 : 1` figure in the plan is a stage-1 first-slice measurement and the
  plan says it will not survive stage 5.

**Inherited debt.** Gaps 9, 10, 18, 19, 22 (**blocking**), 24, 25, 26, 27, 28,
29, 35.

---

### 8.4 Stage 6 — the planner

> **Plan acceptance.** D1–D14 decidable-checked on every plan the corpus
> produces; `planner_invariants.rs` green at 256 cases through the FFI; the
> one-renderer test. Cost: 3–4 wk. Worth alone: `tm plan` kernel-backed; G1
> structurally dead.

**Scope, concretely.**

1. **§8.1–8.2**: window and budget, then the eight steps — walls, routines,
   slots, priority, assign, deferred routines, rest, emit.
   *The window, the budget and the walls are stage 5's since D12 (D10 step L2,
   `Look.windowEnd`, `Look.windowOn`, `Look.budgetOf`, `Look.wallIndex`/`wallsOn`), and
   §8.2 step 3's slot cut since D10 step L3 (`Look.freeIntervals`, `Look.cutSlots` with the
   placed routines as `rests` and the blocks since the last break), and §8.2 step 3's slot
   energy and §8.4's budget limit since D10 step L4 (`Look.hsw100`, `Look.predictAt`,
   `Look.capForLocation`, `Look.energize`, `Look.limitSlots`; day 0's posterior, sleep shift
   and `--allow-home` **landed at step L9** — `Look.day0Window`, `Look.day0Cut`,
   `Look.todayEnergy`, `Look.day0Hist`, site R10's `Arith.roundAway`, `Look.correctAt`):
   `dayPlan` reuses them and never writes a second copy (AGENTS §5.3).*
2. **L26 as decidable checks over the produced `DayPlan`**: the energy filter
   (`item.ci ≤ slot.energy`), no overbooking, walls unmoved, monotone rank. These
   are single-run and therefore cheap — a checker plus a `lift`, which is the
   shape to aim for everywhere in this stage.
3. **The generated Markdown blocks** — the day-plan section and the review block.
   This is what structurally kills G1, and it is an **architecture** row (single
   ownership), not a proof row. Do not credit the Lean compiler for it.
4. **§8.5's posterior correction** — `ramp`, `posteriorNum`, `energyAfter` are
   already in `Arith.lean`, consuming a fitted model as data.
5. **L23 `plan` is pure** — free; it is a function.

**Spec sections.** §8.1, §8.2, §8.3 (the invariants), §8.5's correction, §9
(dynamic adjustment: the running block, overtime, interrupts), §12 for the
emitted text, §11 only as integer numerator/denominator pairs.

**Modules touched.** A new `Planner.lean` and an `Emit.lean`, `Arith.lean`
consumers, `Boundary.lean` (the `report` half of the response, `state.json`
runtime facts), `Check.lean`, `Negative.lean`, `Goals.lean`.

**Both new modules need an `import TmKernel.<Mod>` line in
`kernel/TmKernel/TmKernel.lean`** (§2.3) — and `Emit.lean` especially, because it
owns the generated Markdown blocks, which is the whole of item 3 below: a module
that is not linked cannot own any bytes at all, and nothing would fail.

**The `report` shape is inherited, not invented here.** §8.2 fixes it; if stage 4
left it open, settle it before you widen it, because this stage is where it grows
`Segment`/`SegKind`'s eleven variants and `Diagnostics`' nine families.

**Goals this stage owns** — 15 in `Goals.lean` under `# STAGE 6`, plus the
provisional `Seg`/`DayPlan`/`PlanReq`/`dayPlan` vocabulary *(13 since stage 5 D10 step L2:
the two E7 goals moved into stage 5 under D12 and are proved in `Lookahead.lean`, restated
to the fork's overlap semantics and refuted as written)*:
plan_does_not_overbook, `plan_reserves_one_block_at_a_time`,
`plan_respects_the_energy_filter`, `plan_places_no_block_over_a_wall`,
`plan_places_no_block_over_a_break`,
`plan_places_no_demanding_block_after_wind_down`, `plan_never_moves_a_wall`,
`plan_is_monotone_in_rank`, `plan_puts_hot_before_the_queue`,
plan_never_drops_an_impossible_item,
`plan_never_batches_past_an_equal_ci_candidate` (these eleven are L26's
single-run checks), `the_window_end_solves_the_equation` and
`the_window_end_is_the_least_solution` (E7, *gone to stage 5, above*), and `plan_tail_drop` /
`plan_is_stable_across_a_replan` — L24 and L25, the two relational ones the
recorded recommendation says to leave to the proptest. If you take that
recommendation, the two goals stay in `Goals.lean` and check 7 ends the stage at
2, not 0. That is the correct outcome; say so rather than deleting them.
*Measured at W-39 (2026-09-30): check 7 reads **0**. L24 and L25 were not left to the
proptest: each was refuted as written and proved in a restated form beside it
(`PlanFold.plan_tail_drop`, `PlanFold.plan_is_stable_across_a_replan`), as were the four
single-run goals that remained; the proptest still runs beside them (D5).*
*Since the W-39 repair check 7 reads **1**: the wind-down goal is back, its refutation fallen with gap 3556
(README gap 3713).*

**Depends on.** All of stage 5 and stage 4, plus runtime state that lives in
Rust: `active`, `window`, `budget`, `break`, `interrupt`, `last_plan_hash`.

**Acceptance.** The plan's three items. Note the third is a *Rust* test — the day
section byte-identical across the file, `tm now`, `tm tui` and `tm plan --json`.

**Named traps.**

- **L24 (tail-drop) and L25 (stability) are RELATIONAL, and the recorded
  recommendation is to keep the proptest.** Tail-drop compares `plan(budget)` to
  `plan(budget − Δ)`; stability compares `plan(t)` to `plan(t′ > t)`. Both relate
  two runs of a greedy fold: real inductions, not `decide`.
  `tm-core/tests/planner_invariants.rs` (on `main` then; restored from the fork
  point now) is 882 lines at 256 cases with explicit `--- tail-drop ---` and
  `--- stability ---` sections, and it has empirically caught things.
  **The decision is due before stage 6 starts**, and the recorded recommendation
  is: keep the proptest, state the law in Lean, prove it last or never — *"decide
  that deliberately now rather than discover it in month six."*
- **Aim the proptest through the FFI rather than rewriting it.** The plan's
  acceptance says exactly that, and the same pattern applies to `grammar_proptest.rs`
  (395 lines, restored from the fork point).
- **L27 is expected-refuted and R7 is an open *decision*, not an open *proof*.**
  Lifecycle commands do not commute: `demote ^m1 ; move ^m1 week` breaks a tree
  the reverse order does not, and nobody has decided whether they should. L27
  makes the kernel refuse to be silent about it; it does not answer it.
- **Nine defects are `M` and no kernel proof touches them** (G2, G3, G4, G6,
  G8–G12). Four are the integration bugs whose countermeasures are Rust tests.
  Stage 6 is where `tm plan`'s CLI and JSON surfaces change most, so the `--json`
  matrix test and the CLI conformance test earn their keep here.
- **`Fin 6` forces a decision point but does not make the decision.** Nothing
  stops the CLI writing `.getD 3` and silently filtering `tm start --energy 9`
  away again.
- **Display divides; the kernel does not.** `progress`, `plan_honesty`,
  `as_blocks` and the review "share" family emit integer numerator and
  denominator; Rust divides.
- **`Segment`/`SegKind` is 11 variants and `Diagnostics` is 9 families**, all of
  which cross the boundary as JSON with bounded types and smart constructors —
  ~8 lines per type, and forgetting it on **one** type silently reopens the hole.
- **F3 finally lands here**: `close day` replacing a written review with
  `review pending`, once the kernel owns the generated blocks.
- **The 5 ms TUI stop condition applies to this stage's calls.** Measured at the
  spike: 0.8 ms for a 500-item replan against a 16.7 ms frame. Note `planWf` is
  quadratic in item count and `mapAt` runs the whole of it after every command;
  the recorded answer, if it ever matters, is a fast implementation behind the
  same interface with the proofs on the interface.

**Inherited debt.** Gaps 11, 18, 20, 22, 26, 28, 29, 35; and every `M`/`~` row
of plan §4 that no proof reaches.

**Inherited from stage 5 at its close (2026-09-16), by name** — §8.3's "what remains" is the
authoritative list; this is what stage 6 has to *do* with it:
- **Step L9 (gap 93) — CLOSED at stage 6 W-13 step L9.** What follows is the inheritance as
  stage 5 handed it over; read it as the record of a debt now paid. Day 0 of the
  lookahead is still the host's `DayCapacity::from_slots`. Its opening move was **gap 210**, and
  that is **closed** at stage 6 W-13 track B (D24) — the
  kernel answers a request's `log` and `capacity` sections independently, so the capacity path
  cannot read the replay the same call just ran. **Phase F's F2 and F3 want the same seam**, so
  stage 6 pays for it once and three steps spend it. Design §14.8 priced L9 at 200 definition and
  600 proof lines, −150 Rust, 4-6 agent-days; it came in at **+1,056/−78 Lean and +297/−69 Rust**,
  so the Lean estimate was close and the Rust one wrong in sign.
  `kernel_lookahead_parity.rs` asserted in words that day 0 was the host's; L9 **re-aimed** it,
  and it now compares the kernel's day 0 against the fork's `Ctx::today_slots` exactly, over 92
  day-0 comparisons with 0 disagreements.
- **F2** (the recurrence family: `done_dates` first and count, `last_done`, instances,
  `latest_named`, `is_done`) and **F3** (the priority rule inputs, and `block_minutes_on` moving
  in with the close tranche) — each fact's last Rust reader goes with its tranche.
- **The scope questions**: gaps **132** and **133**, facts the `Hot` scope will not carry.
- **The levers**, all measured and none taken: **121, 122, 123, 126, 127, 143**. The baseline
  they move against is a later verb at three years, **146.9 ms** — the one T11 row that holds
  still: five capped runs across two sessions gave 146.66, 146.85, 146.87, 146.95 and 147.01 ms,
  a spread of 0.2%. **Three of the seven rows do not hold still and must never be quoted as
  single numbers** (W-12, README **gap 240**): over three capped runs here the reseal spans
  **197.5-212.6 ms** (the README's closing block recorded 202.604 and an earlier block 192.455),
  the 3-day-old routine **121.6-136.8 ms** (recorded 136.827) and `review week`
  **248.1-253.3 ms** (recorded 253.270). A step reading any of the three as a regression is
  reading noise; quote the range, or re-measure and quote your own run.
- **Gap 226**: the parity list has no single home and no check, and P32 was issued twice. The
  next entry anyone adds is **P37**.

---

### 8.5 Stage 7, so you know what stages 3–6 are building toward

Delete `tree::record_rank`, `tree::is_real_duplicate`, `store::choose`'s
tie-break, and `cli/items.rs::drop_stale_demotion`. Cost: days. Acceptance: suite
green with those four gone, and `tm check` *is* `parse`. **The deletion is the
proof that the invariant became structural** — until then, "`Store.get` deletes
four pieces of machinery" is a claim about what is *deletable*, not a thing that
has been done.

Two notes to carry: `drop_stale_demotion`'s own doc comment ends *"Upstream fix:
horizon::readopt"*; and gap 2 records that refusing to move a demoted
item while its tombstone stands is **the change that makes `drop_stale_demotion`
unnecessary** — and it is a behaviour change a user must assent to, since `tm`
today allows `tm move ^id day` on a demoted item and leaves the stale `[-]`
behind.

---

## 9. Stop conditions, cutting scope, and recording a gap

### 9.1 The triggers, from `PLAN-lean-kernel.md` §6.3

Named in advance so that stopping is a decision and not a capitulation.

| trigger | fires in | action |
|---|---|---|
| Proof : definition exceeds **3 : 1**, measured at the end of stage 4 — **FIRED 2026-09-13, OVERRIDDEN by the owner (D5); see below** | 4 → 5 | stop proving relational laws; keep decidable checkers plus the existing proptests, and **say so in the README** rather than letting the ratio quietly eat the schedule |
| Any needed proof requires **Mathlib** | any | **stop and re-price at that moment.** 9.7 GB on disk, a 118 MB binary, `Mathlib:static` on every linking machine, and — decisively — Mathlib chooses your Lean version, release candidates included. This is not a decision an agent takes |
| A kernel call in the TUI exceeds **5 ms at 500 items** | 6 | try the session handle (`lean_mark_mt` + a mutex, UI thread only); if that is not enough, the runtime kernel is the wrong shape for the TUI |
| Two consecutive Lean upgrades each cost more than a day of proof repair | any | freeze the toolchain and treat the kernel as a fixed artifact, or fall back to a design-time model |
| After stage 3: a clean exhaustive **depth-3** sweep, plus 60 days of use with no new defect in the covered class | 3 | **the bug class is gone.** Stages 5–6 then buy uniformity, not soundness. *"That is a legitimate reason to stop, and it should be stated out loud if it happens"* |

**The first row fired at stage 4's close (2026-09-13), and the owner OVERRODE it
the same day (D5, §4):** relational (two-run) laws keep being proved, L24/L25
included, and a two-run theorem a change breaks is re-proved, never downgraded or
deleted. Re-measured at `c9ef6f0`: 4.52 : 1; at `b2af1a8` (D6): 4.60 : 1; at stage 4
final step 4 (B3, the commit that closes stage 4): **4.80 : 1** (18,815 proof lines :
3,917 definition lines), 9.36 : 1 in `Close.lean`, 6.22 : 1 in `Report.lean`, by the
same script (`python3 /tmp/claude-1000/proof_ratio.py kernel/TmKernel/TmKernel`) — under
D5 the number informs and stops nothing. The row stays, because a later owner
may re-impose it; the decision and its cost are in README "Stage 4 final,
2026-09-13". The paragraph that follows is its record as it stood before the
override.

**The first row fired at stage 4's close (2026-09-13):** 4.49 : 1 over the
library, 6.43 : 1 in `Close.lean`, 5.63 : 1 in `Report.lean`, measured by a
script a skeptic can rerun (README "Stage 4 closed"). The action is the owner's
to take before stage 5 starts; nothing in stage 5 should begin by proving a
relational law until it is taken.

That last row has the most leverage and the least infrastructure behind it
(§8.1's last trap) — and since `main`'s discard, no harness at all:
`invariant_exhaustive.rs` went with it, so the sweep must be rebuilt against the
kernel-backed binary before depth 3 can even be costed.

Evidence that core Lean suffices for the hard parts, so the Mathlib trigger is
not a formality: `parentsAcyclic_complete`'s pigeonhole is core's
`List.Nodup.length_le_of_subset`, and `sorted_ext_by_key` is hand-proved in about
twenty lines.

### 9.2 How to record a gap

An honest gap is worth more than a disguised one, because the next agent's audit
starts from your gap list. Every one of the last five audits found what it found
that way.

A gap entry states, in this order:

1. **What is not done**, in the terms a reader of the code would use.
2. **Why**, if the reason is a decision rather than time.
3. **What it costs** — which theorem is therefore weaker, which input is
   therefore refused, which command therefore cannot be written.
4. **Which stage should clear it**, if you know.

Append your gaps as a block under an HTML comment banner in `kernel/README.md`,
numbered from whatever is free, and say in the banner that whoever merges
renumbers (§6.4).

**What a disguised gap looks like**, so you can recognise your own:

- A theorem whose name promises more than it states (§5.2).
- A precondition nothing can satisfy, so the conclusion never fires.
- A check no input can fail — *"a checker whose bite is a proof and not a test,
  and that is worth writing down."*
- A README sentence saying "every theorem" when the audit also names a `def`
  (§6.3) — or said "every theorem" while 21 were unaudited, which is what it did
  before `e7b816c`.
- A number quoted from a stale measurement (§5.11).
- A `Negative.lean` block that has quietly started to compile.
- **A goal deleted from `Goals.lean` without a proof** (§3.2). Check 7's number
  goes down and nothing is true — the one way to make this document's headline
  measurement lie.
- A new module that is never imported into `TmKernel/TmKernel.lean` (§2.3): it
  looks built, and check 1 agrees.

### 9.3 The ceiling, which belongs in front of any agent writing prose

Over 39 catalogued defects: 12 unrepresentable, 12 proof obligations, 2 fixed by
single ownership, 4 partial, **9 missed**. Two thirds prevented or caught. The
plan says the sentence out loud, and so should you: *"Anyone quoting this design
as 'tm becomes verified' is overstating it by a factor of three."*

---

## 10. Reference

### 10.1 The package, re-measured at stage 5's CLOSING commit, 2026-09-16 (after `2b26be3`, `47a0443`, `760ead6`)

The theorem column counts declarations including `@[simp] theorem`, which is what
§6.3's third command counts and what reconciles with the audit. The right-hand
column is **stage 4's close** (`30919c1`), kept so this stage's growth is visible:
seven modules are new (`Replay`, `Lookahead`, `Log`, `Capacity`, `Priority`,
`Stamp`, `Tree`) and an eighth entry is the 58-file `Seal*` group, which alone is
half again the size of the whole stage-4 library. Rows no step since touched are
marked unchanged. The `10bae51` column this table used to carry (stage 4's *first*
close) is in this file's history as of `30919c1`.

| module | lines | theorem declarations | at `30919c1`, stage 4's close (lines / theorems) |
|---|---:|---:|---:|
| `Boundary.lean` | 11,353 | 466 | 7,099 / 298 |
| `Replay.lean` | 7,963 | 396 | — (new, phase C) |
| `Line.lean` | 6,829 | 496 | 6,749 / 494 |
| `Close.lean` | 5,838 | 258 | 5,459 / 246 |
| `Lookahead.lean` | 4,752 | 284 | — (new, D10 L1–L8) |
| `Json.lean` | 3,726 | 185 | 2,641 / 126 |
| `Log.lean` | 2,755 | 115 | — (new, D9 step B3) |
| `Plan.lean` | 2,566 | 138 | 2,518 / 135 |
| `Cmd.lean` | 2,196 | 113 | 2,196 / 113 (unchanged) |
| `Cal.lean` | 1,734 | 169 | 833 / 105 |
| `Capacity.lean` | 1,419 | 109 | — (new, stage 5 step 3) |
| `Arith.lean` | 1,080 | 90 | 1,079 / 90 |
| `Report.lean` | 889 | 35 | 889 / 35 (unchanged) |
| `Text.lean` | 888 | 48 | 857 / 46 |
| `State.lean` | 871 | 53 | 871 / 53 (unchanged) |
| `Fast.lean` | 857 | 55 | 857 / 55 (unchanged) |
| `Priority.lean` | 817 | 85 | — (new, stage 5 step 2) |
| `Stamp.lean` | 679 | 22 | — (new, D9 step B2) |
| `Tree.lean` | 541 | 37 | — (new, stage 5 step 1) |
| `Grain.lean` | 310 | 30 | 310 / 30 (unchanged) |
| `Seal.lean` **+ 57 `Seal*` modules** | **15,494** | **762** | — (new, phase W; **58 files**, each with its own import line, §2.3) |
| **78 modules** | **73,557** | **3,946** (one is a docstring line in `Cmd.lean`; the grep skips `Arith.lean`'s `private theorem cancelR`, and the two cancel) | 32,358 / 1,826 (thirteen modules) |
| `TmKernel.lean` | 78 | — (the 78 imports; §2.3) | 13 |
| `Check.lean` | 4,598 | — (3,946 `#print axioms` lines, 3,946 distinct names, 63 `APPENDED` banners) | 2,167 |
| `Negative.lean` | 1,905 | — (147 cheat blocks, highest numbered 157) | 778 |
| `Goals.lean` | 752 | — (13 goals with `sorry`, **all stage 6**; not imported) | 740 |
| **total** | **80,888** | | 36,056 |

§6.3's three counts agree exactly at **3,946** — 3,946 audit lines, 3,946 distinct audited
names, 3,946 declared. The agreement is still two off-by-ones cancelling, and knowing which
is the point of that section: the declared count includes `Cmd.lean`'s prose line at column 0
and excludes `Arith.lean`'s `private theorem cancelR`, which is not audited either, and the
audit still names one **definition**, `Tm.WfPlan`, at `Check.lean:472`. The honest sentence is
unchanged: every theorem in the 78 modules is audited except the private `cancelR`, and the
audit names one definition as well. Re-derived here by §6.3's own multiset diff: exactly two
entries, `whose` declared-and-unaudited and `WfPlan` audited-and-undeclared.

Proof : definition, by the same line-classification script, kept verbatim in the README's
"Stage 4 closed" block (`python3 /tmp/claude-1000/proof_ratio.py kernel/TmKernel/TmKernel`;
the on-disk copy was diffed against that verbatim copy at the close and is identical):
**4.03 : 1** over the 78 modules (42,506 proof lines : 10,543 definition lines), net
3.97 : 1 with witnesses and fixtures removed, 3.00 : 1 counting each declaration's doc
comment with it. Above §9.1's 3 : 1, a trigger the owner overrode (D5), so the number is
recorded and gates nothing. It **fell** from 4.80 : 1 while the library grew 2.3×, and the
arithmetic says why: what this stage added is 23,611 proof : 6,534 definition lines =
**3.61 : 1**, the design's own estimate for the tranche (§14.9, "≈ 3.6 : 1"). The spread is
wide enough that the average should not be quoted alone: `Close.lean` 10.10 : 1, the
`Seal*` group 5.74 : 1 (10,471 : 1,824), `Priority.lean` 4.48 : 1, `Lookahead.lean`
3.99 : 1, `Replay.lean` 3.32 : 1, `Log.lean` 1.86 : 1 (a field table is definition; it rose
from 1.81 when S2 added `emitEvent`), `Seal.lean` alone 0.22 : 1. *At `b344185`, stage 5's
first close:* 4.06 : 1 (42,426 : 10,451). *At stage 4's close:* 4.80 : 1 (18,815 : 3,917).
*At `10bae51`:* 4.49 : 1 (14,616 : 3,252).

Archive: `libTmKernel_TmKernel.a`, **17,202,480 bytes** (17,133,648 at `b344185`; 5,087,900
at stage 4's close: 3.4×).
FFI crate: `shim.c` 66 + `build.rs` 80 + `src/lib.rs` **105** = **251** lines (207 at
`b344185`); tests `kernel.rs` 1,922 lines (1,288), `corpus.rs` 738 (unchanged), `stack.rs`
526 and `tests/harness/mod.rs` 486. FFI tests: 86 + 8 + 6 = **100** (76 at stage 4's close).
Host side: `tm/src/cli/kernel_bridge.rs` 1,511 lines (1,253), `tm/src/cli/kernel_log.rs`
**2,202 — the binary's only reader AND writer of the log** (1,129 at `b344185`, when nothing
in the binary called it; its module header said so two commits longer than it was true, and
its blanket `#![allow(dead_code)]` outlived the switch by four — README gap 238), `tm/src/cli/kernel_capacity.rs` 1,034, `tm/src/cli/closing.rs`
**733** (622), `tm/src/cli/out.rs` **606**, `tm/build.rs` 40. `tm-core/src/log.rs` is **1,806** lines — the writer, the
decoded `Replay` and nothing else — against **3,609** before §12's deletion at `2b26be3`.

`check.sh`: **seven** checks, **3.35 / 3.09 / 3.09 s** over three serial capped runs on a
built tree, peak RSS 1.91-1.95 GiB (3.04 / 3.04 / 3.07 s at stage 5's close; 3.04 / 3.13 /
3.11 s at `b344185`; 2.4 s at stage 4's close), corpus 29/37 files and 4/5 whole plans,
burn-down 13. `cargo test --workspace`: **1,311 passed / 0 failed / 9 ignored across 78
result lines**, 0 warnings, capped (§7.5; 1,309 at stage 5's close, 1,087 across 73 at
`b344185`, 1,008 across 66 at stage 4's close). `cli_latency.rs --include-ignored`: **6
passed, 15.76 s**, the year-of-log and both three-year tests included. T5
(`kernel_replay_parity.rs --include-ignored`): **33 passed, 6.21 s**; the door suite **22**;
`cli_switch_acceptance --include-ignored` **9**; `kernel_log_grammar --include-ignored`
**18**. §12's one-reader grep: **41**, from 125 before the switch. `cargo build -p tm` into
an empty target directory: **18.98 s, 1,556,152 KiB peak RSS** (1.48 GiB; 18.93 s and
1,743,872 KiB at `b344185`). Every figure here was taken under
`systemd-run --user --scope -p MemoryMax=40G -p MemorySwapMax=0`.

*As it stood at `10bae51` (stage 4's first close):* twelve modules, 25,800 lines,
1,520 theorem declarations; `Check.lean` 1,729 lines with 20 `APPENDED` banners;
`Negative.lean` 643 (cheats 1–54); `Goals.lean` 717 (30 goals, 0/1/14/15); `check.sh`
1.1 s warm; `cargo test --workspace` 997 / 0 / 0 across 65 binaries. The `bf7cc63`
column that table carried (stage 3's close) is in this file as of `30919c1`.

`build.rs` runs `lean --print-prefix` **inside** the Lean package so it honours
`lean-toolchain`, then `lake build TmKernel:static`, then compiles `shim.c`, and
emits two `-L` search paths (`lib/lean` *and* `lib` — gmp/uv/ssl/crypto live in
the latter). It has `rerun-if-changed` on every file under `TmKernel/`, so
editing Lean re-drives lake on the next `cargo test`. Since `0c3aaf7` it also
emits `-Wl,-rpath,<toolchain>/lib` for the crate's binaries and tests, so Linux
finds the toolchain's bundled `libc++`; because a dependency's link args do not
propagate, `tm/build.rs` repeats that rpath for the `tm` binary and its test
harnesses.

### 10.2 Statements in the other documents that are stale

Check these before you quote them.

| stale statement | where | what is true |
|---|---|---|
| "`move` is open on `main`" / "426 pairs reachable on tm `main`" | PLAN §4 row A6; `kernel/README.md` | Stage 0 landed on `main` (`557a3d2`, `move_to` calling `destination` → `Err(occupied(...))`), and **`main` was then discarded** (2026-09-12), stage 0's fix with it. The restored `tm-core` is the pre-stage-0 fork point, so its `move_to` has the hole again — but the shipped binary's `move`/`readopt` go through the kernel, where `occupied` is a constructor obligation, so **A6 is dead in the binary** (`d8e8d4d`). The 426 were measured on pre-fix `main`, by a harness this clone no longer holds |
| Rust line citations (`horizon.rs:943`, `:958`, `:1323`, `:1543`, `:1792`) | PLAN §2.1, §3.2 | **they resolve again**, on the restored `tm-core/src/horizon.rs` (unchanged from `4748911`): `move_line` at 943, its `move_to` call at 958, and 1323/1543/1792 inside `close_day`/`close_week`/`close_month`. Fork-point offsets: `move_to` 819, `move_line` 943, `demote_one` 1005, `readopt` 1119, `rank` 1286, `close_day` 1322, `close_week` 1537, `close_month` 1782, `auto_close` 2032; `destination` and `occupied` do not exist there. The `main` offsets this row used to give are unreproducible. **Still cite function names.** `model.rs:686` (`default_on_miss`, Window → Expire), `priority.rs:349` and `planner.rs:323` (the two `round()` sites) still resolve |
| "Five states, not six" | PLAN §2.4, §3.1 | six. `Status` is `settled o \| live h \| demoted`; a lone `[-]` is a state |
| "the exception list ran to **P35**" / design §17's table ending at **P31** | this file (before stage 5's close); `kernel/design/stage5/stage5-D9-D10-design.md` §17 | the list runs to **P36** and design §17 carries only P13–P31. **P32–P36 live in `kernel/README.md`'s blocks alone**: P32 the candidate bounds (D10 L8), P33 (C4), P34 (C5), P35 (S2's block), **P36** a close's primary id (Q6(f)). **P32 was issued twice** and Q6(f)'s entry was renumbered to P36 at stage 5's close; nothing reconciles these numbers, which is README **gap 226**. P37 is the next free one — grep before taking it |
| "the switch is not made" | this file §8.3, 2026-09-15 to 2026-09-16 | **it is made**, at `2b26be3`. The Lean kernel is the binary's only reader of `.tm/log.jsonl` and, since `47a0443`, the only writer of its lines. The sentence was true when written and was removed at stage 5's close |
| "`priority.rs`'s only non-additive edit is `is_impossible`" | this file §8.3, 2026-09-15 to 2026-09-16 | there are **three** since `4748911`: the `use` line gaining `Exact`, `is_impossible` reading `shortfall_min_exact`, and `collect_candidates`' `events` source moving to `Replay::event_names()` (step X1). `capacity.rs` really is purely additive — 198 added, 0 removed |
| `PlanCore` has a `log` field | PLAN §3.1 | it is `{docs, store}`. Stages 5 and 6 need the log and it has nowhere to go |
| `Doc = {path, frontRaw, secs, prose}` | PLAN §3.1 | it is `{path, prose, region}`. Headings and front matter are ranked verbatim prose; §4.2's section is *derived*, not stored |
| The FFI is `tm-kernel-sys/`, ~250 lines | PLAN §5 | it is `kernel/tm-kernel-ffi/`, 192 lines at `bf7cc63` (185 at `c8f3a38`) — still the one stage-3 number that moved in the good direction |
| "2,981 lines, 7 modules, 497 KB archive, 148 theorems" | PLAN §5 | a stage-1 snapshot. §10.1 has today's |
| "scaling `Core` from five fields to the real `Item`'s twenty-two" as remaining stage-1 work | PLAN §5 | it did not happen and will not. `Core` has five fields; the item fields are views over the token vector (§5.1, §5.3) |
| "`moved`/`dropped`/`tags` are sets" in the structural tier | PLAN §3, and it is what earns E3/E4 their **U** | only `tags` exists. `moved`/`dropped` are Rust `state.json` fields with no kernel counterpart (§1) |
| the oracle's "129" and "479" clean counts | `kernel/README.md` | 126 and 481 at `c8f3a38`, twice, byte-identical, against `main`. Deterministic for a fixed seed count; they move when the kernel moves — and it has moved a great deal since. **Unreproducible in this clone** until the oracle is moved to `4748911` (§7.3) |
| "`Core` stores four things" | `kernel/README.md` prose | four again since stage 4 final step 3 (D6): `parent` is a view of the line. Between the tombstone's landing and that step it was five, `parent` a stored `none` (gap 22, closed) |
| "`lake build` from clean 1.6 s; `cargo test` from clean 3.6 s" | `kernel/README.md` header | not re-measured at `c8f3a38` or `bf7cc63`, and certainly not true of today's 20,902-line kernel. The warm numbers in §10.1 are, plus `cargo build -p tm` into an empty target directory with the archive built: 18.1 s |
| "Five separate Rust code paths" / "six entrances to one hole" | in circulation, and in an earlier version of this document | **six catalogued defects (PLAN §4.A rows A1–A6), five of them patched entrances, one hole, one precondition.** §1 settles which number means what; the harness says *five* entrances |
| "the nine T9 CLI tests"; "the remaining seven T9 tests" | AGENTS §8.3 before 2026-09-15; `kernel/README.md`'s X1 block and every block before it | **eight**, out of design §14.6's **ten**. Two are landed and passing in `tm/tests/cli_check_log.rs` (D18 (i) and (ii), `022317d`). The README's S block (`00acba7`) is the first place that says eight, and §8.3 now says it too |
| "gap 128 first", the facts decoder, as the first thing S owes | AGENTS §8.3 and §10.5 before 2026-09-15; `kernel/README.md`'s blocks up to `4aaa99e`'s own | **closed at `4aaa99e`.** `kernel_log::decode_facts` exists and T5's `kernel_replay` is that call. S's list starts at design §14.6's contents 1–3 |
| "943 tests" | in circulation | not sourced anywhere **as a claim about proofs**. 943 is `horizon.rs:943`, the line of `move_line`. The documented figure is line counts: tm-core has 19,298 test lines (re-measured on the restored tree: still 19,298), of which the kernel-area files are 9,497 (49%) — *"the tests proofs substantially replace"*. **A second, real 943 now exists and must not be confused with it:** `cargo test --workspace` passed 943 tests at the restore, `835d960` (984 at `bf7cc63`) |
| "a week→month behaviour change" needing assent; "the month of today" as `horizon.rs:1543`'s rejected rule | AGENTS §8.2 trap (b), §10.5 q1's second half; `Cal.lean`'s header; `kernel/README.md`'s "month of today" row (24) and its week → month tie-break section — all from `6f67873` | **there is no such behaviour change.** `horizon::close_week` already computes `closeTo week now`; `monthOfIsoWeek` names the month a week belongs to and is not the close rule, as `Grain.lean` says. q1's second half is **withdrawn** (§10.5). **Repaired at stage 4 step 1:** §8.2's trap, §10.5 q1 and `Cal.lean`'s header corrected; the README supersedes its row 24 and "Rejected" paragraph by name in its stage-4 block. Left as history, and to be read as wrong on this point: `Negative.lean`'s `CHEAT 24` banner (§6.2), and the origin, PLAN §3.2(b), with PLAN §6.2 q1's and stage-4 row's "two behaviour changes" (quoted in `Goals.lean`'s `# STAGE 4` header, which since stage 4's closing docs commit says to read it as one) — there is one, D1 |
| `main` is the oracle; `git checkout main -- tm-core Cargo.toml Cargo.lock`; `git show main:…` | earlier versions of this document; `tm/DORMANT.md`'s old text; `kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh` (comments and `git archive main`); README gap 36 | `main` is discarded (`f386c56`). The oracle is `4748911`; the restore ran from it (`835d960`); the oracle scripts still say `main` and fail (§7.3) |
| "The branch has no Rust kernel"; "there is currently no binary to drive"; README gap 14 "Nothing in the shipped `tm` binary calls this yet" | earlier versions of §2.2 and §5.13; `kernel/README.md` gap 14 | the workspace is restored and the `tm` binary calls the kernel for seven verbs (`d8e8d4d`, `bd61f11`) |
| `tm/DORMANT.md`: the rewiring "is underway", A6 open "until the kernel-backed wiring lands" | `tm/DORMANT.md` | the wiring landed; the file is superseded by the README's 2026-09-12 block |
| `Boundary.lean` "builds `Lean.Json`"; the JSON edge "unprovable"; check 6 covers "the JSON escaping on both sides" (README gap 6) | README J-route step 1 and 2 paragraphs, "Gap 39 REPRICED"; `kernel/check.sh`'s comment on check 6; AGENTS §2.3's old map `(+ Lean.Data.Json)` | `Lean.Json` is off the wire (`b7f504d`): `jparse` in, `jemit` out, `the_response_call_emits_parses_back` proved. Check 6 now covers only the host's half (§7.1). The README supersedes its own paragraphs by name; `check.sh`'s comment is unedited |
| `kerrName` carries "six" / "eight" strings; the ops list is "six ops, `add` still owed" | README 2026-09-12 ledger repair; its five-verb paragraph; README 2026-09-09 fifth block | ten `KErr` names plus `siteOutOfRange` under `"kernel"`, and nine ops (§2.4) |
| "What remains of stage 3 is the three JSON/newline edge laws below", with `Boundary.lean:815`-style citations | `Goals.lean`'s `# STAGE 3` header | stage 3's section holds **no** goals; its own notes below that header say each was discharged. The header sentence predates them |
| "`the_json_edge_round_trips` stands in `Goals.lean`"; burn-down 41 or higher | README paragraphs before `b7f504d` | discharged under the rename; burn-down **40** |
| q2 "`Id`'s shape" and q8 "what `report` carries" as open | earlier §10.5; README gap 13 ("stands open") | both decided by the owner, 2026-09-12 (§10.5) |
| "`exp(−age/decay)` is replaceable by a rational base at a divergence under 0.007" | in circulation | unsupported by any file in this repository. What is documented: the transcendental is **outside the kernel entirely**; the measured float-parity figures are 0 / 2,251,500 on priority bins and 135 / 150,600 = 0.09% on planned minutes, every disagreement exactly one minute |

### 10.3 Reading order when you are handed a stage

1. This document, §1–§7, then your stage in §8, then §9.
2. `PLAN-lean-kernel.md` §5 (your row), §6.2 (whether your stage has an open
   decision), §6.3 (your stop condition), §3.3 (your laws), §4 (your defect
   verdicts — and which are marked **A**, **~** or **M**, because those are not
   yours to prove).
3. `kernel/README.md`: "What is proved" for the module you are extending, then
   the gap list — one sequence, 1–51, in five places (§6.4) — and the whole
   2026-09-12 block, which is the freshest truth.
4. The module header docstrings for every file you will touch. They name the
   rejected alternative.
5. `kernel/check.sh`. It is the acceptance script and it is short.
6. `tm-spec-v1.md` for the sections your stage implements.
7. The fork point `4748911` as the oracle, by function name (`main` is
   discarded, §2.2).

### 10.4 Re-measuring before you quote

```bash
cd /Users/psixyzt/code/planner/kernel/TmKernel
wc -l TmKernel/*.lean TmKernel.lean Check.lean Negative.lean Goals.lean
grep -cE '^(@\[[^]]*\][[:space:]]*)?theorem ' TmKernel/*.lean   # attr-aware; §6.3
grep -c '^#print axioms' Check.lean
grep -c '^theorem ' Goals.lean                                  # what check 7 prints
cat TmKernel.lean                                               # every module built
ls -l .lake/build/lib/libTmKernel_TmKernel.a                    # archive size
cd /Users/psixyzt/code/planner && git worktree list && git branch -a && git log --oneline -1
# and both suites, capped (§7.5): check.sh's seven lines, cargo test --workspace's totals
```

A worktree in that listing is not evidence of work in flight; check whether its
branch is already merged (at `bf7cc63` there is none to check):

```bash
cd /Users/psixyzt/code/planner && git merge-base --is-ancestor <branch> HEAD && echo merged
```

### 10.5 Open questions that need a human decision, not a proof

Carry these forward; none is yours to settle alone. Answers the owner has given
are recorded here, with the date and the evidence they were taken on; per §4
they are settled, and changing one needs the owner again.

| # | question | due | status at stage 4's close (`10bae51`, 2026-09-13) |
|---|---|---|---|
| 1 | The two close behaviour changes — and by **constructing a stale tree and closing it**, not by reading | before stage 4 | **First half ANSWERED 2026-09-12 (D1):** `close day` targets the week containing *now* — the kernel's `closeTo` — decided after driving stale trees with the restored binary (skipping a weekend double-stamped leftovers onto the month cut list and dropped them off Monday's plan; an item whose parent was in the closing week was deleted, its minutes silently absorbed; a day closed more than 16 days late stranded work in a sealed file). Package: the stamp stays `demoted:D<dd>`; `AUTO_CLOSE_CATCHUP = 16` collapses to one step per grain. Evidence and mechanism: `kernel/README.md`'s stage-4 block (D1). **Second half WITHDRAWN:** the week→month "behaviour change" does not exist — `horizon::close_week` already computes `closeTo week now` (checked by `decide` on four dates; `rfl`-equal to `monthOfWeekByToday`) (§10.2's row; §8.2's trap). The sites were repaired at stage 4 step 1; the residual "which month file holds a week's `# Demoted` record" is README gap 52, **deferred** out of stage 4 (no consumer) |
| 2 | `Id`'s shape — the recorded resolution is weaken the spec, not tighten the data | stage 3 | **ANSWERED 2026-09-12 (D2):** ids stay digits (`freshId`'s `^9`, `^10`); spec §3.1's "4 chars of `[a-z0-9]`" width sentence is weakened to match. Closes gap 13. *The spec edit landed at stage 4's closing docs commit* (§3.1's `Item` listing, §17.2's "Ids:" bullet); the host's old generator still mints base-32 ids on `tm add`'s carve-outs and `--fix-ids` (README gap 61) |
| 3 | `parent`: derive the field and demote `parentsTotal` to a report, or keep it stored and have no hierarchy (gap 22) | **before stage 5, blocking** | **ANSWERED 2026-09-13 (D6):** derive it, strictly — `@parent` is a view over the token vector, `parentsTotal` and `parentsAcyclic` stay load preconditions (`danglingParent`, `parentCycle` refuse the whole tree), and the corpus harness loads whole trees only; B3 is unblocked (README "Stage 4 final"). *As it stood at stage 4's close:* **open — the one question in this table that blocks stage 5.** B3 (`close_week_folds_a_dropped_child_into_its_parent`) stands in `Goals.lean` on it at stage 4's close, and §6.3's child-folding clause is scoped out of the close on it (`children := .gap22Parent`). **LANDED at stage 4 final step 3:** `Core.parent` is `Field.parentRef` of the line; a dangling or cyclic link refuses by name; the column is renamed `childFoldB3`. **B3 LANDED at stage 4 final step 4:** refuted as additive (`close_week_does_not_add_a_dropped_child_to_its_parent`), the fold by §6.4's `max` beside it; the column is `dropIntoParent` |
| 4 | Which side replays the log | before stage 5 | **ANSWERED 2026-09-14 (D9):** the Lean kernel replays the log, all of it; Rust keeps only the statistical fit (plan §3.6), fed the energy and duration observations the kernel hands back. Not built at stage 5 step 1: every log-derived input (minutes done, last completion, instance status) is a plain argument whose type the kernel's own replay will produce, and the D9/D10 tranche wires them. *As it stood at stage 4's close:* **open** — and `move_has_no_inverse_command` makes replay the only correct `tm undo` |
| 5 | R7: where the `p_lounge` capacity mixture rounds (gap 26) | stage 5, consumed by 6 | **ANSWERED 2026-09-14 (D10):** nowhere — expected minutes per level are the exact mixture `p·lounge + (1 − p)·home`, exact pairs through the EDF pass; a deliberate disagreement with fork-point `capacity::lookahead`'s `p ≥ 0.5` threshold, on stage 5's parity exception list. Not built at stage 5 step 1; capacity minutes must be exact rationals and utilisation compares a `Nat` need against a rational availability by cross-multiplication. *As it stood at stage 4's close:* **open** |
| 6 | L24 / L25: prove, or keep the 882-line proptest and say so | **before stage 6 starts** | **ANSWERED 2026-09-13 (D5), by the ratio decision:** prove them; the proptest stays beside the proofs, never in place of them. *As it stood at stage 4's close:* **open**; the proptest is restored and runs (`tm-core/tests/planner_invariants.rs`) |
| 7 | Lifecycle commutation (R7 in the law list) — L27 surfaces it and does not answer it | stage 6 | **open** — L27 is refuted (stage 4 step 3) by a demote/readopt precondition pair, which does not bear on whether pairs that both succeed should commute |
| 8 | What `report` carries, and therefore its shape (§8.2). Nothing in the kernel names it today | before stage 4 writes one | **ANSWERED 2026-09-12 (D3):** a per-item list — id, disposition, destination, stamp, minutes as integer numerator/denominator. Not counts only (the month review would re-derive per-item history from the files, a second reader of one fact), and not stage 6's full diagnostics surface yet. **Landed** at `d7487b2` (`Report.lean`, `ok.report.closes`) and read by the shipped binary since `5557713` |
| 9 | Whether the kernel should refuse a `[-]` outside a week file or `month/…# Demoted`, as `tree.rs` does — a behaviour change (gap 31, §8.1) | stage 3 | **open**, not taken in stage 3 or 4. It came due when `demote` got a section target (`10bae51`), and the kernel now gives two answers to one question — the close refuses `noSection`, the verb falls back to the end of the file — recorded as README gap 60 until the owner answers |
| 10 | A child the week close drops (`[~]` in place, B3) keeps any standing `# Demoted` record where it stood, and the month close takes no settled item: should that record be carried to the next month like any record, merged into its root's record, or retired (README gap 72) | before a month review reads stamp history across months (stage 5–6) | **open** — raised at stage 4 final step 4. The fork point deleted the child's week line and carried the record; the kernel keeps both lines and carries neither. No work is lost (the child's minutes are in its root's record); the next month's review does not see the child's stamp history |
| 11 | Whether `close_keeps_source_order`'s (and `_iff`'s) added hypothesis `hfold` ("the fold drops both lines or neither") is a change B3's spec-settled fold forced, and not a D5 downgrade | before stage 5's next re-proof of it, not blocking | **open**, raised at the stage-4 final repair (README "Stage 4 final, repair", defect 2). The statement without `hfold` is proved **false** (`a_dropped_child_and_its_filed_parent_part_ways`). The case `hfold` excludes, one line dropped and one filed, now has its own order law over the source-file sites (`close_keeps_source_order_across_the_fold`), so every pair one close takes from one file by one action is covered. Nothing was deleted or weakened in the repair |
| 12 | D9/D10 design Q1: confirm the price, or narrow the scope | before the tranche | **ANSWERED 2026-09-14 (D11):** confirmed; D9 and D10 run as parallel tracks. Design §4 Q1, §22 |
| 13 | D9/D10 design Q2: pull stage 6's window, slot cut and energy prediction into stage 5 | before L2 | **ANSWERED 2026-09-14 (D12):** pulled in as L2–L4. Design §4 Q2, §22 |
| 14 | D9/D10 design Q3: the derived replay cache, reading it back, and sync | before W1 | **ANSWERED 2026-09-14 (D13):** allowed; the kernel may read a sealed record back for an explicitly old date; `tm init` excludes `.tm/cache/` from sync. Design §4 Q3, §22 |
| 15 | D9/D10 design Q4: what `--json` shows for exact capacities | before L8 | **ANSWERED 2026-09-14 (D15):** integer floors plus `…_exact: {num, den}`. Design §4 Q4, §22 |
| 16 | D9/D10 design Q5: who writes log lines | after S | **ANSWERED 2026-09-14 (D16):** the kernel, in a new step right after S. Design §4 Q5, §22 |
| 17 | D9/D10 design Q6: the seven fork quirks | — | **ANSWERED 2026-09-14:** the design's recommended dispositions (fix later a, c, e; keep b; fix after the switch d, f; g kept until stage 6). Design §4 Q6, §22 |
| 18 | D9/D10 design Q7: port or delete the unread `Replay` fields | before R11, W1 | **ANSWERED 2026-09-14 (D14):** ported; R11 keeps them and the kernel derives them into sealed day records. Design §4 Q7, §22 |
| 19 | D9/D10 design Q8: how precise `p_lounge` may be | before L6 | **ANSWERED 2026-09-14 (D17):** `capDen = 10^18`, `u128` units, digit strings on the wire. Design §4 Q8, §22 |
| 20 | D9/D10 design Q9: a damaged or hand-edited log | before S | **ANSWERED 2026-09-14 (D18):** `tm check` warnings for malformed and far-future lines, a named fault beyond the rebuild bound, the cap never raised. Design §4 Q9, §22 |
| — | `main`: keep it as the oracle, or discard it | — | **DECIDED 2026-09-12 (D4):** discarded (`f386c56`); the fork point `4748911` is the restore source and the oracle; stage 0's fix, `invariant_exhaustive.rs` and the ability to reproduce anything measured on `main` went with it (§2.2) |

**Stage 4 is closed (2026-09-13); stage 5 is blocked.** Stage 4's gating
decisions (q1, q8) were answered and both landed. **q3 / gap 22 (`parent`) is the
one question in this table that blocks stage 5**, and B3 stands on it. Separately
from this table, §9.1's proof-to-definition trigger **fired** at stage 4's close
(4.49 : 1 over the library), and its action — whether stage 5 keeps proving
relational laws — is also the owner's to take before stage 5 starts. Still owed
to the human, in the order they block: **q3** (blocks stage 5, and B3), the §9.1
decision (before stage 5), **q4** (before stage 5, not blocking), **q5** (stage
5), **q6** (before stage 6), **q7** (stage 6), and **q9** (gap 60) — plus the
30-minute drives of the stage-3 and stage-4 binaries (§5.13).

**Update 2026-09-13 (D5–D8, README "Stage 4 final").** q3 is answered (D6) and the
§9.1 decision is taken (D5: keep proving), which also answers q6. Neither blocks
stage 5 any longer. Gap 55's two halves are decided (D7: past-due dated lines to
`backlog.md # Overdue`; D8: not-yet-due ones demoted with their `due:`). Still owed
to the human: **q4** (before stage 5, not blocking), **q5** (stage 5), **q7**
(stage 6), **q9** (gap 60), and the §5.13 drives. *D7 and D8 landed at stage 4
final step 2, D6 at step 3 (gap 22 closed).*

**Update 2026-09-13, stage 4 final step 4 (README "Stage 4 final, step 4").** B3 is
refuted and renamed with §6.4's `max` law beside it, and **stage 4 holds no goal**
(burn-down 29, all stages 5–6). Nothing in this table blocks stage 5. The step raised
one new question for the owner, **q10** (gap 72: where a dropped child's standing record
goes), not blocking. Still owed to the human, in order: **q4** (before stage 5, not
blocking), **q5** (stage 5), **q10** (stage 5–6), **q7** (stage 6), **q9** (gap 60), and
the §5.13 drives of the stage-3 and stage-4 binaries.

**Update 2026-09-13, stage 4 final repair (README "Stage 4 final, repair").** Four
verification defects are fixed. A refused tree is no longer written by the §5.1 timeouts
(behaviour row 39). The mixed pair has an order law. `NhMm` estimates are read by the
kernel's stage-one reader (row 40). The close's human line counts dropped children
(row 41). The repair raised **q11** (whether `hfold` is a forced change), not blocking.
Still owed to the human: **q4**, **q5**, **q10**, **q11**, **q7**, **q9**, and the §5.13
drives.

**Update 2026-09-14, stage 5 step 1 (README "Stage 5 step 1").** q4 is answered (D9: the
kernel replays the log, all of it) and q5 is answered (D10: the capacity mixture is exact).
Neither is built yet; the step's types are shaped to take them. Still owed to the human:
**q10**, **q11**, **q7**, **q9**, and the §5.13 drives.

**Update 2026-09-14, stage 5 step 2 (README "Stage 5 step 2").** No question in this
table was answered or raised. §7.1's priority, §7.2's rule table and §7.4's hysteresis are
built in `Priority.lean` on D9's and D10's types: log-derived rule inputs are plain
arguments, and the ladder takes an exact rational availability. Still owed to the human:
**q10**, **q11**, **q7**, **q9**, and the §5.13 drives.

**Update 2026-09-14, stage 5 step 3 (README "Stage 5 step 3").** No question in this table
was answered or raised. `Capacity.lean` builds §7.3's EDF reservation pass on D10's type:
numerators over one positive denominator. It follows fork-point `capacity::reserve` and
`capacity::available_until`, and `priority::compute`'s loop. Stage 5 holds no goal in
`Goals.lean`. What remains of the stage waits on the D9/D10 tranche: the replay, the
lookahead, the floor pass and candidate selection. Still owed to the human: **q10**,
**q11**, **q7**, **q9**, and the §5.13 drives.

**Update 2026-09-14, the D9/D10 design's answers (README "Stage 5 D9/D10: the owner's
answers").** The design's nine questions are answered as D11–D18 and Q6's dispositions (rows
12–20 above; §4's table). Nothing in the design's step plan is blocked on the owner. Still owed
to the human: **q10**, **q11**, **q7**, **q9**, and the §5.13 drives.

**Update 2026-09-15, stage 5's close (README "Stage 5 closed").** No question in this table was
answered or raised, and **nothing here blocks the switch**: D9's phases A, B, R, C and W, D10's
L1–L8 and phase F1 all landed, and S is owed for its own reasons (§8.3's list — **not** gap 128,
which closed at `4aaa99e`), not for want of an owner decision. The stage's acceptance ran and is recorded in §8.3: over the log corpus the
only measured disagreement with fork point `4748911` is **P21**, four sightings, none of which
reaches a display. Still owed to the human, unchanged: **q10** (a dropped child's standing
record), **q11** (whether `hfold` was forced), **q7** (lifecycle commutation, stage 6) and **q9**
(gap 60, the `[-]` refusal) — plus the **§5.13 drives**, now of three binaries. The stage-5 drive
is design §14.6's own list, and it cannot be run until S lands, because the shipped binary still
does not read the log through the kernel.

**Update 2026-09-16, STAGE 5 CLOSED (README "Stage 5 closed — the kernel reads and writes the
log").** No question in this table was answered or raised. The switch landed (`2b26be3`), the
kernel writes the lines it reads (`47a0443`, D16), quirk Q6(f) is fixed (`760ead6`), and the
parity harness was **re-run after the switch** through a rebuilt fork-point oracle: over 469 logs
/ 8,442 `Replay` keys / 195,243 scalar values the only disagreement is **P21**, 24 sightings, none
reaching a display; over the capacity surface it is **P1, P2, P3, P27** and nothing else;
`remaining`, the rollup and the series head stay unreachable, denominator **0**. Still owed to the
human, unchanged in kind: **q10** (a dropped child's standing record), **q11** (whether `hfold`
was forced), **q7** (lifecycle commutation, stage 6) and **q9** (gap 60, the `[-]` refusal) — plus
the **§5.13 drives of three binaries**, which are now the *only* thing stage 5 owes the owner and
which **an agent cannot perform** *(partly false: a pty drives it, §5.13, README gap 3527)*: `tm tui` refuses a non-tty by name, and design §14.6's drive
list asks for the TUI through two reloads (README gap 182). The drive is also where two recorded
questions get decided: **gap 131** (a close cannot be aimed at an older period — the refusal is
right, the drive item as written is not performable) and **gap 139** (`--now` at an earlier
instant rolls `.tm/state.json` back — should `--now` be read-only?). **One step of stage 5's own
plan did not land and was carried by name into stage 6: L9 (gap 93). Gap 210 closed at stage 6
W-13 track B and L9 itself closed at stage 6 W-13 step L9** — day 0 of the lookahead is the
kernel's own, derived from its own replay, and `Ctx::window` and `Ctx::today_slots` are gone from
the binary. It was never an owner question; it was work, priced by design §14.8 at 4-6 agent-days.
