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

**Nothing is in flight.** `git worktree list` shows the one checkout and no
other; the `stage-goals`, `orient-demotion` and `wire-fields` worktrees this
paragraph used to list belonged to the original machine and do not exist in this
clone. `git branch -a` shows `rebuild-on-lean` and its remote twin and nothing
else: **`main` is gone** — the owner discarded it on 2026-09-12 (`f386c56`,
§2.2). Stage 3 is closed out as far as its scope reaches (§8.1 says exactly
what that means, and what is still owed by name), and stage 4 is unblocked
(§10.5).

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

**Seven** checks, exit 0, warm wall time 1.1 s (four consecutive capped runs at
`bf7cc63`: 1.13, 1.11, 1.10, 1.10 s; `c8f3a38`'s were 1.15, 1.14, 1.11 s). It is
the kernel's acceptance script, it is short, and you should read it before
claiming any of its checks — and since 2026-09-12 it is **not the whole
acceptance**: `cargo test --workspace` stands beside it (§7.5). Note it is `set -uo pipefail`
and **not** `-e`: all seven run regardless, so one failure does not hide the
others. §7 says what each one proves.

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
Cal ──▶ Grain ──▶ Text ──▶ Line ──▶ State ──▶ Plan ──▶ Cmd ──▶ Close ──▶ Boundary
                   │                                                      ▲
                   └──▶ Json ─────────────────────────────────────────────┘
Arith                       (standalone: nothing imports it but the root)
```

Root import order (`cat TmKernel.lean`): `Arith Cal Grain Text Json Line State
Plan Cmd Close Boundary`. `Json` imports `Text` only; `Close` imports `Cmd`;
`Boundary` imports `Close` and `Json` (stage 4 step 2 — it imported `Cmd`
before). **No module imports `Lean.Data.Json` any more** — the wire is the
kernel's own (§2.4).

- `Cal` — the calendar. Days since 0001-01-01, proleptic Gregorian. ISO weeks.
- `Grain` — the horizon order, all of it derived from `coarsen`.
- `Text` — tokens, numerals, list surgery, `freshId`, the structural `splitOn`/`joinWith`. A token carries its own separator.
- `Json` — the kernel-owned JSON fragment: `JVal`, `jescape`/`junescape`, `jemit`, the fuel-structural `jparse`, `jget`, and `jparse_jemit`. 2,641 lines.
- `Line` — the item line and the whole of §4.1's field grammar, with the parse ⇒ wf bridges. 6,494 lines.
- `State` — entity versus observation. `Core`, `wf`, `Entity`, `render`.
- `Plan` — `Store`, `Doc`, `PlanCore`, `planWf`, `WfPlan`, and the comment rule (`commentAfter`).
- `Cmd` — `lift`, `Transform`, `Dest`, `WfPlan.mapAt`, `KErr`, the commands (`cmdMove cmdDrop cmdSetEst cmdDemote cmdReadopt cmdRank cmdEdit cmdUnset`, and `WfPlan.insertFresh` for `add`), the `EditVal` table.
- `Close` — §6.3's lifecycle as one fold at three grains: the `ClosePolicy` table and its bridges, `close`, the landing rank shift, `close_spec`. Not on the wire yet (kernel/README.md, stage-4 step-2 block).
- `Boundary` — `String → String`: the request readers, `parseCmd`, the loader, `respond`, `call`, `callExport`.
- `Arith` — exact rational arithmetic. Nothing consumes it yet.

**A new module is not built until it is imported.** `kernel/TmKernel/TmKernel.lean`
is eleven `import TmKernel.<Mod>` lines and nothing else; `lakefile.toml` names one
`lean_lib TmKernel` and no module list. So a `.lean` file dropped into
`TmKernel/TmKernel/` that nobody imports is **not compiled by check 1**, is not in
`libTmKernel_TmKernel.a`, and is therefore invisible to the Rust — while
`check.sh` still prints seven `ok`s. Stage 3 added one (`Json`, imported at
`c2ad8f6` in the same commit), stage 4 added `Close` (imported in the commit
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

```jsonc
// request
{"docs":[{"path":"week/2026-W37.md","grain":1,"ix":105695,
          "lines":["# Tasks","- [ ] 5 6b Finish the report ^m1"]}],
 "cmds":[{"op":"move","id":"m1","doc":0}]}
// doc: path, lines (every element a string); grain ∈ 0..2 (day week month) or
//      null/absent = no region; ix required when grain is present
// ops, nine:
//   move{id,doc}  drop{id}  est{id,min}  demote{id,doc,period,grain?}
//   readopt{id,doc}  rank{id,rank}  add{seed,doc,title}
//   edit{id,key,value}            // value "" is the unset form
// demote's grain is a STRING: "d" stamps D<period>, anything else or absent W<period>
// rank is a raw document rank (a line index); add's id is the kernel's (freshId)
```

**The response has one `ok` shape and nine `err` shapes.** Quoting one of them
as if it were the taxonomy is how a host ends up with a `match` that falls
through. All ten, from `Boundary.lean`, keys in the order they are emitted:

```jsonc
{"ok":{"docs":[{"path":…,"lines":[…],"grain":…,"ix":…}]}}   // grain/ix only if the request declared a region
{"err":"<free text>"}                          // jsonErr: see below
{"err":{"kernel":"<name>"}}                    // see below
{"err":{"dupId":"<id>"}}
{"err":{"notADemotion":"<id>"}}
{"err":{"ambiguousDemotion":"<id>"}}
{"err":{"duplicatePath":"<path>"}}
{"err":{"badLine":{"path":…,"line":…,"why":…}}}   // why is repr of a PErr: notAnItem|badState|noId|manyIds
{"err":{"unterminatedComment":{"path":…,"line":…}}}   // line = the opener's 0-based index (a4ccd9c)
{"err":{"itemCheck":"<fault>"}}                // firstItemFault, 7 values: rankCollision danglingParent
                                               // parentCycle danglingDep depCycle sectionDiscipline fileKindShape
```

`"kernel"` carries **eleven** strings, and ten of them are `KErr`, from
`kerrName`: `occupied`, `noSuchId`, `notDemoted`, **`alreadyDemoted`**,
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
five title refusals `titleNewline titleTab titleId titleBlank titleEdge`; and
the edit's `unknownKey <k>`, `keyNotWired <k>` (only `demoted` today, by policy)
and `badValue <k>`. The host (`kernel_bridge::refusal`) maps these names to
`detail.refusal`. Re-derive the list rather than trusting this block:

```bash
cd /Users/psixyzt/code/planner/kernel/TmKernel/TmKernel
grep -n '"err"\|"kernel"\|jsonErr\|lerrJson\|throw\|kerrName' Boundary.lean
grep -n 'def jget' -A 8 Json.lean
```

There is **no `now`, no `log`, no `cfg`, no `model`, no `seed`** in the request,
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
| R2 | No new `axiom` declarations. The only axioms the package may reach are `propext`, `Quot.sound`, `Classical.choice` | `Check.lean` prints every theorem's axiom set; read the diff |
| R3 | No `native_decide`. It discharges a goal by trusting the compiler and the linked C, which is exactly the layer the kernel exists to distrust. `decide` is the workhorse; give it budget instead (§5.10) | `totality.py` |
| R4 | No `partial def`, no `unsafe`, no `opaque`, no `@[implemented_by]`, no `panic!`, no `!`-accessors (`.get!`, `xs[i]!`) | `totality.py` bans `partial def`, `panic!`, `native_decide`, `sorry`, `]!`, `.get!`, `.toOption`; the rest are audit items |
| R5 | No `.toOption`. `Except` all the way through the boundary | `totality.py` |
| R6 | No Mathlib. Core toolchain only (`Fin`, `Nat`, `Option`, `Except`, `Subtype`, `List`, `omega`, `decide`, `simp`, `Lean.Data.Json`) | absence from `lakefile.toml`; and needing it is a **stop condition**, not a decision you take (§9) |
| R7 | No new dependencies of any kind, Lean or Rust | `lake-manifest.json`, `Cargo.toml` |
| R8 | Do not touch `kernel/TmKernel/lean-toolchain` (`leanprover/lean4:v4.33.1`). `lake update` once moved a pinned v4.33.1 to v4.34.0-rc2 unasked and cost two link failures with a misleading error | review |
| R9 | Nothing but `String` crosses the FFI. No `lean_object*` escapes the shim | `nm` on the archive; the shim is 66 lines and stays that way |
| R10 | Every bounded type gets a `Fin`/`Subtype`, a smart constructor its decoder actually uses, and a rejection theorem. Every integer crossing gets a stated width | `Negative.lean` cheats; audit |
| R11 | A field's setter is not exported without its `view ∘ set = id` proof | audit; `Negative.lean` CHEAT 5 |
| R12 | `Negative.lean` must fail to compile | `check.sh` check 4, which inverts the exit code |

`totality.py` takes **one or more directories** and scans each one level deep,
non-recursively. `check.sh` passes **two**:

```bash
cd /Users/psixyzt/code/planner/kernel && python3 totality.py TmKernel/TmKernel TmKernel
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
stage 4 rather than a surprise inside it.

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

**Two live exceptions, both recorded rather than hidden.** `parent` is still a
stored slot and is always `none` (gap 22). And two readers of `est:`
still coexist on the command path (gap 4), which the README labels *"a
live S2"* — by its own accounting the kernel contains one instance of the class
it exists to remove. Do not inherit either silently.

*Status at `bf7cc63`: one exception left.* Gap 4 is **closed** (`7af7f1a`):
`Cmd.setEstE` writes through the field setter, and
`the_command_path_writes_what_the_field_path_reads` — generalised by the edit
widening to `the_edit_path_writes_what_the_field_path_reads`, over every wired
key — is the theorem. `parent` (gap 22) is the one that stands. A new instance
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
binary is still owed (§8.1).

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

**The check that makes this safe**, because the append step is manual and has
demonstrably lost names:

```bash
cd /Users/psixyzt/code/planner/kernel/TmKernel
grep -c '^#print axioms' Check.lean                                     # 1299 (1006 at c8f3a38)
grep '^#print axioms' Check.lean | awk '{print $3}' | sort -u | wc -l   # 1299
grep -hcE '^(@\[[^]]*\][[:space:]]*)?theorem ' TmKernel/*.lean | awk '{s+=$1} END {print s}'   # 1299
```

**These told an inconsistent story and were repaired at `e7b816c`; the trap that
produced it has not gone away.** `#print axioms` accepts **any** constant — a
`def`, a `structure`, an `abbrev` — and prints a normal-looking line, so a name
whose final dotted segment was dropped audits the *type* and cheerfully reports
"does not depend on any axioms". That is how 21 theorems came to be unaudited
while the count looked healthy.

At `bf7cc63` the three numbers agree at 1299 — and the agreement is still the
same two off-by-ones cancelling, which you should know before you quote it
(re-checked by diffing declared short names against audited last segments; the
only mismatches are dotted declaration names such as `Q.le_refl`, the prose line
and the `def` below):

- 1299 audit lines, 1299 **distinct** names: no name is audited twice.
- Every theorem declared in the ten modules is audited. `^theorem` alone misses
  the declared `@[simp] theorem`s, which is why the grep above allows an
  attribute prefix.
- The third number counts one prose line — `Cmd.lean`'s header contains
  *"theorem whose command argument was unused"* at column 0 — so there are 1298
  real declarations, under one fewer distinct short name
  (`clock_rejects_minute_60` exists in two namespaces).
- **Plus one non-theorem** in the audit: `Tm.WfPlan`, a `def`, is still audited,
  now at `Check.lean:475`. That is the last instance of the pattern the repair
  removed. Leave it or delete it deliberately; do not let it breed.

So the honest sentence is *"every theorem in the ten modules is audited, and the
audit names one definition as well"* — not *"every theorem"* with nothing after
it. `check.sh` reports the audit size by grepping its own output, so its printed
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
6. Run `check.sh`, capped (§2.1). All **seven** checks, exit 0 — and
   `cargo test --workspace` green beside it (§7.5).

---

## 7. How to verify your own work before an audit does

### 7.1 The seven checks, and what each one proves

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
a `sorryAx` here means `Goals.lean` leaked into something proved (§3.2). It does
**not** prove coverage; see §6.3.

**4 — `Negative.lean` MUST fail to compile.**

```bash
cd /Users/psixyzt/code/planner/kernel/TmKernel
LEAN_PATH=.lake/build/lib/lean ~/.elan/bin/lean Negative.lean    # exit 1
```

The only check that tests the type system rather than a theorem. `check.sh`
inverts the sense: if this ever compiles, the build fails.

**5 — Rust calls the kernel and gets the right answers.**

```bash
cd /Users/psixyzt/code/planner/kernel/tm-kernel-ffi && cargo test --quiet --test kernel
```

57 tests through `Rust → C shim → Lean` at `bf7cc63` (26 at `c8f3a38`). Proves
the export is reachable and the wire format is what both sides think it is —
and, since J5, it is the main evidence for the one agreement no theorem can
state: that serde_json reads what `jemit` writes and writes what `jparse` reads.

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

The whole-plan number is the one carrying information, and it moved: `1/5 → 4/5`
when the demotion model landed at `8eea3d6`. `plan-basic`, `plan-home-day` and
`plan-travel-day` were refused as `splitLine: m2`; `LErr.splitLine` is now
**deleted**, because the tombstone carries its own bytes and there is nothing
left for it to refuse. The fifth plan is `plan-conflicts`, which exists to be
refused. Do not quote `1/5`, and do not look for `splitLine` — it is gone.

### 7.3 The differential oracle (not in `check.sh`)

**Broken in this clone, and owed.** `build-oracle.sh` runs `git archive main`,
and `main` was discarded on 2026-09-12 (§2.2), so the script fails before it
builds anything. Its source must move to the fork point `4748911` — the README's
"`main` DISCARDED" paragraph says so — and every "no disagreement" it prints from
then on is against the fork-point grammar, whose delta to `main@557a3d2` is stage
0's fix. The numbers below were measured against `main` at `c8f3a38` and cannot
be reproduced here. What the paragraphs below say about its method stands.

```bash
cd /Users/psixyzt/code/planner/kernel/tm-kernel-ffi
./examples/oracle/run-oracle.sh <scratch-dir> [cases-per-seed] [seeds]
```

It extracts `main` into a scratch directory, builds a small binary against the
shipped `tm-core::grammar`, and runs both implementations over two input sets:
the corpus's own item lines, and `main`'s own `grammar_proptest` generator over
several seeds. It writes nothing inside the repository. It is deliberately **not**
a seventh check, because it needs a Rust build of `main` outside the repo, which
is the wrong dependency for an acceptance script that must run on this branch
alone.

It prints the denominator for every comparison, so "no disagreement" is never
confused with "never ran". Four things are comparable through a `String → String`
boundary: is it an item line; does each side hand the line back unchanged; what
id does each read; does `tm edit est=` produce the same line. Title, `ci`,
priority, parent, tags, shape, recurrence, budget, `loc:`, `buffer:` and the
flags are **not** compared, because the kernel keeps those tokens verbatim and
has no answer to differ from (gap 35).

Run twice at `c8f3a38` with `512 4`, byte-identical both times: **138 corpus
lines compared, 126 with nothing to report; 2,048 generated lines compared, 481
with nothing to report.** These are deterministic for a fixed seed count — they
move when the *kernel* moves, not between runs. The README's `129`/`479` were
taken before the demotion model changed; that is the whole point of §5.11.

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
#   984 passed / 0 failed / 0 ignored across 64 test binaries at bf7cc63, 4.9 s warm
```

They do not overlap: the root workspace `exclude`s `kernel/tm-kernel-ffi`, so
`cargo test --workspace` does **not** run the FFI crate's own 63 tests (checks 5
and 6 do), and `check.sh` does not run the CLI, TUI, `tm-core` or proptest
suites. The FFI crate's `build.rs` re-drives `lake` when any file under
`TmKernel/` changes, and `tm` depends on that crate, so the workspace run also
rebuilds the kernel it links (`tm/build.rs` only adds the toolchain `lib/` rpath). A green
`check.sh` with the workspace unrun is half an acceptance; say which half in
the commit if it is all you have.

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
`a_file_splits_into_the_lines_it_was_joined_from` restated over the kernel's own
`Tm.splitOn` and proved as `…_char`, and `joining_lines_is_injective` **refuted**
as `joining_lines_is_not_injective_char`, both `a6dcc96`;
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
  refused; stage 4 territory, recorded not fixed.
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

**Status at stage 4 step 2 (2026-09-12).** Scope items 1 and 2 are landed in
`TmKernel/Close.lean` (`ClosePolicy`, `close`, `close_spec`); items 3 and 4
(`autoClose`, `now` on the wire) are not. `close_day_stamps_a_day_stamp` is
discharged (burn-down 39); narrowed forms of three over-strong goals are proved
beside them and their refute-and-renames are owed; gaps 53–57 are the step's
debts. Read kernel/README.md's stage-4 step-2 block before taking the next step.
*Step 3 (2026-09-12):* `close_is_idempotent` (L16) is discharged as stated, and
L17 and L27 are refuted and renamed (`close_week_and_close_month_do_not_commute`,
`lifecycle_commands_do_not_commute`); burn-down 36. L17's orders differ only in
rank — every line's skeleton commutes (`two_closes_at_one_instant_commute_on_skeletons`).
README stage-4 step-3 block.
*Step 4 (2026-09-12):* scope item 3 is landed — `autoClose` is each grain's
close once, coarsest last (`Close.lean`); L19a and L19b are discharged as
stated, L19c is refuted and renamed (`autoClose_leaves_lines_in_periods_it_passes`)
beside its narrowing `autoClose_strands_no_unfinished_line`, and a loaded
three-month-stale plan is decided catching up with every id kept, one stamp at
most per line and its summed estimate unchanged; burn-down 33. The shipped
binary still runs the sixteen-period loop until `close` reaches the wire.
README stage-4 step-4 block.

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
not a discovery inside it.

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
above still govern its shape.

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
- **If assent is refused, L16 may not be provable.** The idempotence argument is:
  after the fold, no entity's live site is in a closed region of grain `g`, so
  the second run folds over the empty set — which is `closeTo_target_is_open`.
  With `targetContaining`, the fold's own output can be back in scope and the
  proof does not go through. Record it as a stop point, not a surprise.
  *Status: assent was given for (a) (D1), so the `closeTo` argument is the one
  L16 gets.* *Proved at step 3. For one grain the old rule would have broken it
  at month only; at day and week it breaks across grains (L19b) — README
  stage-4 step-3 block, read off the definitions.*
- **L17 is an expected refutation, and a refutation is a deliverable.**
  `close week ∘ close month` is not expected to commute. *Refuted at step 3 —
  through rank in the shared `# Demoted`, not through one close seeing the
  other's output, which D1 rules out.*
- **Four stage-4 goals are stated stronger than §6.3 allows**, and the repair is
  refute-and-rename (§3.2), never a weakened predicate:
  `close_leaves_no_live_line_in_a_closed_region` and
  `autoClose_runs_every_period_it_passes` quantify over settled, recurring and
  wall lines §6.3 leaves in place; `close_writes_every_estimate_through_demoteEst`
  equates the whole line and so forbids the `demoted:` stamp;
  `close_never_demotes_a_wall` forbids the carry fork-point `close_week` performs.
  Priced, with L17's and L27's expectations, in the README's stage-4 block.
- **`demote` must learn to target a *section*** (gap 20). §6.3 files the
  copy into `month/<current>#Demoted`; today `demote` lands it at `freshRank`.
  This changes `demote`, its `normalized`-preservation lemma, and `sectionsWf`.
  §6.2's "outcome with an estimate is a `tm check` warning" is unimplementable
  until then, because the two-line demotion form this kernel writes would trip it.
  *Status (step 2): landed for `close`'s week row (a rank shift makes room in
  `# Demoted`); the `demote` wire verb still lands at `freshRank`, `sectionsWf`
  is unchanged (§10.5 q9), and the warning still needs `parent` (gap 22).*
- **Stage 4 *is* the code that writes the legitimately-differing pair**
  (gap 31). The named fix is a second `RawItem` on `Core` for the
  tombstone, set by `demote` and cleared by `readopt`, with `renderCore` reading
  it at the archive site — and `orientPair` needs a glyph clause, with
  `demotionsOriented` changing alongside it because it is part of `planWf`.
  *Status (step 2): subsumed — that `RawItem` is `Tomb.line`; `close` writes the
  differing pair through `demote`, and neither `orientPair` nor
  `demotionsOriented` changed.*
- **Backlog orientation is fine, and here is why.** `horizonPrecedes (some _)
  none = true`, so every bounded region precedes backlog: a close that files
  overdue work into `backlog.md#Overdue` leaves the tombstone (in the week)
  legitimately preceding the live line (in backlog). `demotionsOriented` will not
  refuse it. Worth knowing because the opposite is the natural guess.
- **Two rows of §6.3 need things stage 5 owns.** "Dated items past due with
  `persist` → `backlog.md#Overdue`" needs `due:` evaluation and §5.3's `on_miss`;
  "unfinished children are dropped, their remaining folded into the parent's
  `est:`" needs §6.4 rollups, which need `parent`, which is always `none`. Either
  pull them forward or scope them out **by name** in the README.
  *Status (step 2): scoped out, and visible in the table itself — the week row's
  `overdue := .stage5OnMiss` and `children := .gap22Parent`.*
- **F3 is missed until stage 6.** `close day` replacing a written review with
  `review pending` needs generated-block ownership. Stage 4 covers F1, F2, F4, F6
  — do not claim §6.3 complete.
- **Recurring items and calendar intervals are never demoted** (§6.3's last
  paragraph). That is a `ClosePolicy` exemption.
- **`demote` is deliberately not idempotent**, because the month review's cut
  list is "≥ 2 stamps" and stamps accumulate on purpose. The stamp must reach the
  file — see §5.3 for the bug where it did not.
- **Two idempotences must not be conflated.** §6.3's "runs automatically on the
  first command after the period ends (idempotent; recorded in `state.json`)" is
  a Rust fact about a `closed` map. L16's `close g` idempotence is a fact about
  the fold on `WfPlan`. Only the second is a kernel theorem.

**Inherited debt.** Gaps 2, 3, 16, 17, 20, 22, 31.

**One thing stage 4 owes stage 5.** Measure the proof-to-definition ratio at the
end of this stage and write it in the README. It is a stop-condition trigger
(§9.1) and stage 5 needs it before it starts.

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
4. **Capacity lookahead (§8.4).** `minutes_at_level : [u32; 6]` per day.
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
hierarchy — a plan-tier decision nobody has taken.

**Acceptance.** The parity harness. **Its exception list is longer than the six
rounding sites**; extend the existing oracle scaffolding rather than writing a
new one — after first moving it off `main`, which no longer exists, to the fork
point `4748911` (§7.3). Stage 5's parity is therefore against the fork-point
Rust.

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
  `jparse_jemit` still holds. The last sentence stands unchanged.
- **`binsWf` and `descending` are two decidable checks a loader should run**
  (gap 27). `ladder_eq_rungs` needs the edges sorted;
  `rungs_antitone` does not. A misconfigured `priority.bins` still produces a
  well-defined antitone bin that is **not** §7.1's ladder, and there is no
  `planWf` clause rejecting it, because config validation lives at the boundary.
- **`0/0` is a decided disagreement, not a rounding site** (gap 25).
  §7.1 says "capacity 0 → `u = ∞`" with no exception for zero need, so
  `utilGe 0 0 e = true` and an item with nothing left to do and no capacity comes
  out **HOT**. An `f64` implementation gets `NaN`, every comparison is false, and
  it falls into the *lowest* bin. Both are defensible. **The parity harness will
  report this and it is not one of the six stated sites** — add it to the
  exception list *before* running, or acceptance fails for a reason already
  decided.
- **R1 is a systematic disagreement, not a rare one.** §3.5 changes `need_min`
  from `round(rem × 1.3)` to **ceiling**, because a margin rounded down stops
  being a margin. The Rust computes it twice — `priority.rs:349` in
  `safety_minutes` and `planner.rs:323` inline — and both must move together or
  the harness sees two different Rust answers for one rule.
  `rounding_the_need_changes_the_bin` is why the ordering path uses
  `utilScaledGe` and never `needMin`.
- **R7 is open and it is the planner's to decide** (gap 26). §8.4
  mixes lounge and home capacity by `p_lounge`, a rational weight over two
  integer minute counts. Whether the planner floors per level, per day, or
  carries the pair exact into the EDF pass is undecided. Decide it here and state
  it, or stage 6 inherits an unstated rounding.
- **The log has nowhere to live.** `PlanCore` is `{docs, store}` — there is no
  `log` field, against the plan's three-field sketch. Instance status comes from
  the log (`done inst=…`, `skip inst=…`), and so do `done_minutes`,
  `blocks_done` and lost minutes. §3.6 keeps the *statistical* layer in Rust —
  but `log::replay` is not statistics. **Decide which side replays, and say so.**
- **Hysteresis is a second relational-ish law and it is not in L1..L27.** §7.4:
  `p` may improve by at most one bin per day relative to yesterday's stored `p`,
  unless the new value is 0. It makes today's priorities depend on yesterday's
  output. Name it and place it in a tier before writing it.
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
- **Series head has no home** (gap 18). `seriesOf` derives the
  `## series:<name>` a placement sits in; §5.4's head rule and the implied
  `after:` a series section carries are planner concepts.
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
provisional `Seg`/`DayPlan`/`PlanReq`/`dayPlan` vocabulary:
`plan_does_not_overbook`, `plan_reserves_one_block_at_a_time`,
`plan_respects_the_energy_filter`, `plan_places_no_block_over_a_wall`,
`plan_places_no_block_over_a_break`,
`plan_places_no_demanding_block_after_wind_down`, `plan_never_moves_a_wall`,
`plan_is_monotone_in_rank`, `plan_puts_hot_before_the_queue`,
`plan_never_drops_an_impossible_item`,
`plan_never_batches_past_an_equal_ci_candidate` (these eleven are L26's
single-run checks), `the_window_end_solves_the_equation` and
`the_window_end_is_the_least_solution` (E7), and `plan_tail_drop` /
`plan_is_stable_across_a_replan` — L24 and L25, the two relational ones the
recorded recommendation says to leave to the proptest. If you take that
recommendation, the two goals stay in `Goals.lean` and check 7 ends the stage at
2, not 0. That is the correct outcome; say so rather than deleting them.

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
| Proof : definition exceeds **3 : 1**, measured at the end of stage 4 | 4 → 5 | stop proving relational laws; keep decidable checkers plus the existing proptests, and **say so in the README** rather than letting the ratio quietly eat the schedule |
| Any needed proof requires **Mathlib** | any | **stop and re-price at that moment.** 9.7 GB on disk, a 118 MB binary, `Mathlib:static` on every linking machine, and — decisively — Mathlib chooses your Lean version, release candidates included. This is not a decision an agent takes |
| A kernel call in the TUI exceeds **5 ms at 500 items** | 6 | try the session handle (`lean_mark_mt` + a mutex, UI thread only); if that is not enough, the runtime kernel is the wrong shape for the TUI |
| Two consecutive Lean upgrades each cost more than a day of proof repair | any | freeze the toolchain and treat the kernel as a fixed artifact, or fall back to a design-time model |
| After stage 3: a clean exhaustive **depth-3** sweep, plus 60 days of use with no new defect in the covered class | 3 | **the bug class is gone.** Stages 5–6 then buy uniformity, not soundness. *"That is a legitimate reason to stop, and it should be stated out loud if it happens"* |

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

### 10.1 The package, measured at `bf7cc63` on 2026-09-12

The theorem column counts declarations including `@[simp] theorem`, which is what
§6.3's third command counts and what reconciles with the audit. The `c8f3a38`
column is the previous stamp, kept so the growth is visible.

| module | lines | theorem declarations | at `c8f3a38` (lines / theorems) |
|---|---:|---:|---:|
| `Line.lean` | 6,494 | 481 | 6,190 / 463 |
| `Boundary.lean` | 3,909 | 161 | 1,939 / 82 |
| `Json.lean` | 2,641 | 126 | — (new, `c2ad8f6`) |
| `Plan.lean` | 2,435 | 132 | 2,033 / 106 |
| `Cmd.lean` | 1,609 | 82 | 847 / 44 |
| `Arith.lean` | 1,079 | 90 | 1,079 / 90 |
| `Text.lean` | 857 | 46 | 708 / 40 |
| `Cal.lean` | 823 | 105 | 823 / 105 |
| `State.lean` | 745 | 46 | 745 / 46 |
| `Grain.lean` | 310 | 30 | 310 / 30 |
| **ten modules** | **20,902** | **1,299** (1,298 real; one is a docstring line) | 14,674 / 1,006 (nine modules) |
| `TmKernel.lean` | 10 | — (the ten imports; §2.3) | 9 |
| `Check.lean` | 1,469 | — (1,299 `#print axioms` lines, 1,299 distinct names, 16 `APPENDED` banners) | 1,102 |
| `Negative.lean` | 592 | — (cheats 1–49 plus a letter block A–F, 27–30 duplicated) | 510 |
| `Goals.lean` | 751 | — (40 goals with `sorry`, 0/11/14/15 by stage; not imported) | 834 |
| **total** | **23,724** | | 17,129 |

Archive: `libTmKernel_TmKernel.a`, 3,704,386 bytes (1,759,720 at `c8f3a38`).
FFI crate: `shim.c` 66 + `build.rs` 69 + `src/lib.rs` 57 = 192 lines (185 at
`c8f3a38`; `build.rs` gained the Linux rpath, `0c3aaf7`); tests `kernel.rs` 942
lines and `corpus.rs` 556 plus `tests/harness/mod.rs` 486. FFI tests: 57 + 6 = 63
(26 + 6 = 32 at `c8f3a38`). Host side: `tm/src/cli/kernel_bridge.rs` 756 lines,
`tm/build.rs` 40. `check.sh`: **seven** checks, 1.1 s warm (1.13/1.11/1.10/1.10 s
over four consecutive capped runs). `cargo test --workspace`: **984 passed / 0
failed / 0 ignored across 64 test binaries**, 4.9 s warm, capped (§7.5).
`cargo build -p tm` into an empty target directory, Lean archive already built:
18.1 s, capped.

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
| `PlanCore` has a `log` field | PLAN §3.1 | it is `{docs, store}`. Stages 5 and 6 need the log and it has nowhere to go |
| `Doc = {path, frontRaw, secs, prose}` | PLAN §3.1 | it is `{path, prose, region}`. Headings and front matter are ranked verbatim prose; §4.2's section is *derived*, not stored |
| The FFI is `tm-kernel-sys/`, ~250 lines | PLAN §5 | it is `kernel/tm-kernel-ffi/`, 192 lines at `bf7cc63` (185 at `c8f3a38`) — still the one stage-3 number that moved in the good direction |
| "2,981 lines, 7 modules, 497 KB archive, 148 theorems" | PLAN §5 | a stage-1 snapshot. §10.1 has today's |
| "scaling `Core` from five fields to the real `Item`'s twenty-two" as remaining stage-1 work | PLAN §5 | it did not happen and will not. `Core` has five fields; the item fields are views over the token vector (§5.1, §5.3) |
| "`moved`/`dropped`/`tags` are sets" in the structural tier | PLAN §3, and it is what earns E3/E4 their **U** | only `tags` exists. `moved`/`dropped` are Rust `state.json` fields with no kernel counterpart (§1) |
| the oracle's "129" and "479" clean counts | `kernel/README.md` | 126 and 481 at `c8f3a38`, twice, byte-identical, against `main`. Deterministic for a fixed seed count; they move when the kernel moves — and it has moved a great deal since. **Unreproducible in this clone** until the oracle is moved to `4748911` (§7.3) |
| "`Core` stores four things" | `kernel/README.md` prose | five. `parent` is still a stored slot; gap 22 says why |
| "`lake build` from clean 1.6 s; `cargo test` from clean 3.6 s" | `kernel/README.md` header | not re-measured at `c8f3a38` or `bf7cc63`, and certainly not true of today's 20,902-line kernel. The warm numbers in §10.1 are, plus `cargo build -p tm` into an empty target directory with the archive built: 18.1 s |
| "Five separate Rust code paths" / "six entrances to one hole" | in circulation, and in an earlier version of this document | **six catalogued defects (PLAN §4.A rows A1–A6), five of them patched entrances, one hole, one precondition.** §1 settles which number means what; the harness says *five* entrances |
| "943 tests" | in circulation | not sourced anywhere **as a claim about proofs**. 943 is `horizon.rs:943`, the line of `move_line`. The documented figure is line counts: tm-core has 19,298 test lines (re-measured on the restored tree: still 19,298), of which the kernel-area files are 9,497 (49%) — *"the tests proofs substantially replace"*. **A second, real 943 now exists and must not be confused with it:** `cargo test --workspace` passed 943 tests at the restore, `835d960` (984 at `bf7cc63`) |
| "a week→month behaviour change" needing assent; "the month of today" as `horizon.rs:1543`'s rejected rule | AGENTS §8.2 trap (b), §10.5 q1's second half; `Cal.lean`'s header; `kernel/README.md`'s "month of today" row (24) and its week → month tie-break section — all from `6f67873` | **there is no such behaviour change.** `horizon::close_week` already computes `closeTo week now`; `monthOfIsoWeek` names the month a week belongs to and is not the close rule, as `Grain.lean` says. q1's second half is **withdrawn** (§10.5). **Repaired at stage 4 step 1:** §8.2's trap, §10.5 q1 and `Cal.lean`'s header corrected; the README supersedes its row 24 and "Rejected" paragraph by name in its stage-4 block. Left as history, and to be read as wrong on this point: `Negative.lean`'s `CHEAT 24` banner (§6.2), and the origin, PLAN §3.2(b), with PLAN §6.2 q1's and stage-4 row's "two behaviour changes" (quoted in `Goals.lean`'s `# STAGE 4` header) — there is one, D1 |
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

| # | question | due | status at `bf7cc63` |
|---|---|---|---|
| 1 | The two close behaviour changes — and by **constructing a stale tree and closing it**, not by reading | before stage 4 | **First half ANSWERED 2026-09-12 (D1):** `close day` targets the week containing *now* — the kernel's `closeTo` — decided after driving stale trees with the restored binary (skipping a weekend double-stamped leftovers onto the month cut list and dropped them off Monday's plan; an item whose parent was in the closing week was deleted, its minutes silently absorbed; a day closed more than 16 days late stranded work in a sealed file). Package: the stamp stays `demoted:D<dd>`; `AUTO_CLOSE_CATCHUP = 16` collapses to one step per grain. Evidence and mechanism: `kernel/README.md`'s stage-4 block (D1). **Second half WITHDRAWN:** the week→month "behaviour change" does not exist — `horizon::close_week` already computes `closeTo week now` (checked by `decide` on four dates; `rfl`-equal to `monthOfWeekByToday`) (§10.2's row; §8.2's trap). The sites were repaired at stage 4 step 1; the residual "which month file holds a week's `# Demoted` record" is README gap 52, **deferred** out of stage 4 (no consumer) |
| 2 | `Id`'s shape — the recorded resolution is weaken the spec, not tighten the data | stage 3 | **ANSWERED 2026-09-12 (D2):** ids stay digits (`freshId`'s `^9`, `^10`); spec §3.1's "4 chars of `[a-z0-9]`" width sentence is weakened to match. Closes gap 13 |
| 3 | `parent`: derive the field and demote `parentsTotal` to a report, or keep it stored and have no hierarchy (gap 22) | **before stage 5, blocking** | **open** — also what B3 needs to fire in stage 4 |
| 4 | Which side replays the log | before stage 5 | **open** — and `move_has_no_inverse_command` makes replay the only correct `tm undo` |
| 5 | R7: where the `p_lounge` capacity mixture rounds (gap 26) | stage 5, consumed by 6 | **open** |
| 6 | L24 / L25: prove, or keep the 882-line proptest and say so | **before stage 6 starts** | **open**; the proptest is restored and runs (`tm-core/tests/planner_invariants.rs`) |
| 7 | Lifecycle commutation (R7 in the law list) — L27 surfaces it and does not answer it | stage 6 | **open** — L27 is refuted (stage 4 step 3) by a demote/readopt precondition pair, which does not bear on whether pairs that both succeed should commute |
| 8 | What `report` carries, and therefore its shape (§8.2). Nothing in the kernel names it today | before stage 4 writes one | **ANSWERED 2026-09-12 (D3):** a per-item list — id, disposition, destination, stamp, minutes as integer numerator/denominator. Not counts only (the month review would re-derive per-item history from the files, a second reader of one fact), and not stage 6's full diagnostics surface yet. No code exists |
| 9 | Whether the kernel should refuse a `[-]` outside a week file or `month/…# Demoted`, as `tree.rs` does — a behaviour change (gap 31, §8.1) | stage 3 | **open**, not taken in stage 3; now due when stage 4 gives `demote` a section target |
| — | `main`: keep it as the oracle, or discard it | — | **DECIDED 2026-09-12 (D4):** discarded (`f386c56`); the fork point `4748911` is the restore source and the oracle; stage 0's fix, `invariant_exhaustive.rs` and the ability to reproduce anything measured on `main` went with it (§2.2) |

**Stage 4 is unblocked.** Its two gating decisions (q1, q8) are answered and its
binary exists. What it still cannot do without the human is fire B3
(`close_week_folds_a_dropped_child_into_its_parent`), which waits on q3. Still
owed to the human, in the order they block: **q3** (blocks stage 5, and B3), **q4**
(before stage 5), **q5** (stage 5), **q6** (before stage 6), **q7** (stage 6), and
**q9** — plus the 30-minute drive of the stage-3 binary (§5.13).
