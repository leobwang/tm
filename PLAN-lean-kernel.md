# Rebuilding tm's kernel in Lean 4

Branch: `rebuild-on-lean`. Written after four spikes, all of which compiled or ran
what they claim. Notes:
`scratchpad/lean-notes/{architecture,ffi-spike,inventory,firstprinciples,against}.md`.

---

## 1. The decision

The semantic core of tm moves from Rust to Lean 4 and runs at runtime. Lean is not
a design-time model checked by refinement testing; the shipped binary calls it.

What that means concretely:

- **One value.** The entire plan — every month, week and day file, backlog,
  routines, optional, calendar, plus the log — is a single Lean value. Every
  command is one total transformation on it.
- **Text in, text out.** The parser and the serializer live in Lean. The UI hands
  the kernel raw file bytes and gets file bytes back. The FFI boundary is
  `String → String`; nothing is marshalled.
- **The checker is the type.** `tm check` is the acceptance predicate of `parse`.
  There is no second, weaker validator to drift from the invariant.
- **Laws, proved or refuted.** Each command carries a stated algebraic law with a
  named subdomain. A refutation is a result, not a failure; six are already
  compiled, and one of them (the conservation law that three Rust commits tried to
  enforce) is false as stated.
- **Exact integers.** No floats and no fixed point in the kernel. `Rat` is
  available and deliberately unused.
- **Derived, not enumerated.** Horizons are a containment chain with a saturating
  successor, so §6.3's three close rules become one operation at three grains. An
  id names an entity; a line is an observation of it, so the multiplicity bound is
  a theorem rather than a predicate someone must remember to run.

What it replaces: roughly 8,600 of tm-core's 27,352 code lines — `model`, `tree`,
`recur`, `horizon`, `priority`, `capacity`, `planner`, plus `grammar.rs` (1,246)
and `check.rs` (710), plus the generated Markdown blocks and four semantic leaks in
`tm/src`. What it does not replace: file I/O, the TUI, CLI arg parsing, ICS, the
statistical layer, review monitors, SVG. That is about 70% of the system and it
keeps being written the way that produced the bugs.

Repository layout:

```
planner/
  kernel/                     Lake package, lean-toolchain pinned to v4.33.1
    TmKernel/{Grain,State,Cmd,Plan,Arith,Text,Boundary}.lean
    Check.lean                axiom audit + the law index
    Negative.lean             must FAIL to compile; CI asserts the failure
  tm-kernel-sys/              Rust: build.rs (73 lines), shim.c (136), one extern fn
  tm-core/                    shrinks to store/log/ics/energy/review/emit-svg/config
  tm/                         CLI + TUI, unchanged in shape
```

---

## 2. What the spikes established

### 2.1 The finding that shapes the design

The `against` spike proved by exhaustive search that the five "separate"
duplicate-id bugs are **one missing precondition in one function**.
`horizon::move_line` (horizon.rs:943) calls `move_to` (:958), which computes
`to_path` and appends the line **without ever asking whether `to_path` already
holds `key`**.

```
alphabet 141 commands, 19,740 depth-2 sequences, 389 s
  → 164 violating sequences at HEAD
  → 1 of them needs a single command on a fresh `tm init --example` tree
```

```console
$ tm check                    # no problems, exit 0
$ tm move ^m2 month           # ^m2 week/2026-W37.md → month/2026-09.md, exit 0
$ tm check
month/2026-09.md:8:  error[dup-id]: duplicate id ^m2; also at month/2026-09.md:11
2 errors, 0 warnings          # exit 2
```

Grouped by shape: 131 are `… ; move ^X month09`, 21 are `demote ^X ; move/readopt
^X week`, 12 are `close week ; move/readopt ^X week`. All three funnel through the
same call.

**The structural answer is that there is no append.** Item lines are not stored. A
document body holds prose only — headings, blanks, comments, generated blocks —
each with verbatim bytes and a rank. An item line is *rendered* from the entity
that owns it. `move` cannot put a line anywhere; it can only replace a `Site`, and
replacing it into the file the tombstone occupies is refused by the constructor.
Compiled:

```lean
theorem move_into_archive_file_is_rejected (e : Entity) (t r : Site)
    (h : e.val.archive = some r) (hd : r.doc = t.doc) : moveTo t e = .error .occupied

theorem no_two_lines_of_one_id_in_one_file (p : PlanCore) (l₁ l₂ : Line)
    (h₁ : l₁ ∈ p.lines) (h₂ : l₂ ∈ p.lines)
    (hid : l₁.id = l₂.id) (hdoc : l₁.site.doc = l₂.site.doc) : l₁.site = l₂.site

theorem lines_per_id_le_two (p : PlanCore) (i : Id) :
    ((p.lines).filter (fun l => l.id == i)).length ≤ 2
```

**Correction from the stage-one audit, recorded here because it changes what the
theorem above is worth.** `Site.doc` is a *list index*. Nothing in the first
version of the package required two documents to carry distinct `path`s, so two
documents at different indices could be one file on disk and a demote could put
two `^m1` lines into it with the theorem above still true. Path injectivity is
now part of `planWf`, and the claim is restated over what reaches the disk:

```lean
theorem no_two_lines_of_one_id_in_one_path (p : WfPlan) (l₁ l₂ : Line)
    (h₁ : l₁ ∈ p.val.lines) (h₂ : l₂ ∈ p.val.lines) (hid : l₁.id = l₂.id)
    (hpath : pathAt p.val l₁.site.doc = pathAt p.val l₂.site.doc) : l₁.site = l₂.site
```

Two further corrections from the same audit belong with it, because both are the
**same missing-precondition shape** this section is about:

- `Site.doc` was an unbounded `Nat` and the boundary took it straight off the
  wire, so `move ^m1 7` in a one-document plan wrote a placement into document 7,
  `renderDocAt` rendered the documents that exist, and the item was **deleted
  with the kernel returning `ok`**. A relocation's destination is now a
  `Dest p`, whose second field is a proof that the index is a document of `p`,
  and `no_line_is_lost` says nothing a plan holds can fall off the end.
- `glyphAt` is the only writer of a state box, and the loader is its inverse.
  The first loader mapped `Glyph.demoted` to `live free` with no archive, so a
  `[-]` line came back `[ ]` **with no command run at all** — the shipped bug 2,
  reproduced inside the verified kernel. The inverse is now written down as a
  partial function with `glyphAt_statusOfGlyph` / `glyphAt_statusOfGlyphDemoted`
  as its two halves, and where it is `none` the loader rejects.

Two second-order facts from the same spike, both of which the design has to answer:

- The **checker is weaker than the invariant**. `tree::is_real_duplicate`
  (tree.rs:1181) fires only on two lines in one file or two live lines. A tree with
  `^m2` on three lines — live in `week/2026-W37`, archive copies in `month/2026-08`
  *and* `month/2026-09` — passes `tm check` at exit 0. That is exactly the
  corruption `d123c80` was written to prevent.
- The invariant is **knowingly maintained in the CLI**. `tm/src/cli/items.rs:596`,
  `drop_stale_demotion`, whose own doc comment ends `Upstream fix:
  horizon::readopt.`

### 2.2 The invariant inventory

39 distinguishable defects across the history, and 17 structural invariants
(S1–S17), 12 command obligations (T1–T12), 14 single-run planner properties
(D1–D14), 7 relational ones (R1–R7), and 7 statistical families (H1–H7) that have
no soundness theorem worth proving.

The split by module, code lines only (comments, blanks and inline `#[cfg(test)]`
excluded):

| | code | comment | blank | inline tests |
|---|---|---|---|---|
| `tm-core/src` | 17,665 | 6,429 | 1,570 | 3,647 |
| `tm/src` | 9,687 | 2,856 | 789 | 662 |
| **total** | **27,352** | 9,285 | 2,359 | 4,309 |

The `inventory` spike put the verifiable fraction at ~5,550 lines (20%). This
design raises it to ~8,620 (~30%) because the parser and the generated-block
emitter move in. Of tm-core's 19,298 test lines, the kernel-area files (horizon
2,192, tree 978, priority 2,067, planner 2,588, recur 1,272, check 400) are 9,497
— 49%. Those are the tests proofs substantially replace.

### 2.3 The FFI: recipe and measured cost

Everything here was built and run, twice independently (`ffi-spike`, `against`),
and re-verified in this session against the architecture package: clean
`lake build TmArch:static`, 246,344-byte archive, `nm` shows `T _tm_kernel_call`,
toolchain `leanprover/lean4:v4.33.1`.

```bash
# 1. The archive. `lake build` alone gives only .olean + .c IR.
lake build TmKernel:static          # → .lake/build/lib/libTmKernel_TmKernel.a

# 2. Link flags, authoritative source:
lake env leanc --print-ldflags
# -L <prefix>/lib/lean -L <prefix>/lib \
# -lleancpp -lInit -lStd -lLean -lleanrt -lc++ -lLake -lgmp -luv -lssl -lcrypto \
# -Wl,-dead_strip
#   TWO -L paths: gmp/uv/ssl/crypto live in lib/, not lib/lean/.
#   <prefix> from `lean --print-prefix` run INSIDE the package, so it honours
#   lean-toolchain.
```

```c
/* shim.c — the whole surface, 136 lines, mandatory forever */
int         tm_kernel_init(void);              /* once, 0.6–2.0 ms */
const char *tm_kernel_call(const char *req);   /* returns malloc'd UTF-8 */
void        tm_kernel_free(const char *p);

/* init sequence */
lean_initialize_runtime_module();
lean_object *r = initialize_TmKernel_TmKernel(1, lean_io_mk_world());
if (!lean_io_result_is_ok(r)) { lean_io_result_show_error(r); return 1; }
lean_dec_ref(r);
lean_io_mark_end_initialization();
lean_set_exit_on_panic(false);
```

The shim is mandatory, not a convenience. `lean.h`'s host API is `static inline`
and therefore has no linkable symbol — verified with `nm`: `lean_dec`, `lean_inc`,
`lean_dec_ref`, `lean_io_mk_world`, `lean_io_result_is_ok`, `lean_string_cstr`,
`lean_alloc_ctor` are all inline-only, and `lean_initialize_runtime_module` /
`lean_initialize_thread` are exported but declared in **no** public header.
`bindgen` cannot help; inline functions have no symbol to bind. The init symbol
embeds the Lake package name — find it with `nm`, do not guess.

Measured:

| what | number |
|---|---|
| `cargo build` from clean, driving lake end to end | 2.26 s |
| no-op rebuild / after a Lean edit | 0.89 s / 1.63 s |
| `lake build TmArch:static` from clean (this session's package) | 1.33 s |
| kernel init | 0.6–2.0 ms, once |
| realistic replan, 500 items, JSON boundary | **0.8 ms** vs a 16.7 ms frame |
| Lean compute vs Rust, same fold | 4.6× |
| per item: JSON / raw / pure compute | 1.6 µs / 0.33 µs / 1.6 ns |
| static binary, no Mathlib | 3.84 MB (3.57 MB without core JSON) |
| one-time integration tax | ~250 lines (shim 136 + build.rs 73 + extern 30) |
| per new transformation after that | ~5 lines |
| baseline for comparison: `cargo build --release`, whole workspace | 17.2 s → 10.8 MB |

Four negative findings that the design is built around:

1. **A Lean panic is a silent wrong answer.** `xs[99]!` prints a C backtrace to
   stderr, returns `Inhabited.default`, and the host gets exit code 0.
   `lean_set_exit_on_panic(true)` turns that into a hard `exit(1)` with no unwind,
   so the TUI leaves the terminal in raw mode. Neither is acceptable. §3.4 gives
   the three-layer answer.
2. **A shared `lean_object*` SIGSEGVs.** One object across 8 threads × 200k reads:
   exit 139 in 3 of 5 runs. With `lean_mark_mt`: 5/5 clean over 1.6M reads. The
   `String → String` boundary is immune by construction — nothing escapes the shim.
3. **A plain `structure` constrains nothing.** `structure Horizon where depth : Nat`
   accepted `horizon: 99` and `horizon: 77`. Nine of eleven adversarial JSON inputs
   were accepted. Worst of them: `est: -3` became `est: null` via `.toOption` —
   **tm's own estimate-erasure bug, reproduced inside the verified kernel's
   boundary code**. Fix is `Fin`/`Subtype` plus a smart constructor used by
   `FromJson`, ~8 lines once per type.
4. **Mathlib takes the toolchain hostage.** 9.7 GB on disk, a 118 MB binary (31×),
   `Mathlib:static` on every linking machine — and `lake update` silently rewrote a
   pinned `v4.33.1` to `v4.34.0-rc2`, costing two link failures with the misleading
   error `_l_Bool_Internal_not___boxed`. No Mathlib. Everything needed (`Fin`,
   `Nat`, `Option`, `Except`, `Subtype`, `Std.HashMap`, `List`, `omega`, `decide`,
   `simp`, `Lean.Data.Json`) is core; core JSON costs 270 KB.

Recorded honestly on the other side: Mathlib's absence is not free.
`List.Nodup.append` and `nodup_map_iff_of_inj_on` do not exist in core;
`lines_per_id_le_two` needed three hand-written helpers (~30 lines, four failed
attempts). Expect that tax to recur.

### 2.4 Derivation: where it pays and where it does not

The charter, from `firstprinciples` and calibrated on the 五行 exercise: **derive
where a wrong answer is wrong; tabulate where a different answer is merely
different — and where you tabulate, keep the table as a compile-checked
transcription.** The negative test on the calibration: corrupt one row of the
enumerated 克 table and the build fails at the bridge theorem; restore it and it is
clean.

Where it pays, proved:

- **Identity vs observation.** Four of the five duplicate-id bugs become `rfl`; the
  fifth appears as an unsolved goal (`⊢ r' ≠ r`) at the moment the author writes
  the buggy line.
- **Horizon.** The close target grain derives completely, and §6.3's third row
  becomes the fixed point of the same rule (`coarsen month = month := rfl`). The
  attempt also proved two things about tm nobody had written down: the week→month
  step **is not a containment** (`¬ Refines weekG monthG`; `#eval` of a day that is
  31 Jan and the next that is 1 Feb inside one ISO week gives week indices
  `(4,4)` against month indices `(1,2)`), and the three closes answer the index
  question three different ways — `close_day` uses the block containing the closed
  region (horizon.rs:1323), `close_week` the block containing now (:1543),
  `close_month` the successor at the same grain (:1792).
- **Lifecycle.** `[-]` is not a state; it belongs to placement. Five states, not
  six. That single move is what makes bugs 2–5 unstateable.

Where it does not pay, also proved: **`specBin 110 ≠ derivedBin 110`.** Three of
§7.1's four bin edges are halvings; the fourth is 0.1, not 0.125. Adopting the log₂
generator is not a refactor — it changes which task the planner shows you first,
and there is nothing to recover in exchange, because every monotone map from a
ratio to a small ordinal is legitimate. The whole yield of formalising §7.1 is
antitonicity, ten lines.

And one case that runs the other way, which is why this is a test and not a rule of
thumb: §5.3's `on_miss` table is presented as 2-D over (shape, recur), but
`model.rs:686` is `Shape::Window => Expire, _ => Persist` — the recur column does
nothing. The one-line principle (*a window is a chance, a point or interval a
commitment*) reproduces the implementation exactly and answers two cells the table
never covered. Derive that one.

### 2.5 Size and the effort estimate, with its basis

| input | number | source |
|---|---|---|
| Rust code lines in scope | 8,620 (~30%) | 6,664 semantics + grammar 1,246 + check 710 |
| public functions in the semantics half | 294 | `against` §3.1 |
| Lean definitions, at 0.6× | ~5,200 lines | `against` §3.1 |
| proof : definition, measured on the easy fragment | **1.09 : 1** (222 : 241) | this session's `TmArch` package |
| proof : definition, recalled for hard domains | 3 : 1 (CompCert) … 20 : 1 (seL4) | **literature, not verified here** |

Those two ratios bracket a range so wide it is not a forecast. The design's answer
is to **not prove most things**: §3.1's three tiers push the bulk of the invariants
into structure (zero proof) or into one decidable checker (zero proof, one `lift`
per command). What is actually proved is the 27 laws of §3.3 and round-trip B. The
1.09:1 figure will not survive stage 5; treat 3:1 over the parts that need real
induction as the planning number, and see §6.3 for the stop condition if it goes
past that.

Calendar estimate, stage by stage, in §5. Total: **3.5–5 months** of focused work
to stage 6. This is a forecast built on four spikes, not a measurement.

---

## 3. The architecture

### 3.1 The state object

```lean
structure PlanCore where
  docs  : Array Doc            -- every file, PROSE ONLY
  store : Store                -- every item, keyed by id
  log   : List String          -- append-only JSONL, verbatim

structure Doc where
  path     : String
  frontRaw : String                        -- YAML front-matter, verbatim
  secs     : Array String                  -- heading lines, verbatim, by SecIx
  prose    : Array (SecIx × Nat × String)  -- (section, rank, verbatim) non-item lines

structure Store where
  get      : Id → Option Entity
  dom      : List Id
  domSpec  : ∀ i, i ∈ dom ↔ (get i).isSome = true
  domNodup : dom.Nodup
```

Item lines are absent from `Doc` entirely. **"An id names one item" is not an
invariant here — it is what "function" means.** `Std.HashMap` instantiates the
interface; the abstraction keeps proofs off HashMap internals, which the FFI spike
found are opaque to `decide` (`by decide` and `by rfl` both fail on `wf [] = true`
for a HashMap-backed checker, and succeed on the list-backed one). Behind an
interface they are the same artifact, and only `domSpec`/`domNodup` need bridging.

This deletes `tree::record_rank` (tree.rs:1170), `tree::is_real_duplicate` (:1181),
`store::choose`'s tie-break, and `cli/items.rs::drop_stale_demotion` (:596) — four
pieces of machinery that exist only because the invariant is not structural.

```lean
structure Core where
  live      : Site             -- the one placement that is work
  archive   : Option Site      -- at most one tombstone a close left behind
  status    : Status
  remaining : Nat              -- minutes; ONE field, not §3.2's three-way fallback
  stamps    : List Nat

def wf (c : Core) : Bool := wfPair c.live c.archive     -- decidable
def Entity := { c : Core // wf c = true }               -- the only way in
```

Three tiers, and **which invariant lives in which tier is the load-bearing
decision**:

| tier | cost | what lives here |
|---|---|---|
| structural | free | one entity per id; ≤1 live and ≤1 archive placement; an item's horizon *is* its file (no `horizon` field — kills S2); `ci : Fin 6`, `!k : Fin 4`, `Dur = Nat` minutes; `moved`/`dropped`/`tags` are sets not `Vec`+`dedup` (kills E3/E4); `Nat` does not overflow (kills E6) |
| per-entity proof field | ~1 line per constructor call, unforgettable | S1's local half: the tombstone is in a *different file* from the live line |
| plan-level `Subtype` | one decidable checker over the whole value | `@parent` total+acyclic (kills F5); `after:` total+acyclic; section discipline S10; per-file-kind shapes S11; `Normalized` (rank distinctness); series head uniqueness |

**A correction to the `firstprinciples` design, found by hitting it.** That spike
used a dependent proof field (`archive_elsewhere : ∀ r, archive = some r → r ≠ live`)
and recorded its cost: `{e with live := r}` stops working, because the proof's type
mentions the field being changed. The architecture spike's first `Cmd.lean` failed
to compile in eight places for exactly that reason. **A 22-field `Item` with
dependent proof fields is not maintainable; a 22-field `Core` with a Bool `wf` and
a `Subtype` is.** Both cheats stay compile errors — verified by uncommenting them:

```
error: `live` is not a field of structure `Subtype`               -- hand the raw record through
error: Application type mismatch: rfl has type ?m.7 = ?m.7
       but is expected to have type wf {…} = true                 -- fake the proof
error: unsolved goals   ⊢ e.val.remaining = 0                     -- a close that zeroes what it measured
```

You lose only the sharpness of the goal message.

**`[-]` is not a status.** Five states; the glyph is a function of placement:

```lean
inductive Outcome | done | dropped
inductive Holder  | free | self | world
inductive Status  | settled (o : Outcome) | live (h : Holder)

def glyphAt (c : Core) (s : Site) : Glyph :=
  if c.archive = some s then Glyph.demoted            -- the tombstone, always
  else match c.status with
    | .settled .done => .done  | .settled .dropped => .dropped
    | .live .self    => .active | .live .world      => .waiting
    | .live .free    => if c.archive.isSome then .demoted else .todo
```

The file format is unchanged: an entity mid-demotion still emits two lines, same
id, both `[-]`, and `exactly_one_live` proves exactly one of them is live. §6.3's
rule "readopt: `[-]` → `[ ]`, stamp kept" is *derived* — `readopt_reopens` is the
one theorem in the package that depends on **no axioms at all**.

Ranks are a plan-level predicate, not a per-entity obligation: two entities
colliding on a rank is an ordering ambiguity, not a corruption. The parser
establishes `Normalized` by assigning rank = line index; every command preserves it
by taking `rank := 1 + max rank in the target section`, fresh by construction — one
lemma per command, not an obligation at each call site.

### 3.2 The generating structures

```lean
abbrev Grain := Fin 3                              -- day ⊂ week ⊂ month
def coarsen (g : Grain) : Grain := ⟨min (g.val + 1) 2, by omega⟩

theorem coarsen_day   : coarsen day   = week  := rfl
theorem coarsen_week  : coarsen week  = month := rfl
theorem coarsen_month : coarsen month = month := rfl   -- §6.3 row 3, DERIVED
theorem coarsen_saturates_only_at_month : ∀ g, coarsen g = g ↔ g = month := by decide

def closeTo (g : Grain) (now : Day) : Region := regionOf (coarsen g) now
theorem closeTo_target_is_open (g) (now) : ¬ Closed (closeTo g now) now
```

Backlog is the **absence** of a bound, not a coarser grain — which is why
saturation is the right generator and not an accident. `#eval (closeTo day 250,
closeTo week 250, closeTo month 250)` gives `(week 35, month 8, month 8)`: §6.3's
three rows, generated.

Two behaviour changes fall out. **Both are findings, and both need your assent
before stage 4** (§6.2).

**(a) `close_day` changes.** horizon.rs:1323 targets the week containing the
*closed day*; the derived rule targets the week containing *now*.

```lean
theorem impl_day_rule_disagrees : targetContaining day 6 ≠ closeTo day 7 := by decide
theorem containing_can_target_a_closed_region : Closed (targetContaining day 6) 7 := by decide
```

Closing Sunday on Monday, today's code files leftovers into a week that is already
closed. `auto_close` masks this by iterating catch-up in grain order — real, works,
nowhere in the spec, and nothing in the types depends on it. This is also what
makes close idempotence provable at all (§3.3).

**(b) week→month is not a containment, so the tie-break must be named.**
horizon.rs:1543 breaks it silently by taking the month of *today*. Proposal:

> `monthOf(w)` = the civil month containing week `w`'s Thursday.

Stable, independent of `now`, and a generalisation of ISO 8601's own week-year rule
rather than an invention.

**Recurrence** gets one denotation `Log → Instant → Option Occurrence` and keeps all
four constructors as *syntax*, because `Recur`-as-a-function is not serialisable,
not `DecidableEq`, and not writable in a Markdown line — and §0 says the Markdown is
the database. That is the honest limit. The gain is one classification theorem
(`calendar_is_history_independent` vs `afterDone_is_history_dependent`) which turns
§5.1's two prose notes into the same fact seen twice, and it is what D1 becomes a
postcondition on.

**Where derivation is refused, named so the list stays finite:** §4.1's field table
(your carve-out, and it is right); §7.1's bin edges and ladder constants (proved
harmful, above); `Loc`, which is `Option Name` because admission is the only query;
§6.3's residue — copy-vs-move disposition, the off-chain `backlog#Overdue` target,
child-folding, stamp accrual, exemptions — as a **typed table `ClosePolicy` indexed
by `Grain`**; and `Holder`/`Outcome`, three and two values genuinely. Deriving the
order is what makes that residue a finite visible list instead of 995 lines.

### 3.3 The command algebra

```lean
abbrev Transform := WfPlan → Instant → Except KErr WfPlan
-- WfPlan := { p : PlanCore // planWf p = true }, and planWf IS what `tm check` runs
```

34 CLI verbs, ~24 of which mutate. Every one is one `Transform`. Legend: **P** =
proved and compiled, **P\*** = provable, not yet built, **R** = refuted and
compiled, **R\*** = expected refutation, **?** = open and expensive.

| # | command | claimed law | subdomain | verdict |
|---|---|---|---|---|
| L1 | `move t` | idempotent | success domain | **P** `move_idem` |
| L2 | `move t` | last-wins | **first move succeeds** | **P** `move_last_wins` |
| L3 | `move` | last-wins | globally | **R** `move_last_wins_refuted_globally` |
| L4a | `move t` | invertible by `move e.live` | success domain | **P** `move_back_restores` |
| L4b | `move` **command** | invertible | all | **R** `move_back_at_a_fresh_rank_is_not_the_inverse` |
| L5 | `move` | rejects tombstone collision | all | **P** `move_into_archive_file_is_rejected` |
| L6 | `drop` | idempotent | all | **P** |
| L7 | `drop` | `settled` absorbing | all | **P** |
| L8 | `drop` | preserves the archive glyph | all | **P** |
| L9 | `edit est=v` | `remaining = v` | all | **P** `set_is_not_silent`, `view_set_is_not_silent` |
| L10 | `edit` | last-wins | all | **P** |
| L11 | `demote` | idempotent | one period | **R** `demote_not_idem` |
| L12 | `readopt ∘ demote = id` | on the nose | week items | **R** `readopt_demote_not_id` |
| L13 | `readopt ∘ demote = id` | modulo stamps | `archive = none ∧ live free` | **P** |
| L14 | conservation | floor `remaining` at the recorded value | all | **R** `conservation_naive_overrides_the_user` |
| L15 | conservation, corrected | floor **unless the user set an est since** | all | **P** `demoteEst_conserves`, `demoteEst_respects_user` |
| L16 | `close g` | idempotent | all | **P\*** |
| L17 | `close week ∘ close month` | commutes | all | **R\*** |
| L18 | `close g` | never targets a closed region | all | **P** `closeTo_target_is_open` |
| L19 | `autoClose` | `closed` monotone; every period *run* | bounded window | **P\*** |
| L20 | `rank id n` | idempotent, order-preserving | within a section | **P\*** |
| L21 | `add` | fresh id: `assigned ∩ existing = ∅` | all | **P\*** |
| L22 | `undo ∘ cmd = id` | on the nose | all | **R\*** — holds only on the state projection |
| L23 | `plan` | pure | all | **P** (free; it is a function) |
| L24 | `plan` | tail-drop (§8.3) | budget monotone | **?** |
| L25 | `plan` | stability across `t' > t` (§8.3) | all | **?** |
| L26 | `plan` | energy filter, no overbooking, walls unmoved, monotone rank | all | **P\*** decidable over the produced `DayPlan` |
| L27 | any lifecycle pair | commutes | all | **R\*** — open product question |

Six refutations are compiled. Each is a case where a test suite would have quietly
agreed with the false law:

- **L3** was not expected. A *failed* first move is not the same as no first move:
  if the destination collides with the tombstone the composite errors while the
  single move succeeds. Lean produced the two open goals before any test existed.
  It matters for the TUI, which retries.
- **L4**: a move assigns a fresh rank in the destination section, so moving back
  does not restore the old one. Consequence: **`tm undo` must replay the log, never
  apply an inverse.**
- **L11/L12** are the case your constraint 3 named in advance, and they hold up.
  Stamps accumulate deliberately, to drive the month review's "≥ 2 stamps" cut
  list. The kernel has to say which reading of §6.3 it means.
- **L14 is the most important.** The naive conservation law is the invariant three
  separate Rust commits tried to enforce, and it is **false**: flooring at the
  recorded value silently overrides a deliberate `tm edit ^m2 est=1b`. Lean refuses
  the naive law. It does **not** hand you the exception — only running the binary
  did that, over three commits. What the kernel buys is that the exception is
  written once, in the signature (`demoteEst (userSet : Bool) (rec : Nat)`), where
  a later writer cannot fail to read it, rather than in a 30-line doc comment on a
  private function.

**How `close` becomes one operation.** Fold over
`{ i ∈ dom | live site is in a region of grain g Closed at now }`, applying
`demoteEst` into `closeTo g now`, subject to `ClosePolicy g`. Idempotence has a
one-paragraph proof shape: after the fold no entity's live site is in a closed
region of grain `g` (that is `closeTo_target_is_open`, already proved), so the
second run folds over the empty set. **That is why the derived close target is
worth its behaviour change** — with `targetContaining`, the fold's own output can
be back in scope and the proof does not go through. And because `closeTo` targets
now rather than the successor, catch-up is one step: `autoClose`'s 16-period
iteration collapses to "close each grain once, coarsest last", and F1 becomes a
`none`-vs-`some` case in one place instead of a loop bound.

### 3.4 The boundary

```lean
@[export tm_kernel_call]
def callExport (input : String) : String := call input
```

Verified in the built archive: `nm libTmArch_TmArch.a` → `T _tm_kernel_call`.

```json
{ "cmd":"move", "args":{"id":"m2","to":"month"},
  "docs":[{"path":"month/2026-09.md","text":"…"}, …],
  "log":["…"], "now":"2026-09-07T10:00:00-05:00", "cfg":{…}, "model":{…}, "seed":91237 }

{ "ok": { "docs":[{"path":"…","text":"…"}], "events":["…"], "report":{…} } }
{ "err": { "kernel": {…} } }        /* structured, never a bare string */
```

Adding a command is one case in `dispatch` plus a thin Rust wrapper. The FFI
signature, the shim and `build.rs` never change.

**Parser and serializer in Lean.**

```lean
def parse  : Seed → Array (Path × String) → Except Report (WfPlan × Array Repair × Seed)
def render : WfPlan → Array (Path × String)
```

Acceptance means `parse` is total and its success value is a `WfPlan` **by
construction**. `tm check` is `parse` plus a formatter for `Report`; exit 2 is
`parse` returning `.error`.

**Byte-faithfulness is the representation, not a test.** An item line is stored as
its token vector with verbatim spelling; the semantic fields are a *view* of it.

```lean
structure Tok where kind : TokKind ; raw : String ; val : Nat
abbrev RawLine := List Tok
def serialize (r : RawLine) : String := r.foldl (fun acc t => acc ++ t.raw) ""

theorem edit_is_silent :                        -- THE SHIPPED BUG, as a theorem
    ∃ (r : RawLine) (v : Nat), viewRemaining (setLeadEst v r) = viewRemaining r
                             ∧ some v ≠ viewRemaining r
theorem view_set_is_not_silent (v) (r) : viewRemaining (setEst v r) = some v
theorem edit_touches_only_its_token (v) (r) :
    ∀ t ∈ r, t.kind ≠ TokKind.estKey → ∃ t' ∈ setEst v r, t'.raw = t.raw
```

One such pair per field — fifteen fields, fifteen small theorems — and **a setter
is not exported without its `view ∘ set = id` proof**. The third theorem is
byte-faithfulness as a *diff* property over untouched tokens, which is the form
users actually care about.

**The round trip is two theorems, and only one of them is true.**

```
(B, retraction)  ∀ p : WfPlan,  parse seed (render p) = .ok (p, #[], seed)
(A, section)     ∀ ts, Canonical ts → parse seed ts = .ok (p, #[], _) → render p = ts
```

B is unconditional and is the one to prove. **A is false in general** and must be
scoped to `Canonical` text, because `parse` deliberately appends a missing `^id`
in place and `tm check --fix-ids` exists to do exactly that. Presenting A as
unconditional would be the same class of error as L14's naive conservation law.
`grammar_proptest.rs` (512 cases) is the right tool for A on real corpora and
should be kept, aimed through the FFI.

**Ids.** `Seed` is an explicit argument, so id generation is the only
nondeterminism and it is removed. Rust supplies the seed and stores the returned
one. Freshness is a theorem, not a retry loop. `Repair` entries are returned,
never applied silently.

**Bounded types are not optional and not the default.**

```lean
abbrev Ci := Fin 6
def Ci.ofNat? (n : Nat) : Option Ci := if h : n < ciCount then some ⟨n, h⟩ else none
theorem ci_rejects_out_of_range : Ci.ofNat? 6 = none := by decide
```

Every bounded type gets a smart constructor used by its `FromJson`: `ci` (0–5),
explicit `!k` (1–4), `energy` (0–5), `Grain`, on-miss, state. `Except` all the way
through; **`.toOption` is banned** and is in the CI grep. Lean's `Nat` is arbitrary
precision and Rust's `u32` is not, so every integer crossing gets a stated width
and an upper bound at the constructor.

**Panics — three layers, all required.**

1. **The kernel is total.** No `!`, no `partial`, no `panic!`, no `native_decide`.
   Enforced by a CI grep; it passes on the current package. This is the same
   discipline that makes the code provable, so it costs nothing extra.
2. **Rust redirects Lean's stderr** (`dup2` to a pipe) for the duration of a call
   in TUI mode, so a backtrace cannot shred the ratatui screen.
3. **`lean_set_exit_on_panic(false)`**, and Rust treats "response is not valid
   JSON" or "no response" as `KernelFault`: restore the terminal, print the
   captured stderr as a bug report, exit 1. Loud and recoverable beats silent and
   wrong.

**Stateless, one call per event.** 0.8 ms at 500 items against a 16.7 ms frame
budget. The TUI's per-keystroke work is `plan`, not re-parse, and keystrokes that
do not change the tree need no call. Add an opaque session handle only if a
measurement demands it — and then it needs `lean_mark_mt` plus a mutex and must
never leave the UI thread.

### 3.5 Arithmetic

Exact integers. No floats, no fixed point, `Rat` available and deliberately unused.
This is forced (Lean 4.33.1 has 421 `Float.*` constants, 69 theorems, and **zero**
about `+ * / ≤ <`; `example (x y : Float) : x + y = y + x := by rfl` fails) and it
is cheap (0 / 2,251,500 disagreements on priority bins; 135 / 150,600 = 0.09% on
`planned_minutes`, every one exactly one minute).

Every ratio in §7 and §8 appears inside a comparison, and a comparison of ratios
cross-multiplies into `Nat`, so the quotient is never formed:

| § | as written | cross-multiplied |
|---|---|---|
| 7.1 | `u ≥ 1` (HOT), `u = need/avail` | `avail = 0 ∨ need ≥ avail` — replaces `f64::INFINITY` and its five `is_finite()` guards |
| 7.1 | `u ≥ edge`, edge `= n/d` | `need·d ≥ avail·n` |
| 7.1 | `u ≥ edge` with safety `13/10` | `rem·13·d ≥ avail·10·n` — **the `round()` at priority.rs:349 leaves the ordering entirely** |
| 7.3–8.2 | EDF avail, reserve, hysteresis, batching, budget, `ci ≤ slot.energy`, `max:` caps, wall disjointness | `Nat`, exact |
| 8.5 | the `w(Δt)` ramp | `rampNum : Nat → Nat` over denominator 180; `ramp_antitone` proved |

**Six rounding sites, each stated at its site, never inherited:**

| # | site | rule |
|---|---|---|
| R1 | `need_min` for the EDF reservation | **ceiling** `⌈rem·13/10⌉` — a change from `round()`, because a margin rounded down stops being a margin. Note the Rust has this rule **twice** (priority.rs:349 and planner.rs:323): the E8 pattern |
| R2 | `budget` | floor, one `Nat.div` on `(windowMin·rNum)/(blockMin·rDen)` |
| R3 | `window_min = round(window_hours × 60)` | **eliminate**: change `config.day.window_hours : f64` to `window_min : Nat`; the site vanishes |
| R4 | `planned_min = round(est × multiplier)` | round-half-up `(est·n·2 + d)/(2d)` — this is the 0.09% one-minute drift |
| R5 | slot energy after the §8.5 posterior | `roundClamp : Rat → Fin 6` |
| R6 | the short last block, "≥ 30m or dropped" | a **comparison**, not a rounding — recorded so nobody adds one |

Two sites that look like rounding and are not: writing `est:` back chooses its unit
exactly (`minutes % block_min = 0 → Nb` else `Nm`, no information lost, round trip
survives); and `progress` / `plan_honesty` / `as_blocks` are display-only — **the
kernel emits numerator and denominator as integers and Rust divides**. That last
rule is also the fix for the `review.rs` "share" family of defects: a share is a
pair of counts in the kernel and a float only on screen.

The one transcendental, `exp(−age/decay)`, is outside the kernel entirely.

### 3.6 What stays in Rust

| what | why |
|---|---|
| **All file I/O**: atomic writes, the mtime conflict guard (exit 3), `.tm/`, directory walking | a concurrency protocol against a filesystem; provable only against a model of the filesystem (T11) |
| **The TUI**: ratatui, key handling, terminal state, layout, hour band, `pad`/`truncate` | G6/G7/G11 live here and stay here. `DayBar::col_of`/`start_of` inverse-ness is a genuine algebraic property — as a Rust property test |
| **CLI arg parsing and `--json` shaping** | G2 and G3 stay Rust bugs. Stated plainly: this design does not fix them. the integration-bug table below says what does |
| **`ics.rs` (1,055 lines)** | RFC 5545 conformance is provable only against a formalisation of RFC 5545 that does not exist. **The line: ICS never touches the kernel.** `sync-cal` writes `calendar/<week>.md` as ordinary Markdown and the kernel reads it like any other doc |
| **The statistical layer**: `energy.rs` fitting, `model.json`, shrinkage means, `exp(−age/decay)`, duration multipliers, `p_lounge`, `expected_arrival`, the v2 regression | "sound" has no meaning here. **The kernel consumes a fitted model as data; it never fits one.** The model enters the request as `{"energy":…,"duration":…}` and is typed on entry as exact rationals |
| **`review.rs`'s monitors (1,509 lines)** | H7 — definitions, not theorems. With the §3.5 correction: the kernel emits integer numerators and denominators |
| **SVG rendering** | a picture; no invariant |

Moving in, beyond the obvious semantics modules: **`grammar.rs`** (forced by the
text-to-text boundary and correct on the merits — the `est:` and `--unset ci` bugs
are grammar-side), **`check.rs`** (as `parse`'s acceptance predicate, which is the
fix for "the checker is weaker than the invariant"), **the generated Markdown
blocks** (day-plan section and review block — this is what structurally kills G1),
and the four semantic leaks in `tm/src`: `items.rs::apply_pair`,
`items.rs::drop_stale_demotion`, `ctx::wake_time` (E8), and `lifecycle`'s drop
resolution.

---

## 4. What gets proved, defect by defect

**U** = unrepresentable, no proof needed. **P** = caught as a failed proof
obligation (you must have stated the property). **~** = partial: the type forces a
decision point but not the right decision. **M** = missed. **A** = fixed by single
ownership of the semantics — architecture, not type theory. Do not credit the Lean
compiler for the **A** rows.

### A. "An id names one item" — six paths

| # | defect | verdict | mechanism |
|---|---|---|---|
| A1 | `close month --drop` marked the *archive copy* `[~]`, so both lines read as live | **U** | the glyph is a function of placement, not a stored field (`drop_preserves_archive_glyph`) |
| A2 | `demote_one` wrote a second archive copy into a newer month | **U** | `archive : Option Site`; writing replaces |
| A3 | the month close carried a record into a file that already had one | **U** | same |
| A4 | `readopt` brought a record back into the file its stale line was in | **U** | readopt *consumes* the tombstone (`readopt_clears_archive`, `rfl`) |
| A5 | `store::choose` and `Tree::get` ranked duplicates differently, so `tm edit` read one line and rewrote another | **U** | `store.get : Id → Option Entity` — there is nothing to rank |
| A6 | **still open at HEAD**: `tm move` never checks the destination; 164 sequences | **U** | there is no append; `move` replaces a Site and the collision is a constructor obligation |

### B. "A close's measurement is not lost" — three paths, and a corrected law

| # | defect | verdict | mechanism |
|---|---|---|---|
| B1 | `readopt`'s absorb threw away the archive copy's `est:` | **P** | L15 |
| B2 | `demote_one` threw away the `est:` of the copy it supersedes | **P** | L15 |
| B3 | `close_week` did not fold dropped children into the parent's `est:` | **P** | `ClosePolicy week` + L15 |

The naive law is **refuted** (L14). The corrected one carries an exception that
Lean would not have handed you; what the kernel buys is that the exception lives in
the signature.

### C. Two syntactic slots for one field

| # | defect | verdict | mechanism |
|---|---|---|---|
| C1 | `tm edit est=X` wrote the leading estimate, reported success, changed nothing | **U** | one `remaining` field; `view_set_is_not_silent` per field; `edit_is_silent` is the shipped bug as a theorem |
| C2 | `--unset ci` could not see the *positional* ci digit | **U** | the same pair for `ci` |

### D. Recurrence

| # | defect | verdict | mechanism |
|---|---|---|---|
| D1 | `today_instances` planned the laundry twice | **P** | one denotation; a postcondition on instance selection |
| D2 | ordinal-keyed recurrences took the pending ordinal from the wrong place; `every:Nd` had no epoch | **~** | `InstanceKey` indexed by the recurrence kind is structural; the epoch is a spec gap, not a theorem |

### E. Planner

| # | defect | verdict | mechanism |
|---|---|---|---|
| E1 | the Active reservation covered the whole remaining estimate; a 6b item swallowed 355 minutes | **P** | L26 / D14 |
| E2 | batching gathered past an equal-`ci` candidate | **P** | L26 / D13 + D6 |
| E3 | `diff()` deduplicated moved items with `Vec::dedup` | **U** | `moved` is a set |
| E4 | `resume` built `dropped` the same way | **U** | same |
| E5 | free positions included breaks | **P** | placement property D12 |
| E6 | `remaining_budget × block_min` overflowed from a hand-edited `state.json` | **U** | `Nat` |
| E7 | `window_and_budget` solved a fixed point by iterating | **~U** | totality forces a termination argument or a bound |
| E8 | two wake fallbacks — planner used midnight, `Ctx` expected arrival, so every ci-4/5 item became ineligible | **A** | single ownership. Rust could have had this too |

### F. Lifecycle

| # | defect | verdict | mechanism |
|---|---|---|---|
| F1 | `auto_close` stamped skipped periods closed *unrun* | **P** | L19; and catch-up becomes one step |
| F2 | `close month --drop ^id` did nothing after auto-close | **P** | L16 + convergence |
| F3 | `close day` replaced a written review with `review pending` | **P** | needs generated-block ownership — arrives at stage 6, **M** until then |
| F4 | `close_week` demoted walls instead of carrying them | **P** | `ClosePolicy` exemptions |
| F5 | a parent cycle made `close_week` delete every line in it | **U** | acyclicity in `planWf`; the traversal is total by construction |
| F6 | `close_day` double-counted `est:` against logged minutes | **P** | arithmetic postcondition |

### G. What a kernel misses — the honest half

| # | defect | verdict | what covers it instead |
|---|---|---|---|
| G1 | `tm plan` wrote the day section with a private stand-in renderer in `cli/render.rs`, so the file, `tm now` and `tm tui` printed three different texts | **A** | the kernel owns the generated blocks; there is exactly one implementation of the day-section text. Structural, but architectural |
| G2 | `tm init --dir X` died: a positional's clap arg id shadowed the global `--dir` | **M** | integration-bug table below |
| G3 | `--json` never reached the error path | **M** | integration-bug table below |
| G4 | `tm close day --help` advertised `--drop`, which the runtime rejects | **M** | integration-bug table below |
| G5 | `tm start --energy 9` was silently filtered away | **~** | `Fin 6` forces a decision point at the boundary; nothing stops the CLI writing `.getD 3` |
| G6 | `pad`/`truncate` counted characters, so `⏰` broke every column | **M** | Rust unit tests; stays in the TUI |
| G7 | `DayBar::col_of` / `start_of` not inverse when `1440 % cols ≠ 0` | **~** | a genuine algebraic property — as a Rust property test in the renderer |
| G8 | ICS: `UNTIL` as a UTC instant, `BYDAY` outside `FREQ=WEEKLY`, … | **M** | RFC 5545 conformance tests; ICS never touches the kernel |
| G9 | `Log::read` on invalid UTF-8; `append_all` on a torn last line; `FsStore::abs` accepting an escaping path | **M** | Rust; I/O stays in Rust |
| G10 | generated skills told Claude to read fields `tm review --json` does not emit | **M** | a schema test over the emitted JSON |
| G11 | TUI: hour band clamped to 06..24 hiding a night wall; stacked layout truncated; `J`/`K` on `# Demoted` acted on a different item | **M** | integration-bug table below |
| G12 | `tm add "- [ ] …"` did not accept the line as written; `tm init` named files from the machine clock, not the tree's `tz` | **M** | the first half becomes a parser property (stage 2); the second stays Rust |

### Tally

| verdict | count | of 39 |
|---|---|---|
| **U** unrepresentable | 12 | A1–A6, C1, C2, E3, E4, E6, F5 |
| **P** proof obligation | 12 | B1–B3, D1, E1, E2, E5, F1–F4, F6 |
| **A** single ownership | 2 | E8, G1 |
| **~** partial | 4 | D2, E7, G5, G7 |
| **M** missed | 9 | G2, G3, G4, G6, G8–G12 |

Two thirds are prevented or caught. **Anyone quoting this design as "tm becomes
verified" is overstating it by a factor of three.**

### The four integration bugs, and what actually covers them

Four defects this session were integration bugs, and no kernel proof touches any of
them:

| bug | shape | countermeasure |
|---|---|---|
| a module wired to a stand-in (G1) | `cli/render.rs` re-implemented `tm_core::emit` | **the only one the design fixes**: the kernel owns the bytes of every generated block, so a stand-in has nothing to stand in for. Acceptance: one test asserts the day-section text is byte-identical across the file, `tm now`, `tm tui` and `tm plan --json` |
| a finished screen never routed into the binary | code compiled, was never reachable | **make the router exhaustive**: screens become an enum and dispatch a `match` with no `_` arm, so an unrouted screen is a compile error. Plus a smoke test that opens every screen by its key and asserts a non-empty first frame |
| a flag clash (G2), `--help` advertising a flag the runtime rejects (G4) | clap derive: a positional's arg id shadowed a global | **a CLI conformance test**: for every subcommand, parse `--help`, extract every advertised flag, and assert the runtime accepts it. Run against the built binary, not the clap tree |
| errors not JSON (G3) | `--json` never reached the error path | **a matrix test**: every verb × {success, error} × {plain, `--json`}, asserting exit code and that `--json` output parses as JSON with a `error` key. ~40 cases, one table-driven test |

All four were found by using the binary. That is not a coincidence and it is not
fixable by a proof. **Each stage below carries a manual exercise session as part of
its acceptance** — 30 minutes of driving the shipped binary on a real tree. Eleven
of 39 defects came from exactly that and from nothing else.

---

## 5. The staged plan

Every stage ships a working binary. Nothing is a big-bang cutover.

| # | scope | cost | acceptance | worth alone if everything after is abandoned |
|---|---|---|---|---|
| **0** | Fix `move_line` in Rust **now** | 1–3 days | the depth-2 sweep is clean; the 173-line proptest green at 10k cases | HEAD stops shipping a one-command corruption. Unconditionally worth it |
| **1** | Kernel core: `Grain`, `State`, `Cmd`, `Plan`, `Arith`, `ClosePolicy` — **in progress** | 1–2 wk | clean `:static` build, zero `sorry`, axiom audit, `Negative.lean` fails, 27 laws each P or R by name | §6.3 and the lifecycle stop being prose. A canonical definition of `Sound` five writers cannot re-derive differently |
| **2** | Grammar: `Tok`, `RawLine`, `parse`, `render`, round-trip B, fifteen `view ∘ set` pairs | 3–5 wk | B proved; `render ∘ parse` byte-identical over the full fixture corpus; C1/C2 dead as theorems | a checked parser usable as an oracle against Rust even with no FFI |
| **3** | Boundary: `shim.c`, `build.rs`, `dispatch` for `move`/`demote`/`readopt`/`drop`/`edit`/`rank`/`add` | 1 wk | `cargo build` from clean drives lake and links; those seven verbs kernel-backed; full suite green; panic probe returns `KernelFault`, not exit 0 | half the lifecycle verbs are structurally sound in the shipped binary; the id class is dead in production |
| **4** | `close`, `autoClose`, `ClosePolicy`; L16–L19 | 2–3 wk | close idempotent at library *and* CLI level; a 3-month-stale tree catches up losing nothing; the two behaviour changes landed with assent | §6.3 becomes one operation at three grains; F1–F4, F6 covered |
| **5** | `recur`, `tree` rollups, `priority`, `capacity`, exact arithmetic | 3–4 wk | parity harness: kernel vs Rust over the fixture corpus agrees except at the six stated rounding sites | floats leave the decision path; D1/D2, E7 covered |
| **6** | `planner`; L26 single-run laws; L24/L25 left to the existing proptest through the FFI | 3–4 wk | D1–D14 decidable-checked on every plan the corpus produces; `planner_invariants.rs` green at 256 cases through the FFI; the one-renderer test | `tm plan` kernel-backed; G1 structurally dead |
| **7** | Delete `tree::record_rank`, `tree::is_real_duplicate`, `store::choose`'s tie-break, `cli/items.rs::drop_stale_demotion` | days | suite green with those four gone; `tm check` *is* `parse` | the compensating machinery is gone, which is the proof the invariant became structural |

**Stage 0, in detail, because it ships this week and does not wait for anything.**
The `against` spike's design: (1) `move_line` refuses — or absorbs — when `to_path`
already holds `key`; (2) `FsStore::with_before_write_hook` (store.rs:1380) changes
from `Fn(&Path, usize) -> ()` to returning `Result`, so a write can be vetoed, and
a hook runs `Tree::duplicate_ids` on the post-state (on under `debug_assertions`,
behind `--paranoid` in release); (3) land the 173-line proptest and the depth-2
sweep in CI. Do not wait months for the kernel to fix a bug that ships now.

**Stage 1 is being built now.** Its first slice exists and compiles: 2,981 lines of
Lean across 7 modules, no Mathlib, clean `lake build TmKernel:static` in 1.6 s from
clean, a 497 KB archive exporting `_tm_kernel_call`, zero `sorry`, 148 theorems,
and an axiom audit over 62 key theorems showing only `propext` / `Quot.sound` /
`Classical.choice`. What remains in stage 1: scaling `Core` from five fields to the
real `Item`'s twenty-two, the `ClosePolicy` table, the plan-level checkers
(`Normalized`, the two acyclicity predicates, section discipline), and the four
`P*`/`R*` laws that are stated but not built. Also outstanding, and named by the
stage-one audit: the plan-level round trip is proved through the entity the loader
builds (`load_render_line`, `paired_renders_each_placement`) but not through
`renderDocAt`'s re-sort of the store's lines — that last step needs a permutation
argument over the store's domain and an insertion-sort stability lemma, neither of
which core Lean supplies.

**Cost basis.** Stage 1's shape is measured (one session produced 799 lines with a
1.09:1 proof-to-definition ratio; an audit and its repair took that to 2,981 lines,
and the repair was almost entirely *boundary* code and its proofs — which is the
cost signal worth carrying forward: the core was right and the edge was not). Stage 2 is the biggest unknown: `grammar.rs` is
1,246 Rust lines and round-trip B is an induction over the whole token grammar; it
is the stage most likely to overrun and the one with a named stop condition. Stage
3 is measured at ~250 lines one-time. Stages 5 and 6 are where the ratio blows up,
because calendar arithmetic and the assignment fold are where real inductions live.
Total to stage 6: **3.5–5 months**. This is a forecast, not a measurement.

---

## 6. Risks, open questions, stop conditions

### 6.1 The case against, restated fairly

The `against` spike made an argument that this plan proceeds in spite of, not
because it was refuted. It deserves to be on the record in its own terms:

1. **The invariant was already written as executable Rust.** `Tree::duplicate_ids`
   (tree.rs:908) computes exactly the sentence that broke six times. The gap was
   never expressiveness. **Nothing ran the stated invariant on the post-state of a
   command.** That is a test-harness gap, and a 173-line proptest closes it — it
   failed on 3 of 3 pre-fix commits in 7–14 seconds each, and on HEAD in 3 seconds.
2. **Three days versus months.** The cheap design catches 4 of 9 named defects
   demonstrably and ~7 of 9 plausibly. This plan's stage 0 *is* that design, which
   is the honest resolution: do the cheap thing first and keep it.
3. **The kernel is 25–30% of the code.** Seventy percent keeps being written the
   way that produced the bugs, and 11 of 39 defects live entirely there.
4. **The one-root-cause finding cuts both ways.** That all 164 violations come from
   one missing precondition supports "one guard fixes it" — and equally supports
   "five patches were applied and the hole is still open at HEAD".
5. **The FFI marshalling is unverified**, and it is the same class of code that
   produced the `est:` defect. The FFI spike reproduced tm's estimate-erasure bug
   *inside* the boundary code of a verified kernel, on the first try.
6. **tm's operations are not `state → state` today.** `horizon.rs` does 8 store
   reads and 11 writes *inside* operations; `archived_record` (:621) reads the
   store because an earlier close may have written that copy after the `Ctx::files`
   snapshot. The purity refactor is a precondition of the rewrite — and it is
   itself a large part of the fix, so **measure again after it**.

The float objection is the one the spike itself downgraded, and this plan agrees:
no transcendentals in scope, integer observables, 0.09% one-minute drift. Nobody
should reject or accept this proposal on float grounds.

**What it costs to be wrong.** Three to five months of work; a second language and
a second toolchain (2.7 GB each, three installed) that every contributor and every
CI job needs; a permanent hand-written C shim; a two-language spec-change tax on a
spec that has changed repeatedly during this build; and — the real one — a kernel
that is 30% of the system, leaving the 70% that produced eleven of the defects
untouched. If the honest outcome is "the bug class was already dead after stage 0",
the rest is a specification exercise with a runtime dependency attached.

### 6.2 Open questions that need a decision, not a proof

1. **Two behaviour changes need your assent before stage 4**, and both change what
   lands in which file: the derived `close_day` target (the week containing *now*,
   not the week containing the closed day) and the ISO-Thursday week→month
   tie-break. The first is what makes close idempotence provable. Both were read
   off line citations, not observed by running the binary — **"this is a bug" vs
   "this is an undocumented deliberate choice" is a judgment reading cannot
   settle**, and `auto_close`'s grain-ordered catch-up masks both. Construct a
   stale tree and close it before deciding.
2. **`Id`.** §3.1 says 4 chars of `[a-z0-9]`; `pub struct Id(pub String)` enforces
   nothing; `tm check` accepts `^ZZZZZZZZZZ`; and the spec's own §4.3 fixture ships
   `^O1`, `^m1`, `^t3`. A refinement type turns that into a compile error on day
   one. **The right resolution is to weaken the spec, not the data** — and only a
   human can tell that case from the case where the type is right.
3. **`inventory`'s R7 stands open.** Lifecycle commands do not commute:
   `demote ^m1 ; move ^m1 week` breaks a tree the reverse order does not. Nobody
   has decided whether they should. L27 makes the kernel refuse to be silent about
   it; it does not answer it.
4. **L24 (tail-drop) and L25 (stability) are unpriced.** They relate two runs of a
   greedy fold — real inductions, not `decide`. `inventory` budgets tail-drop alone
   at plausibly a week; it currently has a working 882-line proptest at 256 cases
   that has empirically caught things. **Recommendation: keep the proptest, state
   the law in Lean, prove it last or never.** A kernel that proves 25 of 27 laws
   and property-tests 2 is not compromised — but decide that deliberately now
   rather than discover it in month six.
5. **Scaling `Core` to the real `Item` is not obviously the same difficulty.** Five
   fields versus twenty-two. The subtype-over-dependent-record choice is precisely
   so this scales, and the failure mode of the alternative was hit firsthand — but
   nobody has done it yet.

### 6.3 Stop conditions

Named in advance, with triggers, so that stopping is a decision and not a
capitulation.

| trigger | action |
|---|---|
| Stage 2 exceeds 6 weeks, or round-trip B will not close | the parser stays in Rust; the boundary becomes structured JSON instead of text. Re-price stages 3–6 — this changes the design, not just the schedule |
| Proof : definition exceeds 3 : 1 measured at the end of stage 4 | stop proving relational laws. Keep decidable checkers plus the existing proptests, and say so in the README rather than letting the ratio quietly eat the schedule |
| Any needed proof requires Mathlib | stop and re-price at that moment: 9.7 GB, a 118 MB binary, `Mathlib:static` on every linking machine, and Mathlib choosing the Lean version, including release candidates |
| A kernel call in the TUI exceeds 5 ms at 500 items | try the session handle (with `lean_mark_mt` and a mutex, UI thread only); if that is not enough, the runtime kernel is the wrong shape for the TUI |
| Two consecutive Lean upgrades each cost more than a day of proof repair | freeze the toolchain indefinitely and treat the kernel as a fixed artifact, or fall back to the design-time model |
| After stage 3, an exhaustive depth-3 sweep is clean and 60 days of use produce no new defect in the covered class | **the bug class is gone.** Stages 5–6 are then buying uniformity, not soundness. That is a legitimate reason to stop, and it should be stated out loud if it happens |

---

## 7. Standing rules

Each earned by something that went wrong in a spike.

- **Pin `lean-toolchain`.** A change to it is a reviewed decision. `lake update`
  moved a pinned v4.33.1 to v4.34.0-rc2 without asking and cost two link failures
  with a misleading error.
- **No Mathlib.** Revisit only against a proof that genuinely needs it, and price
  the 118 MB and the toolchain coupling at that moment.
- **The kernel is total.** No `!`, no `partial`, no `panic!`, no `native_decide`,
  no `sorry`, no `.toOption`. CI:

  ```bash
  ! grep -RnE 'partial def|panic!|native_decide|\.toOption|sorry|get!|\]!' kernel/TmKernel
  ```

  (curate the pattern; it passes on the current package)
- **Nothing but `String` crosses the boundary.** No `lean_object*` escapes the
  shim; thread safety then has nothing to get wrong.
- **Every bounded type gets a `Fin`/`Subtype` and a smart constructor used by its
  `FromJson`**, and every integer crossing gets a stated width. ~8 lines per type;
  forgetting it on one type silently reopens the hole.
- **A field's setter is not exported without its `view ∘ set = id` proof.**
- **`Negative.lean` must fail to compile**, and CI asserts the failure. It is the
  only test that checks the type system is still doing its job.
- **Each stage ends with 30 minutes of driving the shipped binary on a real tree.**
  Eleven of 39 defects came from that and from nothing else.

---

## Appendix: reproducing the evidence

```bash
# The architecture package (stage 1's first slice)
cd scratchpad/lean-arch/TmArch
~/.elan/bin/lake build TmArch:static                     # 1.33 s clean
LEAN_PATH=.lake/build/lib/lean ~/.elan/bin/lean Check.lean    # axiom audit
LEAN_PATH=.lake/build/lib/lean ~/.elan/bin/lean Negative.lean  # MUST fail: 4 errors
nm .lake/build/lib/libTmArch_TmArch.a | grep tm_kernel_call    # T _tm_kernel_call

# The FFI spike
cd scratchpad/lean-ffi/tm-ffi-demo && cargo build --release    # 2.26 s clean
./target/release/tm-ffi-demo --bench --trust --bounded --panic --shared --shared-mt

# The counterfactual harness and the exhaustive sweep
scratchpad/lean-against/repo/tm-core/tests/invariant_proptest.rs      # 173 lines
scratchpad/lean-against/repo/tm-core/tests/invariant_exhaustive.rs    # 19,740 pairs
scratchpad/lean-against/exhaustive.txt                                # 164 violations

# The minimal live reproducer
scratchpad/lean-inventory/REPRO-move-dup-id.sh
```

Notes in full: `scratchpad/lean-notes/architecture.md` (984 lines),
`ffi-spike.md`, `inventory.md`, `firstprinciples.md`, `against.md`.
