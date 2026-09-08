# `tm` kernel in Lean 4 — stage one

This is the first stage of the `rebuild-on-lean` kernel described in
`../PLAN-lean-kernel.md`. It is small on purpose. Everything it claims below
is compiled, and the acceptance script re-checks every claim in about four
seconds.

```
kernel/
  TmKernel/            Lean 4 package, no Mathlib, toolchain pinned to v4.33.1
    TmKernel/Grain.lean      the horizon order, derived from one generator
    TmKernel/Text.lean       tokenizer, decimal numerals, the inverse lemmas
    TmKernel/Line.lean       the item line: parse, serialise, the est: view
    TmKernel/State.lean      entity vs observation; the id invariant, locally
    TmKernel/Plan.lean       the plan as one object; the invariant, globally
    TmKernel/Cmd.lean        five commands, each with its law proved or refuted
    TmKernel/Boundary.lean   String -> String; one @[export]
    Check.lean               axiom audit (42 theorems)
    Negative.lean            MUST FAIL to compile — the demonstration
  tm-kernel-ffi/       Rust: the C shim, build.rs, and 9 tests that call Lean
  check.sh             stage-one acceptance
  totality.py          the kernel must be total; this enforces it
```

## Build and check

```bash
./check.sh                     # everything below, ~4 s
```

or by hand:

```bash
cd TmKernel && ~/.elan/bin/lake build TmKernel:static
LEAN_PATH=.lake/build/lib/lean ~/.elan/bin/lean Check.lean     # axiom audit
LEAN_PATH=.lake/build/lib/lean ~/.elan/bin/lean Negative.lean   # MUST print errors
cd ../tm-kernel-ffi && cargo test                               # Rust -> C -> Lean
```

Measured on an M-series Mac: `lake build TmKernel:static` from clean **1.3 s**;
`cargo test` from clean, driving lake and linking the Lean runtime, **3.5 s**;
the linkable archive is **408 KB** and the test binary **3.8 MB**.

**No Mathlib.** Everything used — `Fin`, `Nat`, `Option`, `Except`, `Subtype`,
`List`, `omega`, `decide`, `simp`, `Lean.Data.Json` — is core toolchain.
Mathlib would cost 9.7 GB on disk, a 118 MB binary, and — decisively — it
chooses your Lean version. `lean-toolchain` is pinned; changing it is a
reviewed decision.

The Rust crate is **its own cargo workspace on purpose**, so `cargo build` in
the tm workspace does not require `elan` to be installed.

## What this stage is for

`tm`'s duplicate-id bugs were not five bugs. The `against` spike established
by exhaustive search that they are **one missing precondition** in
`horizon::move_line -> move_to` (horizon.rs:943), which appends a line to the
destination file without asking whether that file already holds the id. 164
violating depth-2 command sequences remain reachable at tm HEAD; one of them is
a single command on a fresh `tm init --example` tree.

**The structural answer is that there is no append.** Item lines are not
stored anywhere. A `Doc` holds prose only; an item line is *rendered* from the
entity that owns it, and an entity owns exactly one live placement and at most
one archive placement, in a different file. `move` cannot put a line somewhere
— it can only replace a `Site`, and replacing it into the file the tombstone
occupies is refused by the constructor.

The consequence is `every_transform_preserves_the_invariant`: there is no
preservation proof, and none to write, because the invariant is a theorem about
*every* `PlanCore`. Commands that do not exist yet cannot break it either.

## The demonstration

`Negative.lean` writes the bug the way the Rust wrote it and **fails to
compile**. This is the whole argument for the rebuild, so it is a checked
artifact: `check.sh` fails if `Negative.lean` ever starts compiling.

```
$ LEAN_PATH=.lake/build/lib/lean lean Negative.lean

Negative.lean:17:15: error: `live` is not a field of structure `Subtype`
Negative.lean:17:2: error: Fields missing: `val`, `property`

Negative.lean:21:29: error: Application type mismatch: The argument
  rfl
has type
  ?m.7 = ?m.7
but is expected to have type
  wf (let __src := e.val;
      { live := t, archive := __src.archive, status := __src.status,
        line := __src.line, stamps := __src.stamps }) = true

Negative.lean:30:74: error: Application type mismatch: The argument
  p.property
has type
  planWf p.val = true
but is expected to have type
  planWf { docs := p.val.docs.modify k (appendLine (serializeItem i g r)),
           store := p.val.store } = true

Negative.lean:38:74: error: unsolved goals
bm : Nat
e : Entity
⊢ remainingOf bm e.val.line ≤ remainingOf bm (setEst 0 e.val.line)

Negative.lean:44:0: error: Not a definitional equality: the left-hand side
  viewRemaining bm (setLeadWord w r)
is not definitionally equal to the right-hand side
  unitValue bm w
EXIT=1
```

Five cheats, five compile errors:

| cheat | what it is | why it fails |
|---|---|---|
| 1 | hand the raw record through, as `move_to` does | `Core` is not `Entity` |
| 2 | fake the obligation with `rfl` | `rfl : ?a = ?a` is not `wf c = true` |
| 3 | **the original bug**: append the rendered line to the destination file | a document holds prose only, and `planWf` says none of it parses as an item, so the appended plan cannot be constructed |
| 4 | a close that zeroes the estimate it just measured | the conservation obligation is not dischargeable |
| 5 | export `setLeadWord` as "edit the estimate" — what `tm edit est=` did | the `view ∘ set = id` obligation every setter must discharge cannot be discharged for it |

## What is proved

96 theorems; the audit in `Check.lean` covers 42 of them and shows only
`propext` / `Classical.choice` / `Quot.sound`, **never `sorryAx`**. Three
(`drop_idem`, `readopt_reopens`, `grain_rejects_99`) depend on no axioms at all.

### The generating structures

`Grain := Fin 3` (day ⊂ week ⊂ month), and one generator, `coarsen`, the
**saturating** successor of that chain. Backlog is the *absence* of a bound,
not a coarser grain, which is why saturation is the right generator rather than
an accident.

- `coarsen_month : coarsen month = month := rfl` — §6.3's third close row is
  not a special case, it is the **fixed point** of the first two.
- `demote_is_one_step` — demotion is a step along the chain, not a row in a
  table of legal transitions.
- `closeTo_target_is_open` — the derived close rule can never file work into a
  file that is already closed. This is what makes close idempotence provable
  at stage 4.
- `impl_day_rule_disagrees` and `containing_can_target_a_closed_region` — the
  rule `horizon.rs:1323` uses (the week containing the *closed day*) **can**
  target an already-closed week, and does, when Sunday is closed on Monday.
  `#eval` gives `(week 0, week 1)`. **This is a behaviour change that needs
  the user's assent**, and it is recorded here, not decided.

`Check.lean` prints §6.3's three rows generated from one rule at three grains:
`(week 35, month 8, month 8)`.

### Entity versus observation

An id names an entity; a line is an observation of it at a site. `[-]` is not
a status — five states, not six — and the glyph is a function of placement.

- `archive_elsewhere`, `one_line_per_file`, `exactly_one_live` — one file, one
  line, and exactly one of the (at most two) lines is the live one, so the
  ambiguity of `[-]` in the file is harmless: the role is positional.
- `no_two_lines_of_one_id_in_one_file` — **the sentence six code paths
  violated**, for every possible plan.
- `lines_per_id_le_two` — and no plan has three lines of one id.
- `every_transform_preserves_the_invariant`,
  `every_transform_keeps_lines_le_two` — for *any* transformation, including
  ones not yet written.
- `prose_is_never_an_item` — a document's prose contains nothing that parses as
  an item, so the only item lines a file emits are the ones its entities render.

### The grammar

The subset this stage **interprets**: `<indent>- [<state>] <tokens…>`, with the
six state glyphs, whitespace-separated tokens kept verbatim, exactly one `^id`
token, and `est:<N>b|m|h` plus the leading estimate `<N>b|m|h` read as numbers.
Everything else — `@parent`, `#tag`, `!k`, `due:`, `at:`, `every:`,
`on-event:`, `waiting:`, `max:`, front matter, headings, blank lines, comments,
generated blocks — is **preserved byte for byte and not interpreted**. That is
the honest boundary: the subset that is *parsed* is the whole file; the subset
that is *understood* is the state box, the id, and the estimate.

- `tokenize_raw` — the token vector concatenates back to exactly the bytes read.
- `serialize_parse` (**round trip A**) — every line the parser accepts
  serialises back byte for byte, *including the state box and the `^id`, which
  are regenerated from the status and the store key rather than copied*. So a
  line whose `^id` disagrees with the id that names it is not a state this
  kernel can hold.
- `parse_serialize` (**round trip B**) — anything the kernel writes it reads
  back identically, on `CanonicalItem`, which is decidable. That the setters
  *preserve* `CanonicalItem` is **not** proved — see gap 10.
- `renderSplit_splitDoc` — **round trip over a whole file**: splitting a
  document into prose and items and putting it back reproduces the file
  exactly.
- `readNat_digitsOf` — the decimal round trip, so a written `est:` value is the
  value that is read back.
- `view_set_is_not_silent` — the obligation that kills the shipped
  `tm edit est=` bug, and `lead_edit_is_silent` — **the shipped bug itself, as
  a theorem**: with an `est:` token present, writing the leading estimate
  changes nothing the kernel reads.

### The commands and their laws

Five commands, each a `Transform = WfPlan → Except KErr WfPlan`.
**P** = proved, **R** = refuted.

| law | verdict | theorem |
|---|---|---|
| `move` rejects a collision with the tombstone | **P** | `move_into_archive_file_is_rejected`, `plan_move_into_archive_file_is_rejected` |
| `move` is idempotent (success domain) | **P** | `move_idem` |
| `move` is last-wins (**first move succeeds**) | **P** | `move_last_wins` |
| `move` is last-wins globally | **R** | `move_last_wins_refuted_globally` |
| `move` is invertible | **R** | `move_not_invertible` |
| `drop` is idempotent; `settled` absorbing | **P** | `drop_idem`, `settled_absorbing` |
| `drop` preserves the archive line's glyph | **P** | `drop_preserves_archive_glyph` |
| `edit est=v` ⟹ the view reads `v` | **P** | `set_is_not_silent`, `set_last_wins` |
| `demote` is idempotent | **R** | `demote_not_idem` |
| `readopt ∘ demote = id` on the nose | **R** | `readopt_demote_not_id` |
| `readopt ∘ demote = id` modulo stamps | **P** | `readopt_demote_id_mod_stamps` |
| conservation: floor `remaining` at the recorded value | **R** | `floor_and_respect_are_incompatible` |
| conservation, corrected | **P** | `demoteEst_conserves`, `demoteEst_respects_user` |

The refutations are the point, not decoration:

- **`move` is not last-wins globally** because a *failed* first move is not the
  same as no first move: if the destination collides with the tombstone the
  composite errors while the single move succeeds. This matters for the TUI,
  which retries.
- **`move` is not invertible**, so `tm undo` must replay the log and never
  apply an inverse.
- **`demote` is not idempotent**, and that is correct: stamps accumulate
  deliberately, to drive the month review's "≥ 2 stamps" cut list. Idempotence
  holds only modulo `stamps`, and the kernel has to say which it means rather
  than leave two readings of §6.3 available.
- **The conservation law that three separate Rust commits tried to enforce is
  false.** `floor_and_respect_are_incompatible` proves that **no** rule can
  both floor `remaining` at the value a close recorded and leave a deliberate
  `tm edit est=1b` alone. Lean refuses the naive law. It does *not* hand you
  the exception — only running the binary did that. What the kernel buys is
  that the exception is written once, in `demoteEst`'s signature, where a later
  writer cannot fail to read it.

### The boundary

One export, `@[export tm_kernel_call] def callExport (input : String) : String`
(verified in the archive: `nm` shows `T _tm_kernel_call`). Nothing but a string
crosses, so there is no marshalling, no `lean_object*` in Rust, and no
thread-safety protocol to remember — the FFI spike SIGSEGV'd in 3 of 5 runs
sharing one `lean_object*` across 8 threads; here there is nothing to share.

The C shim is **mandatory and permanent**: `lean.h`'s host API
(`lean_inc`, `lean_dec`, `lean_dec_ref`, `lean_io_mk_world`,
`lean_io_result_is_ok`, `lean_string_cstr`) is `static inline` and has no
linkable symbol, and `lean_initialize_runtime_module` is exported but declared
in no public header. `bindgen` cannot help. It is 66 lines.

Bounded types get a smart constructor used by the decoder
(`grain_rejects_99 : Grain.ofNat? 99 = none`), and `.toOption` is banned and
enforced by `totality.py` — it is how the FFI spike silently turned `est: -3`
into `est: null`, reproducing tm's own estimate-loss bug inside the boundary
code of a *verified* kernel.

Nine Rust tests call the kernel through the shim. The one that matters:

```rust
#[test]
fn move_into_the_tombstones_file_is_refused() {
    let out = call(&req(
        r#"[{"op":"demote","id":"m1","doc":1,"period":37},
            {"op":"move","id":"m1","doc":0}]"#)).unwrap();
    assert_eq!(out, r#"{"err":{"kernel":"occupied"}}"#);
}
```

## What this does **not** cover

Stated plainly, because a small thing that compiles is worth more than a large
sketch, and because the gaps are where the next stage's cost lives.

1. **The plan-level round trip is evaluated, not proved.** Line-level A and B
   and the whole-file `renderSplit_splitDoc` are theorems. That the store,
   rebuilt from a parse and read back out, reproduces the same per-document
   item list is *demonstrated* by `cargo test` and `#eval`, not proved: it
   needs a permutation argument over the store's domain that I did not build.

2. **Reloading a demoted item is not supported.** After `demote`, the plan
   renders two `[-]` lines with one id in two files — exactly today's tm format
   — but the loader accepts at most one line per id, so that output cannot be
   read back. tm distinguishes the archive copy by its `# Demoted` section;
   sections are not modelled here. This is the single biggest functional gap
   and it belongs to stage 2.

3. **`Core` has five fields; tm's `Item` has twenty-two.** The
   subtype-over-dependent-record choice is precisely so that this scales, but
   it has not been scaled. Sections, `@parent`, `after:`, recurrence, shapes,
   due dates, budgets and tags are all absent. So are acyclicity, section
   discipline and per-file-kind shape rules — the rest of the plan-level tier.

4. **No calendar arithmetic.** `Day` is a `Nat` and `index` is `d`, `d/7`,
   `d/30`. It is enough to *evaluate* the close rule and to prove the two
   disagreement theorems; it is not ISO week and civil month arithmetic. The
   week→month tie-break (`firstprinciples` proved week does not refine month)
   is not implemented.

5. **No `close`, no `autoClose`, no `ClosePolicy`, no planner, no priority, no
   recurrence, no exact-arithmetic layer.** L16–L27 of the architecture are not
   here. In particular the two relational laws — tail-drop and stability — are
   not attempted, and the recommendation in the plan stands: keep the existing
   882-line proptest, state the laws in Lean, and prove them last or never.

6. **The line-splitting at the very edge is unverified.** The kernel's document
   round trip is over `List (List Char)`. Splitting a file's bytes on newlines
   and joining them again happens in JSON at the boundary, and
   `String.intercalate "\n" (s.splitOn "\n") = s` is not a core theorem.

7. **`Id` is `List Char`, not §3.1's "4 chars of `[a-z0-9]`".** The spec's own
   §4.3 fixture ships `^O1`, so the tight type would fail the build on day one.
   The right resolution is to weaken the spec, not the data — but that is a
   judgment a human has to make, and it is recorded here rather than silently
   taken.

8. **Nothing in the shipped `tm` binary calls this yet.** Stage 3 wires it in.
   The Rust crate here is a bridge and nine tests, not an integration.

9. **`setEst` is not proved to preserve `CanonicalItem`**, so round trip B is
   not yet chained across an edit. It holds for the replace branch; it is
   *false in general* for the insert branch, because inserting a token before an
   id token that was the line's first token leaves that id token without a
   separator. Real lines never look like that — which is exactly the kind of
   reasoning this kernel exists to stop relying on.

10. **The proof-to-definition ratio here is not a forecast.** This fragment has
    no planner, no calendar arithmetic and no relational laws — the three places
    the ratio blows up.

## Standing rules, each earned by something that went wrong in a spike

- Pin `lean-toolchain`; a change to it is a reviewed decision. `lake update`
  silently moved a pinned v4.33.1 to v4.34.0-rc2 and cost two link failures.
- No Mathlib. Revisit only against a proof that genuinely needs it, and
  re-price the 118 MB binary and the toolchain coupling at that moment.
- The kernel is total: no `partial`, no `panic!`, no `!`-suffixed partial
  function, no `native_decide`, no `sorry`, no `.toOption`. `totality.py`
  enforces it and `check.sh` runs it.
- Nothing but `String` crosses the boundary.
- Every bounded type gets a `Fin`/`Subtype` and a smart constructor used by its
  decoder.
- A field's setter is not exported without its `view ∘ set = id` proof.
- **`Negative.lean` must fail to compile**, and `check.sh` asserts the failure.
  It is the only test that checks the type system is still doing its job.
