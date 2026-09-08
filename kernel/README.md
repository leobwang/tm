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
    Check.lean               axiom audit (120 theorems)
    Negative.lean            MUST FAIL to compile — the demonstration
  tm-kernel-ffi/       Rust: the C shim, build.rs, and 21 tests that call Lean
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

Measured on an M-series Mac: `lake build TmKernel:static` from clean **1.6 s**;
`cargo test` from clean, driving lake and linking the Lean runtime, **3.6 s**;
the linkable archive is **497 KB** and the test binary **3.9 MB**.

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
destination file without asking whether that file already holds the id. 426
violating depth-2 command pairs of 39,601 (199-command alphabet) are reachable
on tm `main`, and none on `fix-move-precondition`; one of them is
a single command on a fresh `tm init --example` tree.

**The structural answer is that there is no append.** Item lines are not
stored anywhere. A `Doc` holds prose only; an item line is *rendered* from the
entity that owns it, and an entity owns exactly one live placement and at most
one archive placement, in a different file. `move` cannot put a line somewhere
— it can only replace a `Site`, and replacing it into the file the tombstone
occupies is refused by the constructor.

The consequence is `no_two_lines_of_one_id_in_one_path`: for that half of the
invariant there is no preservation proof, and none to write, because it is a
theorem about *every* `PlanCore`. Commands that do not exist yet cannot break it
either.

**An audit of the first version of this package found that the structural claim
was true and the boundary around it was not**, and the corrections are the
substance of the current version. Three of them are worth stating up front,
because each is the *same* class of defect as the one the rebuild exists to
remove:

- a `[-]` line did not survive a read with **no commands at all** — the loader
  sent `Glyph.demoted` to a live open item and the kernel rewrote the user's
  file. The line-level round trip theorem did not catch it because it is stated
  about the glyph the *parser returned*, and the pipeline throws that glyph away
  and asks `glyphAt` for a new one. `load_render_line` and
  `paired_renders_each_placement` are stated about the entity the loader builds,
  which is what the FFI renders from;
- `move` to a document index that does not exist **deleted the item and returned
  `ok`** — the same missing precondition, moved from "the destination already
  holds this id" to "the destination is not a file". A destination is now a
  `Dest`, whose second field is a proof that the index is a document of this
  plan, and `no_line_is_lost` is the theorem that nothing can fall off the end;
- two documents could share a `path`. Every index-level theorem stayed true
  while two `^m1` lines landed in one file. Paths are now injective by
  `planWf`, and the theorem is restated over paths.

**A second audit found one more, and it is a correction to the first fix in that
list**, which makes it worth stating separately: an inverse can fail by having no
value, and it can fail by having **two**.

- `demote` renders `[-]` at *both* of an entity's sites, so for the two-line form
  it writes, both orientations of the pair are entities that render exactly those
  two lines. The loader tried one and then the other and took the first that
  worked, so **which line was the tombstone was decided by the order the host
  listed the documents in** — the same two files, listed the other way round,
  made `drop` mark the other one. The module header said the loader "never picks
  a nearby state", and that was true of the case where nothing renders and false
  of the case where two things do. What decides it is the domain: a close leaves
  the tombstone in the region it closed and files the work into `closeTo`, which
  is never itself closed, so the two horizons are **ordered**. A `Doc` now
  carries its `Option Region`, `demotionsOriented` joins `planWf`, and the loader
  inverts an order instead of trying orientations. A pair the documents do not
  order is `LErr.ambiguousDemotion`, by name.

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

Negative.lean:51:60: error: omega could not prove the goal:
No usable constraints found.        -- `Dest p.val` wants `n < p.val.docs.length`

Negative.lean:58:55: error: Application type mismatch: The argument
  rfl
has type
  ?m.6 = ?m.6
but is expected to have type
  (statusOfGlyph q.glyph).isSome = true
in the application
  (statusOfGlyph q.glyph).get ⋯

Negative.lean:68:47: error: Application type mismatch: The argument
  rfl
has type
  ?m.8 = ?m.8
but is expected to have type
  demotionsOriented { docs := planDocs, store := store } = true
in the application
  planWf_of_parts h1 h2 h3 rfl
EXIT=1
```

Eight cheats, eight compile errors:

| cheat | what it is | why it fails |
|---|---|---|
| 1 | hand the raw record through, as `move_to` does | `Core` is not `Entity` |
| 2 | fake the obligation with `rfl` | `rfl : ?a = ?a` is not `wf c = true` |
| 3 | **the original bug**: append the rendered line to the destination file | a document holds prose only, and `planWf` says none of it parses as an item, so the appended plan cannot be constructed |
| 4 | a close that zeroes the estimate it just measured | the conservation obligation is not dischargeable |
| 5 | export `setLeadWord` as "edit the estimate" — what `tm edit est=` did | the `view ∘ set = id` obligation every setter must discharge cannot be discharged for it |
| 6 | take a relocation's destination straight off the wire, which is what let `move ^m1 7` delete the item from a one-document plan | a `Dest` is an index **plus a proof it is a document of this plan**, and a `Nat` decoded from JSON cannot supply the second field |
| 7 | read a lone `[-]` back as an ordinary open item, which is what the first loader did | the inverse of `glyphAt` is a *partial* function and `statusOfGlyph .demoted` is `none`; `.get` needs a proof there is something there |
| 8 | build the plan without answering which of a demotion's two `[-]` lines is the tombstone — deciding it by document order was this, with the assertion hidden in a `match` | `planWf` has five parts; `rfl` is not a proof of any of them |
| 9 | wave the **item half** of the plan-level tier through, which is what "cycles are only a `tm check` warning" amounts to once `tm check` and the acceptance rule are one function | `itemsWf` is a part of `planWf` like the other four |
| 10 | claim a transform that lands in range and keeps its tombstone behind it always succeeds | since `Normalized` and `after:` acyclicity joined `planWf`, `mapAt_ok_of_inRange` carries a fifth obligation and will not apply without it |
| 11 | `ci: 9` | `Fin 6`, reached through a smart constructor and never through a numeral — `(9 : Fin 6)` would *silently* wrap to 3 |
| 12 | `#lean #lean` as two tags | tags are a set structurally: `{ l : List (List Char) // l.Nodup }`, whose proof lives inside the field's own type so `{c with …}` still works |
| 13 | `win:25:00`, `every:month:32` | `Fin 1440` and `Fin 31`, each with the smart constructor its decoder must use |

## What is proved

234 theorems; the audit in `Check.lean` covers 120 of them and shows only
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
- `demotion_target_follows_the_closed_region` — and the close rule *orders* the
  two files of a demotion: the tombstone's region comes strictly before the one
  the work was filed into, in `horizonPrecedes` (lex on grain then block, with
  backlog last because nothing closes backlog). Below month the grain settles it;
  at month it is `Closed` that does, which is why the fixed point needs the
  hypothesis and the other two rows do not. This is the fact the loader inverts,
  and `horizonPrecedes_asymm` is why the inversion has exactly one answer.

`Check.lean` prints §6.3's three rows generated from one rule at three grains:
`(week 35, month 8, month 8)`.

### Entity versus observation

An id names an entity; a line is an observation of it at a site. `[-]` is not
a status — five states, not six — and the glyph is a function of placement.

- `archive_elsewhere`, `one_line_per_file`, `exactly_one_live` — one file, one
  line, and exactly one of the (at most two) lines is the live one. The role is
  positional, and an earlier version of this line went on to say that the
  ambiguity of `[-]` in the file is therefore harmless. It is harmless *inside*
  an entity, which is all these three theorems are about, and it is not harmless
  at the boundary: two `[-]` lines are two positions and the bytes do not say
  which position is which. What says it is the pair of files
  (`the_tombstone_is_behind_the_live_line`).
- `no_two_lines_of_one_id_in_one_file` — **the sentence six code paths
  violated**, for every possible plan. It quantifies over `Site.doc`, a list
  *index*.
- `no_two_lines_of_one_id_in_one_path` — **the same sentence about what reaches
  the disk.** Two documents at different indices carrying one path are one file,
  and the index-level theorem says nothing about that: before path injectivity
  joined `planWf`, a demote put two `^m1` lines into one `w.md` with every
  stated theorem still true. This is the version whose name matches its
  statement.
- `no_line_is_lost` — every line of every plan lands in a document that exists,
  so rendering document by document emits all of them. This is what makes
  `move ^id 7` impossible rather than silent.
- `lines_per_id_le_two` — and no plan has three lines of one id.
- `prose_is_never_an_item` — a document's prose contains nothing that parses as
  an item, so the only item lines a file emits are the ones its entities render.
- `glyphAt_statusOfGlyph`, `glyphAt_statusOfGlyphDemoted` — `glyphAt` is the
  only writer of a state box, and these are its **inverse**: the entity a loader
  builds from a glyph renders that same glyph back. Where the inverse is `none`
  the configuration is unreachable and the loader rejects rather than picking
  something close.
- `the_tombstone_is_behind_the_live_line` — and where the inverse is not a
  function of the glyphs at all, because a demotion writes `[-]` at both sites,
  it is a function of the two **files**: in every accepted plan an entity's
  archive placement sits in a horizon strictly before its live one. That is a
  fourth conjunct of `planWf`, so `mapAt` re-establishes it on the post-state of
  every command (`mapAt_rejects_unoriented`), which is what stops the kernel
  writing a pair it would then have to guess at.

### Closure, and what is not free

The first version of this package carried a theorem named
`every_transform_preserves_the_invariant` whose `f`, `p` and `_h` binders were
all unused: it was `no_two_lines_of_one_id_in_one_file` with three ignorable
arguments, and its name promised a closure property it did not state. **It is
withdrawn**, along with `every_transform_keeps_lines_le_two`. What replaces it
is the honest split:

- the id-uniqueness half genuinely *is* structural. Restating it with a command
  bound in front adds no information, so it is not restated;
- the other three parts are **not** free. `sitesInRange`, `pathsDistinct` and
  `demotionsOriented` are decidable predicates that `WfPlan.mapAt` re-establishes
  by computation on the post-state of every command — the `lift` pattern, at the
  plan level;
- `mapAt_ok_of_inRange` and `cmdMove_succeeds` are the proofs that the commands
  can discharge them, so the check is a proof obligation and not a trapdoor that
  turns legitimate commands into errors. Every hypothesis in both is
  load-bearing;
- `mapAt_rejects_unoriented` and
  `demote_into_a_horizon_that_does_not_follow_is_rejected` are the proofs that it
  *bites*: a command that would leave a demotion the loader could not orient
  errors, and nothing is written. Both directions matter — a check nothing can
  fail is decoration, and a check a legitimate command fails is a trapdoor;
- `transform_closed` states closure at the type where it is a real claim: over a
  bare `PlanCore`, with the refinement forgotten, which is what a host would
  hold if the kernel returned a record instead of a subtype.

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
  back identically, on `CanonicalItem`, which is decidable.
- `setEst_canonical` and `setEst_line_reparses` — **the setters preserve
  `CanonicalItem`**, so round trip B chains across an edit. This was a stated
  gap and it was not a missing proof, it was a bug: `- [ ]^m1` is a line the
  parser accepts whose id token carries no separator, and one `tm edit est=`
  produced `- [ ] est:45m^m1`, in which `est:45m^m1` is a single word and the
  line has no id token at all. `insertBeforeId` now hands the id token the space
  when it has none of its own.
- `load_render_line` — **the line round trip through the pipeline the FFI
  actually runs**: parse the bytes, build the entity, ask `glyphAt` for the box,
  serialise, and get the same bytes. The `[-]` regression is a counterexample to
  *this* statement and not to `serialize_parse`, which is exactly why it
  survived a package with a round-trip theorem in it.
- `paired_renders_each_placement` — and for the two-line form a `demote` writes,
  each site renders the box that was in the file at that site. The kernel can
  now read back its own output; the first loader rejected two lines of one id
  outright.
- `paired_placement_renders_back` — **and it reads it back as one entity, not as
  whichever of two the argument order happened to reach first.** The orientation
  is `orientPair a b`, symmetric in its arguments (`orientPair_comm`), so the
  conclusion names the tombstone instead of offering a disjunction over the two
  ways the pair could be read — which is what this theorem's conclusion used to
  be, and was the honest shape for a loader that decided by list order.
  `pairedEntity_order_independent` is the same claim about the loader step
  itself, and `unordered_horizons_are_rejected` is what happens when the two
  documents do not settle it.
- `scanLines_prose` — every prose line of an accepted document failed to parse
  **because it is not an item line**, not because it is a broken one. A line
  with an item's shape that does not parse is now an `LErr.badLine`, which was
  dead code before: `- [Z] x ^a1` and `- [ ] two ^a1 ^a2` were accepted, kept
  and written back.
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
| `move` is invertible by moving it back | **P** | `move_back_restores` |
| the `move` *command* is invertible | **R** | `move_back_at_a_fresh_rank_is_not_the_inverse`, `move_out_and_back_is_not_the_inverse` |
| a move lands on a rank nothing else has | **P** | `freshRank_gt` |
| a destination that is not a document is refused | **P** | `move_to_a_document_that_does_not_exist_is_rejected` |
| a move whose destination exists and is ahead of the tombstone succeeds | **P** | `cmdMove_succeeds` |
| a demotion files work forward, or it does not happen | **P** | `demote_into_a_horizon_that_does_not_follow_is_rejected`, `mapAt_rejects_unoriented` |
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
- **`move` is invertible at the `Site` level and the *command* is not**, and the
  first version of this package got that backwards. It refuted invertibility
  against `moveTo ⟨e.live.doc, 0⟩` — rank 0, which nobody proposes — while
  `move_back_restores`, the inverse a reasonable person *would* propose, is
  provable in this same kernel. The claim is withdrawn and replaced by the two
  statements that are true: moving a line back to the site it came from restores
  it exactly, and the **command** cannot do that, because the wire form carries
  a document and not a rank and the rank is generated fresh
  (`freshRank_gt`). So `tm undo` must replay the log — for a reason, not by
  assertion.
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

### The item, and the rest of the plan-level tier

`Core` accounts for all twenty-two of §3.1's fields, in eighteen of its
own. Four are absent on purpose — `id` is
the store key, `horizon` is the file (`Site.doc`), `src` is `live` plus `line`,
and `est`/`est_original` are *views* of the token vector — and two more are
derived rather than stored: `series` is the section a placement sits in, and
§3.2's `effective_shape` is a fact about the parent. The rest are typed:
`ci : Option (Fin 6)`, `!k : Option (Fin 4)`, a four-constructor `Shape` over
`Fin 1440` clock times, `Recur` as **syntax** (a denotation is not
serialisable and §0 says the Markdown is the database), budgets as minutes,
tags as a `Nodup` subtype.

Widening the record costs nothing at the other two tiers, and that is the whole
reason the design is `Bool` + `Subtype`:
`wf_ignores_the_item_fields` sets all thirteen new fields at once and is `rfl`.

Five of them mean nothing until the whole plan is consulted, so they join the
third tier — one decidable checker, `itemsWf`, inside `planWf`, re-established
by computation on every command's post-state:

| check | §  | proved |
|---|---|---|
| `Normalized` — rank distinctness | 7.4 | `site_names_one_line`: a `(document, rank)` names one line, the positional dual of "an id names one item". `no_prose_line_shares_a_rank`: and no prose entry can shadow an item line in `weave` |
| `@parent` total | 3.1 | `parent_names_an_item` |
| `@parent` acyclic | 6.1 | `parentsAcyclic_sound` and `parentsAcyclic_complete`; `every_item_has_a_root`, `no_item_is_its_own_ancestor` |
| `after:` total | 5.5 | `dep_names_an_item` |
| `after:` acyclic | 5.5 | `afterAcyclic_sound` and `afterAcyclic_complete`; `no_deadlocked_set` |
| section discipline | 4.2 | `a_demoted_section_is_a_month_section`, `a_pinned_section_is_a_day_section`, `a_day_file_holds_only_pinned_items` |
| per-file-kind shapes | 4.3 | `month_items_are_outcomes`, `calendar_lines_are_intervals`, `routine_lines_are_open`, `routine_lines_have_a_window_or_after_done`, `optional_items_declare_a_duration` |

**Acyclicity over a finite domain, without Mathlib, is the substance**, and it
is done twice because the two relations have different shapes.

`parent` is a partial *function*, so its check is a bounded walk: climb
`|dom| + 1` links and you must have fallen off the top. Both directions are
proved, and the second is the one that says the bound is not a guess —
`parentsAcyclic_complete` takes a chain that survived `|dom| + 1` links,
observes that all `|dom| + 1` of its ids are ids of a `Nodup` domain of size
`|dom|`, and gets a repeat out of `List.Nodup.length_le_of_subset` (core, not
Mathlib). A repeat is a cycle (`chain_dup_gives_cycle`). So the checker rejects
nothing that is really acyclic, and `climb_reaches_a_root` says the walk stopped
because it ran out of *parents* and not out of fuel — which is what makes §3.2's
`root(item)` total.

`after:` is a *relation*, so its check is a peel: strike out every id that no
longer waits on anything still standing, `|dom|` times. The characterisation of
"cyclic" here is the standard finite one — a **deadlocked** set, non-empty, in
which every id waits on another id of the set — and with it both directions are
arithmetic rather than pigeonhole: `|r|` peels either clear the set or reach a
fixed point, because a peel that changes anything strictly shortens the list,
and a non-empty fixed point *is* a deadlocked set (`peelN_empty_or_fixed`,
`fixed_is_deadlocked`).

And both checks bite: `self_parent_is_rejected` and `self_dep_is_rejected`.

The cost is quadratic in the number of items — `|dom| + 1` walk steps per id,
`|dom|` peels over `|dom|` ids, and `Normalized` recomputes `PlanCore.lines`
once per document — and `mapAt` runs the whole of `planWf` after every command.
That is deliberate at this size (a personal planner is hundreds of items, and
the FFI round trip is 3.6 s from clean including linking the Lean runtime); if
it ever matters, the answer is the one the store already uses — a fast
implementation behind the same interface, with the proofs on the interface.

§4.2's **section is derived, not stored** — the last heading line at or before
the placement's rank — so it cannot disagree with the file and a move changes
it for free. §5.3's default `on_miss` is derived too, from one sentence (a
window is a chance that passes; anything with a date persists), and its four
table rows are `rfl`; rows 3 and 4 differ only in `recur` and give the same
answer, which is why the generator does not read `recur`.

§3.2's `effective_shape` is a function over the tree and is **one step, not a
closure** — the spec says *parent*, and
`effectiveShape_does_not_reach_the_grandparent` is the theorem that pins that
down so nobody has to read the code to find out which rule it is.

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

A request document carries `path`, `lines`, and — for a file that is a horizon
block — `grain` and `ix`. The **response carries the horizon back**, because a
demotion's two lines are told apart by the regions of their files: a response
that dropped them would be one the kernel could not read, which
`the_kernel_reads_back_what_it_writes` would catch. A document with no `grain` is
backlog, the absence of a bound; that is a legal document and only a *pair* of
lines across two such documents is refused.

Twenty-one Rust tests call the kernel through the shim: ten for the behaviour
the proofs carry, and eleven that are the audits' findings as the exact requests
that reproduced them. The one that matters:

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

1. **The plan-level round trip is evaluated, not proved — and this is the gap
   that hid a real bug, so be precise about where it now stops.** Proved:
   round trips A and B for a line (`serialize_parse`, `parse_serialize`), across
   an edit (`setEst_line_reparses`), over a whole file's prose/item split
   (`renderSplit_splitDoc`), and — new, and the direct answer to the `[-]`
   regression — **through the entity the loader builds**, for a line on its own
   (`load_render_line`) and for the two-line demotion form
   (`paired_renders_each_placement`). Not proved: that the *store*, rebuilt from
   a parse and read back out through `renderDocAt`, reproduces the same
   per-document line list. That step needs `sortByRank` to be the identity on an
   already-ordered list plus a permutation argument over the store's domain, and
   without Mathlib both are real work. It is checked by
   `the_kernel_reads_back_what_it_writes`, which demotes and then feeds the
   kernel's own output back in and asserts the bytes are identical.

2. **A lone `[-]` is rejected, not read; and so is a pair the documents do not
   order.** A demotion is two lines — the tombstone and the live line — and an
   entity with no archive placement has no configuration that renders `[-]`. So a
   `[-]` whose partner is missing (a hand-deleted week file, say) is
   `LErr.orphanDemotion` rather than a silent rewrite to `[ ]`, which is what it
   used to be. Today's `tm` accepts it and repairs it in
   `cli/items.rs::drop_stale_demotion`; in this design that repair belongs in the
   `Repair` array of the plan's §4.4, returned and never applied silently, and
   that is stage-2 work. The two-line form itself loads and round trips —
   provided the request says which horizon each file is. Two `[-]` lines in two
   documents with no declared region, or with the same one, are
   `LErr.ambiguousDemotion`: the kernel's own output is never in that state
   (`demotionsOriented` is part of `planWf`), so this is a diagnostic for a host
   that dropped the regions, and the same `Repair` argument applies to it.

   **Which is also a behaviour restriction, recorded rather than decided.** While
   a tombstone stands, the item's live line may only be moved to a horizon after
   the tombstone's — `readopt` consumes the tombstone and then the item can go
   anywhere. `tm` today allows `tm move ^id day` on a demoted item and leaves the
   stale `[-]` behind, which is the state `drop_stale_demotion` exists to repair.
   Refusing it is what makes the two-line form readable at all, so it is a
   consequence of the fix and not an independent choice; it is still a change a
   user has to assent to.

3. **`Core` carries §3.1's item fields now; the *parser* does not fill them
   in.** `ci`, `!k`, `@parent`, `scope`, `shape`, `recur`, `on-miss:`,
   `min:`/`max:`, `atomic`, `after:`, `loc:`, `buffer:` and `#tags` are fields
   with the types §3.1 gives them, and the plan-level tier that reads them is
   proved and joined into `planWf` (above). **What is missing is the other half
   of the pipe: `parseItem` still keeps every token verbatim and interprets
   none of them**, so every entity the loader builds has these fields at their
   defaults. Three consequences, all real:

   * a `@parent` or `after:` token in a file is not *read*, so parent totality
     and both acyclicity checks hold of everything the boundary can currently
     build. The theorems are about arbitrary `PlanCore`s and `mapAt`
     re-establishes them on every post-state, but no request can make them fire
     yet. They are proved, not exercised;
   * `routines.md`, `optional.md` and `calendar/*.md` are **rejected at load**
     with `{"err":{"itemCheck":"fileKindShape"}}`, because §4.3 says their lines
     carry a scope and a shape and the loader gives them neither. That is the
     honest price of putting §4.3 into the acceptance rule while the parser half
     is still to come; the alternative — a rule that the default values satisfy
     — would be a check that cannot fire, which is the defect class this kernel
     exists to remove. Month, week, day, backlog and out-of-layout paths load
     exactly as before;
   * §4.2's section discipline **is** live end to end, because a section is
     derived from the document's prose and the placement's rank rather than
     stored. An item under a day file's `## Log`, or a `# Pinned` heading in a
     month file, is `{"err":{"itemCheck":"sectionDiscipline"}}` today.

   Writing the token → field parser, and the setters that keep the token vector
   and the fields in step (each with its `view ∘ set = id` proof, as `setEst`
   has), is the next slice.

4. **No calendar arithmetic, and therefore no horizon-name resolution.** `Day`
   is a `Nat` and `index` is `d`, `d/7`, `d/30`. It is enough to *evaluate* the
   close rule, to prove the two disagreement theorems, and to prove that a close
   orders the two files of a demotion; it is not ISO week and civil month
   arithmetic. The week→month tie-break (`firstprinciples` proved week does not
   refine month) is not implemented.

   So `tm move ^id week` — turning the *word* into a file — is not done here: the
   wire form names a document and `resolveDest` turns that into a `Dest`. A
   previous version of `Cmd.lean` carried `DocRegion`, `findDoc`,
   `resolveHorizon` and `demoteTarget` for this, and **nothing called any of
   them**; a report of that version claimed they had become live, and that was
   wrong. They are deleted. Dead code that reads like a design decision is worse
   than no code, because it says a question has been settled that has not been,
   and wiring the toy calendar into the command path to make them live would have
   been a worse lie than leaving them. `HorizonRef` went with them, and what it
   said — backlog is the *absence* of a bound — is now said by `Doc.region`,
   which is a field the loader actually reads.

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

9. **`CanonicalItem` excludes a line with trailing whitespace**, because the
   tokenizer emits a final token with an empty word for it and `Tok.wf` requires
   words to be non-empty. Such lines parse, render and edit correctly — the FFI
   tests cover them — but `setEst_canonical` does not apply to them, so for that
   family the reparse after an edit is checked rather than proved. Widening
   `toksWf` to allow an empty word in the last position would close it and costs
   a re-proof of `tokenize_toks`.

10. **`sitesInRange` and `demotionsOriented` are checked at load rather than
    established by construction.** The loader takes document indices from
    `zipIdx` over the document list, so every site it builds is in range, and it
    takes each placement's region from the same document it takes the index from,
    so `orientPair` establishes the orientation for every entity it builds.
    Proving either needs the same `zipIdx` bound lemma. The boundary runs the
    decidable checks instead and returns structured errors, which is the same
    discipline as `Grain.ofNat?` — but they are checks, not constructions, and
    the difference is recorded.

11. **`Normalized` is preserved at run time, not by a theorem.** Because rank
    distinctness joined `planWf`, a move onto a rank another line of the
    destination already occupies is now refused — so `cmdMove_succeeds` and
    `mapAt_ok_of_inRange` each carry one more hypothesis, and both say so in
    their doc comments. At the boundary `applyCmd` always passes `freshRank`,
    which `freshRank_gt` proves is strictly greater than every rank in the
    destination; but the step from that to "and therefore `Normalized` still
    holds of the post-state" is **not written**. It needs a replacement lemma
    for `PlanCore.lines` under a single-entity update. Until it is, rank
    freshness rests on `mapAt`'s decidable re-check at run time rather than on
    a proof, and a command that collided would return `badHorizon` rather than
    corrupt anything.

12. **`series` has a name but no head.** `seriesOf` derives the
    `## series:<name>` a placement sits in. §5.4's *head* — "the first member
    that is not Done or Dropped is active, the rest are invisible to the
    planner" — and the implied `after:` a series section carries are planner
    concepts, and the planner is not here.

13. **`@parent` is an `Id`, not §3.1's `Ref`.** §3.1 says
    `parent: Option<Ref>` where a `Ref` is `@id` **or `@label`**. Label
    resolution needs a title index and a rule for ambiguity; the kernel takes
    ids only, and a boundary that accepted labels would have to resolve them
    before it built the store. `pref:` (`wake+10m` or a clock time) is not
    modelled either — it needs the day's `wake`, which is day-file front matter
    the kernel does not read.

14. **§6.2's "outcome with an estimate" warning is not checked.** `shapesWf`'s
    month rule is the shape half only (a month item's shape is `none`). The
    estimate half — "an item in `month/` with an estimate and no children is a
    `tm check` warning" — would refuse the two-line demotion form *this kernel
    writes*, because §6.3's close copies the line, estimate and all, into the
    month file, and `demote` here lands it at a fresh rank rather than inside
    `# Demoted`. Making it real needs `demote` to target a *section*, which is
    stage-4 close work. Recording it rather than weakening it.

15. **The proof-to-definition ratio here is not a forecast.** This fragment has
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
