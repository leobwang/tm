# `tm` kernel in Lean 4 — stage one

This is the first stage of the `rebuild-on-lean` kernel described in
`../PLAN-lean-kernel.md`. It is small on purpose. Everything it claims below
is compiled, and the acceptance script re-checks every claim in about four
seconds.

```
kernel/
  TmKernel/            Lean 4 package, no Mathlib, toolchain pinned to v4.33.1
    TmKernel/Cal.lean        the calendar: civil dates, ISO weeks, one tie-break
    TmKernel/Grain.lean      the horizon order, derived from one generator
    TmKernel/Text.lean       tokenizer, decimal numerals, the inverse lemmas
    TmKernel/Line.lean       the item line: parse, serialise, the est: view
    TmKernel/State.lean      entity vs observation; the id invariant, locally
    TmKernel/Plan.lean       the plan as one object; the invariant, globally
    TmKernel/Cmd.lean        five commands, each with its law proved or refuted
    TmKernel/Boundary.lean   String -> String; one @[export]
    Check.lean               axiom audit, one line per theorem
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
  which is what the FFI renders from, and
  `the_kernel_reads_back_what_it_writes` now covers the whole document: read a
  request, file its lines under their ids, render every document back, and the
  bytes are the bytes that came in;
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

Negative.lean:71:51: error: Application type mismatch: The argument
  rfl
has type
  ?m.11 = ?m.11
but is expected to have type
  itemsWf { docs := planDocs, store := store } = true
in the application
  planWf_of_parts h1 h2 h3 ?m.9 rfl

Negative.lean:251:2: error: Type mismatch
  sorted_ext_by_key fun x => x.fst
has type
  ∀ (l₁ l₂ : List (Nat × List Char)),
    List.Pairwise (fun a b => a.fst < b.fst) l₁ → …
but is expected to have type
  ∀ (l₁ l₂ : List (Nat × List Char)),
    List.Pairwise (fun a b => a.fst ≤ b.fst) l₁ → …
                     -- `<` is not `≤`: rank distinctness is what the plan-level
                     -- round trip needs, and this is the type error that says so
EXIT=1
```

Every cheat, one compile error:

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
| 16 | form the quotient `u = need/avail` in `Nat`, which is integer division | `3/4` reaches the `1/2` edge and `3/4 = 0` reaches nothing; `utilGe` cross-multiplies and never divides |
| 17 | round a ratio whose denominator nobody checked | `n / 0` is `0` in Lean, so §8.1's budget with `block_min = 0` would be a silent wrong answer; a rounding site takes a `Pos` |
| 18 | round the safety margin down, as `priority.rs:349` does | a margin rounded down stops being a margin; R1's rule is a ceiling and `needMin_covers` is why |
| 19 | derive §7.1's bin edges instead of tabulating them | three of four are halvings, so `1/2^i` looks generative; it disagrees with the spec at every `u` in `[0.1, 0.125)` |
| 20 | guard the division by zero, as `is_finite()` does | §7.1 says capacity zero makes `u = ∞`, so it reaches every edge; the guard inverts the rule exactly where the item cannot be finished |
| 21 | hand a date through as valid, which is how `Feb 30` reaches a calendar | `ValidDate` is a `Subtype` over a *decidable* predicate, and `Date.valid ⟨2024,2,30⟩` computes to `false` |
| 22 | number weeks inside the civil year — "week 1 starts January 1st" — and call it the ISO week | at 2027-01-01 the naive rule says week 1 and ISO says 2026-W53 |
| 23 | name a week's month without naming a tie-break, by assuming the week determines it | the rewrite has nothing to rewrite; `week_does_not_refine_month` is the counterexample |
| 24 | declare `horizon.rs:1543`'s "month of today" stable | the same week files into August or September depending on the day you run it |
| 25 | drop the century rule and keep "every fourth year" | refuted by computation at y = 100 |
| 26 | get the phase of the seven-day cycle wrong by one | the three weekday cross-checks exist for this and they fire |
| 27 | "the store hands its lines back in rank order, so the sort is a formality" | `decide` refutes it on a two-element list; the store enumerates its domain, not the file |
| 28 | drop rank distinctness from the round trip and keep the conclusion | `sorted_ext_by_key` needs a **strict** order; with `≤`, two lines at one rank are two files with the same members |
| 29 | read a file back without asking whether ranks are distinct | `renderDocAt_loadCore` takes `normalized`; without it, which of two lines at one rank comes first depends on the order the host listed its documents |
| 30 | relocate to rank 0 rather than `freshRank` | `move_at_freshRank_normalized` is about `freshRank` and nothing else; rank 0 is exactly the collision `Normalized` forbids |
| 31 | check a rank is free by looking only at the item lines | a document's ranks are its prose ranks **and** its item ranks in one list (`weave` orders them against each other), so `SitesFree` has two clauses |

## What is proved

Every theorem across nine modules. `Check.lean`'s axiom audit covers all of them
and shows only `propext` / `Classical.choice` / `Quot.sound`, **never
`sorryAx`**; a handful depend on no axioms at all. (`check.sh` prints the count
it actually audited, so the number is in the run and not in this file.)

The audit covers all of them, across all nine modules.


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

  These two were written against the toy index, and they **survive the real
  calendar unchanged** — days 6 and 7 of the kernel's epoch are a Sunday and
  the Monday after it (`epoch_day_6_is_a_sunday`), which is the case the
  finding names. They are now also stated on a date a reader can check
  (`impl_day_rule_disagrees_2026`: Sunday 2026-09-06 closed on Monday
  2026-09-07) and, more to the point, **generalised**:
  `impl_rule_disagrees_iff` and `containing_targets_a_closed_region_iff` say
  the two rules differ, and the Rust's target is already closed, **exactly**
  when the coarser period rolled over in between. So the finding is about
  closing late, not about one witness.
- `demotion_target_follows_the_closed_region` — and the close rule *orders* the
  two files of a demotion: the tombstone's region comes strictly before the one
  the work was filed into, in `horizonPrecedes` (lex on grain then block, with
  backlog last because nothing closes backlog). Below month the grain settles it;
  at month it is `Closed` that does, which is why the fixed point needs the
  hypothesis and the other two rows do not. This is the fact the loader inverts,
  and `horizonPrecedes_asymm` is why the inversion has exactly one answer.

`Check.lean` prints §6.3's three rows generated from one rule at three grains:
`(week 35, month 8, month 8)` — the same three values the toy index printed,
now for the right reason (day 250 of the epoch is 0001-09-08, whose ISO week
ordinal is 35 and whose month ordinal is 8).

### The calendar

`Cal.lean` replaces the toy index. A `Day` is days since **0001-01-01**
proleptic Gregorian, which is a Monday — so `n % 7` is the weekday and `n / 7`
is the ISO week ordinal, with no offset constant.

- `toDay_ofDay` and `ofDay_toDay` — **the load-bearing theorem**: civil date and
  day number are mutually inverse, on every valid date and every `Nat`. Nothing
  else in the module would be trustworthy without it. `ofDay_valid` says every
  `Day` lands on a *valid* date, so there is no partial accessor and no default.
- `ys_step` — the year table advances by exactly `yearLen`, which is where the
  leap rule and the day count are tied together. Inverting it is one guess and
  one correction (`yoe_bracket`), not a search: within a 400-year era a year
  start is never more than 97 days past `365 * k`.
- the month table is **data** (§4.1's carve-out) and everything derived from it
  is checked exhaustively by `decide` — 731 days and 416 (month, day) pairs.
- `dayOfIso_isoOf` / `isoOf_dayOfIso` — ISO week dates are a faithful coordinate
  system: `2026-W37-1` names one day and no other. `iso_2026_09_07` is the
  spec's own file name, checked.
- `isoWeeksIn_52_or_53`, and `isoWeeksIn_53_iff` — a year has 52 or 53 ISO
  weeks, and it has 53 **iff** it starts on a Thursday or is a leap year
  starting on a Wednesday. The classic rule, derived rather than tabulated.
  `iso_2027_01_01 = 2026-W53-5` and `iso_2025_12_29 = 2026-W01-1` are the
  neighbouring-ISO-year cases a naive implementation gets wrong.
- the weekday phase is the **one datum that is not derived** — the seven-day
  cycle's period is arithmetic but its phase is a fact about the world. It
  enters through the definition of `weekdayOf` and is cross-checked against
  1970-01-01 (Thursday), 2000-01-01 (Saturday) and 2026-09-07 (Monday).

### The week → month tie-break, which is a choice

`week_does_not_refine_month` — an ISO week can straddle two civil months
(2026-W36 runs Aug 31 to Sep 6), so the `day ⊂ week ⊂ month` chain is
containment at its first step and coarsening only at its second, and naming a
week's month is a **choice**.

**Chosen:** `monthOfIsoWeek w` is the civil month containing week `w`'s
Thursday — total, monotone, a month the week actually meets
(`monthOfIsoWeek_is_met`), and a function of `w` alone. Its stability is
*structural*: `now` is not in the type.

**Rejected:** "the month of today", which is what `horizon.rs:1543` does. It is
written down as `monthOfWeekByToday`, whose week argument is unused, and
`monthOfWeekByToday_is_not_stable` files one week into two different months
depending on the day the command runs. A file name that depends on when you
looked is not a file name.

`closeTo_week_is_not_monthOfWeek` keeps the two apart: `closeTo week now` files
into the month containing `now`, which is right because a close happens at a
time; the tie-break names the month a week *belongs* to, which must not depend
on when you asked. They are different functions and they differ.

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
- `the_kernel_reads_back_what_it_writes` — **round trip over a whole
  *request*, which is the step that used to be a test.** For every document of
  every request `loadPlan` accepts, taking the file apart into prose and
  entities, filing the entities under their ids, and reading them back out
  through `renderDocAt` reproduces the input lines. The detour that had to be
  survived is the store: it enumerates its **domain**, not the file, so the
  lines come back in an order that has nothing to do with the document, and
  something has to put them in order without *choosing*. Four theorems do it —
  `loadCore_lines_mem` (the plan's line list is exactly the request's item
  lines, so the enumeration order drops out), `buildEntity_renders` (the entity
  an id's lines build renders exactly those lines, which is `load_render_line`
  and `paired_renders_each_placement` lifted from "the bytes agree" to "the list
  agrees"), `sortByRank_id`/`sortByRank_strict`, and `sorted_ext_by_key` (a
  strictly rank-ordered list is determined by its members). **Rank distinctness
  is what makes the last one available**, which is `Normalized` earning its
  place in `planWf`.
- `runPlan_renders_the_input` — the same statement at the exact call site, for
  every `(document, index)` pair `runPlan` hands to `renderDocAt`, and
  `loadPlan_docs` says the response has one entry per request document in the
  request's order. `the_round_trip_is_not_vacuous` decides that a concrete
  two-document request does load, so the hypothesis is not empty.
- `a_command_rewrites_only_the_files_it_touches` — and the other leg: a command
  re-renders every document, so `demote` in `week/` rewrites `month/` and
  `backlog.md` too. A file neither the old nor the new entity has a line in
  comes back byte-identical. `lines_set` — the replacement lemma for
  `PlanCore.lines` under a single-entity update — is what says so, and it is the
  same lemma `Normalized` preservation needs.
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
| `Normalized` — rank distinctness | 7.4 | `site_names_one_line`: a `(document, rank)` names one line, the positional dual of "an id names one item". `no_prose_line_shares_a_rank`: and no prose entry can shadow an item line in `weave`. `normalized_set`: and a command that lands on free sites preserves it — `lines_set` is the replacement lemma it rests on, and `move_at_freshRank_normalized` and its four siblings discharge it for the five commands |
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

1. **The plan-level round trip is proved now — and what is left is the JSON
   edge, which is gap 6.** Proved: round trips A and B for a line
   (`serialize_parse`, `parse_serialize`), across an edit
   (`setEst_line_reparses`), over a whole file's prose/item split
   (`renderSplit_splitDoc`), through the entity the loader builds
   (`load_render_line`, `paired_renders_each_placement`), and — this is the step
   that used to be a test — over a whole **request**: the store, rebuilt from a
   parse and read back out through `renderDocAt`, reproduces the same
   per-document line list (`the_kernel_reads_back_what_it_writes`,
   `runPlan_renders_the_input`). `sortByRank` is the identity on an
   already-ordered list (`sortByRank_id`), strict on a rank-distinct one
   (`sortByRank_strict`), and a strictly ordered list is determined by its
   members (`sorted_ext_by_key`), so the store's enumeration order does not
   reach the bytes.

   `the_kernel_reads_back_what_it_writes` (the Rust test) is therefore now a
   consequence rather than the evidence: the test's second call carries no
   commands, so its output is the round trip of its input, which is the first
   call's output.

   **What text can still reach the kernel that no theorem covers**, stated
   exactly:

   * **the JSON/string edge**, both directions. The theorems begin at `ReqDoc`
     (a `List (List Char)`) and end at `renderDocAt`'s `List (List Char)`.
     `Json.parse`, `Json.compress`, `String.toList` and `String.ofList` are
     between that and the wire and none of them is proved here; nor is splitting
     a file's bytes on newlines and joining them again, which is the host's job.
     That is gap 6, and it is now the *only* unproved step on the text path. In
     particular a request line containing a literal newline round trips as one
     line here and becomes two lines on disk, and nothing in the kernel notices;
   * **requests the loader rejects.** Every theorem here is conditioned on
     `loadPlan docs = .ok p`. `badLine`, `dupId`, `splitLine`, `notADemotion`,
     `orphanDemotion`, `ambiguousDemotion`, `duplicatePath`, `siteOutOfRange`
     and the seven `itemCheck` faults are covered by their own theorems
     (`scanLines_prose`, `unordered_horizons_are_rejected`,
     `a_shapeless_calendar_line_is_rejected`, …) but not by the round trip, which
     says nothing about them and should not;
   * **the post-command render, except for the files the command did not
     touch.** `a_command_rewrites_only_the_files_it_touches` covers the
     untouched documents; what a `move` or `demote` does to the *destination*
     file's byte order is not stated beyond "the rank is fresh, so the line goes
     last". Stability — a command changes as little as possible — is a
     stage-5 relational law and is not attempted;
   * **`Normalized` for a loaded plan is still a load-time check.** It is true by
     construction (`splitDoc` hands each line index to exactly one of prose and
     items) but it is not proved that way; `loadPlan` runs the decidable check
     instead, which is the same discipline — and the same recorded gap — as
     `sitesInRange` and `demotionsOriented` in gap 10.

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

4. **The calendar is real now; horizon *names* are still not.** `Cal.lean`
   gives proleptic Gregorian civil dates with a proved round trip, ISO 8601 week
   dates with the week-numbering year, the civil month ordinal, and the
   week→month tie-break (the month of the week's Thursday) named as a choice
   with the alternative it rejects. `Grain.index` is those three functions, not
   `d`, `d/7`, `d/30`. What is **still missing**, and it is what "horizon-name
   resolution" actually needs:

   - **no rendering or parsing of file names.** The kernel can say that
     2026-09-07 is `2026-W37-1` as a triple of numbers; it cannot produce or read
     the string `week/2026-W37.md`. So `tm move ^id week` — turning the *word*
     into a file — is still not done here, and the wire form still names a
     document that `resolveDest` turns into a `Dest`. This is a small amount of
     work (a decimal renderer and its inverse already exist in `Text.lean`) but
     it is work, and claiming the calendar closes it would be false;
   - **nothing ties a `Doc`'s declared `Region` to its `path`.** A host may still
     send `{"path":"week/2026-W37.md","grain":1,"ix":35}` and the kernel will
     believe it; the true ISO week ordinal of 2026-W37 is 105695. The FFI
     fixtures do exactly this. Nothing in the kernel depends on the value — the
     horizon order compares grains first — but the correspondence is unchecked,
     and it is the obvious place for the next boundary bug;
   - **days only: no time of day, no time zone.** §4.1's `due:2026-09-11T23:59`,
     `at:`, and the tree's `tz` have nowhere to live. Stages 5 and 6 need them;
   - **no `Int`**: a `Day` is a `Nat` from 0001-01-01, so dates before that year
     are unrepresentable. That is deliberate (it is what makes `ofDay` total and
     the ISO week ordinal `n / 7` with no offset) and it costs nothing a planner
     wants, but it is a restriction and not an oversight.

   A note for whoever writes the next proof here: `omega` does **not** see
   through the `Day` abbreviation when `Day` is the type argument of `=` or `≤`,
   so every day-valued *result* type in `Cal.lean` is written `Nat`. Getting
   this wrong produces "omega could not prove the goal" on statements that are
   arithmetically trivial, which costs an hour to diagnose.

5. **No `close`, no `autoClose`, no `ClosePolicy`, no planner, no priority, no
   recurrence, no exact-arithmetic layer.** L16–L27 of the architecture are not
   here. In particular the two relational laws — tail-drop and stability — are
   not attempted, and the recommendation in the plan stands: keep the existing
   882-line proptest, state the laws in Lean, and prove them last or never.

6. **The line-splitting at the very edge is unverified**, and since gap 1
   closed it is the *only* unproved step on the text path. The kernel's document
   round trip is over `List (List Char)`. Splitting a file's bytes on newlines
   and joining them again happens in JSON at the boundary, and
   `String.intercalate "\n" (s.splitOn "\n") = s` is not a core theorem.
   `Json.parse`/`Json.compress` and `String.toList`/`String.ofList` are in the
   same position. A request line containing a literal newline round trips as one
   line inside the kernel and becomes two lines on disk.

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

10. **`sitesInRange`, `demotionsOriented` and `Normalized` are checked at load
    rather than established by construction.** The loader takes document indices
    from `placementsOf`'s counter, so every site it builds is in range; it takes
    each placement's region from the same document it takes the index from, so
    `orientPair` establishes the orientation for every entity it builds; and
    `splitDoc` hands each line index to exactly one of prose and items, so ranks
    within a document are distinct. All three are therefore true of every plan
    the loader builds, and none of the three is *proved* that way. The boundary
    runs the decidable checks instead and returns structured errors, which is
    the same discipline as `Grain.ofNat?` — but they are checks, not
    constructions, and the difference is recorded. (`mem_placementsOf` is now the
    lemma the first two would be built from; the third would additionally need
    `PlanCore.lines` of a loaded plan to be `Nodup`, which
    `loadCore_lines_mem` gives as a membership statement and not as a list.)

11. **`Normalized` after a command is a theorem now; the six other item-level
    conjuncts are not, and should not be.** `normalized_set` (Plan.lean) is the
    preservation proof: a single-entity update onto sites nothing else occupies
    — no other line of the plan, no prose line of that document — leaves the plan
    `Normalized`. It rests on `lines_set`, the replacement lemma README's
    previous version said was missing: the store's domain does not move, so the
    plan's line list is the old one with exactly that entity's lines swapped out
    in place.

    At the boundary, `normalized_of_fresh_or_old` reduces the obligation to one
    hypothesis every command satisfies — each line of the new entity is either on
    `freshRank` in the destination or on a site the entity already had — and
    `move_at_freshRank_normalized`, `demote_at_freshRank_normalized`,
    `readopt_at_freshRank_normalized`, `drop_normalized` and `setEst_normalized`
    discharge it for the five. `docProseMax_ge` is the other half of the
    arithmetic: `freshRank_gt` beats every *line* rank in the destination, and
    this beats every *prose* rank, which matters because `Normalized` counts both
    in one list.

    `applyCmd_move_succeeds` is `cmdMove_succeeds` with the rank hypothesis
    gone: what is left is `itemsWfButRanks`, the six conjuncts a move can
    genuinely violate — a move into a day file outside `# Pinned` breaks
    `sectionsWf`, a move into `month/` can break `shapesWf`. Those are real
    refusals, not gaps.

    **What is left**: `cmdMove_succeeds` and `mapAt_ok_of_inRange` in Cmd.lean
    still take the full `itemsWf` hypothesis. Weakening them to
    `itemsWfButRanks` is now a mechanical change and is not made here only
    because Cmd.lean was outside this change's scope.

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

<!-- ===================================================================
     THE EXACT-ARITHMETIC LAYER (`TmKernel/Arith.lean`), added on its own
     branch.  Appended as a block so the three stage-one branches merge.
     =================================================================== -->

## The exact-arithmetic layer (`TmKernel/Arith.lean`)

1,078 lines, 91 theorems, no `Float`, no fixed point, no `Rat`. §7 and §8 are
written in decimals; every one of those decimals is a *comparison*, and a
comparison of ratios cross-multiplies into `Nat`. `u = need/avail` is never
formed: `u ≥ p/q` is `q·need ≥ p·avail`, and a scale constant folds into the
same product, so §7.1's safety-1.3 test against an edge is
`13·rem·q ≥ 10·avail·p` — three multiplications and one `≤`.

What is proved: `Q.le` (cross-multiplication) is reflexive, transitive on
ratios that denote something, antisymmetric up to value, total, a **congruence**
for `n/d ≈ (k·n)/(k·d)` — which is what licenses folding a constant in — and,
on ratios that are whole numbers, literally the `Nat` order. The
implementation-side tests then agree with the order on the formed ratio
(`utilGe_eq_le`, `utilScaledGe_eq_le`), unconditionally, `avail = 0` included.
The bin ladder is a count of missed edges, hence antitone for any edge list at
all; on §16's shipped edges it is §7.1's `bin(u)` exactly — the five half-open
intervals, derived rather than sampled. Rounding is three named rules
(`floorQ`, `ceilQ`, `halfUpQ`), each with its adjunction, its monotonicity, and
a proof that it is within one minute of the exact value; R1, R2, R4 and R5 are
built on them and R3 is eliminated by typing the window in minutes.

Gap 5 above says "no exact-arithmetic layer"; that clause is superseded. The
rest of gap 5 — no `close`, no `ClosePolicy`, no planner, no priority, no
recurrence, and tail-drop and stability unattempted — still stands.

### What it does **not** cover

12. **`Check.lean` does not audit these 91 theorems.** The file is outside this
    branch's scope, so the acceptance run's "axiom audit (70 theorems)" is the
    pre-existing list. The audit was run by hand over all 91 and every one
    depends only on `propext` / `Quot.sound` / `Classical.choice`; ten depend on
    no axioms at all. Whoever merges the three stage-one branches should append
    the `Arith` names to `Check.lean` so CI covers them too.

13. **`0/0` is a decision, not a derivation.** §7.1 says "capacity 0 → `u = ∞`",
    with no exception for zero need, so `utilGe 0 0 e` is `true` and an item
    with nothing left to do and no capacity comes out HOT. An `f64`
    implementation gets `NaN` there, every comparison is false, and it falls off
    the ladder into the *lowest* bin — `+3`. The two disagree, both are
    defensible, and this is the kind of "bug versus undocumented deliberate
    choice" that reading cannot settle. `utilDefined` is the guard; the kernel
    takes the spec's sentence literally and says so
    (`util_zero_over_zero_is_undefined`, `util_zero_over_zero_is_hot`).

14. **R7 is open.** §8.4's future-day capacity mixes the lounge and home
    capacities by `p_lounge`, which is a rational weight over two integer
    minute-counts. Nothing in this layer rounds it; whether the planner floors
    the mixture per level, per day, or carries it exact into the EDF pass is a
    decision the planner has to make and state, and it is not made here.

15. **`ladder_eq_rungs` needs the edges sorted; `rungs_antitone` does not.**
    That asymmetry is deliberate — antitonicity is the property the list
    actually supports — but it means a misconfigured `priority.bins` (not
    descending) still produces a well-defined, antitone bin that is *not* the
    ladder §7.1 describes. There is no `planWf` clause rejecting such a config,
    because config validation lives at the boundary and the boundary is not this
    branch's file. `binsWf` and `descending` are the two decidable predicates a
    loader should run.

16. **The energy posterior is arithmetic here, not statistics.** `ramp`,
    `posteriorNum` and `energyAfter` implement §8.5's *correction*, exactly and
    over `Int`. Fitting the model, `exp(−age/decay)`, the shrinkage means and
    `p_lounge` stay in Rust, as §3.6 says. `energyAfter` also has no monotonicity
    theorem in `δ`: it is a clamp composed with a rounding, both monotone, but
    the composition was not needed by anything yet and was not proved.

17. **Nothing consumes this layer.** Priority and the planner are stages 5 and 6.
    `needMin`, `budgetBlocks`, `plannedMin` and `energyAfter` are the four sites
    §7 and §8 will call; until they exist, the parity harness against the Rust
    `f64` path (§3.5's 0/2,251,500 and 135/150,600 measurements) cannot be re-run
    against *this* code, and those numbers are quoted from the spike, not
    reproduced here.
