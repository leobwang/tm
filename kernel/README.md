# `tm` kernel in Lean 4 — stage one

This is the first stage of the `rebuild-on-lean` kernel described in
`../PLAN-lean-kernel.md`. It is small on purpose. Everything it claims below
is compiled, and the acceptance script re-checks every claim in about a
second.

```
kernel/
  TmKernel/            Lean 4 package, no Mathlib, toolchain pinned to v4.33.1
    TmKernel/Cal.lean        the calendar: civil dates, ISO weeks, one tie-break
    TmKernel/Grain.lean      the horizon order, derived from one generator
    TmKernel/Text.lean       tokenizer, numerals (padded and bare), splitting
    TmKernel/Line.lean       the item line and the whole of §4.1's field grammar
    TmKernel/State.lean      entity vs observation; §3.1's fields, as views
    TmKernel/Plan.lean       the plan as one object; the invariant, globally
    TmKernel/Cmd.lean        five commands, each with its law proved or refuted
    TmKernel/Boundary.lean   String -> String; one @[export]
    Check.lean               axiom audit, one line per theorem
    Negative.lean            MUST FAIL to compile — the demonstration
    Goals.lean               stages 3-6 as unproved statements; imported by nothing
  tm-kernel-ffi/       Rust: the C shim, build.rs, and 32 tests that call Lean
  check.sh             stage-one acceptance
  totality.py          the kernel must be total; this enforces it
```

## Build and check

```bash
./check.sh                     # everything below, ~1.1 s warm
```

or by hand:

```bash
cd TmKernel && ~/.elan/bin/lake build TmKernel:static
LEAN_PATH=.lake/build/lib/lean ~/.elan/bin/lean Check.lean     # axiom audit
LEAN_PATH=.lake/build/lib/lean ~/.elan/bin/lean Negative.lean   # MUST print errors
LEAN_PATH=.lake/build/lib/lean ~/.elan/bin/lean Goals.lean      # `sorry` warnings, no errors
cd ../tm-kernel-ffi && cargo test                               # Rust -> C -> Lean
```

Measured on an M-series Mac: `lake build TmKernel:static` from clean **1.6 s**;
`cargo test` from clean, driving lake and linking the Lean runtime, **3.6 s**;
the linkable archive is **1.7 MB** (1,759,720 bytes at `c8f3a38`).

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
        line := __src.line, parent := __src.parent }) = true

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

Negative.lean:453:34: error: Application type mismatch: The argument
  arch
has type
  Site
but is expected to have type
  Tomb                            -- a tombstone with no bytes is not a value

Negative.lean:459:0: error: Not a definitional equality: the left-hand side
  glyphAt { live := live, archive := some { site := arch, line := a },
            status := Status.live Holder.free, line := l } live
is not definitionally equal to the right-hand side
  Glyph.demoted                   -- a reopened record is `[ ]`, not `[-]`

Negative.lean:473:2: error: Type mismatch
  the_tombstone_is_behind_the_live_line p i e r hget harch
has type
  glyphOfStatus e.val.status = Glyph.demoted ->
    horizonPrecedes (docRegion p.val r.doc) (docRegion p.val e.val.live.doc) = true
but is expected to have type
  horizonPrecedes (docRegion p.val r.doc) (docRegion p.val e.val.live.doc) = true

Negative.lean:75:51: error: Application type mismatch: The argument
  rfl
has type
  ?m.11 = ?m.11
but is expected to have type
  itemsWf { docs := planDocs, store := store } = true
in the application
  planWf_of_parts h1 h2 h3 ?m.9 rfl

Negative.lean:306:2: error: Type mismatch
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
| 7 | *withdrawn* — it said a record beside a standing tombstone may not be `[ ]`, and §6.3's `readopt` produces exactly that | it refused a shape the spec writes; replaced by 36–42, and the withdrawal is recorded in `Negative.lean` where the cheat was |
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
| 36 | a tombstone that is a placement and nothing else | `Core.archive` is a `Tomb` — a site **and** the bytes standing there — so "an archive with no text" is not a value |
| 37 | force `[-]` on the record whenever a tombstone stands, which is what made §4.3's fixture unreadable | the box at a live site is the status and nothing else (`glyphAt_live`); a reopened record is `[ ]` |
| 38 | demand the horizon order of *every* demotion pair, not only the ones whose boxes tie | `the_tombstone_is_behind_the_live_line` now carries the glyph hypothesis, and without it the statement is false of §4.3's own pair |
| 39 | refuse a pair whose two lines differ, which is what `LErr.splitLine` said | §6.3's close writes them differently on purpose; the constructor is gone |
| 40 | `demote` that writes one token vector to both sites, so the stamp reaches the week file too | the tombstone is `⟨e.live, e.line⟩` and the record's line is the stamped one; they are not equal |
| 41 | `readopt` that reopens anything, which loses the `est:` and the stamp the tombstone carries | §6.3 reopens a *demoted line*; `readopt` returns an `Except` and answers `notDemoted` |
| 42 | assume a second `demote` can succeed — the assumption the withdrawn `demote_not_idem` rested on | §6.3 gives an item one archive record and the month close *moves* it; the composite is `alreadyDemoted` |
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
| 43 | insert an item over a standing one — hand `Store.insertFresh` the proof that the id is *taken* | `insertFresh` demands `(get i).isNone = true`, the dual of `Store.set`'s `isSome`, and there is no third door that takes neither proof; freshness for `add` is L21's theorem, not a runtime retry |

## What is proved

Every theorem across nine modules. `Check.lean`'s axiom audit names every one of them and shows only `propext` / `Classical.choice` / `Quot.sound`, **never
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

### Which line of a demotion pair is the tombstone, which is a choice

§6.3 marks the archive record twice and the two marks can disagree, so the
kernel has to say which one governs. **Chosen: the box first, the files
second.**

* **The box.** §6.3's week close marks the week line `[-]` and files a `[-]`
  copy into `month/<current>#Demoted`. The only thing that reopens a box is
  `tm readopt` ("`[-]` → `[ ]`, stamp kept"), and what it reopens is the
  record. So a line that is not `[-]` is never an archive copy, whichever file
  it is in.
* **The files.** The record goes to `closeTo`, which is strictly after the
  region that was closed (`demotion_target_follows_the_closed_region`).

They agree wherever both speak, and each is silent where the other is not. The
box is silent straight after a close, when both lines read `[-]`. The files are
silent — and *wrong* — on the readopted pair, which leaves the reopened record
in a **week** and the standing archive in a **month**: §4.3's own fixture,
which `check_fixtures.rs` asserts `tm` reports with zero problems. There the
file order names the week line as the tombstone and the week line reads `[ ]`.

**Why that order and not the other**, from §3.1 rather than from either
implementation: `state` is a **stored** field of an item and `horizon` is
"derived from file path". A derived fact may break a tie the stored one leaves;
it may not overrule it. §6.3 supplies both the stored mark and the tie-break,
and using them in that order is the only reading that accepts every pair the
lifecycle writes.

`tree.rs`'s `record_rank` — `(is_archive_copy, ↓stamps, ¬in_month_demoted)`,
smallest wins — has the same shape, and the kernel reaches it from §6.3 rather
than from the Rust. The one difference: where the Rust breaks a tie among
archive copies by **stamp count**, the kernel breaks it by **horizon**. They
agree on every pair §6.3 writes, because the close appends `demoted:` to the
copy it files forward and to nothing else, so the record always has strictly
more stamps *and* sits in the later region; the horizon is the one of the two
the kernel can also *check* on a command's post-state
(`demotion_target_follows_the_closed_region`), which is what makes
`demotionsOriented` a proof obligation rather than a heuristic.

**Rejected: horizon order alone**, which is what this package did until now. It
was proved correct for the case both lines render `[-]` and it is wrong on the
other one; the kernel picked the week line as the tombstone, saw `[ ]`, and
returned `notADemotion`. Three of the five fixture trees failed to load whole
because of it.

**What the choice costs.** `demotionsOriented` is weaker: it demands the
horizon order only when the record's own box is `[-]`. It still bites —
`demote` writes a `[-]` record, so every demotion a close performs discharges
it, and `demote_into_a_horizon_that_does_not_follow_is_rejected` and
`mapAt_rejects_unoriented` are the proofs — and what it stopped demanding is a
condition no reader ever needed. Both halves are `decide`d over one plan:
`a_backwards_demotion_is_refused` (a `[-]` record with its tombstone in a later
horizon is not a plan) and `a_reopened_record_needs_no_horizon` (reopen the
same record and it is). Relax the conjunct to `true` and the first fails;
restore the unconditional demand and the second fails. One recorded behaviour restriction goes with
it: while a tombstone stands, a **reopened** live line may now be moved
anywhere, because its box says which line it is. A live line that is still
`[-]` may not, and that is the case the check exists for.

### Entity versus observation

An id names an entity; a line is an observation of it at a site. The glyph is a
function of placement **and** status: on the live line of a half-finished
demotion `[-]` is positional, and standing alone it is a state — §6.3's archive
copy, which `tm close month` leaves in a `# Demoted` section with no partner in
the file set. Six states, not five; the fifth-versus-sixth question was decided
by the corpus, which refused every `# Demoted` section in the fixture trees
(gap 2).

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
- `glyphAt_statusOfGlyph`, `glyphAt_statusOfGlyph_paired`,
  `every_glyph_has_a_state`, `a_lone_demotion_renders_back` — `glyphAt` is the
  only writer of a state box, and these are its **inverse**: the entity a loader
  builds from a glyph renders that same glyph back. The inverse is `statusOfGlyph`
  and it is **total, paired or not**: `glyphOfStatus_statusOfGlyph` and
  `statusOfGlyph_glyphOfStatus` make `Status ≃ Glyph` a bijection with no side
  condition, and `glyphAt_live` says the box at a live site is the status and
  nothing else. *(This is a change. The previous version had a second, partial
  inverse `statusOfGlyphDemoted` excluding `[ ]`, on the reading that a demotion
  writes `[-]` at both sites. §6.3's `readopt` is "`[-]` → `[ ]`, stamp kept",
  and what it reopens is the record, so a `[ ]` beside a standing archive is a
  shape the lifecycle produces — §4.3's own fixture pair. The partial inverse
  and its theorem are **deleted**; `Negative.lean`'s CHEAT 37 is the rule
  itself, refused.)*
- `a_differing_demotion_pair_renders_back` — **the pair's two lines may
  differ, and both come back.** §6.3's close writes the record with `est:` =
  remaining and a `demoted:` stamp and leaves the week line as it stood, so two
  lines of one id with different bytes is the *normal* case. `Core.archive` is
  a `Tomb` — a placement and the bytes standing at it, in one field, so a
  tombstone with no text is not a value — and `renderCore` writes the record's
  bytes at the record and the archive's at the archive. `LErr.splitLine`, which
  said "an entity owns one token vector, so there is no value that renders
  both", was a rule about the model and not about the data; it is gone, and
  `Negative.lean`'s CHEAT 36 and CHEAT 39 are the two ways of bringing it
  back.
- `the_fields_are_the_line`, `coreOfLine_shape` and its siblings — §3.1's item
  fields are **views of the token vector**, so two records carrying the same
  line carry the same fields and there is no second copy for a command to leave
  behind. `core_fields_round_trip` chains that onto round trip B:
  a `Fields` laid out as bytes reads back off the `Core` as itself.
- `the_spec_calendar_line_is_an_interval`, `the_spec_calendar_line_has_a_loc`,
  `the_spec_demoted_line_is_read_whole`, `the_spec_item_line_is_read_whole` —
  §4.3's and §4.1's own lines, read as §3.1's fields and `decide`d, so the
  kernel rechecks them on every build. The first is the line the corpus refused
  before the wiring.
- `the_tombstone_is_behind_the_live_line` — and **where the glyphs tie**, the
  inverse is a function of the two **files**: in an accepted plan, an entity
  whose record also reads `[-]` has its archive placement in a horizon strictly
  before the record's. That is a conjunct of `planWf`, so `mapAt` re-establishes
  it on the post-state of every command (`mapAt_rejects_unoriented`), which is
  what stops the kernel writing a pair it would then have to guess at. The
  glyph hypothesis is load-bearing and it is what this theorem gained: drop it
  and the statement is false of §4.3's own pair, whose record is a `[ ]` in a
  **week** and whose archive is a `[-]` in a **month**. See "which line is the
  tombstone" below for why that is the right order to consult them in.
- `the_kernel_can_read_the_pairs_it_writes` — **closure, and the reason
  `demotionsOriented` is in `planWf` at all.** Take a pair out of an accepted
  plan — the two lines it denotes, at the placements it holds them, with the
  regions its own documents declare — and hand them back to the loader: it
  returns the entity they came from. The proof splits on whether the record's
  box is `[-]` and reaches for the horizon only in the branch where the boxes
  tie, which is exactly the branch the conjunct covers.
  `the_spec_demotion_pair_loads` and `the_spec_demotion_pair_round_trips` are
  §4.3's own two lines, `decide`d, so the kernel rechecks on every build that
  the pair it used to refuse loads and comes back byte for byte — and
  `the_spec_pair_puts_the_tombstone_in_the_month` is **the choice itself**,
  `decide`d: the record is the week line and the tombstone is the month line,
  which is the answer the box gives and the exact opposite of the one horizon
  order gives. `the_spec_pair_is_one_entity_with_a_tombstone` is the other half
  of the same reading — two lines, one entity, not two entities and not one
  line dropped.

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

`<indent>- [<state>] <tokens…>`, with the six state glyphs, whitespace-separated
tokens kept verbatim, exactly one `^id` token, and — since the field-grammar
slice — **the whole of §4.1**: nineteen `key:value` spellings, five flags, both
positional slots, the four sigil tokens, the title, the unknown keys it
preserves and the words it cannot classify.  Everything outside an item line
(front matter, headings, blank lines, comments, generated blocks) is preserved
byte for byte and not interpreted.

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
- `paired_renders_each_placement` — and for the two-line form §6.3 writes, each
  site renders the box **and the token vector** that were in the file at that
  site: the theorem now pins the whole two-line list, which is the version the
  differing-bytes pair needs. It used to carry `a.item = b.item` as a
  hypothesis, and `pairedEntity` enforced it by refusing every pair that failed
  it — which is every pair a close writes.
- `paired_placement_renders_back` — **and it reads it back as one entity, not as
  whichever of two the argument order happened to reach first.** The orientation
  is `orientPair a b`, symmetric in its arguments (`orientPair_comm`), so the
  conclusion names the tombstone instead of offering a disjunction over the two
  ways the pair could be read — which is what this theorem's conclusion used to
  be, and was the honest shape for a loader that decided by list order.
  `pairedEntity_order_independent` is the same claim about the loader step
  itself, and `unordered_horizons_are_rejected` is what happens when two `[-]`
  lines' documents do not settle it.
- `the_kernel_can_read_the_pairs_it_writes` — the other direction, and the one
  that makes `demotionsOriented` earn its place in `planWf`: the two lines an
  accepted plan denotes, handed back to the loader, come back as the entity
  they came from.
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

### §4.1's field grammar

The value types live in `Tm.Field`, one module before `State.lean`, because
`State.lean` imports `Line.lean` and the grammar cannot name types it comes
before.  **They are §3.1's types**: `State.lean` opens them by name rather than
declaring a second copy, and §3.1's item fields are views of the token vector
rather than slots beside it.  See gap 3.

- **A round trip per value format.**  `parse_render_dur`, `parse_render_clock`,
  `parse_render_date`, `parse_render_moment`, `parse_render_interval`,
  `parse_render_window`, `parse_render_pref`, `parse_render_rule`,
  `parse_render_afterDone`, `parse_render_onEvent`, `parse_render_onMiss`,
  `parse_render_rate`, `parse_render_deps`, `parse_render_loc`,
  `parse_render_stamps`, `parse_render_ci`, `parse_render_prio` — every value
  the kernel writes it reads back as the same value, unit included.  Where a
  format needs a side condition the condition is decidable and named
  (`Rule.wf`, `intervalWf`, `windowWf`, `Loc.wf`, `depsWf`, `Dur.noDays`,
  `dayWf`), never assumed.
- **`row_*`, thirty-eight of them** — every row of §4.1's value table, read by
  the kernel, `decide`d at compile time.  `at:`'s short and long end forms, the
  short end that rolls past midnight, the overnight `win:`, `2w:Sun`,
  `month:15`, `2d~1d`, `reply/7d`, `6b/w`, `^k7q2,^m2`, `event:visa`,
  `W36,W37`, `wake+10m`.
- **`extract_phase0` — the induction over the token grammar.**  §4.1's line is a
  four-phase machine (ci slot, estimate slot, title, tokens), and it is four
  structurally recursive functions.  `extract_phase0` says that a view which
  reads a word the same way wherever the word sits reads the whole line as a
  plain scan; its three hypotheses are exactly the three places position can
  matter.  `keyPairs_raw` is the instance the setters rest on.  `flagsOf` is
  deliberately *not* an instance, because §4.1's flag rule is positional.
- **`field_round_trip` (round trip B, at the level of fields)** —
  `viewFields (renderItem i f) = f` on the decidable `Fields.wf`.  This is the
  direction round trip A does not give you and the one `PLAN-lean-kernel.md`
  named as the stage's biggest unknown.
- **`render_round_trip`** — and the two round trips joined:
  `renderItem_canonical` puts the rendered line inside `CanonicalItem`, so what
  the kernel writes from a `Fields` it reads back as the same **bytes** and the
  same **fields**.
- **`demo_wf` / `demo_line_bytes`** — `Fields.wf` is satisfiable and richly: a
  fully populated item, its `Fields.canonicalWf` `decide`d, and the exact bytes
  it writes spelled out.  A precondition nothing satisfies would make round trip
  B vacuous; this is the check.
- **`lookupKey_setKey`, and eighteen `view_set_*`** — there is **one** generic
  setter, `setKey`, and every field's `view ∘ set = id` is three lines from it.
  That is the shape of the fix for C1: the shipped bug was one setter out of a
  family writing the wrong slot, and a family with one member has no odd one
  out.  `setKey_canonical` and `setKey_line_reparses` carry the byte-level
  guarantee across the edit, and `unsetKey_canonical` /
  `unsetKey_line_reparses` carry it across a *removal* — which can break a line
  as surely as an insert can, because removing a token changes which token is
  the head and `toksWf` cares about the head's separator.
- **`view_set_remaining` and `view_set_ci`** — C1 and C2 dead as theorems:
  `est:` overrides the leading estimate and `ci:` overrides the positional
  digit, so the setter writes the slot the *view* reads.
  `est_key_overrides_the_leading_estimate` is the shipped bug's line
  (`- [ ] 6b Read est:1b ^t3`) with both numbers on it, and
  `unset_ci_key_leaves_the_positional_digit` is the `--unset ci` shape stated
  rather than papered over: removing the key leaves the digit, so a complete
  unset has to clear both slots.
- **`setFlag` returns `Option`** — §4.1 reads a flag only after a
  `@ # ! ^ key:` token, so a flag on a line with no such token would be absorbed
  into the title.  `view_set_flag` fires only when it succeeded and
  `setFlag_needs_a_boundary` is the refusal; `grammar.rs` calls this
  `EditError::FlagNeedsBoundary`.
- **The two §4.1 rules that are easy to lose**, as theorems about every line
  rather than about the ones a test tried:
  `unclassified_token_stays_in_the_title` and `unknown_key_is_reported`
  (preserved *with* its key and value, and reported).  `junk_extra_keys`,
  `junk_problems`, `junk_title` and `junk_bytes` are the same four claims on
  `- [ ] Read re:this @m1 note:xyz !9 ^t3`, `decide`d — including that the junk
  still round trips byte for byte.
- **`flag_word_in_the_title_is_title_text` / `flag_word_after_the_id_is_a_flag`**
  — the same word, two positions, two readings, both `decide`d.
- **`spec_line_*`** — §4.1's own header example, read: ci 4, leading estimate
  `2b`, remaining estimate `1b` (the `est:` override), title, `@m1`, `#lean`,
  `due:`, `max:`, `^t3`, no problems, and the bytes back — two spaces before
  `@m1` included.
- **`cap_is_an_alias_of_max`** — `cap:` has no field of its own, and writing
  normalises it to `max:`.  Two names for one budget is the defect class this
  kernel exists to remove, so the enum is named for the field.

Two layout choices in `renderToks` are deliberate and are recorded because they
are visible in the output: the `^id` **leads** the token run rather than
trailing it (§4.1 allows any order; the id is the one token always present, so
leading it makes "the title ended here" true by construction and makes a
trailing flag safe with no side condition), and the title-word guard
`slotGuard` is `grammar.rs`'s `EditError::Ambiguous` written as a
*precondition* — the kernel refuses to write a line whose title begins with `5`
or `2h` into an empty positional slot, rather than writing one that reads back
differently.

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
| a second demotion is refused, not resolved | **P** | `demote_on_a_standing_tombstone_is_refused`, `demote_twice_is_not_a_thing` |
| `readopt` reopens a **demoted** line or nothing | **P** | `readopt_of_a_live_record_is_refused`, `readopt_after_demote_succeeds` |
| stamps accumulate across demote → readopt → demote | **P** | `stamps_accumulate_across_readopt` |
| `edit est=v` ⟹ the view reads `v` | **P** | `set_is_not_silent`, `set_last_wins` |
| `demote` is idempotent | *withdrawn* | see below |
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
- **`demote` is the week close, once, and `demote_not_idem` is withdrawn
  because it went vacuous.** §6.3 gives an item **one** archive record: the week
  close creates it, and the month close "moves them to the next month file",
  which is `move`. So `demote` refuses an item that already carries a tombstone,
  and the old refutation's second hypothesis has no witness. A vacuous
  refutation is worse than none — it reads as a proof that the composite
  behaves, when the composite does not exist. `stamps_accumulate_across_readopt`
  replaces it and is stronger: it names the list (`demoted:W36,W37`) rather than
  saying two of them differ, and it is §6.3's actual cycle — close, readopt,
  close.

  The refusal is also what makes the tombstone's bytes safe, and both ways of
  *not* refusing lose a line. Overwrite the standing tombstone and its file's
  line vanishes from the render with the kernel returning `ok` — the failure
  `no_line_is_lost` is named after, reached through the one field that theorem
  cannot see, since the entity still has two placements and both are in range.
  Keep it instead and the line the record is **leaving** disappears, which is
  the line §6.3's week row says must stay behind as `[-]`. Both were reachable
  from a request; `a_second_demotion_is_refused_rather_than_dropping_a_line` is
  the FFI test.
- **`readopt` reopens a demoted line or nothing**, which is §6.3's own
  precondition ("moves a *demoted line* into the current week, `[-]` → `[ ]`,
  stamp kept"). Without it, `readopt` on §4.3's fixture — where the record is
  already `[ ]` and the **tombstone** is the line carrying `est:` = remaining
  and `demoted:W37` — consumed the tombstone, threw both away and returned
  `ok`. "Stamp kept" was precisely what was lost, and `readopt_keeps_stamps`
  did not catch it because it reads the *record's* line. This was invisible
  until this branch: `splitLine` used to force the two lines' bytes to be
  equal, so the record carried the stamp too. `KErr.notDemoted` was a
  constructor no function produced; this is what it is for.
- **The conservation law that three separate Rust commits tried to enforce is
  false.** `floor_and_respect_are_incompatible` proves that **no** rule can
  both floor `remaining` at the value a close recorded and leave a deliberate
  `tm edit est=1b` alone. Lean refuses the naive law. It does *not* hand you
  the exception — only running the binary did that. What the kernel buys is
  that the exception is written once, in `demoteEst`'s signature, where a later
  writer cannot fail to read it.

### The item, and the rest of the plan-level tier

`Core` accounts for all twenty-two of §3.1's fields, in **four** slots. Four
are absent on purpose — `id` is the store key, `horizon` is the file
(`Site.doc`), `src` is `live` plus `line`, and `series`/`effective_shape` are
derived in `Plan.lean` from the document and the tree. The rest are *views of
the token vector*, one function each: `Core.shape`, `Core.recur`,
`Core.budget`, `Core.after`, `Core.loc`, `Core.buffer`, `Core.stamps`,
`Core.waiting`, `Core.tags`, `Core.ci`, `Core.prio`, `Core.flags`,
`Core.scope`, `Core.splittable`, `Core.extra`, `Core.title`, `Core.est`. And
their types are §4.1's, opened from `Field` rather than copied — one `Shape` in
the kernel, over `DT`/`Moment` and not a re-encoding; `Recur` as **syntax** (a
denotation is not serialisable and §0 says the Markdown is the database);
`Stamp` knowing `W37` from `D07`; `Dur` keeping the unit §4.1 says a rewrite
keeps; `ci : Option (Fin 6)` and `!k : Option (Fin 4)` still bounded; tags
still a `Nodup` subtype. `parent` is the one exception and gap 22 says why.

That is a *narrowing*, and it is what makes the widening free at the other two
tiers: `wf_ignores_the_item_fields` used to set thirteen fields at once and be
`rfl`, and now it sets the one slot they all live in — a stronger statement,
because there is nothing left it does not cover.

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

**One gap sequence, 1–36, in three places.** Gaps 1–23 are here; 24–29 are in
the `Arith.lean` block below; 30–36 are in the acceptance-evidence block below
that. "Gap N" therefore names exactly one paragraph, and a cross-reference from
any block to any other is unambiguous. Number new gaps from 37 and keep the
sequence.

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
     `loadPlan docs = .ok p`. `badLine`, `dupId`, `notADemotion`,
     `ambiguousDemotion`, `duplicatePath` and the `itemCheck`
     faults have theorems of their own where they have any (`scanLines_prose`,
     `unordered_horizons_are_rejected`, `a_shapeless_calendar_line_is_rejected`,
     `an_unpinned_day_item_is_rejected`) and three of them cannot be reached from
     a request at all — see gap 10. The round trip says nothing about any of
     them, and should not;
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

2. **A lone `[-]` loads now; a pair the documents do not order still does
   not.** *(Was: "a lone `[-]` is rejected, not read." That was a kernel bug and
   the corpus found it — every `# Demoted` section in the fixture corpus was
   refused with `LErr.orphanDemotion`, §4.3's own `month/2026-09.md` included.)*
   The reading that produced it was "a demotion is two lines, so an entity with
   no archive placement has no configuration that renders `[-]`". §6.3's *week*
   close does write two, but `tm close month` then carries the
   `month/…# Demoted` copy into the next month file and touches nothing else,
   so a `# Demoted` section holds `[-]` lines whose partner is in a file the
   host need not have handed over. The Rust core is blunter: `State::Demoted`
   is a variant of the state enum (`model.rs`), `is_archive_copy` is a
   predicate on **one** item, and `Tree::build` short-circuits a key group of
   size one before any pairing is attempted (`tree.rs`). So `Status` has six
   cases, not five; `statusOfGlyph` is total; `glyphAt_statusOfGlyph` holds
   with no side condition; and `LErr.orphanDemotion` is gone. *(A second,
   partial inverse `statusOfGlyphDemoted` survived this fix — "while a
   tombstone stands, the live line reads `[-]`, never `[ ]`" — and it was the
   same mistake one step further on: §6.3's `readopt` reopens the record while
   the archive stands. It is deleted; see gap 31 and CHEAT 37.)* The two-line
   form loads and round trips, in both its shapes and whether or not the two
   lines' bytes agree — provided that, where both boxes read `[-]`, the request
   says which horizon each file is. Two such lines in two
   documents with no declared region, or with the same one, are
   `LErr.ambiguousDemotion`: the kernel's own output is never in that state
   (`demotionsOriented` is part of `planWf`), so this is a diagnostic for a host
   that dropped the regions, and the same `Repair` argument applies to it.

   **Which is also a behaviour restriction, recorded rather than decided —
   and it shrank.** While a tombstone stands and the live line still reads
   `[-]`, that line may only be moved to a horizon after the tombstone's. Once
   the line has been reopened — `tm readopt`, or any other status — the box says
   which line it is and the move is unrestricted. `tm` today allows
   `tm move ^id day` on a demoted item and leaves the stale `[-]` behind, which
   is the state `drop_stale_demotion` exists to repair. Refusing it *for the
   `[-]`/`[-]` case* is what makes that form readable at all, so it is a
   consequence of the fix and not an independent choice; it is still a change a
   user has to assent to.

3. **§4.1's field grammar is wired into `Core`, and the duplicate types are
   deleted rather than bridged.** *(Was: "not yet wired". The corpus measured
   the cost — every calendar line refused with `itemCheck: fileKindShape`,
   §4.3's own `at:2026-09-07T12:50/13:50` included.)* The map from
   `Field.Shape` to a second `Tm.Shape` was never written, and it is not
   written now: **the second copy is gone.** §3.1's `Shape`, `Recur`, `Rule`,
   `Rate`, `Period`, `OnMiss`, `Dep`, `WindowRange`, `Loc`, `Stamp`, `Dur`,
   `DT`, `Moment` and `Clock` are §4.1's, opened by name from `Field`; the
   import order permits it, because `State.lean` imports `Line.lean` and can
   name what it declares. And §3.1's item fields are **views of `line`**, not
   slots beside it: `Core` stores four things (`live`, `archive`, `status`,
   `line`) — `archive` being a `Tomb`, a placement and the frozen bytes standing
   at it, which are an *observation* and not a second copy of any field and `Core.shape`, `Core.recur`, `Core.budget`, `Core.after`,
   `Core.loc`, `Core.buffer`, `Core.stamps`, `Core.waiting`, `Core.tags`,
   `Core.ci`, `Core.prio`, `Core.flags`, `Core.scope`, `Core.splittable`,
   `Core.extra`, `Core.title` and `Core.est` read it. `the_fields_are_the_line`
   is the theorem that says there is nothing for a second reader to disagree
   with; `wf_ignores_the_item_fields` is now one binder instead of thirteen and
   covers every field there is. The plan-level tier fires on what the boundary
   builds: `shapesWf` accepts §4.3's calendar files and `afterTotal` catches
   `plan-conflicts`' dangling `after:^t9` and its `^z1`/`^z2` cycle.

   What this made visible, and fixed: `demote` used to append its `demoted:`
   stamp to a slot beside the line, and `renderCore` prints the line — so the
   stamp reached no file and §6.3's month review would have cut on a number
   nobody wrote. `demote` now writes it with `Field.setDemoted`, takes a
   `Field.Stamp` (which knows `W37` from `D07`) rather than a bare `Nat`, and
   `readopt_demote_id_mod_stamps` states the resulting bytes exactly.

4. **Two readers of `est:` coexist.**  The stage-one `viewRemaining`
   (`Nat`-valued, what `Cmd.lean` and `Boundary.lean` call) and the
   field-level `viewRemainingDur` are two functions over one slot — which is
   the shape of the defect this kernel exists to remove.  They do not
   *disagree* about the bytes: `the_two_est_setters_write_the_same_token` shows
   `estWord v` and `keyWord Key.est (renderDur (.simple v .minutes))` are the
   same token, so the stage-one view reads what the field-level setter writes.
   But they are not one function, and the stage-one `unitValue` does not read
   `NhMm` or `Nd` where `parseDurND` does.  Gap 3's wiring made `Core.est` the
   field-level reader (`viewRemainingDur`), so the *entity* has one; what still
   has two is the command path, where `Cmd.setEstE` and `Boundary`'s `est`
   request go through the stage-one `Nat` reader.  Collapsing those is the next
   slice, and until it happens this is a live S2.

5. **State-less lines are still not representable.**  §4.1 says
   `routines.md` and `optional.md` omit the state box.  `ci:` as a *key* is
   implemented — it is the mechanism §4.1 gives for those files, and
   `viewCi` reads it in preference to the positional digit — but `parseItem`
   still requires `- [<glyph>]`, so a box-less line is prose to this kernel.
   Fixing it means a `RawItem` that records whether the box was there, which
   changes a type `State.lean`, `Plan.lean`, `Cmd.lean` and `Boundary.lean` all
   use.

6. **`renderItem` writes a legal line, not the conventional one.**  The `^id`
   leads the token run (see above), the title is written with single spaces
   between words, and `Fields.canonicalWf` refuses an unclassifiable word that
   begins with `^`.  The last is forced: `serializeItem` regenerates the id
   from the store key and recognises an id token by "starts with `^`", so a
   rendered `^%` would be rewritten as the id.  A line the kernel *reads* still
   keeps `^%` in the title (`junk_title`); this is a restriction on the
   renderer only, and it is the same looseness gap 13 records about `Id`.

7. **`render ∘ view` is not claimed, and is false on whitespace.**  Round trip B
   is `view ∘ render`.  The other composition fails for a mundane reason: the
   title's internal whitespace lives in the *token vector* (and round trip A
   preserves it — `spec_line_bytes` keeps the two spaces before `@m1`), but
   `titleSegment` returns words, so re-rendering writes single spaces.  Round
   trip A is the theorem that covers a line read from a file; round trip B is
   the theorem that covers a line the kernel composes.

8. **The conflict *diagnostics* `build_item` emits are not modelled, only the
   precedence.**  `shape_at_wins`, `shape_win_needs_dur`, `shape_due_is_last`,
   `recur_every_wins` and `recur_afterDone_beats_onEvent` say which key wins;
   `grammar.rs` also pushes "conflicting shape keys (at: wins)" onto
   `item.problems`, and `problems` here reports only unknown keys and
   unclassifiable words.  Likewise `title_conflict`: the guard exists as
   `slotGuard`, a precondition, not as a diagnostic a `tm check` could print.

9. **Weekday and duration spellings are narrower than `chrono`'s.**
   `parseWeekday` accepts four spellings a day (`Mon`, `mon`, `Monday`,
   `monday`); `chrono` accepts more.  And `parseDur` keeps `1h90m` as written
   where the Rust normalises it to `2h30m` — mine round trips, the Rust's does
   not, and the *minute* readings agree.  `every:week` / `every:Nw` is in
   `Rule` because §4.3's routines example uses it and §3.1's `Rule` has no
   constructor for it; that is a gap in the spec, recorded rather than papered
   over.

10. **The calendar is real now; horizon *names* are still not.** `Cal.lean`
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

11. **No `close`, no `autoClose`, no `ClosePolicy`, no planner, no priority, no
   recurrence, no exact-arithmetic layer.** L16–L27 of the architecture are not
   here. In particular the two relational laws — tail-drop and stability — are
   not attempted, and the recommendation in the plan stands: keep the existing
   882-line proptest, state the laws in Lean, and prove them last or never.

12. **The line-splitting at the very edge is unverified**, and since gap 1
   closed it is the *only* unproved step on the text path. The kernel's document
   round trip is over `List (List Char)`. Splitting a file's bytes on newlines
   and joining them again happens in JSON at the boundary, and
   `String.intercalate "\n" (s.splitOn "\n") = s` is not a core theorem.
   `Json.parse`/`Json.compress` and `String.toList`/`String.ofList` are in the
   same position. A request line containing a literal newline round trips as one
   line inside the kernel and becomes two lines on disk.

13. **`Id` is `List Char`, not §3.1's "4 chars of `[a-z0-9]`".** The spec's own
   §4.3 fixture ships `^O1`, so the tight type would fail the build on day one.
   The right resolution is to weaken the spec, not the data — but that is a
   judgment a human has to make, and it is recorded here rather than silently
   taken.

14. **Nothing in the shipped `tm` binary calls this yet.** Stage 3 wires it in.
   The Rust crate here is a bridge and its test suites, not an integration.

15. **`CanonicalItem` excludes a line with trailing whitespace**, because the
   tokenizer emits a final token with an empty word for it and `Tok.wf` requires
   words to be non-empty. Such lines parse, render and edit correctly — the FFI
   tests cover them — but `setEst_canonical` does not apply to them, so for that
   family the reparse after an edit is checked rather than proved. Widening
   `toksWf` to allow an empty word in the last position would close it and costs
   a re-proof of `tokenize_toks`.

16. **`sitesInRange`, `demotionsOriented` and `Normalized` are checked at load
    rather than established by construction.** The loader takes document indices
    from `placementsOf`'s counter, so every site it builds is in range; it takes
    each placement's region from the same document it takes the index from, so
    `orientPair` establishes the orientation for every entity it builds (it
    consults the horizon exactly when `demotionOriented` demands it, which is
    what `the_kernel_can_read_the_pairs_it_writes` says in the other
    direction); and
    `splitDoc` hands each line index to exactly one of prose and items, so ranks
    within a document are distinct. All three are therefore true of every plan
    the loader builds, and none of the three is *proved* that way. The boundary
    runs the decidable checks instead and returns structured errors, which is
    the same discipline as `Grain.ofNat?` — but they are checks, not
    constructions, and the difference is recorded. (`mem_placementsOf` is now the
    lemma the first two would be built from; the third would additionally need
    `PlanCore.lines` of a loaded plan to be `Nodup`, which
    `loadCore_lines_mem` gives as a membership statement and not as a list.)
    `Goals.lean` states all three — `the_loader_builds_sites_in_range`,
    `the_loader_builds_a_normalized_plan` and
    `the_loader_builds_oriented_demotions`. The last was held back while the
    orientation model was in flux ("a goal written against the current
    `orientPair` would be stale before it was read"); it is settled now, so the
    goal is written.

    **The consequence, stated rather than hidden: four diagnostics are
    unreachable from a well-formed request.** `siteOutOfRange`, the plan-level
    `ambiguousDemotion` that `firstUnoriented` names, `itemCheck:
    rankCollision`, and — since the orientation became lexicographic — the
    *inner* `notADemotion` in `pairedEntity` (gap 31) cannot fire on anything
    the loader itself builds — and, since
    `move_at_freshRank_normalized` and its siblings, `rankCollision` cannot fire
    on an `applyCmd` post-state either. They are kept because "cannot happen" is
    exactly what the shipped `move_to` also said, and because a hand-written
    transform can still reach them; but a checker that no *input* can fail is a
    checker whose bite is a proof and not a test, and that is worth writing down.
    The load-time `ambiguousDemotion` raised by `pairedEntity` is a different
    thing and is reachable — `two_demoted_lines_with_no_horizons_are_rejected_by_name`
    is the request that reaches it.

17. **`Normalized` after a command is a theorem now; the six other item-level
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

18. **`series` has a name but no head.** `seriesOf` derives the
    `## series:<name>` a placement sits in. §5.4's *head* — "the first member
    that is not Done or Dropped is active, the rest are invisible to the
    planner" — and the implied `after:` a series section carries are planner
    concepts, and the planner is not here.

19. **`@parent` is an `Id`, not §3.1's `Ref`.** §3.1 says
    `parent: Option<Ref>` where a `Ref` is `@id` **or `@label`**. Label
    resolution needs a title index and a rule for ambiguity; the kernel takes
    ids only, and a boundary that accepted labels would have to resolve them
    before it built the store. `pref:` (`wake+10m` or a clock time) is not
    modelled either — it needs the day's `wake`, which is day-file front matter
    the kernel does not read.

20. **§6.2's "outcome with an estimate" warning is not checked.** `shapesWf`'s
    month rule is the shape half only (a month item's shape is `none`). The
    estimate half — "an item in `month/` with an estimate and no children is a
    `tm check` warning" — would refuse the two-line demotion form *this kernel
    writes*, because §6.3's close copies the line, estimate and all, into the
    month file, and `demote` here lands it at a fresh rank rather than inside
    `# Demoted`. Making it real needs `demote` to target a *section*, which is
    stage-4 close work. Recording it rather than weakening it.

21. **The proof-to-definition ratio here is not a forecast.** This fragment has
    no planner, no calendar arithmetic and no relational laws — the three places
    the ratio blows up.

22. **`parent` is the one §3.1 field still stored, and it is always `none`.**
    Every other item field is a view of `Core.line` (gap 3); `parent` is not,
    and the reason is `parentsTotal`, not the grammar — `Field.parentRef` reads
    `@O2` off the line today. §6.1 says "a week item may be a child of a month
    item", `parentsTotal` is a **load precondition** rather than `tm check`'s
    `@ghost` report (§17.2, which is how tm treats it), and so reading the
    field would make a document set that is one file stop loading: every
    `week/*.md` and `backlog.md` in the corpus would go from `ok` to
    `danglingParent` the moment it is wired. The choice — derive the field, or
    demote `parentsTotal` to a report the way `check.rs` has it — is a decision
    about the plan tier and is not taken here. Consequence: §3.2's
    `effectiveShape` prep rule, `effectiveCi` inheritance and `rootPrio` are
    proved and cannot fire on anything the boundary builds.

23. **~~The demotion pair is still one token vector, and `orientPair` still
    orders by horizon~~ — fixed; this is what is left of it.** Both halves are
    closed: `Core.archive` is a `Tomb` (a placement *and* the bytes standing
    there), and `orientPair` is lexicographic — the `[-]` line is the
    tombstone, and horizon order is the tie-break when both lines are `[-]`.
    The measurement moved from 1/5 to 4/5 whole plans, and `plan-conflicts`,
    the remaining refusal, is the fixture that exists to be refused. See "which
    line of a demotion pair is the tombstone" above for the spec argument and
    what the choice costs.

    **Two things this opened that are recorded rather than closed.**

    * **The tombstone's bytes are checked by the parser and by nothing else.**
      `itemsWf`'s field-derived conjuncts — `afterTotal`, `afterAcyclic`,
      `shapesWf` — all read `Core.line`, the record. So a line the kernel
      refuses standing alone is accepted verbatim as the archive half of a
      pair: `- [-] 1 1b T after:^m1 ^m1` is `itemCheck: depCycle` alone and
      `ok` as a tombstone. This is a direct consequence of deleting
      `splitLine`, which used to force the two lines' bytes to be equal.
      For the dependency half it is also what `tree.rs` does — `dangling_parents`
      and the child/root walk are `n.primary` only, so tm does not check
      archive copies either — and it is the behaviour you want: an archive is a
      frozen record in a file the lifecycle no longer edits, and making a later
      unrelated edit retroactively invalidate it would be worse. `shapesWf`'s
      file-kind rule is the one where the argument is weaker. Recorded rather
      than decided.
    * **`LErr.notADemotion` has two producers and one of them is now dead.**
      The outer guard in `pairedEntity` — neither line is `[-]` — is reachable
      and is the one that matters. The inner one, `pairEntity` returning
      `none`, cannot fire: `orientPair_cases` gives `arch.glyph = Glyph.demoted`
      and the `dupId` guard gives distinct documents, which are the only two
      ways `pairEntity` fails. Before this change that branch was the *live*
      one — it is how a `[ ]` record was refused. It stays for totality; it
      joins gap 16's list of checks no input can fail.

    **What is *not* closed, and it is a real divergence from the oracle.**
    `tree.rs`'s `is_archive_copy` also constrains *where* a `[-]` line may be
    an archive copy: a week file, or a `month/…# Demoted` section, and nothing
    else — "a `[-]` line anywhere else (backlog, day, a month section that is
    not `# Demoted`) is not something a close produces, so it still counts as a
    live copy and collides". The kernel asks only whether the box is `[-]`. So
    a `[-]` in `backlog.md` paired with a `[ ]` in a week file loads here as a
    demotion and is a duplicate id to `tm`. Nothing in the corpus is in that
    state and no command the kernel has can reach it — `demote`'s tombstone is
    always the file the record left, which is a horizon strictly before the
    destination — but `planWf` is supposed to be no weaker than `tm check`, and
    on this one predicate it is. Closing it needs the *section* of a placement
    to reach the plan tier, which is `sectionsWf`'s machinery pointed at a new
    question; it is a small change and it is a behaviour change, so it is
    recorded rather than taken.

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
     Its gaps were renumbered into the single 1-36 sequence at c8f3a38;
     they were 12-17 before that.
     =================================================================== -->

## The exact-arithmetic layer (`TmKernel/Arith.lean`)

1,079 lines, 90 theorems (measured at `c8f3a38`), no `Float`, no fixed point,
no `Rat`. §7 and §8 are written in decimals; every one of those decimals is a
*comparison*, and a comparison of ratios cross-multiplies into `Nat`.
`u = need/avail` is never formed: `u ≥ p/q` is `q·need ≥ p·avail`, and a scale
constant folds into the same product, so §7.1's safety-1.3 test against an edge is
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

Gap 11 above says "no exact-arithmetic layer"; that clause is superseded. The
rest of gap 11 — no `close`, no `ClosePolicy`, no planner, no priority, no
recurrence, and tail-drop and stability unattempted — still stands.

### What it does **not** cover

*Gaps 24–29, continuing the single sequence that starts at "What this does not
cover" above.*

24. **~~`Check.lean` does not audit these 91 theorems~~ — closed.** It did not
    when this block was written: the acceptance run's audit was the pre-existing
    list and the `Arith` names were checked by hand. They were appended at
    `58ee343` and the generator's name-stripping bug was repaired at `e7b816c`.
    Measured at `c8f3a38`: `grep -cE '^\s*(@\[[^]]*\][[:space:]]*)?theorem '
    TmKernel/Arith.lean` is 90 and `grep -c '^#print axioms Tm.Arith' Check.lean`
    is 90 — every theorem in this module is audited by CI, and none depends on
    anything but `propext` / `Quot.sound` / `Classical.choice`; ten depend on no
    axioms at all.

25. **`0/0` is a decision, not a derivation.** §7.1 says "capacity 0 → `u = ∞`",
    with no exception for zero need, so `utilGe 0 0 e` is `true` and an item
    with nothing left to do and no capacity comes out HOT. An `f64`
    implementation gets `NaN` there, every comparison is false, and it falls off
    the ladder into the *lowest* bin — `+3`. The two disagree, both are
    defensible, and this is the kind of "bug versus undocumented deliberate
    choice" that reading cannot settle. `utilDefined` is the guard; the kernel
    takes the spec's sentence literally and says so
    (`util_zero_over_zero_is_undefined`, `util_zero_over_zero_is_hot`).

26. **R7 is open.** §8.4's future-day capacity mixes the lounge and home
    capacities by `p_lounge`, which is a rational weight over two integer
    minute-counts. Nothing in this layer rounds it; whether the planner floors
    the mixture per level, per day, or carries it exact into the EDF pass is a
    decision the planner has to make and state, and it is not made here.

27. **`ladder_eq_rungs` needs the edges sorted; `rungs_antitone` does not.**
    That asymmetry is deliberate — antitonicity is the property the list
    actually supports — but it means a misconfigured `priority.bins` (not
    descending) still produces a well-defined, antitone bin that is *not* the
    ladder §7.1 describes. There is no `planWf` clause rejecting such a config,
    because config validation lives at the boundary and the boundary is not this
    branch's file. `binsWf` and `descending` are the two decidable predicates a
    loader should run.

28. **The energy posterior is arithmetic here, not statistics.** `ramp`,
    `posteriorNum` and `energyAfter` implement §8.5's *correction*, exactly and
    over `Int`. Fitting the model, `exp(−age/decay)`, the shrinkage means and
    `p_lounge` stay in Rust, as §3.6 says. `energyAfter` also has no monotonicity
    theorem in `δ`: it is a clamp composed with a rounding, both monotone, but
    the composition was not needed by anything yet and was not proved.

29. **Nothing consumes this layer.** Priority and the planner are stages 5 and 6.
    `needMin`, `budgetBlocks`, `plannedMin` and `energyAfter` are the four sites
    §7 and §8 will call; until they exist, the parity harness against the Rust
    `f64` path (§3.5's 0/2,251,500 and 135/150,600 measurements) cannot be re-run
    against *this* code, and those numbers are quoted from the spike, not
    reproduced here.

<!-- ===================================================================
     THE ACCEPTANCE EVIDENCE (`kernel/corpus/`, the corpus harness and the
     differential oracle), added on its own branch.  Appended as a block so
     the stage-two branches merge.  Its gaps were renumbered into the single
     1-36 sequence at c8f3a38; they were 18-24 before that.
     =================================================================== -->

## The acceptance evidence: the fixture corpus, and the Rust as an oracle

Stage 2's acceptance is "`render ∘ parse` byte-identical over the full fixture
corpus". That corpus now lives here — `kernel/corpus/`, the five fixture plan
trees copied verbatim off `main` at `557a3d2`, 37 Markdown files,
`PROVENANCE.md` records the copy — and two harnesses read it.

### 1. The corpus round trip (`check.sh` check 6)

`tm-kernel-ffi/tests/corpus.rs` pushes every Markdown file through the
`String → String` boundary **with no commands at all** and compares the bytes
that come back with the bytes that went in. It is a measurement, not a theorem,
and it reaches two steps round trip B cannot: the split of a file's bytes into
lines and back (gap 6), and the JSON escaping on both sides of the FFI.

```
CORPUS: 33/37 files and 4/5 whole plans round-trip byte-identically
```

**Nothing in the corpus is silently rewritten.** Not one file is accepted and
handed back changed — the failure mode the first loader had, where a `[-]` came
back as `[ ]` on a plain read. `no_file_is_silently_rewritten` asserts that
unconditionally, with no baseline and no exemption; `corpus_round_trip` is a
ratchet against `corpus/round-trip.expected`, so a file that stops
round-tripping fails the build and a file that starts round-tripping does not.
Re-measure with `TM_CORPUS_BLESS=1 cargo test --test corpus`; the table, and the
minimal set of lines behind each refusal, print under `-- --nocapture`. The
baseline is re-blessed when a fix lands, so the four whole plans are recorded
`ok` and a regression to `splitLine` fails the build rather than passing
quietly.

**The four files that do not round-trip are all `plan-conflicts/`**, the fixture
that exists to make `tm check` print, and each refusal names a defect
`corpus/PROVENANCE.md` lists as deliberate:

| file | diagnostic | the line, and the listed defect |
|---|---|---|
| `plan-conflicts/backlog.md` | `dupId: a1` | two `^a1` lines — "a duplicate id" |
| `plan-conflicts/calendar/2026-W37.md` | `itemCheck: fileKindShape` | line 8, `- [ ] 3 Office hours  loc:JCL ^g7` — "a calendar entry with no time" |
| `plan-conflicts/day/2026-09-07.md` | `itemCheck: sectionDiscipline` | line 19, `^p2` — "a day-file item outside `# Pinned`" |
| `plan-conflicts/week/2026-W37.md` | `badLine: manyIds` | line 23, `^%` beside `^q7` — "an odd token `^%`, two ids on one line"; the same file's `danglingDep` catches "a dangling `after:^t9`" and "a two-item `after:` cycle" |

Before the field wiring the count was 26/37: four `calendar/*.md` refused with
`itemCheck: fileKindShape` (gap 30) and four `month/2026-09.md` refused with
`orphanDemotion: m2` (gap 2), both of them kernel defects and both now fixed.
The one `plan-conflicts` calendar refusal that remains is the *right* one, and
it is the wiring working: eight calendar lines, one refused.

**Four of the five whole plans load and round-trip**, up from one. `plan-basic`,
`plan-home-day` and `plan-travel-day` were `splitLine: m2` until the demotion
model changed — one entity, one token vector, and a tombstone chosen by horizon
order — which is gap 31 and is now closed; `plan-recur`, the one fixture tree
with no demoted line, always loaded. The fifth is `plan-conflicts`, whose four
refusals are the four rows above and are what that fixture exists to have.

### 2. The differential oracle (`examples/oracle/`, `examples/oracle-compare.rs`)

The plan says a checked parser is worth having "even with no FFI" because it can
be run against the Rust. `examples/oracle/run-oracle.sh` extracts `main` into a
scratch directory, builds a small binary against the shipped
`tm-core::grammar`, and runs two input sets through both parsers:

* the corpus's own 138 item lines — real tm syntax, every one with an id;
* 2,048 lines from **`main`'s own `grammar_proptest` generator**, the 512-case
  strategy that ships, over four seeds.

Four things are comparable through a `String → String` boundary, and the tool
prints the denominator for each so that "no disagreement" is never confused with
"never ran": is it an item line; does each side hand the line back unchanged;
what id does each read (asked by putting the *same line twice* in one document,
which makes the loader name the id it parsed); and does `tm edit est=` produce
the same line.

```
corpus lines     138 compared, 126 with nothing to report
generated       2048 compared,  481 with nothing to report
```

Measured at `c8f3a38` with `run-oracle.sh <scratch> 512 4`, run twice and
byte-identical both times. The counts are deterministic for a fixed seed count —
they move when the *kernel* moves, not between runs. They were 129 and 479
before the demotion model changed at `8eea3d6`.

**Byte faithfulness holds on both sides everywhere.** 2,186 lines, and neither
implementation ever returned a line different from the one it was given. That is
the strongest single result in this section, and it is the property stage 2 is
named after.

The disagreements are gaps 30–33.

### What this does **not** cover

*Gaps 30–36, continuing the single sequence that starts at "What this does not
cover" near the top of this file.*

30. **~~`shapeWfFor`'s `.calendar` clause is unsatisfiable~~ — fixed; this is
    what it was.** The corpus harness found it: **every one of the 20 calendar
    item lines in the corpus was refused**, including the ones written exactly
    as §4.1 writes an interval (`at:2026-09-07T12:50/13:50`), because the
    loader built every `Core` with `shape := Shape.none` and `.calendar`
    demands an interval. No line the boundary could construct satisfied that
    clause; it was a rule that could only ever say no. Gap 3's wiring closes
    it, `Negative.lean`'s CHEAT 30 is the refutation of the assumption that
    made it invisible, and
    `State.lean`'s `the_spec_calendar_line_is_an_interval` is the `decide`d
    reading of the line that was refused. The one calendar line still refused
    is `plan-conflicts`' `- [ ] 3 Office hours  loc:JCL ^g7` — "a calendar
    entry with no time", which that fixture exists to have refused.

31. **~~The kernel's demotion is two byte-identical `[-]` lines; tm's is
    not~~ — fixed; this is what it was.** Every `month/2026-09.md` in the
    corpus carries
    `- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2` in
    `# Demoted`, and the matching `week/2026-W37.md` carries
    `- [ ] 4 6b Rollback path passes tests   @O2 ^m2`. Together they were
    `splitLine`, and that was the only thing between three of the five fixture
    trees and a whole-plan round trip. The diagnosis had two halves and neither
    was a fixture defect; both are closed.

    * **The two lines legitimately differ.** §6.3 says the copy filed into the
      month carries "`est:` = remaining" and a `demoted:` stamp, so the spec's
      own demotion pair has two lines with different bytes, and an entity
      owning one token vector cannot render both. `Core.archive` is now a
      `Tomb` — the placement and the bytes standing at it, in one field, so
      there is no value with a tombstone and no text — `renderCore` writes the
      archive's own bytes at the archive site, `demote` freezes the line it is
      leaving there and puts the stamp on the copy, and `readopt` discards it.
      `LErr.splitLine` had nothing left to refuse and is deleted.
    * **The orientation is by horizon, and for this pair it is by glyph.**
      `orientPair` is lexicographic now: a `[-]` line beats a live one, and
      horizon order is consulted only when both are `[-]`. `demotionsOriented`
      demands the horizon order only in that same case. The argument is from
      §6.3 and §3.1, not from `tree.rs`, and it is written out under "which
      line of a demotion pair is the tombstone" above, with what the choice
      costs and what stays open (gap 23).

    The oracle also settled what these two lines are: `check_fixtures.rs`
    asserts `plan-basic` is clean with **zero** problems, warnings included, and
    `invariant_common/mod.rs` names `^m2` "the one sanctioned pair" — §4.3's
    example carried live in `week/2026-W37` and as the `[-]` archive copy in
    `month/2026-09 # Demoted`. It is the **pre-close** shape; the post-close
    shape is `[-]`/`[-]`, which this kernel already read. Both are legal and
    both load. `the_spec_demotion_pair_loads` is §4.3's own two lines
    `decide`d, so the kernel rechecks the acceptance on every build.

32. **A tab is not a separator, and neither is a second space.**
    `Text.lean`'s `isSp c := c == ' '`, but §4.1 says "whitespace-separated
    words" and `tm-core::grammar` splits on a whitespace run. Measured on the
    2,048 generated lines:

    * `parseBody` matches the literal `- [`, so `- <TAB>[ ] …` and `-  [ ] …`
      (two spaces) are **not item lines**. 1,049 lines. This one is silent: the
      line is kept as prose and written back unchanged, so nothing complains and
      the item is simply invisible to every command, to ranks and to `tm check`;
    * `- [ ] x<TAB>^a1` is refused as `noId` — 9 lines the Rust reads fine;
    * `- [ ] x ^a1<TAB>` yields the id `"a1\t"` — a store key with a tab in it,
      which the Rust's own `Id::is_valid` would reject. 8 lines got a different
      id this way;
    * and it reaches an operation that ships: on
      `- [>] … @j<TAB>est:48h … ^w4 … est:2h09m`, `tm edit est=45m` writes the
      *first* `est:` in the Rust (documented: "the first occurrence of a repeated
      key wins") and the *second* in the kernel, because the kernel cannot see
      the first. Re-read the kernel's line with the Rust and the estimate is
      `48h`, not `45m`. This is the shape of the bug the rebuild exists to make
      impossible, in the same operation, and the kernel is on the wrong side of
      it. CHEAT 27 and CHEAT 28.

    Otherwise the `est` edit agrees exactly: 132 corpus lines and 44 generated
    lines, one disagreement, the one above.

33. **Every `^`-leading word is an id.** `isIdWord w := w.head? == some '^'`,
    where §4.1 says a token the parser cannot classify stays in the title, and
    the Rust keeps `^`, `^%` and `^é` there with a `tm check` problem. So a bare
    `^` names an entity whose id is the empty list — and two lines ending in `^`
    are `dupId ""` — `^%` names one called `%` (18 lines where the Rust reads no
    id and the kernel reads one), and a line carrying both `^%` and a real
    `^q7` is refused as `manyIds` (11 lines). The last of those is
    `plan-conflicts/week/2026-W37.md:23`, which the shipped parser reads with id
    `q7`. CHEAT 29.

34. **Gap 6 is measured, not closed.** `split_lines`/`join_lines` are
    `str::split('\n')` and `join("\n")`, the identity on every `String`, and
    `split_join_is_identity` checks that on all 37 corpus files (the line count
    is exactly the newline count plus one) and on the shapes that break naive
    splitters — empty, `"\n"`, no final newline, CRLF. `escaping_survives_the_
    boundary` then pushes quotes, backslashes, tabs, `U+0001`, DEL, an astral
    character and a CRLF file through the FFI and back, none of which the corpus
    contains. But the *Lean* side of the split is still not a theorem, and this
    is a harness written in the same language as one half of the boundary. It is
    a much better measurement than none; it is not a proof.

35. **The oracle compares four things, and the item has twenty-two fields.**
    Title, `ci`, `!k`, `@parent`, `#tags`, shape, recurrence, budget, `loc:`,
    `buffer:` and the flags have no observable counterpart at stage 1, because
    the kernel keeps those tokens verbatim and does not interpret them (gap 3).
    Every one of them is a place the two implementations could differ silently,
    and the oracle would not know. What it *does* show is the shape of what to
    expect when the parser lands: on the generated set the Rust reports 391
    "missing state", 244 duplicate-key, 95 unclassified-token and 32
    invalid-interval problems on lines the kernel accepts without comment. Those
    are not disagreements yet; they are the list of checks the kernel still owes.

36. **The oracle is not in `check.sh`.** It needs a Rust build of `main` in a
    scratch directory outside the repository, which is the wrong dependency for
    an acceptance script that must run on this branch alone. Run it by hand:
    `tm-kernel-ffi/examples/oracle/run-oracle.sh`. The corpus harness, which
    needs nothing but this branch, *is* check 6.

<!-- ===================================================================
     THE BURN-DOWN (`TmKernel/Goals.lean`, `check.sh` check 7).
     =================================================================== -->

## The burn-down: `TmKernel/Goals.lean`

Everything above this line is compiled. Everything stages 3 to 6 still owe was,
until now, **prose** — in `PLAN-lean-kernel.md` §3.3's law table, in §4's
defect-by-defect verdicts, and in the gap list above. Prose can be skimmed past,
and an agent or a contributor who cannot build a thing can quietly leave it out,
at which point the gap becomes invisible.

`TmKernel/Goals.lean` makes the remainder a **verifiable artefact**: 52
outstanding obligations, each a Lean `theorem` whose statement elaborates
against the real kernel and whose proof is `sorry`.

| stage | goals | what they are |
|---|---|---|
| **3** | 12 | `rank` and `add` (L20, L21); L22's expected refutation; the JSON/string/newline edge (gaps 6 and 12); gap 16's two by-construction proofs; gap 4's one estimate reader |
| **4** | 11 | L16–L19 and L27: `close` idempotent, `autoClose` catching up in one step, `ClosePolicy`'s wall exemption, the conservation fold; F1, F2, F4, B1–B3 |
| **5** | 14 | §6.4's rollups, §5.4's series head (gap 18), §7.2's priority and §7.4's hysteresis, §7.3's EDF pass over §8.4's capacity |
| **6** | 15 | §8.3's single-run invariants (L26), E1, E2, E5, E7's window fixed point, and L24/L25 stated but recommended for the proptest |

### Why a statement that only typechecks is worth something

A statement that elaborates is **guaranteed to be well-formed and to name real
definitions**. A goal nobody can state precisely is a goal nobody has
understood, and finding that out now costs a session; finding it out in stage 6
costs the stage. Writing these produced three findings before any proof was
attempted:

* §8.3's "monotone rank" cannot be stated over §7's `p` yet, because `p` needs
  stage 5's EDF capacity — so the goal stands in `rootPrio` and `effectiveCi`
  and says so at the declaration;
* §5.4's series head and §6.4's rollups turned out to be *fully* stateable over
  vocabulary that already exists, which moves them out of "stage 5 is a big
  unknown" and into "stage 5 has thirteen named lemmas";
* B3 (`close_week` folding a dropped child's remaining into its parent) cannot
  **fire** until gap 22's decision about `Core.parent` is taken. That is now a
  visible precondition of stage 4 rather than a surprise inside it.

### The rules that make it safe

1. **Nothing imports it.** `TmKernel.lean` does not, and no module of the
   library does. Its `sorry`s therefore cannot reach a proved theorem, and
   check 3 — the axiom audit over `Check.lean`'s 1,006 names — is what enforces
   that. A `sorryAx` there means `Goals.lean` leaked.
2. **`totality.py` names it, and only it.** The exemption is `EXEMPT =
   {"Goals.lean"}`, one filename, not a loosened pattern: a `sorry` added to any
   real module is still a check-2 failure. Check 2 now scans the package root as
   well as the library, so the exemption is load-bearing rather than decorative.
3. **It elaborates on its own**, exactly as `Check.lean` does. Check 7 runs it
   and fails on an *error*; the `sorry` warnings are the point.

### How to burn it down

The count in check 7's line is a **burn-down, not a score**. A stage that
discharges a goal:

1. proves it in the module it belongs to (`Cmd.lean` for a command law,
   `Plan.lean` for a plan-level one, and so on);
2. appends its name to `Check.lean`, so the axiom audit covers it;
3. **deletes it from `Goals.lean`**, and the number drops.

Removing a provisional `def … := sorry` is the same move: it is replaced by the
real definition in the real module. A goal that turns out to be **false** is a
finding, not a failure — rename it to the negation, prove that, and record it
the way `move_last_wins_refuted_globally` and `demote_not_idem` are recorded.
Four goals are already marked **R\*** (expected refutation) at their doc
comments: L17 (`close_week_and_close_month_commute`), L22
(`move_has_an_inverse_command`), L27 (`lifecycle_commands_commute`) and
`joining_lines_is_injective`. A fifth, `the_json_edge_round_trips`, is flagged
as likely needing *narrowing* to the fragment the kernel emits rather than
refuting outright — and if it does not hold there either, that is a finding.

The number rises only when a new debt is admitted, which is a thing worth
noticing in a diff.

### What is deliberately *not* in it

`Goals.lean`'s header carries the list, with what would have to exist first for
each. In summary: the recurrence denotation (D1, D2) and `close day`'s
double-count (F6) all need a parsed `LogEvent`, and `PlanCore.log` is
`List String` held verbatim; `ClosePolicy`'s five rows are stage 4's to design;
generated-block ownership (F3, G1) is §4's **A** verdict — architecture, not
type theory, and the plan says not to credit the compiler for it; R7's capacity
mixing is a decision, not a proof obligation; and §7.1's bin ladder is left
alone on purpose, because three of its four edges are halvings and the fourth is
1/10, so the only property it supports is antitonicity and that is already
proved (`Arith.rungs_antitone`).

<!-- ===================================================================
     APPENDED 2026-09-09 (stage-3 boundary session, rebuild-on-lean).
     Whoever merges: gap numbers 37-39 below continue the single
     sequence (30-36 are in the acceptance-evidence block above).
     =================================================================== -->

## Stage-3 session 2026-09-09: one goal discharged, three blockers recorded

**Discharged.** `the_char_edge_round_trips` (stage 3, gap 6) is now
`Boundary.lean`'s `theorem the_char_edge_round_trips (s : String) :
String.ofList s.toList = s := @String.ofList_toList s`, audited in
`Check.lean`. The general statement is core's own — no narrowing was needed
after all. The burn-down moved 52 → 51. What gap 6 still owes is the JSON half
and the newline half, and this session established *why they are hard*, which
is recorded as gaps 37–39 rather than left as unpriced prose.

37. **`Key.ofName?` is not invertible by the tactics that remain.** Gap 4's
    collapse — `the_command_path_writes_what_the_field_path_reads` — needs the
    shape inversion "`Field.Key.ofName? w = some k` → `w` is the literal
    spelling of `k`", because the skip branch of `setEstIn`'s induction
    (`viewEstKey` reading the *first* `.est` key) must show a non-`est:` word
    yields no `.est` key pair. Every route this session tried fails:
    `unfold at h` + `split at h` runs the deterministic `isDefEq` heartbeat
    budget (200 000 — `maxHeartbeats` does not raise it); a ten-deep `cases w`
    over the first character leaves false branches where `simp` makes no
    progress, because equality of the opaque `Char` constructor against a
    symbolic tail does not reduce. The in-package `cases hn : Key.ofName? k`
    uses all discharge the **none** direction from Bool hypotheses; none ever
    inverts the `some` direction. What closing this looks like — an explicit
    `ofName?` equation set, a `Decidable` instance over the 19 spellings with a
    proved characterization, or restructuring the induction so the skip branch
    never needs the word's shape — is a design choice with cost; gap 4's goal
    stays in `Goals.lean` and says so. No new gap is open for it: it is gap 4's
    blocker, named.

38. **Legacy `String.splitOn` does not reduce in the kernel, which prices
    gap 12's two goals.** `"a\nb".splitOn "\n"` is stuck to `rfl` and to
    `decide` (its `splitOnAux` walks `String.utf8BytePos`/`extract` over
    runtime-only byte offsets); `decide` on
    `"\n".intercalate ("a\nb".splitOn "\n") = "a\nb"` fails for the same
    reason, and `native_decide` is banned (R3). The modern `String.split c`
    *does* carry lemmas — `String.toList_split_intercalate` and friends prove
    the intercalate/split round trip down at the `toList` level — but the
    kernel's boundary uses `splitOn` nowhere today, so gap 12's honest closure
    is either stating both goals over `String.split '\n'` (a wire change the
    host must make too) or porting the `List (List Char)` version of that
    lemma to `splitOn` through a toList bridge nobody has written. This is the
    reason `joining_lines_is_injective`'s *refutation* is not a one-liner
    through `["a\nb"]` either: the negation quantifies over the same
    non-reducing function, so even a witness needs the bridge. `#eval` says
    what the VM computes; no kernel-level tactic does.

39. **`Lean.Json.parse ∘ compress` has no core lemma in either
    direction.** Probe against v4.33.1's environment: no
    `Lean.Json.parse_compress`, `compress_parse`, or equivalent exists
    (`unknownIdentifier`). So the JSON half of gap 6's goal — the fragment
    restriction `Goals.lean` anticipated — does not fall out of core the way
    the char half did; it needs the parser and printer reasoned about
    directly (a real, bounded job), or a proof carried in from upstream.
    Recorded so the next session does not re-probe for it.

**Owed by name (unchanged, and unchanged in kind).** The Rust/CLI half of
stage 3's acceptance — `cargo build` from clean over the restored workspace,
"full suite green", the CLI-level panic probe — is still owed, because this
checkout's `origin` carries only `rebuild-on-lean`: `git checkout main --
tm-core Cargo.toml Cargo.lock` is impossible here, `main`@`557a3d2` being
unreachable from this remote. On this branch the FFI suite (26 tests) and the
corpus ratchet (6 tests, `33/37 files and 4/5 whole plans`) are the whole of
the Rust-side evidence, and `main` as oracle remains unrun.

**One environment fix landed this session** (`0c3aaf7`): `tm-kernel-ffi`'s
`build.rs` now emits `-Wl,-rpath,<toolchain>/lib` for the binary and its
tests, so Linux test binaries find the toolchain's bundled `libc++`/`libunwind`
the way macOS's embedded `install_name` always did. `check.sh` is 7/7 on this
machine with it.

<!-- #### Stage-3 session 2026-09-09 (second block): gap 16's loader pair discharged.
     Whoever merges: this block adds no gap numbers; gap 16 itself narrows. -->

**Gap 16, two of three discharged (2026-09-09).** `the_loader_builds_sites_in_range`
and `the_loader_builds_oriented_demotions` are theorems in `Boundary.lean`,
proved from `buildEntities_spec` by casing the per-id filter list in the shape
`buildEntity_renders` started — no entity the loader builds can carry a site
outside `docs`, and no pair it builds can be oriented against its documents'
regions, because both facts are read off the placements the documents themselves
produced. Supporting lemmas proved alongside, all audited: `placement_doc_lt`,
`docRegion_loadCore_placement`, `siteInRange_loadCore`, `placement_bounds_pair`,
`entityInRange_loadEntity`, `demotionOriented_loadEntity`. `siteOutOfRange` and a
mis-oriented demotion are now unreachable *by proof* rather than by checking,
which is what gap 16 asked for on those two conjuncts.

What gap 16 still owes is the rank half — `the_loader_builds_a_normalized_plan`
stays in `Goals.lean`. It is not blocked in the sense gaps 37–39 are: the chain
runs from `buildEntities_spec` through `splitDoc` handing each line index to
exactly one of prose and items into the `(docRanks p k).Nodup` that the `decide`
in `normalized` eats, and it is ordinary List work sized at one sitting. It was
left standing so this block ships green.

Audit moves 1007 → 1015 with the eight new names; §6.3's three counts
(1015 audit lines / 1015 distinct names / 1015 attr-aware theorem declarations)
reconcile. Check 7's burn-down moves 51 → 49. `check.sh` 7/7; corpus unchanged at
`33/37 files and 4/5 whole plans`.

<!-- #### Stage-3 session 2026-09-09 (third block): gap 16 CLOSED.
     Whoever merges: this block adds no gap numbers. -->

**Gap 16 closed (2026-09-09).** The third conjunct, `the_loader_builds_a_normalized_plan`,
is a theorem in `Boundary.lean`: every plan the loader builds has distinct ranks
within each document, so `itemCheck: rankCollision` is now unreachable from a
request that loaded at all — a precondition by proof, not a fault to observe.
Three facts assemble it, all proved and audited:
`splitDoc_prose_nodup` / `splitDoc_items_nodup` / `splitDoc_slots_separated`
(`Plan.lean` — `splitDoc` hands each line index to exactly one reader);
`placements_slot_nodup` (`Boundary.lean` — no two request lines name one
(doc, rank) slot, by induction on the document list against the strict rank
order `splitDoc` maintains); and `store_lines_nodup` (`Boundary.lean` — the
store renders at most one line per slot: a lone entity renders one line, a pair
straddles two documents because `pairedEntity` refuses same-document pairs, and
`archive_elsewhere` is what makes the refusal the right fact). Supporting
infrastructure along the way: `render_nodup`, `flatMap_nodup_store`,
`Store.insert_dom`, `foldl_insert_dom_nodup`, `slots_nodup_of_nodup`,
`ranksIn_nodup_lines`, `getElem?_eq_some_of_lt`.

Audit moves 1015 → 1028 with thirteen new names; §6.3's three counts
(1028 / 1028 / 1028) reconcile. Check 7's burn-down moves 49 → 48.
`check.sh` 7/7; corpus unchanged at `33/37 files and 4/5 whole plans`.

The remaining STAGE 3 goals stand where the blockers record them: the two
`String.splitOn` laws on gap 38 (the legacy splitter does not reduce in the
kernel, and the negation witness needs the same bridge); the JSON edge on gap
39 (no `Lean.Json.parse`/`compress` round-trip lemma in core v4.33.1); the
gap-4 `est` goal on gap 37 (`Key.ofName?` is not invertible in the
`some`-direction — deterministic `isDefEq` timeout at nineteen literal branches,
and `Char` equality is opaque so even closed words fail `decide`); `cmdRank`/
`freshId` and their three laws, which are new commands rather than unproved
facts about existing ones; and `move_has_an_inverse_command`, whose expected
refutation waits on a `freshRank` analysis of what `move` writes.

<!-- #### Stage-3 session 2026-09-09 (fourth block): the L22 `freshRank` analysis,
     done; the refutation itself still stands in `Goals.lean`.
     Whoever merges: this block adds no gap numbers. -->

**L22, analysed (2026-09-09).** `move_has_an_inverse_command` waits on a
`freshRank` analysis of what `move` writes. The analysis is done and it has one
finding worth more than the remaining proof work. **The witness for the
refutation must have a line surviving in the origin file above the moved
item's rank.** `freshRank` is the maximum rank left in the file plus one, so on
a one-item file the vacated rank *reproduces itself*: move the item out, and
fresh rank of the origin is exactly the rank it left; a re-`move` back lands on
it and the composite *is* an inverse — entity bytes untouched by `move`, site
restored, docs field unchanged, so the plan equals the original. The
refutation therefore needs two item lines (or an item below any surviving
prose line) — which is exactly the fact `move_out_and_back_is_not_the_inverse`
already depends on, read from the other side: `freshRank_gt` is what makes the
fresh rank strictly greater, and it needs the surviving line. An undo built as
"apply the inverse command" is wrong on trees, but it would be *accidentally
right on some plans*, which is a worse thing to build against than an
unconditional no.

The remaining proof work is mechanical once framed: `inv (.move i n)` evaluates
to one of five command shapes, and each fails in one line of entity-level
argument — `drop`/`est`/`demote` change the status bytes or horizon of whatever
id they touch; a command touching a different id cannot restore the moved
site, because `Store.get` is a function and site equality injects out of the
`some`; and a `move` lands on `freshRank`, which `freshRank_gt` pushes strictly
past the surviving ranks, so it reaches neither the old rank (back) nor the old
document's index arithmetic (forwards). The general negation stays in
`Goals.lean` until that sweep is written; `move_out_and_back_is_not_the_inverse`
remains the compiled composite for the one shape it was stated about.

<!-- #### Stage-3 session 2026-09-09 (fifth block): the `rank` verb kernel-backed;
     L20a/L20b discharged; burn-down 48 → 46. -->

The sixth of §13's seven verbs is now real.  `tm rank ^id n` (§7.4: "line
order is your rank within a priority class") moves a line **within its own
file** — the verb `move` cannot express that, and the type says so: `cmdRank :
Id → Nat → Transform`, not a `Relocation`, because no `Dest` is demanded and no
file changes.  On the wire: `{"op":"rank","id":"m1","rank":10}`; the ops list
is now `move{id,doc} drop{id} est{id,min} demote{id,doc,period,grain?}
readopt{id,doc} rank{id,rank}` — six ops, `add{id? seed}` still owed.

New in `Cmd.lean`: `setRankE` (the entity transform — `lift` with the live rank
rewritten in place), `wf_setRank` (rank is invisible to `wf`: the predicate
speaks of *which files* hold an id's lines, never where inside a file a line
sits), `setRankE_idem` (L20a at entity level), `lift_ok_of_wf`, `mapAt_at`
(the forward success form of `mapAt` with the refinement kept — the inverse
reading is `mapAt_ok_shape`), `Store.set_same` and `planCore_set_same` (writing
back a found entity is the identity — the two no-ops L20a stacks).

New in `Boundary.lean`: `ReqCmd.rank`, its `parseCmd` case (wire field
`"rank"`), its `applyCmd` case (no `resolveDest` — there is no destination to
resolve), and the two laws themselves. They live in Boundary even though the
verb lives in `Cmd` for one mechanical reason: both read a successful
`cmdRank` through `mapAt_ok_shape`, and the import chain `Plan ← Cmd ←
Boundary` will not bend backwards.

- `rank_is_idempotent` (L20a). Ranking a line where it already is changes
  nothing: three stacked no-ops — `setRankE_idem`, `Store.set_same`, and
  `mapAt` handing back the very `WfPlan` it got.
- `rank_preserves_the_order_of_the_others` (L20b). Two items the command did
  not name read back entity-identical (`Store.get_set_other` twice), so their
  relative order survives automatically. The `hdoc` hypothesis is carried but
  never consumed: the order actually survives *across* files too, but the law
  plan §3.3 asked for is the per-file one, and proving less than the statement
  uses is honest where proving more than it states would not be.

**A success form is still owed.** There is no `cmdRank_succeeds` mirroring
`cmdMove_succeeds`: the wire `rank` is a user-chosen `Nat` (unlike `move`'s
`freshRank`), and discharging `itemsWf` of the post-state needs the
`PlanCore.lines` replacement lemma — README gap 11, unchanged. Both laws are
therefore *conditional* on `.ok`, which is exactly what `add_assigns_a_fresh_id`
does not need and `cmdRank_succeeds` does.

**Negative tests at the FFI** (`kernel.rs`: 26 → 29): a rank past the last line
relocates the line verbatim down the file; a rank already taken (the prose and
item ranks of a file share one index space — `rank m1 5` collides with the
item at 5) is refused `{"kernel":"badHorizon"}` with no documents in the
response at all, i.e. nothing was written; and `rank` twice is byte-identical
to `rank` once (the wire L20a).

`Check.lean`: 8 names under a fourth APPENDED banner; audit 1028 → 1036;
zero `sorryAx`. `Goals.lean`: the `cmdRank` provisional def and the two law
goals deleted; STAGE 3's header rewritten to record six of seven verbs and the
one provisional signature (`freshId`) left.  `Negative.lean` untouched.

Note for whoever writes the L22 negation sweep next: the `ReqCmd` shape list
in the fourth block ("five shapes") is stale as of this commit — `.rank` makes
it six. The freshRank argument covers `.rank` the same way: `rank` also cannot
restore a rank `freshRank` vacated, and it cannot restore a *document* either.

<!-- #### Stage-3 session 2026-09-09 (sixth block): `freshId` landed with L21
     proved; burn-down 46 → 45. Gap 13 annotated, unchanged in substance. -->

The last provisional signature of stage 3 is now a definition.  `freshId` and
its freshness law live in `Text.lean` next to the numeral round trip they
depend on — `digitsOf_injective` is `readNat_digitsOf` read backwards, and it
is what makes a search over rendered numerals a search over *numbers*: no two
candidates collide (`candidates_nodup`).

`freshId seed existing` takes the first of `digitsOf seed`, `digitsOf (seed+1)`,
… that no existing item claims.  §8.1's rule — "freshness must be a theorem,
not a retry loop" — is what the proof below satisfies: among
`existing.length + 1` distinct candidates, at least one escapes a filter over
`existing.length` claimed ids, so the `[]` branch of the `match` is
**unreachable by a consistent pair of inputs** and stands only because a
`match` must be total.  `add_assigns_a_fresh_id` runs the pigeonhole through
`List.Nodup.length_le_of_subset` for exactly that case split.

What this does **not** do is decide gap 13: §3.1 wants ids to be four
`[a-z0-9]` characters and the kernel's type does not say so.  The generator
emits digits, so it is consistent with the recorded resolution (weaken the
spec — digits are a subset of `[a-z0-9]`) and with no other; the shape choice
is still the human's.  An `add` verb — the `Seed`/`Repair` round trip, the
wire fields, the insert as a command — is therefore still owed, and its
success form would lean on gap 11 like `cmdRank_succeeds` does.

`Check.lean`: 3 names under a fifth APPENDED banner; audit 1036 → 1039; zero
`sorryAx`.  `Goals.lean`: the `freshId` provisional def and the L21 goal
deleted.  `Negative.lean` untouched.

<!-- ===================================================================
     APPENDED 2026-09-12 (stage-3 continuation session, rebuild-on-lean).
     Ledger repair after a 22-agent audit of 0c3aaf7..9840ea8: the proofs
     were confirmed sound and the prose stale.  Adds no gap numbers;
     supersedes earlier paragraphs by name, never by editing them.
     =================================================================== -->

## Stage-3 continuation 2026-09-12: the ledger repaired

**Gap 4 CLOSED (7af7f1a).** `Cmd.setEstE` is rewritten through the field
setter `Field.setEst` — the "restructure the induction so the skip branch
never needs the word's shape" escape route that gap 37 itself priced — so the
request path and `Core.est` share one reader pair, and
`the_command_path_writes_what_the_field_path_reads` is a theorem of
`Cmd.lean`, discharged from `Goals.lean` and audited.  The stage-one `Nat`
body survives as `setEstFoldE`, fold arithmetic off the wire (`demoteEst` is
its only caller), and L9/L10 — `set_is_not_silent`, `set_last_wins` — are
restated over `setEstFoldE`.  This supersedes, by name: the live gap-4
paragraph above ("Two readers of `est:` coexist … a live S2" — the command
path no longer reads through the stage-one reader, so the S2 is retired);
gap 37's closing clause ("gap 4's goal stays in `Goals.lean` and says so" —
it no longer does); and the law-table row "`edit est=v` ⟹ the view reads
`v`", whose cited theorems now state the *fold* setter's law — the wire law
is `the_command_path_writes_what_the_field_path_reads`.

**`add` LANDED (9840ea8).** All seven of §13's verbs are on the wire — `move
drop est demote readopt rank add` — with `kernel.rs` at 26 → 33 tests and
`Negative.lean` CHEAT 43 (the freshness door; its banner, missed at landing,
now stands over it).  Two corrections to that commit's message: `kerrName`
carries **six** strings (`occupied noSuchId notDemoted alreadyDemoted
badHorizon badItem`), not seven; and a command-path `badItem` reaches the
wire as `{"err":{"kernel":"badItem"}}` **only** — `firstItemFault` is a
loader-path field (the `itemCheck` diagnostic), so the host cannot print it
for a command refusal.  Also recorded here because it was documented nowhere:
the seed landed as a **per-add wire field** (`{"op":"add","seed":n,…}`)
rather than PLAN §3.4's request-level `Seed`/`Repair` round trip — a
deliberate, narrower shape.

**Owed theorems, by name.** `cmdRank_succeeds` and a Lean-level rank
*rejection* theorem — the taken-rank refusal ("the check bites", §5.8)
exists only as a Rust test today — and `cmdAdd_succeeds`: `add`'s three laws
are all conditional on `.ok`, and where `rank`'s omission was recorded in the
fifth block, `add`'s was not, until here.  CORRECTION to the fifth block's
pointer (the sixth repeats it): the "`PlanCore.lines` replacement lemma" it
says is missing **exists** — `lines_set` at Plan.lean:1588, landed
pre-baseline — and the right cross-reference is gap 17, not gap 11.  The
success forms are unpriced work, not blocked work.

**Gap 38, mechanism corrected.** `splitOnAux` (toolchain
Init/Data/String/Legacy.lean:61) is defined by **well-founded recursion** —
`termination_by` over byte distances — and WF fixpoints are stuck at
`Acc.rec` in the kernel; that is why nothing reduces.  `String.utf8BytePos`,
which gap 38 cites, does not exist in v4.33.1.  And a **third** closure route
gap 38 did not price: the kernel's own structural `Tm.splitOn` (Text.lean:659)
with `splitOn_joinWith` (Text.lean:706) already proved and already on the
wire path — Line.lean rewrites through it at 1789/2127/2234 — so gap 12's
goals can be stated over the kernel's splitter with no wire change and no
toList bridge.

**Gap 39, addendum.** The general statement is also suspect at `Json.obj`:
`Json` equality is structural over the underlying `RBNode` and `parse`
rebuilds objects by insertion, so `parse (compress j)` can return a
differently-shaped, semantically-equal tree.  The honest narrowing of
`the_json_edge_round_trips` is the run-emitted fragment or an
up-to-equivalence relation — not only the `JsonNumber` restriction its doc
comment anticipated.

**L22, analysis corrected (supersedes that part of the fourth block).**
`move_out_and_back_is_not_the_inverse` computes `freshRank` on the
**pre-move** plan and feeds `freshRank_gt` the moved item's **own** line
(Boundary.lean:925–931) — it needs no surviving line in the origin file.  The
fourth block's "the witness must have a line surviving above the moved item's
rank" is therefore wrong of the compiled composite: the surviving-line
witness is **sufficient, not necessary** (sparse ranks also break the
accidental inverse), and "a one-item file reproduces the vacated rank" holds
only when that rank is exactly `docProseMax + 1`.  The negation sweep is
still the remaining work, and its shape count is seven now — `.add` cannot
restore a moved site either, since it may only insert a fresh id.

**Gap 13 stands open.** `add` shipped digit ids — consistent with the
recorded resolution (weaken the spec: digits are a subset of `[a-z0-9]`) and
with no other — but the id-*shape* decision is still the human's; nothing in
this session or the two before it takes it.

Measured at this commit: burn-down 44 (`grep -c ^theorem Goals.lean`); audit
1051 lines / 1051 distinct names / 1051 attr-aware theorem declarations
(§6.3's three counts reconcile); `kernel.rs` 33 tests; no goal discharged and
no theorem added by this block — it is a documentation repair.

**Owed theorems, LANDED (supersedes "Owed theorems, by name" above).**  All
three sit at the end of Boundary.lean, so every Boundary line number this
block cites stays true.  §5.8's bite for `rank` is
`rank_onto_a_taken_rank_is_refused`: an occupant of `⟨doc, n⟩` anywhere in
`p.val.lines` (what reaches the disk, §5.9) carrying another id survives the
single-entity swap (`lines_set`) and collides with the rewritten live line, so
`mapAt`'s re-check finds `Normalized` false and the verb is `.error
.badHorizon` with nothing written — the Lean form of kernel.rs's
`rank_onto_a_taken_rank_is_refused_and_writes_nothing` (`^t3`'s rank 5).
`cmdRank_succeeds` (plus the wire wrapper `applyCmd_rank_succeeds`) mirrors
`cmdMove_succeeds` on `lines_set`/`normalized_set`, exactly as the corrected
pointer above says it could: the honest hypotheses are the two freshness facts
(`hlines` — any plan line already at the target site is the item's own, which
keeps L20a's re-rank a success; `hprose` — no prose line owns the rank) and
`itemsWfButRanks` of the post-state, because a rank rewrite can genuinely
break `sectionsWf` by ranking a day-file line out of `# Pinned`.
`cmdAdd_succeeds` needed the insert-shaped replacement lemma `lines_set`
cannot supply — `lines_insertFresh` (the domain grows; the new render block
lands in front, verbatim) — plus `normalized_insertFresh_of_fresh`,
`add_at_freshRank_normalized`, `sitesInRange_insertFresh` and
`demotionsOriented_insertFresh`; `docsWf` and `pathsDistinct` transfer because
the insert does not touch `docs`.  What stays a hypothesis is
`itemsWfButRanks` of the inserted state — the day-file refusal
(`add_outside_a_day_files_pinned_section_is_refused_by_name`) goes through
exactly that check, so discharging it outright would prove a false theorem.
Satisfiability of each hypothesis set is a running FFI test:
`rank_moves_a_line_within_its_own_file` (rank 10),
`add_inserts_a_fresh_id_into_the_requested_file`,
`two_adds_in_one_request_get_two_ids_and_two_ranks`.  The stale "still owed"
sentence in `cmdRank`'s doc comment (Cmd.lean) now points at the landed pair
instead.  Re-measured after this landing: burn-down 44, unchanged — these
were convention debt, never `Goals.lean` entries; audit 1061 lines / 1061
distinct names / 1061 attr-aware declarations (ten new under Check.lean's
`APPENDED 2026-09-12` banner: the three owed forms, the wire wrapper, and six
supporting lemmas); `check.sh` 7/7; `kernel.rs` 33 tests, unchanged.
One §5.8 direction for `add` stays generic, and is owed **by name** rather
than by implication: the compiled bites are `insertFresh_rejects` (the
`planWf`-level refusal) and the five parse-level title refusals; the
command-shaped `itemsWf` bite — `applyCmd (.add …)` on a day file outside
`# Pinned` is `.error .badItem` — has no Lean theorem, and its evidence
today is the Rust test `add_outside_a_day_files_pinned_section_is_refused_by_name`.
Read d0aced9's subject line ("bite and success, both directions") with that
scope: both directions are compiled for `rank`; for `add` the bite is
parse-level and `planWf`-generic only.

**L22 DISCHARGED — refuted, and the sweep is compiled.**  The `Goals.lean`
entry `move_has_an_inverse_command` (an expected refutation) is **renamed to
its negation** and proved: `move_has_no_inverse_command` (end of
Boundary.lean) — there is no `inv : ReqCmd → ReqCmd` that maps every
successful `move`'s post-plan back to its pre-plan, quantifier for
quantifier the negation of the stated law.  This supersedes, by name, the
fourth block's closing sentence ("the general negation stays in `Goals.lean`
until that sweep is written" — it no longer does) and compiles the corrected
analysis above: the witness (`undoWitnessRequest`/`undoWitnessPlan`, a
decided `loadPlan` witness like `sampleRequest`) carries `^m2` surviving at
rank 2 above the rank 1 that `^m1` vacates, and `inv`'s single answer to
`.move ^m1 1` is cased over all **seven** `ReqCmd` shapes, each refuted on
one observable — off-target ids leave the moved site standing (`Store.get`
is a function); `drop`/`est` keep the moved site; `rank` keeps the document;
`readopt` refuses a live record (`notDemoted`); `demote` writes a tombstone
the pre-plan does not carry; `add` grows `store.dom` by one; and a `move`
back lands on `freshRank`, pushed past `^m2`'s rank by `freshRank_gt`
(2 < 1, absurd).  The consequence is the one the plan already words: **`tm
undo` must replay the log, never apply an inverse command** — and it is now
a theorem, not a policy.  No predicate was weakened; the goal is deleted
from `Goals.lean` per §3.2.  Re-measured at this landing: burn-down **43**
(`grep -c '^theorem' Goals.lean`); audit 1063 lines / 1063 distinct names /
1063 attr-aware declarations (two new under the `APPENDED 2026-09-12`
banner: `the_undo_witness_loads`, `move_has_no_inverse_command`);
`check.sh` 7/7 (corpus 33/37 files, 4/5 whole plans, unchanged);
`kernel.rs` 33 tests, unchanged.  Adds no gap numbers.

**Gap 12's two goals DISCHARGED — at the char representation.**  The
`Goals.lean` pair quantified over legacy `String.splitOn`, which is
kernel-stuck (gap 38, with this block's mechanism correction), and the
audited third route above is the one taken: the kernel's own structural
`Tm.splitOn` with the join it already owns.  Two theorems land at the end of
`Text.lean`'s splitter section, both audited under Check.lean's `APPENDED
2026-09-12` banner.  `a_file_splits_into_the_lines_it_was_joined_from_char`
(via the general `joinWith_splitOn`): `joinWith '\n' (splitOn '\n' cs) = cs`,
**unconditional**, by structural induction — note it is the *other*
composition than `splitOn_joinWith`, which needs the no-separator hypothesis;
split-then-join needs none because splitting manufactures groups that cannot
hide the separator.  `joining_lines_is_not_injective_char` is the expected
refutation **renamed to its negation** per §3.2: `∃ gs, splitOn '\n'
(joinWith '\n' gs) ≠ gs`, witness `[['a','\n','b']]`, closed by `decide`
since everything is structural.  The ledger move, loudly (§3.1 item 4): the
`String.splitOn`-level statements are **deleted from `Goals.lean` and not
restated** — the legacy splitter does not reduce in the kernel and no kernel
code path consumes it, so a String-level goal would defend a function the
kernel neither runs nor can compute with; the char level is where
`mkDoc`/`renderDocAt` actually operate.  What that leaves as an obligation is
**host agreement**, named: Rust's `split('\n')` in `tm-kernel-ffi` must
compute what `Tm.splitOn '\n'` computes, and the FFI corpus tests are its
evidence, not a proof.  Edge semantics were checked, not assumed (all by
`#eval` against the built library): `Tm.splitOn '\n' [] = [[]]`, agreeing
with Rust's `"".split('\n')` = `[""]` — **no disagreement at the empty
file** — and leading / trailing / double newlines produce the same empty
segments on both sides (`"\na"` → `[[],['a']]`, `"a\n"` → `[['a'],[]]`,
`"a\n\nb"` → `[['a'],[],['b']]`).  The one asymmetry worth a sentence:
`joinWith '\n' [] = [] = joinWith '\n' [[]]`, so `joinWith` conflates the
zero-group list with the one-empty-group list — harmless because `[]` is
outside `splitOn`'s image (`splitOn_ne_nil`) and no host `lines` result is
empty.  The boundary decision gap 12's refutation has always pointed at —
reject or escape a request line carrying a literal newline — is still open
and still gap 12's live remainder; this discharge prices it, it does not
take it.  Re-measured at this landing: burn-down **41** (`grep -c '^theorem'
Goals.lean`); audit 1066 lines / 1066 distinct names / 1066 attr-aware
declarations (three new: `joinWith_splitOn`,
`a_file_splits_into_the_lines_it_was_joined_from_char`,
`joining_lines_is_not_injective_char`); `check.sh` 7/7; `kernel.rs` 33
tests, unchanged.  Adds no gap numbers.

**Gap 39 REPRICED — the JSON edge is opaque, not hard, and both routes the
ledger priced are closed.**  Probed v4.33.1's own source ahead of the
attempt (`Lean/Data/Json/{Printer,Parser,Basic}.lean` in the toolchain
tree): `Json.compress` and `Json.render` are `partial def`s, and so is
every recursive worker of `Json.parse` — `Parser.strCore`, `natCore`,
`natCoreNumDigits`, `arrayCore`, `objectCore`, `anyCore` — plus
`JsonNumber.countDigits` and even `Json`'s `BEq` worker `beq'`.  That is
not gap 38's kind of stuck: a well-founded definition still carries
propositional equation lemmas the kernel accepts, while a `partial def`
elaborates to an opaque constant whose logical value is *unconstrained by
the compiled code* — no equations, nothing to unfold, nothing
`simp`/`decide`/induction can touch.  Measured, not assumed (probes against
the built library, transcripts paraphrased per §5.11): `rfl` fails on
`Json.compress Json.null = "null"` — the simplest possible instance — with
`compress` stuck as a term; `Json.compress.eq_def` exists but rewrites one
step to the **private** partial worker `compress.go`, a daggered name this
package cannot even mention, beneath which no equation exists;
`Json.Parser.strCore.eq_def` is an unknown constant; `simp [Json.parse]`
stalls at Parsec iteration over `String.Iterator` byte offsets — gap 38's
mechanism, one level down.  Consequence, stated plainly: **the goal
`the_json_edge_round_trips` can be neither proved nor refuted here** — the
behaviour of `Json.parse ∘ Json.compress` is a property of compiled code,
exactly the layer R3 exists to distrust, and `native_decide`, the one
tactic that can see that layer, is banned.  Every narrowing still worded
over the toolchain pair inherits the same fate: the fragment restriction
the goal's doc comment anticipated, and the up-to-equivalence variant this
block's own addendum priced.  This supersedes, by name: gap 39's closing
route ("it needs the parser and printer reasoned about directly (a real,
bounded job)" — there is nothing to reason about; that route is
impossible, not bounded), and one detail of this block's "Gap 39,
addendum": v4.33.1's `Json.obj` carries a `Std.TreeMap.Raw String Json`,
not an `RBNode` — the insertion-rebuild hazard it describes survives with
the structure renamed.  Two VM-level facts sharpen the picture, and
neither can be promoted to a theorem (all by `#eval` against the built
library): the general statement is **false** — `Json.num ⟨100, 2⟩` (the
number 1.00) compresses to `"1"` and re-parses as `⟨1, 0⟩`, structurally
distinct — while the emitted fragment looks healthy (`Nat` literals and
the `ok`/`err` object shapes with an escaped-string payload re-parse
`beq`-equal).  So §3.2's rename-to-negation route is closed too: the
refutation quantifies over the same opaque constants.  **The honest route
is gap 12's pattern one level up**, priced now so the next session starts
at the lemma list, not the probe: (J0) a kernel-owned fragment type
`JVal` — `str (List Char) | num Nat | arr (List JVal) | obj (List ((List
Char) × JVal))`, objects as ordered assoc lists, so the tree-rebuild
hazard vanishes by construction; (J1) structural `jescape`/`junescape` at
the char level, mirroring the printer's escape classes (`"`, `\`, `\n`,
`\r`, `< 0x20` as `\uXXXX`, all else verbatim), with `junescape_jescape :
junescape (jescape s ++ '"' :: rest) = some (s, rest)` — the crux:
induction on `s`, one case per class, carrying a hex-quad render/parse
round trip in `digitsOf`'s reducing style (Text.lean owns the technique);
(J2) `parseNat (renderNat n ++ rest) = some (n, rest)` for `rest` not
opening with a digit — a real guard, discharged at each use site, where
the next byte is `,`, `]` or `}`; (J3) `jemit : JVal → List Char`,
compress-shaped; (J4) a fuel-structural `jparse` with fuel := input
length so it reduces, and `jparse_jemit : jparse (jemit v ++ rest) = some
(v, rest)` for **all** `v`, by the nested induction `JVal` needs under
its `List`s; (J5) the wire change — `run` builds `JVal` and `call`
returns `String.ofList (jemit r)`, after which Lean's `compress` leaves
the output path the way legacy `String.splitOn` left the split path.
Byte note for J5, measured: `mkObj` emits keys sorted (`compress` of a
`b`-then-`a` build prints `a` first), an assoc list keeps build order —
so either list fields pre-sorted and keep today's bytes, or accept a
reorder that serde_json-level assertions (kernel.rs asserts through
parsed values) never see; measured at J5, not assumed.  (J6) the
discharge, `the_response_run_emits_parses_back`, unconditional over
`JVal` — the narrowing lives in the type, which is the license the
goal's doc comment grants.  What stays evidence rather than proof is host
agreement, and it is the *only* agreement that was ever real: serde_json —
not Lean's `parse`, which never sees `call`'s output in production — is
the reader of these bytes, and kernel.rs's 33 tests plus the corpus's 6
exercise exactly that.  Size, priced against the splitter work: J1 is
Text.lean's splitter section again (≈300–500 lines with the `\u` branch),
J4 the largest single proof (≈400–700), J2/J3/J6 small, J5 touches
Boundary.lean's response builders plus an FFI re-measure — two to three
sessions, not one.  The goal therefore **stands** in `Goals.lean` (§3.1
item 6; its doc comment now points here), no predicate was weakened, no
theorem lands, `Check.lean` is untouched — the omission is this
sentence — and `Negative.lean` is untouched.  Re-measured at this landing:
burn-down **41**, unchanged (`grep -c '^theorem ' Goals.lean`); audit 1066
lines / 1066 distinct names / 1066 attr-aware declarations, unchanged;
`check.sh` 7/7 (corpus 33/37 files, 4/5 whole plans, unchanged).  Adds no
gap numbers; takes no cheat numbers.

**The edit verb widened: nine keyed fields on the wire, one reader end to
end.**  Same 2026-09-12 session, edit-widening block.  The wire gains one op:
`{"op":"edit","id":"t3","key":"pref","value":"07:30"}` — `key` is any spelling
`Field.Key.ofName?` accepts (so `cap` and `max` are one key, and the write
always lands as `max:` — `set_max_writes_max`), `value` is the raw text of the
field's value exactly as it would stand on the line, and an **empty** `value`
is the unset form `tm edit ^id <key>=`.  The standing `est` op is untouched on
the wire and is now *definitionally* the keyed edit at `est`
(`the_est_op_is_the_keyed_est_edit := rfl`), so the two can never drift.
§5.3's discipline, in both directions: the value is parsed by the same
`Field` parser the loader's view for that key binds (`editValOf`, one table;
`ndDur?_is_parseDurND` pins the est/dur branch to the loader's own
`parseDurND`), and the accepted value is written by the same Line.lean setter
whose `view ∘ set = id` proof stands (R11) — so what lands on the line is the
field's **canonical rendering** of the parsed value (`est=045m` writes
`est:45m`; a value that only round-trips up to normalisation is normalised at
the write, never re-encoded by a second grammar).  Wired keys, chosen by
value-grammar simplicity and §4.1 usage: `est`, `dur`, `buffer`, `pref`,
`on-miss`, `after-done`, `min`, `max`, `ci`.  Refusals are named at the tier
they occur (§5.7): `unknownKey <k>` / `keyNotWired <k>` / `badValue <k>` ride
`parseCmd`'s free-text `err` exactly as `add`'s five title refusals do
(`parseCmd_rejects_edit_variants` — `badValue ci` at `7` is the `Fin 6` smart
constructor biting through the wire, `badValue est` at `3d` is `NdDur`
refusing a day-carrying estimate, both R10); `tabbedLine` and `keyAbsent` are
new `KErr` names on the command path.  Both §5.8 directions at every tier:
entity (`editE_ok_of_tabless` / `editE_refuses_a_tabbed_line`,
`unsetE_ok_of_present` / `unset_of_a_key_the_line_does_not_carry_is_refused`),
dispatch (`applyCmd_edit_succeeds` / `applyCmd_est_succeeds` /
`applyCmd_unset_succeeds`, each with the honest `itemsWfButRanks` hypothesis
`cmdRank_succeeds` modelled, and `Normalized` discharged outright by
`normalized_after_edit` since an edit moves no placement), and the gap-4 shape
generalised: `the_edit_path_writes_what_the_field_path_reads` — one theorem
over all nine constructors, `Core.est` for C1's slot pair, `Core.ci` for
C2's, no hypothesis on the entity's other bytes;
`the_unset_path_removes_what_the_field_path_reads` is the removal half; and
the dispatch table itself cannot hide a C1 (`setVal_writes_the_token_the_
loader_reads` and `editValOf_key`, both generic over keys).

**Gap 32, narrowed on the whole edit path — and the est op's standing
exposure repaired.**  `Text.isSp` is space-only, so a tab is a word character
to this kernel and whitespace to the shipped Rust tokenizer: on a line with a
tab before a repeated `est:`, Rust's `tm edit est=45m` writes the *first*
`est:` and this kernel would write the *second* — the S2 shape, in the one
shipped operation.  The sanctioned narrow route is taken: **every** edit-path
command (`edit`, unset, and the already-shipped `est` op) refuses a line whose
raw bytes contain a tab — indent, any separator, any word (`lineHasTab`) —
loudly and by name, `{"err":{"kernel":"tabbedLine"}}`.  The check bites
(`edit_of_a_tabbed_line_is_refused`, `est_of_a_tabbed_line_is_refused`,
`unset_of_a_tabbed_line_is_refused`), it is not vacuous
(`the_tab_guard_is_not_vacuous`: a week file whose item line carries a tab
inside a word loads whole and trips the guard, by decision), and the
complement holds (a tabless line is never refused on that ground —
`editE_ok_of_tabless` and the three `applyCmd_*_succeeds` forms).  Routing
the `est` op through the guard is a **behaviour change to a shipped op, on
the refusal side only**, recorded here loudly: before, `est` on a tabbed line
wrote against the wrong token reading; now it refuses.  Re-measured after the
change: corpus ratchet unmoved (check 6: 33/37 files, 4/5 whole plans — the
corpus is tabless, as check 6's stability confirms), and all 33 pre-existing
FFI tests pass unchanged (40 total now; the 7 new ones are kernel.rs's
edit-widening block, `edit_keyed_pref_writes_through_the_field_grammar`
through `unset_of_a_key_the_line_does_not_carry_is_refused`).  Gap 32 itself — `isSp`, the 1,049 of 2,048 generated lines that
are silently prose — **stays open**: widening `isSp` is a grammar-wide
behaviour change and remains plan-tier.

**Gap 40 (edit): nine of the eighteen keys are deliberately not wired.**
Continues the single gap sequence; 37–39 are above.  `keyEditable` is false,
`editValOf` parses nothing (`editValOf_refuses_unwired_keys`), and the wire
refusal is `keyNotWired <k>`, for: `due`, `at`, `win`, `every`, `on-event`,
`after`, `loc`, `waiting` — each has its setter and `view ∘ set = id` proof
in Line.lean, but that proof carries a wf hypothesis (`Moment.wf`,
`intervalWf`, `windowWf`, `Rule.wf`, `OnEvent.wf`, `depsWf`, `Loc.wf`,
`dayWf` respectively) and the **parse ⇒ wf bridge lemma does not exist yet**
(for the date-carrying ones it reduces to a `readNat` width bound threaded
through `mkDate?`/`ofDay_toDay`; for `after` it also owes an honest success
form against `afterTotal`/`afterAcyclic`, which a dangling `after:^…` really
does break).  Exposing one without its bridge would mean either shipping the
setter with no success theorem or re-encoding the value grammar at the
boundary — the two failure modes this widening exists to rule out.  And
`demoted` is not deferred but **excluded by policy**: `demoted:` stamps are
lifecycle state that `demote`/`readopt` own (`demote_stamps`,
`readopt_keeps_stamps`); an edit that could forge or strip a stamp would
bypass the demotion story, so `EditKey`'s bound keeps it off the wire
(Negative.lean CHEAT 45 is that door staying shut).

**Gap 41 (edit): unset of `est` or `ci` clears the key slot only.**  `est:`
overrides the leading estimate and `ci:` the positional digit (C1/C2), so
after `{"key":"est","value":""}` the view falls back to the leading estimate,
and after unsetting `ci:` to the positional digit — Line.lean states both
rather than fixing them (`unset_ci_key_leaves_the_positional_digit`, and
`viewRemainingDur`'s fallback).  A host that means "no estimate at all" must
know the lead slot survives; a complete `--unset` has to clear both slots,
and that is a decision about line surgery on the *positional* grammar, not
taken here.  Numbers, re-measured at this landing: `check.sh` 7/7; audit
**1090** lines / 1090 distinct names / 1090 attr-aware declarations (was
1066; +24, all under the 2026-09-12 banner's edit-widening block in
Check.lean); burn-down **41**, unchanged — this scope item owned no standing
goal and admits no new one; Negative.lean takes CHEATS **44–46** (Fin 6
bypass, unwired-key bypass, day-carrying `NdDur`) under their own banner;
FFI 33 → **40** tests, corpus 33/37 files and 4/5 whole plans, unchanged.

**`main` DISCARDED — an owner decision, recorded 2026-09-12.** The owner has
ruled `main` obsolete — its Rust kernel is superseded by the Lean one — and it
will not be pushed to this remote (`origin` carries `rebuild-on-lean` alone;
`main@557a3d2` was never here). What that discards and what survives, by name:

- **Survives, in this clone's own history.** `rebuild-on-lean` forked from
  `main`, so the pre-fork workspace stands at `4748911` (the parent of
  `6d9b1ba` "Remove the Rust kernel in favour of the Lean one"): all seventeen
  `tm-core` modules, the root `Cargo.toml`/`Cargo.lock`, and the full test
  suite — `grammar_proptest.rs` and `planner_invariants.rs` included, the two
  harnesses the L24/L25 recommendation keeps. Stage 3's restore instruction
  becomes `git checkout 4748911 -- tm-core Cargo.toml Cargo.lock`.
- **Discarded: stage 0's fix.** `4748911` predates the `move_to` precondition
  (`fn destination` — zero hits there), so the restored Rust carries the A6
  hole. The two verbs the 426-pair sweep proved reach it — `move` (400) and
  `readopt` (26) — are exactly the verbs stage 3 kernel-backs, where
  `occupied` is a constructor obligation; until that wiring lands, the
  restored binary is pre-stage-0 and must not be driven as if it were `main`.
- **Discarded: `invariant_exhaustive.rs`.** The 199-command sweep harness
  lived only on post-fork `main`. §9.1's depth-3 gate is now gated on a
  harness that must be rebuilt, not merely run; the depth-2 numbers
  (426/39,601) stay historical, measured on a commit this repository no
  longer holds.
- **Degraded: the oracle.** §7.3's `run-oracle.sh` extracts `main`; it must
  move to `4748911`, and stage 5's parity acceptance compares against the
  fork-point grammar — the named delta to `557a3d2` is stage 0 alone, as far
  as this repository can know. "No disagreement" claims quote the fork point
  from now on.
- AGENTS.md's "`main` is the oracle" instructions are historical from this
  block forward; this paragraph supersedes them by name.

**The workspace is restored — stage 3 scope item 1, landed 2026-09-12.** Per
the `main`-discard decision above, the restore ran as that block prescribes:
`git checkout 4748911 -- tm-core Cargo.toml Cargo.lock`. The branch's `tm/`
differed from the fork point only by its own `DORMANT.md`, whose text now says
the workspace is restored and the rewiring is underway; every other file is
byte-identical to `4748911`. On this Linux machine the root workspace builds
clean and needed **zero portability fixes**: `cargo test --workspace` is
**943 passed / 0 failed / 0 ignored across 61 test binaries** — no semantic
exceptions, so no `#[ignore]` was spent (`main@557a3d2`'s advertised 957
included the post-fork sweep harness this clone no longer holds). The binary
runs: `tm init --example` writes 22 files and exits 0; `tm check` on that tree
prints `no problems` and exits 0. **The restored binary is pre-stage-0**: as
recorded above, its `move_to` lacks the destination/occupied precondition, so
A6 is open in Rust until the kernel-backed `move`/`readopt` wiring lands —
that wiring, not a Rust patch, is the fix. The root workspace (members
`tm-core`, `tm`) and `kernel/tm-kernel-ffi` coexist without exclusion —
the ffi crate's own `[workspace]` table keeps the deliberate separation
(AGENTS 2.2), and cargo raised no nesting complaint. No new external
dependency entered (R7): every crate in the restored lockfile is the fork
point's own. `check.sh` re-measured after the restore: **7/7 ok**, corpus
33/37 files and 4/5 whole plans, unchanged.

**The five lifecycle verbs are kernel-backed — A6 is dead in the shipped
binary (same 2026-09-12 session, stage-3 wiring block).**  `tm move`,
`tm drop`, `tm edit est=` (the est op, alone on the command line),
`tm demote` and `tm readopt` now run through the Lean kernel; everything
else (`close`, `plan`, `review`, `recur`, `check`, the TUI's own screens,
`rank`, `add`, the keyed `edit`/unset forms) stays on the old Rust path this
step.  The wiring is **one choke point**, `tm/src/cli/kernel_bridge.rs`:
read every plan file through the store with its §1.3 guard
(`FsStore::read_guarded`, new in `tm-core/src/store.rs`) → resolve horizon
words to paths and generate each document's `grain`/`ix` **in the host**
(gap 10's recorded stance; the numbers are the kernel's own — 2026-W37 is
`(1, 105695)`, month `12·(year−1)+month−1`, day = days since 0001-01-01 — a
compiled test, `regions_are_the_kernels_numbers`) → one
`{"docs":[{path,grain,ix,lines}],"cmds":[…]}` request → one
`tm_kernel_ffi::call` → write only the changed documents back atomically
with the read-time guard still enforced (`FsStore::write_guarded`: mtime +
content hash, no retry — a racing writer is the §1.3 conflict, exit 3,
nothing clobbered).  The response's `grain`/`ix` are **carried, not
dropped** (AGENTS 8.1's named trap): every returned document's region is
kept on the bridge's `BridgeDoc` and verified against what was declared, and
an echo that dropped or moved one refuses to write at all.  Every kernel
refusal reaches the user **by name** — `occupied noSuchId notDemoted
alreadyDemoted badHorizon badItem tabbedLine keyAbsent siteOutOfRange dupId
notADemotion ambiguousDemotion duplicatePath badLine itemCheck`, re-derived
from `Boundary.lean` (note `kerrName` now carries **eight** strings; the
2026-09-12 ledger's "six" predates the edit widening's `tabbedLine` and
`keyAbsent`) — in the human line (`tm: kernel refusal: occupied — …`) and
in the `--json` document (`kind:"kernel"`, `detail.refusal:"occupied"`;
exit code 1, the CLI's ordinary-error discipline — this CLI reserves 2 for
`tm check`'s return and 3 for write conflicts, so refusals are 1 on
purpose).  R7: `tm` gained `tm-kernel-ffi = { path = "../kernel/tm-kernel-ffi" }`
— **in-repo, not a new external dependency**; the root lockfile's only new
entry is the path crate itself (its `cc` build-dep was already present).
Two build-system facts, recorded: the root `Cargo.toml` now carries
`exclude = ["kernel/tm-kernel-ffi"]` — once the path dependency exists,
cargo refuses two nested workspace roots, so this **supersedes, by name**,
the restore paragraph's "coexist without exclusion … no nesting complaint"
sentence; and `tm/build.rs` (new) adds the Lean toolchain `lib/` rpath to
the `tm` binary and test harnesses, because a dependency's
`cargo:rustc-link-arg` does not propagate (without it the binary dies at
startup on `libc++.so.1`).  What stays old-path *inside* the five verbs, by
name: id-less routine/optional/inbox lines (the kernel cannot address a
line with no `^id` — gap 5), and `tm edit` invocations that are not exactly
one `est=` pair.

**Behaviour changes, each observable and each refused loudly — recorded,
not absorbed** (the tests updated to the new behaviour cite this block):

- *(a) Kernel-backed verbs demand a loadable tree.*  A duplicate id, an
  itemish line that does not parse, an unordered demotion pair, or a
  non-UTF-8 plan file anywhere in the tree refuses the verb by name
  (`dupId`/`notADemotion`/`badLine`/`itemCheck`/`ambiguousDemotion`…), even
  when the verb's target is a different item in a different file — the old
  path edited its one line and left the corruption standing.  Compiled:
  `a_kernel_backed_verb_refuses_an_unloadable_tree_by_name` (two same-file
  duplicates are `dupId`; two cross-file live lines are `notADemotion`, the
  loader refusing to read them as a demotion).
- *(b) The headline: `move`/`readopt` refuse tombstone collisions —
  `occupied` — so the duplicate-id class (six catalogued defects, five
  patched entrances, one hole) is dead in the shipped binary.*  On a fresh
  `tm init --example` tree, `tm move ^m2 month` — the demoted milestone
  into its own record's file, the single-command A6 reproduction — now
  exits 1 with `occupied` and writes nothing, where the restored
  pre-stage-0 `move_to` silently appended the second line.  Compiled:
  `move_into_the_tombstones_file_is_refused_by_name`,
  `a_kernel_refusal_is_a_named_document`.  Three siblings of the same
  shape: `tm readopt` of §4.3's shipped live-beside-record pair (`^m2`) is
  `notDemoted` where the old path *absorbed* the record into the live line
  (`readopt_into_another_horizon_leaves_the_tree_valid` now asserts the
  refusal; the dup-id hazard it used to guard is gone by refusal); a second
  `tm demote` of an id with a standing record is `alreadyDemoted` where the
  old path overwrote the record
  (`demote_with_a_standing_record_is_refused_by_name`); and a real
  demote-then-readopt round trip removes the tombstone, so the same-week
  readopt leaves one line with no CLI-side stale-copy cleanup
  (`readopt_brings_a_demoted_line_back`, rewritten over a real demotion).
- *(c) `tm edit est=` refuses tabbed lines by name* (`tabbedLine`, gap 32's
  guard, recorded kernel-side in the edit-widening block above — now it
  reaches the shipped binary: `est_edit_of_a_tabbed_line_is_refused_by_name`).
- *(d) Placement and rendering drift the suite caught, kept as designed and
  the tests updated to cite this block.*  (1) The kernel places a relocated
  line itself, at a fresh rank — the end of the destination file; there is
  no section parameter on the wire, so `tm move --section` is refused with
  a message pointing here, and `tm move ^id day` is refused `badHorizon`
  whenever `# Pinned` is not the day file's last section (§6.2 constrains
  day items to `# Pinned`; the shipped day file ends `## Log`/`## Notes`) —
  `move_to_a_day_is_refused_by_name`, was `move_to_a_day_pins_the_line`.
  (2) `tm demote` writes the copy at the end of the month file (inside the
  fixture's trailing `# Demoted`; a *bare* month file gets the copy with no
  heading created) and **no longer computes a remaining onto the copy** —
  the copy carries the line's own `est:`/leading estimate, and `est_min`
  now reports exactly that (fixture values unchanged: `^m4` → 120, post-edit
  `^t3` → 180).  (3) The est op always writes the **`est:` token** in the
  field's canonical minutes rendering (`est=3b` → `est:180m`; a line
  without `est:` gains one — the old path rewrote the *leading* estimate
  there, and the leading slot is now never invented or rewritten:
  `edit_est_moves_the_remaining_estimate_not_the_one_as_written`,
  `edit_est_reaches_a_line_with_no_positional_slot`,
  `edit_unset_removes_a_key`).  (4) `tm/templates/skills/plan-week.md`'s
  fenced `tm readopt ^m2 --to week` example moved to prose with the
  `notDemoted` rule stated, since on the example tree it is now a refusal
  (`every_documented_command_runs` enforces fenced commands run), and its
  snapshot `init_tree__skill_plan_week` was re-blessed;
  `cli_items__readopt_json` (a snapshot of the absorb behaviour) is
  deleted with its test's rewrite.

Re-measured at this landing: `cargo test --workspace` **950 passed / 0
failed / 0 ignored across 61 binaries** (was 943 at the restore; the delta
is the new bridge/refusal tests net of the rewrites); `kernel/check.sh`
**7/7 ok**, corpus 33/37 files and 4/5 whole plans, burn-down **41**, audit
1090 — all unchanged (no Lean source was touched).  Still owed from stage
3's scope, by name: the CLI wiring of `rank` and `add` and the keyed
`edit`/unset ops onto the same choke point (the kernel wire already carries
all of them); the panic probe (layer 3 exists in `lib.rs`; the probe and
the layer-2 stderr `dup2` do not); and the four integration-bug
countermeasures of AGENTS 8.1 item 7.

**Rank, add and the keyed edit are kernel-backed — the seven-verb surface is
complete (same 2026-09-12 session, stage-3 wiring block; this is the "rank,
add and the keyed edit" block other paragraphs cite).**  All three ride the
same choke point (`kernel_bridge::apply`); nothing else changed shape.  What
each wiring is, and what it changed observably — recorded, never absorbed:

- *`tm rank ^id n`.*  The wire op is `rank{id,rank}` with a **raw document
  rank** (a line index — a parsed line's index is the rank `splitDoc`
  assigns), and the kernel refuses a taken rank (`badHorizon`,
  `rank_onto_a_taken_rank_is_refused`) rather than renumbering — so the host
  compiles the position into a **rotation**, one atomic request: the moved
  line to the always-free rank past the end of the file, each item between
  old and new position into the rank its neighbour just vacated, the moved
  line into the freed target rank.  Every line is byte-identical afterwards;
  only the order changes (`rank_down_rotates_the_section_and_keeps_every_
  byte`).  Changes: (1) items rotate through the section's *item* slots, so
  prose interleaved in a section keeps its own line — the old path reinserted
  the line and shifted the prose with it; (2) a day file whose `# Pinned` is
  not the last section refuses the whole reorder `badHorizon`, because the
  rotation's temporary rank sits past the last section — the same family as
  the recorded move-to-day refusal; (3) a no-op rank (already at the clamped
  position) makes no kernel call, writes nothing, and still records its undo
  entry, as before.  Id-less lines — the moved one or any line the rotation
  passes through — keep the old path (gap 5).
- *`tm add`.*  `{"op":"add","seed":…,"doc":…,"title":…}`: the seed comes
  from the same hasher `id_gen` seeds (`--now` + the text, §17.2 — nothing
  new is stored), sized to four digits; the id is the kernel's own —
  `freshId` renders the seed as digits and bumps past every taken id,
  freshness by L21 — so **assigned ids are digit strings now**, not the old
  four-character base-32 (gap 13's recorded resolution: digits are a subset
  of `[a-z0-9]`; the shape decision stays the human's).  The kernel places
  the line at `freshRank` — the end of the file.  What stays on the old Rust
  path, each carve-out by name on `kernel_addable`: `--section` (no section
  on the wire — the recorded move rule), id-less destinations
  (`routines.md`/`optional.md`/`inbox.md`, gap 5's mirror), an explicit
  `^id` in the text (`parseCmd` refuses `^` in a title; the old taken-id
  check still guards the explicit form), a state other than `[ ]` (no box
  on the wire), and a destination whose **last** heading is a `## series:`
  section — §5.4: the kernel would append the line as a silent, invisible
  non-head, which is exactly what the old path's series-skip exists to
  prevent, so that placement logic stays host-side.  Change: `tm add --to
  day` on the shipped day file (ends `## Log`/`## Notes`) is refused
  `badItem` with nothing written, where the old path appended an
  out-of-section line §6.2 forbids (`add_to_a_day_outside_pinned_is_
  refused_by_name`; the FFI twin is `add_outside_a_day_files_pinned_
  section_is_refused_by_name`).
- *The keyed `edit`/unset.*  `tm edit ^id k=v … [--unset k …]` rides the
  wire when **every** requested change is a wired key — `est dur buffer
  pref on-miss after-done min max cap` (`cap` and `max` one key; the write
  lands `max:`, `set_max_writes_max`) — as `{"op":"edit","id","key","value"}`
  per change, the raw value text on the wire, in one request; an `est=`
  pair goes as the `est` op in canonical minutes (the CLI's `Dur` grammar
  still reads it, so `est=2b` keeps its block arithmetic and `est=zzz` its
  old message; `the_est_op_is_the_keyed_est_edit` pins the equivalence).
  An **empty value** (`tm edit ^id pref=`) is the wire's unset form and now
  works from the CLI.  Changes: values land as the field's canonical
  rendering; a bad value is `badValue <k>` **by name** in the human line
  and the `--json` document (the free-text `err` is mapped, not swallowed:
  `badValue`/`keyNotWired`/`unknownKey`/the five `title…` names each reach
  `detail.refusal`); an unset of a key the line does not carry is
  `keyAbsent` where the old path reported success and removed nothing; a
  tabbed line refuses the whole edit (`tabbedLine`, gap 32's guard, now on
  every wired key).  What stays on the old Rust path, by name: id-less
  lines (gap 5); `--set` (documented as a raw verbatim token — the kernel
  would canonicalize it); the typed non-key edits `title`/`p`/`state`; the
  deferred keys gap 40 names (`due at win every on-event after loc
  waiting`, plus `demoted` excluded by policy — the wire refusal is
  `keyNotWired`, named); `--unset ci` (the wire clears the `ci:` slot only
  and gap 41 wants both slots); and — gap 41's mirror, decided here —
  **`ci=` rides the wire only when the line's ci already lives in the
  `ci:` key slot**: on a line whose ci is the positional digit the kernel
  write would leave both slots populated (`tm check`: "ci given twice"),
  and the positional digit is §4.1 line surgery the wire does not carry,
  so those edits keep the old positional rewrite.

**The bare-`tm init` tree was unloadable to the kernel — a landmine standing
since the five-verb landing, found and defused here.**  The starter
templates' guidance comments carried example item lines (`- [ ] … ^m1`,
`after:^t4`), and this kernel has **no HTML-comment awareness**: `scanLines`
reads any `- [c] …` line as an item wherever it stands, so a fresh `tm init`
tree refused *every* kernel-backed verb — `itemCheck: danglingDep` on ids
that exist only inside `<!-- -->` guidance (`tm init && tm add … --to week`
exited 1).  The five-verb landing never saw it because every test tree was
the `plan-basic` fixture or `--example`, whose comments carry no itemish
lines.  Host-side fix, taken: the three starter templates with itemish
guidance (`week-body.md`, `month-body.md`, `backlog.md`) now bullet their
examples `• [ ]` instead of `- [ ]` — prose to both readers, byte-visible in
`tm init`'s output, and a copy-paste of one is a loud non-item rather than a
silent live line.  Kernel-side, **owed by name** (a Lean change this step
may not take): comment-awareness in `scanLines`/`splitDoc` — the loader
should read `<!-- … -->` spans as prose the way the shipped Rust parser
does; until it lands, any hand-written plan file with itemish bytes inside a
comment refuses every kernel-backed verb by whatever name the comment's
content earns (`dupId`, `danglingDep`, `badLine`…), loudly but surprisingly.

**A fork-point tm-core defect, found by the restored proptest harness and
fixed: `fix_flag_boundaries` reordered flags.**  `grammar_proptest`'s
`add_flag_and_remove_parent_keep_flags` (running fresh cases, as L24/L25
kept it alive to do) shrank to `- [ ] A @A atomic due:2026-01-01 open @A ^a`:
`set_parent(None)` removes both `@A` tokens, orphaning `atomic` against the
title, and the old repair moved every orphan after the `^id` — past `open` —
so the flags came back `open atomic` where the line said `atomic open`.
Since `boundary_before` is monotone, the orphans are exactly the flags
before the line's *first* boundary token; they now move, as a group and in
order, to just after **that** token instead.  The shrunk case is persisted
in `grammar_proptest.proptest-regressions` (fourth `cc` entry), so it
replays deterministically from here on.

Re-measured at this landing: `cargo test --workspace` **955 passed / 0
failed / 0 ignored across 61 binaries** (was 950; +5 CLI tests for the three
wirings, the tm-core fix and template change cost nothing); `kernel/check.sh`
**7/7 ok**, corpus 33/37 files and 4/5 whole plans, burn-down **41**, audit
**1090** — all unchanged (no Lean source was touched).  Still owed from
stage 3's scope, by name: the panic probe and the layer-2 stderr `dup2`
(next in this session), and the four integration-bug countermeasures of
AGENTS 8.1 item 7.

**Panic layers 2 and 3, landed — AGENTS 8.1 scope item 6, and the
constructed probe (same 2026-09-12 session, stage-3 wiring block).**  Layer
1 is totality (CI-enforced) and layer 3 stood in the ffi crate
(`lean_set_exit_on_panic(false)` in `shim.c`; `KernelFault` in `lib.rs`,
"loud and recoverable, never a wrong answer") but nothing integrated it and
layer 2 did not exist.  Now:

- *Layer 2 — the stderr `dup2`.*  While `tm tui` owns the screen
  (`kernel_bridge::capture_kernel_stderr(true)` for the whole session),
  every kernel call runs with fd 2 redirected to a pipe drained by its own
  thread (so a backtrace longer than the pipe buffer cannot block the
  writer), the original fd restored right after the call — a Lean runtime
  backtrace can no longer shred the ratatui alternate screen.  Whatever was
  captured rides the fault's `detail.stderr`.  The `pipe`/`dup`/`dup2`/
  `close` symbols are declared `extern "C"` in `kernel_bridge.rs` itself —
  no `libc` crate entry, R7 untouched; on non-Unix the capture is a no-op.
  A failed capture never fails the verb.
- *Layer 3, integrated.*  A kernel **fault** (`KernelFault`, an unparseable
  response, a wrong-shaped echo — everything `fault_issue` names
  `kernelFault`) is now distinguished from a named *refusal* everywhere:
  `KernelIssue::is_fault` / `CliError::is_kernel_fault`.  In the TUI a
  refusal stays a status-line message and the session keeps running; a
  fault propagates out of the one verb seam (`tui::verb` returns it), the
  event loop unwinds, **the terminal is restored on the way out**, and the
  fault prints as a bug report — "please report this — nothing was written
  to the plan", plus the captured kernel stderr, indented, when layer 2
  caught any — with exit 1.  On the plain CLI the same fault prints the
  same report (no capture window, so no stderr block) and exits 1; under
  `--json` it is the standard failure document, `kind:"kernel"`,
  `detail.refusal:"kernelFault"`.
- *The probe, constructed — the trap by name ("a panic probe needs
  something that can panic").*  The kernel is total by CI, so there is no
  reachable panic; the probe injects the fault at the host's own seam:
  with `TM_KERNEL_FAULT_PROBE` set, the bridge makes the real kernel call
  and then replaces the response bytes with a non-JSON marker.  The tests
  assert the **host's** reaction, not the kernel's:
  `the_panic_probe_faults_loudly_and_writes_nothing` (cli_errors.rs — exit
  1, `kernel fault` named on stderr, no success output, the plan file
  byte-identical, and the `--json` document carrying
  `detail.refusal:"kernelFault"`) and
  `a_kernel_fault_propagates_and_a_refusal_stays_a_message` (tui — the
  fault propagates out of the verb seam where `run` restores the terminal;
  the `occupied` refusal on the same tree stays a message).  The `dup2`
  machinery itself is host-tested
  (`stderr_capture_takes_fd2_and_gives_it_back`: bytes written to fd 2
  inside a window land in the capture and fd 2 comes back).

Re-measured at this landing: `cargo test --workspace` **959 passed / 0
failed / 0 ignored across 61 binaries** (was 955; +4 — the two capture/fault
unit tests, the CLI probe, the TUI seam test); `kernel/check.sh` **7/7 ok**,
corpus 33/37 files and 4/5 whole plans, burn-down **41**, audit **1090** —
all unchanged (no Lean source was touched).  Still owed from stage 3's
scope, by name: the four integration-bug countermeasures of AGENTS 8.1 item
7 (the one-renderer test, the exhaustive screen router, the `--help`-vs-
runtime conformance test, the verb × {success, error} × {plain, `--json`}
matrix); and, recorded above, the kernel-side HTML-comment awareness in
`scanLines`/`splitDoc`.

**Three of the four integration-bug countermeasures, landed — AGENTS 8.1
scope item 7 (same 2026-09-12 session, stage-3 wiring block; supersedes the
"still owed" list of the panic-layers paragraph above for these three).**
PLAN §4's last table names four; the three that are CLI-surface work are
stage 3's, all built as tests against the **built binary**
(`CARGO_BIN_EXE_tm`), never the clap tree:

- *The `--help`-vs-runtime conformance test (G2/G4's class)* —
  `tm/tests/cli_conformance.rs`.  The walk discovers the verb tree from the
  binary's own help output (top level, `tm close`'s custom `Periods:`
  heading, `tm routine`'s verbs — **38 pages**, re-measured: 34 §13 verbs +
  3 close periods + `routine done`), extracts every advertised long flag
  from each `Options:` section, and asserts the runtime accepts it: `tm
  <verb…> --<flag> [dummy] --help` must not die with clap's `unexpected
  argument` (an "invalid value" on the dummy is acceptance — the flag was
  recognised; `unexpected argument` is G4).  Every page must also advertise
  the globals `--json`/`--dir` (G2's shadowing died there).  A probe floor
  (≥100 flag probes) keeps a silently-empty parser from passing vacuously.
- *The verb × {success, error} × {plain, `--json`} matrix (G3's class)* —
  `tm/tests/cli_json_matrix.rs`.  Table-driven over all 34 §13 verbs, four
  legs each, a fresh `plan-basic` copy per leg: success/plain exits 0;
  success/json is one JSON document on stdout; error/plain is the `tm: …`
  line on stderr with the expected exit code and an empty stdout;
  error/json is the `ErrorDoc` document on stderr (`ok:false`, `kind`,
  `message`, `exit_code`).  A size assertion pins the table at 32 rows +
  `init` + `check` so it cannot shrink silently.  **Named exceptions, not
  skips**: `tm tui` has no headless success leg (it needs a tty; that
  refusal *is* its error leg, both renderings), and a failed `tm check`
  reports its problem document on **stdout** with exit 2 — §13 reserves 2
  for validation problems and the stderr document for the verb itself
  failing — so `check` (dep-cycle poison, `error[dep-cycle]`) and `init`
  (no plan directory exists yet; "not empty" is the error) carry their own
  four-legged tests beside the table.
- *The exhaustive screen router* — the compile-time half **already stood**
  in the restored-and-rewired source and is hereby recorded rather than
  rebuilt: `tui/app.rs`'s `Screen` is an enum and every dispatch on it
  (`App::screen_key`, `today.rs`'s body match, `Screen::title`) is a
  `match` with no `_` arm, so an unrouted screen is a compile error.  What
  was missing was the runtime half, now `tm/tests/tui_screen_router.rs`:
  for every screen, press its §12.6 digit through the binary's own
  `action_for` → `apply` path (the same one `tui/mod.rs`'s event loop
  drives), draw the full frame into a ratatui `TestBackend`, and assert a
  non-empty body **distinct from every other screen's** — a screen that
  routes but draws another's pane fails.  The test's own `digit_of` match
  has no `_` arm either, so a new `Screen` variant refuses to compile until
  it gets a key and a smoke case; digits `0`, `6`–`9` are asserted to route
  nowhere.

*The fourth countermeasure is not this stage's, by name*: the one-renderer
test (G1 — day-section text byte-identical across the file, `tm now`, `tm
tui` and `tm plan --json`) belongs to **stage 6**, whose PLAN §4 acceptance
row names it next to `tm plan` being kernel-backed; it stays owed there,
not here.

No shipped-binary behaviour changed in this landing — it is tests only —
and the matrix legs were each probed by hand against the built binary
before being pinned, so every expected exit code in the table is a
measurement, not a guess.  Re-measured: `cargo test` **980 passed / 0
failed / 0 ignored across 64 binaries** (was 959/61; +21 across the three
new test binaries — 2 conformance, 5 matrix, and the router binary's 14,
twelve of which are the `#[path]`-included TUI modules' own unit tests
compiled into it); `kernel/check.sh` **7/7 ok**, corpus 33/37 files and 4/5
whole plans, burn-down **41**, audit **1090** — all unchanged (no Lean
source was touched).

**The bridge writes newline-faithful files — the read-only drive
verification's one major defect, fixed (same 2026-09-12 session, stage-3
wiring block).**  Observed at the byte level: before `tm move ^a1 week` the
week file ended `…^p1\n`; after, it ended `…^p1\n\n- [ ] 2 30m Insurance
claim … ^a1` — a blank line before the appended item and **no final
newline** — and `tm add --to <file>` appended likewise.  The mechanism was
the split/join convention at the choke point (`tm/src/cli/kernel_bridge.rs`):
a newline-terminated file split naively on `'\n'` grows a trailing empty
segment, which the kernel reads as a ranked prose line; `freshRank` appends
**after** it (the blank line), and the join back emits no final newline (the
lost EOF byte).  The fix is host-side only, at the bridge, both directions:

- *request build*: split on `'\n'`, then strip **exactly one** trailing
  empty segment iff the file ends with `'\n'` — the kernel sees the file's
  real lines, none phantom;
- *write-back*: a rewritten file is `lines.join("\n") + "\n"` —
  newline-terminated, exactly one `'\n'` between any two lines;
- *the recorded convention for a file that does NOT end in a newline*: read
  as-is (there is no trailing empty segment to strip); untouched, it is
  never written and stays byte-identical, missing EOF newline included;
  rewritten, it comes back **newline-terminated** — the bridge normalizes
  rewritten files to the POSIX text-file shape rather than propagating a
  missing final newline.  `changed` is judged on the kernel's line lists,
  not reconstructed bytes, so the normalization itself never triggers a
  write.

This *supersedes, for the bridge only*, the bridge's own recorded
convention (its module docs' former "lines split the way the kernel joins
them — `Tm.splitOn '\n'`, the recorded host agreement", now rewritten in
place): the corpus harness's naive identity `split('\n')`/`join('\n')`
(`tests/harness/mod.rs`, check 6) remains correct for its read-only,
no-commands round trip — the two conventions agree byte-for-byte on every
document the kernel does not change — but a host that lets the kernel
*append* must not send the phantom line, and the bridge now does not.  The
gap-12 **host agreement** paragraph above is untouched: it names
`tm-kernel-ffi`'s harness split, which is unchanged.
Pinned by four byte-level tests in `tm/tests/cli_items.rs` (full-file byte
compares, not contains-checks): `move` into a newline-terminated file gains
exactly the moved line plus one final `'\n'` and the source loses exactly
that line; `add` likewise; the no-final-newline convention above, both
halves; and the write-changed-docs-only rule asserted byte-for-byte on
every file the verb did not touch.

**Correction to the countermeasures paragraph above, by name.**  The
"Three of the four integration-bug countermeasures, landed" paragraph says
all three run against the built binary (`CARGO_BIN_EXE_tm`), never the clap
tree — that is true of `cli_conformance.rs` and `cli_json_matrix.rs`, but
`tm/tests/tui_screen_router.rs` is in-process (a ratatui `TestBackend` over
the binary's own modules pulled in by `#[path]` includes), not a spawned
binary.

**Recorded, not fixed here: on a stale tree the fork-point day-close
catch-up/rollover runs before command dispatch, so its writes precede — and
survive — a kernel refusal of the command itself.**  Observed on a fresh
`init --example` tree dated five days back: five close-day events and a
demote were written by the catch-up before the command's own A6 `occupied`
refusal arrived, so "a refusal writes nothing" holds for the *command's*
kernel call but not for the housekeeping that ran ahead of it.  This is
pre-existing fork-point behaviour (`Ctx` housekeeping, §6.3 auto-close /
§5.1 timeouts, predates the kernel wiring) and stage-4 territory by PLAN's
own row — `close`/`autoClose` move into the kernel there — so it is
recorded here by name rather than patched around.

Re-measured at this landing: `cargo test --workspace` **983 passed / 0
failed / 0 ignored across 64 binaries** (was 980; +3 — the three byte-level
newline tests, the untouched-files assertion riding the move test);
`kernel/check.sh` **7/7 ok**, corpus 33/37 files and 4/5 whole plans,
burn-down **41**, audit **1090** — all unchanged (no Lean source was
touched; the corpus harness was read, not modified).  One drive-verification
minor needed no change: `cli/out.rs`'s `is_kernel_fault` was reported
dead-code-warned in the binary crate, but a clean `cargo check -p tm
--all-targets` today emits **zero warnings** — it is live at
`tm/src/tui/mod.rs` (the fault-vs-refusal fork at the verb seam) and
exercised by `a_kernel_fault_propagates_and_a_refusal_stays_a_message`.

**Two write paths, two newline conventions — recorded, by name.** The
byte-level re-verification of the bridge fix found the divergence it
implies: the bridge normalizes every file it rewrites to newline-terminated
(the convention above), while the **legacy** non-bridge writers —
`store.insert_line` and whatever else still rewrites files on the old Rust
path (reached today by `tm add`'s series carve-out, and by every verb the
kernel does not yet back) — rewrite a non-newline-terminated file **as-is**.
No recorded claim is broken (the convention is bridge-scoped everywhere it
is written) and neither path corrupts bytes; but the same tree can now be
touched by both conventions, and the divergence retires only as the legacy
writers do — stage 4 (`close`), stage 6 (`plan`), and gap 5's id-less lines
are the remaining callers. Also repaired at this commit:
`kernel_bridge.rs`'s module-doc verb list, which still enumerated five
verbs after `rank`, `add` and the keyed `edit` joined [`apply`].

**The J-route's first step: the kernel owns a JSON value, its escaping and its
numerals — and the escaping round trip is a theorem.**  Same 2026-09-12
session, J-route step 1.  "Gap 39 REPRICED" above measured that `Lean.Json`'s
printer and parser are `partial def`s — opaque constants with no equation
lemmas — and priced the replacement as J0–J6.  This lands **J0–J2** in a new
module, `TmKernel/Json.lean` (imported in `TmKernel/TmKernel.lean` at the same
commit, between `Text` and `Line`; §2.3's silent failure was checked for, not
assumed).  **No wire change**: `Boundary.lean` still builds `Lean.Json`, the
Rust is untouched, and `Goals.lean` is untouched — `the_json_edge_round_trips`
stands until J6, exactly as that paragraph says it should.

*J0, the type.*  `JVal` is `null | bool Bool | num Nat | str (List Char) |
arr (List JVal) | obj (List (List Char × JVal))` — objects an **ordered assoc
list**, so `Json.mkObj`'s sorted-`TreeMap` rebuild hazard vanishes by
construction and `jval_objects_keep_their_order` says the order is in the
value.  Two things measured rather than assumed.  (a) **The numerals are `Nat`
because the wire has no others**: every number the boundary emits is
`lerrJson`'s `badLine` line count, `regionJson`'s `grain` (a `Fin 4` value) and
`regionJson`'s `ix`, all `Nat`; every number it ingests goes through
`Boundary.getNat`.  No negative, no exponent, no `JsonNumber` — so a site that
ever needs one must widen `JVal.num`, visibly, in a diff.  (b) **`deriving
DecidableEq` fails on `JVal`** — v4.33.1 answers *"None of the deriving
handlers for class `DecidableEq` applied to `JVal`"*, because the recursion is
*nested* (through `List`), not mutual.  The escape hatch a search engine offers
is `termination_by sizeOf`, and §5.10 says why that is the wrong one here: a
well-founded definition does not reduce in the kernel, so every `decide` in
this module would stop working.  The instance is instead three **mutually
structural** `Bool` functions (`jbeq`/`jbeqL`/`jbeqO`) with `jbeq_sound`,
`jbeq_refl` and `jbeq_iff` — proved through the **four-motive `JVal.rec`** that
the nested inductive generates (motives for `JVal`, `List JVal`,
`List (List Char × JVal)` and the pair).  That eliminator is the one J4's
`jparse_jemit` will need, so this section is a rehearsal for it as much as it
is J0; the working shape is `refine JVal.rec (motive_2 := …) (motive_3 := …)
(motive_4 := …) ?null … ?pair a`, because the `induction … using` form leaves
motives 2–4 as metavariables and auto-introduces binders unevenly.

*J1, the crux, landed.*  `junescape_jescape : ∀ cs, junescape (jescape cs) =
.ok cs` — **unconditional**, no fragment restriction, no hypothesis.  That is
the theorem `Lean.Json`'s `partial def`s make unstatable, and the kernel's doc
lines are arbitrary user bytes, so anything weaker would be §5.4's boundary
hole with a proof attached.  The case analysis lives in `junescape_escOf` (one
character at a time, so the round trip itself is an induction with no cases);
the `\uXXXX` branch turns on `hexQuad_escOf` and core's `Char.ofNat_toNat`.
Everything is structural — `jescape`, `junescape` (whose `\u` branch recurses
six characters in, still on a proper tail), `jdigits`, `jbeq` — so no fuel and
no well-founded recursion, and every byte-level claim below is `rfl` or
`decide`.

*The three decisions J1 takes, stated rather than left implicit, each with a
theorem.*  (1) **Emit narrow, accept wide.**  `jescape` emits exactly what
Lean's own printer emits — `\"`, `\\`, `\n`, `\r`, a lowercase `\u00xx` quad
for every other character below `0x20`, everything at or above `0x20`
verbatim, non-ASCII and `DEL` included (`the_emitted_escape_classes`,
`jescape_keeps_high_bytes_verbatim`).  `junescape` *additionally accepts*
`\/`, `\t`, `\b`, `\f` and either-case hex quads, because serde_json emits all
of those and serde_json is the only reader and writer these bytes ever had
(`junescape_accepts_the_host_short_escapes`); the asymmetry is itself a
theorem, `the_accepted_escapes_exceed_the_emitted_ones`.  (2) **Raw bytes that
RFC 8259 forbids in string content are refused**, not passed through: a raw `"`
is `JEsc.rawQuote` and a raw character below `0x20` is `JEsc.rawControl`
(§5.7 — every diagnostic is named), so when J4's scanner hands `junescape` the
bytes between two quotes the refusals restate the scanner's guarantees.
(3) **A lone surrogate escape is refused by name** — gap 42 below.  Six
refusals are theorems, each naming its own constructor:
`junescape_refuses_a_truncated_escape`, `…_a_truncated_hex_quad`,
`…_a_bad_hex_quad`, `…_an_unknown_escape`, `…_a_raw_quote`,
`…_a_raw_control`, plus `junescape_refuses_a_lone_surrogate` and its
non-vacuity partner `the_surrogate_guard_is_not_vacuous` (the quads just below
and just above the surrogate block are accepted, so the guard is not swallowing
the whole `\u` branch).  §5.2's witnesses are `demoEscLine` — a line carrying a
quote, a backslash and a tab — pinned byte-for-byte by `demo_jescape_bytes`,
read back by `demo_junescape_bytes`, and shown to be moved at all by
`the_escaping_is_not_vacuous` (the round trip alone is true of `jescape = id`).

*J2, numerals, and §5.3 taken seriously.*  There is **no second numeral
grammar**: `jrenderNat` is an `abbrev` for `Text.lean`'s `digitsOf`
(`jrenderNat_is_digitsOf` is `rfl`), so `readNat_digitsOf` and
`digitsOf_injective` apply to it unchanged.  The only new thing is the
**next-byte guard**, which is what a numeral inside a larger document needs and
a numeral alone does not: `jparseNat_jrenderNat (n) (rest) (h : notDigitStart
rest = true) : jparseNat (jrenderNat n ++ rest) = some (n, rest)`, over
`jdigits_append`.  Both directions, per §5.8: `the_next_byte_guard_bites` shows
the conclusion is **false** without the guard — `1` followed by `2` reads as
`(12, [])`, not `(1, ['2'])` — and `the_next_byte_guard_is_satisfiable` shows
the guard holds of every byte a numeral is actually followed by (`,`, `]`, `}`,
a space, end of input), so §7.4 item 2's vacuity trap is closed by exhibition
rather than by assertion.

**Gap 42 — `junescape` refuses a surrogate-pair escape instead of recombining
it.**  (1) *What is not done*: a two-escape surrogate pair (`\ud83d` followed by
`\ude00`) is not joined into the one astral character it spells; the first
half is refused with `JEsc.surrogateEscape`.
(2) *Why — a decision, not time*: Lean's `Char` is a Unicode **scalar** value,
so `0xd800`–`0xdfff` is not a `Char` and `jescape` can never emit one; a
recombination branch would therefore be code that `junescape_jescape` does not
cover — untested logic inside the one function this module exists to prove.
(3) *What it costs*: a host that escapes astral characters as pairs — which
JavaScript's `JSON.stringify` does and **serde_json does not**, since it writes
them as UTF-8 bytes — is refused, by name, rather than mis-decoded.  Today it
costs nothing at all, because `Lean.Json` is still the reader on the wire.
(4) *Which stage clears it*: J5, and only if a non-serde host is ever put on
the other end; the refusal is the right behaviour otherwise.

**What this step did not do, by name.**  J3 (`jemit`), J4 (the fuel-structural
`jparse` and `jparse_jemit`, still the route's largest single proof), J5 (the
wire change in `Boundary.lean`'s response builders, plus the byte re-measure
the "Gap 39 REPRICED" paragraph demands — `mkObj` sorts keys, an assoc list
keeps build order) and J6 (the discharge of `the_json_edge_round_trips`) are
all untouched and unchanged in price.  The burn-down therefore **stays at 41**:
this step discharges no goal, adds no goal, and that is the intended shape —
the goal is discharged at J6 or not at all.  `Negative.lean` is untouched and
this block **takes no cheat numbers**: nothing here introduces a bounded type
or a smart constructor, and the surrogate and control-byte bounds are runtime
refusals with named errors rather than type-level doors.  R10's doors arrive
with J3/J5.

Re-measured at this landing, every number from the committed harness (§5.11):
`kernel/check.sh` **7/7 ok**; axiom audit **1122 theorems** (was 1090; +32, the
whole of `Json.lean`), and §6.3's three counts agree at 1122 — `grep -c '^#print
axioms' Check.lean` = 1122, distinct names = 1122, and
`grep -hcE '^(@\[[^]]*\][[:space:]]*)?theorem ' TmKernel/*.lean` summed = 1122
(the two cancelling off-by-ones §6.3 documents are unchanged, since every name
added here is a plain `theorem` and the delta is +32 on all three); corpus
**33/37 files and 4/5 whole plans**, unchanged; `Goals.lean` burn-down **41**,
unchanged; `cargo test --workspace` **983 passed / 0 failed**, unchanged; the
FFI suite **46 tests** (40 kernel + 6 corpus), unchanged.  Nothing outside
`TmKernel/Json.lean`, `TmKernel/TmKernel.lean` (one import line) and
`Check.lean` (one banner plus 32 lines) was edited.

**The J-route's second step: `jparse ∘ jemit` is the identity on `JVal`, and
`jparse` never refuses for fuel.**  Same 2026-09-12 session, J-route step 2
(J3–J4), landed in `TmKernel/Json.lean` (already imported; no new module).
**No wire change**: `Boundary.lean` still builds `Lean.Json`, the Rust is
untouched, and `Goals.lean` is untouched — `the_json_edge_round_trips` stands
until J6.  A first attempt at this step was killed mid-build by the OOM killer
and left its work uncommitted; it was diagnosed under memory caps and salvaged,
not redone — the emitter, the parser, `jval_jemit` and `jparse_jemit` are its
work, and what changed is listed below.

*J3, the emitter.*  `jemit` is six mutually structural functions, one per
parser entry point (`jemitArr`/`jemitTail` differ only in the separator, as
`jarr`/`jtail` do), compress-shaped and in **assoc-list order**:
`demo_jemit_bytes` pins the bytes, `the_emitter_keeps_build_order` shows they
are not `mkObj`'s sorted ones, `the_emitter_is_compress_shaped` that no
whitespace is written and none inside a string is dropped.  `jfuel` counts the
parser frames reading `jemit v` opens, and `jfuel_le_jemit : jfuel v ≤ 2 *
(jemit v).length` is why the parser takes its fuel from the bytes.

*J4, the parser and the theorem.*  `jparse l := jparseWith (2 * l.length + 2)
l` over six mutually **fuel-structural** entry points (`jval`, `jarr`,
`jtail`, `jobj`, `jpair`, `jotail`) — no well-founded recursion, so small
witnesses still evaluate — refusing in `Except JErr`, thirteen named
constructors (§5.7).  **`jparse_jemit (v : JVal) : jparse (jemit v) = .ok v`**,
unconditional: no fragment restriction and **no duplicate-key side condition**,
because an object is an ordered assoc list and `{"a":1,"a":2}` reads back as
both pairs in order (`the_round_trip_survives_duplicate_keys`).  It rests on
`jval_jemit`, the four-motive `JVal.rec` step 1 rehearsed, with each list motive
a conjunction (one component per entry point); on `jstring_jescape`, which is
J1's `junescape_jescape` plus `jscan_jescape` (the scanner stops at exactly the
quote the emitter wrote, one `escOf` class at a time); and on J2's next-byte
guard, discharged at every numeral site by `notDigitStart_jemitTail`/`…OTail`
rather than assumed.  **Supersedes, by name, two details of "Gap 39
REPRICED"'s J4 pricing**: it wrote `jparse_jemit : jparse (jemit v ++ rest) =
some (v, rest)` with fuel := input length.  The prefix form cannot hold for
every `rest` — a numeral followed by a digit reads as a longer numeral — so it
is `jval_jemit`, under `notDigitStart rest = true` and `jfuel v ≤ f`, and the
headline is the whole-document form in `Except JErr`; and the fuel is `2 *
length + 2`, because `n` arrays nested around a numeral open `3n+1` frames for
`2n+1` bytes.

*Beyond the pricing: the derived fuel is enough for every input.*  J5 will hand
`jparse` **host** bytes, which are not `jemit` images, so `jfuel_le_jemit`
alone would leave `JErr.outOfFuel` as a possible spurious refusal of a real
request.  `jparse_never_runs_out (l : List Char) : jparse l ≠ .error
.outOfFuel` closes it for all `l`, by two inductions on the fuel over all six
entry points: `jparser_consumes` (every successful frame consumes a byte, at any
fuel) and `jparser_fuel` (a frame given twice its input's length, plus one or
two by entry point, never runs out).  Likewise `jparseNat_some_of_digit` makes
the `JErr.badNumber` doc comment's "unreachable through `jval`" a theorem.  Both
were docstring claims in the salvaged draft; neither is one now.

*Both directions, and §7.4.*  It bites, each refusal by its own constructor
over small `List Char` inputs: `jparse_refuses_empty_input`,
`…_an_unterminated_string`, `…_trailing_garbage`, `…_a_bad_escape`,
`…_a_raw_control_byte`, `…_a_trailing_comma` (array and object),
`…_an_unterminated_array`, `…_a_missing_separator`, `…_a_bare_key`,
`…_a_missing_colon`, `…_an_unterminated_object`,
`…_what_the_fragment_has_no_type_for` (`-3`, `1.5`, `1e3`), and
`jparseWith_refuses_when_the_fuel_runs_out`.  It does not over-bite:
`the_real_request_bytes_round_trip` and `…_response_…` take `kernel.rs`'s
`duplicate_ids_are_rejected_at_load` bytes verbatim, `jparse_accepts_host_whitespace`
puts all four RFC 8259 whitespace bytes at every token boundary a host may use
and reads the value whose compressed bytes the kernel emits, and
`the_json_round_trip_is_not_vacuous` shows the parser is not constant.  §7.4:
every binder is used; both `jval_jemit` hypotheses are satisfiable
(`jparse_jemit` discharges them for every `v`) and the digit guard bites —
`the_jval_jemit_digit_guard_bites` by evaluation (`7` then `7` reads as `77`)
and **`Negative.lean` CHEAT 47** as a type error, under a new end-of-file
banner, failing as an *application type mismatch* at `notDigitStart ['7'] =
true` (checked against the transcript, not just "the file failed").  Item 5 is
answered honestly: none of this is on the FFI path until J5.  The salvaged
draft's orphan `deriving instance DecidableEq for Except` — which did not even
parse, a doc comment preceding `deriving instance` — is **removed**, per step
1's house decision: every `Except` witness is `rfl` or a tuple of `rfl`s, and
every `≠` is `nofun` after rewriting.

**The memory-bomb finding, and the rule it implies.**  Evaluating the parser
by `decide`/`rfl` directly over `"…".toList` of a string literal grows without
bound — `{"a":1 "b":2}` passed an 8 GB cap in 15 s, `{"a" 1}` hit the
200000-heartbeat `whnf` limit at ~2 GB, and uncapped the draft's ~85-byte
request exhausted the machine twice — so **a byte-level `decide` over a parser
run must be small and spelled as a `List Char` literal, and a realistic input is
an instance of the round-trip theorem, not an evaluation** (`jemit v = bytes`
is decided, `jparse bytes = .ok v` is `jparse_jemit`).  Measured under caps,
the cost is the *combination*: `toList` alone decides instantly, and so does
the parser over the same bytes as a `List Char` literal — a 92-byte request by
`rfl` in ~0.5 s at ~520 MB — so the literal's decoding is what the parser run
re-forces.  The heartbeat timeout on `jparse_refuses_a_missing_colon` was the
same bomb with a budget, fixed by the spelling and **not** by raising
`maxHeartbeats`.  The whole of `Json.lean` now elaborates in ~2.3 s at ~0.97 GB
peak under an 8 GB cap.

**Gap 43 — `jparse` accepts leading zeros.**  (1) *What is not done*: RFC
8259's `int = zero / ( digit1-9 *DIGIT )` is not enforced on input; `007` reads
as `JVal.num 7` (`jparse_accepts_leading_zeros`).  (2) *Why — a decision*: J2
took "no second numeral grammar" — `jparseNat` is `readNat` over the digit run —
and a leading-zero refusal would be read-side logic `jparse_jemit` never
exercises, since `digitsOf` never emits one; the reading stays unique (two
spellings, one value, like `\t` and `	`), so §5.6 is not broken.  (3)
*What it costs*: `jparse` is a left inverse of `jemit` and not a right one —
already true of whitespace and the short escapes — and a non-RFC host numeral
is accepted rather than refused; serde_json never writes one, so no production
byte is affected.  (4) *Which stage clears it*: J5, only if strict input
conformance is ever required — one guard in `jval`'s digit branch plus a
`digitsOf` leading-digit lemma to keep `jval_jemit` closing.

**What this step did not do, by name.**  J5 — the wire change in
`Boundary.lean`'s response builders, the byte re-measure "Gap 39 REPRICED"
demands, and two things this step surfaced for it: the rule the `Boundary`
readers take for a duplicate key (this parser keeps both pairs, while a
`serde_json::Value` map keeps only one), and R10's stated width for
`JVal.num`, which is an unbounded `Nat` here — and J6, the discharge of
`the_json_edge_round_trips`, are untouched.  The burn-down therefore **stays at
41**, the intended shape: no goal discharged, none added.

Re-measured at this landing, every number from the committed harness (§5.11):
`kernel/check.sh` **7/7 ok**; axiom audit **1207 theorems** (was 1122; +85, all
of them `Json.lean`'s J3–J4 theorems, under one new `APPENDED 2026-09-12
(stage-3, J-route step 2 …)` banner), and §6.3's three counts agree at 1207 —
`grep -c '^#print axioms' Check.lean` = 1207, distinct names = 1207, and the
attr-aware `theorem` grep over `TmKernel/*.lean` = 1207 (+85 on all three; one
docstring line that would have put `theorem` at column 0 was reflowed so the
third count gains no new off-by-one); every new theorem's axioms are within
`propext`, `Quot.sound`, `Classical.choice`; corpus **33/37 files and 4/5 whole
plans**, unchanged; `Goals.lean` burn-down **41**, unchanged; `cargo test
--workspace` **983 passed / 0 failed / 0 ignored across 64 binaries**,
unchanged; the FFI suite **46 tests** (40 kernel + 6 corpus), unchanged.  Gap
43 and CHEAT 47 are taken; new gaps start at 44 and new cheats at 48.  Edited:
`TmKernel/Json.lean`, `Check.lean` (one banner plus 85 lines), `Negative.lean`
(one banner plus CHEAT 47) and this file.

**J5, the response side: every byte `call` writes is `jemit`'s.**  Same
2026-09-12 session, J-route step 3, first of its two commits.  `Boundary.lean`'s
response builders — `jsonErr`, `lerrJson`, `regionJson`, `loadPlan`'s four
refusals, `runPlan` — now return a `JVal`, and `call` emits every response with
`String.ofList ∘ jemit`; `Json.compress` is off the wire.  A one-key helper,
`jone`, joined `Json.lean`, and `Boundary.lean`'s edits were kept line-neutral
past the import block (+1 line for `import TmKernel.Json`), so the ledger's
`Boundary.lean:N` citations shift by exactly one until the request side lands.
**The request side is untouched at this commit**: `call` still reads with
`Json.parse`, and the readers `getStr`/`getNat`/`getArr`/`strLines`/
`parseRegion`/`parseDoc`/`stampOf`/`parseCmd` still take `Lean.Json`.

*What moved on the wire — measured, not inferred.*  A differential harness ran
79 requests through the kernel at `3c2621c` and through this tree (every corpus
Markdown file alone, each of the five corpus plans whole, 22 command requests
over the W37/September fixture covering all seven verbs — `readopt` and a
day-grain `demote` included — and their parse-tier and kernel refusals, and 15 hand-written requests covering every `err` shape, `\u` control
bytes, a surrogate pair, `\/`, `\b`, `\f`, `null` grain, missing `cmds`, host
whitespace and malformed JSON).  For all 79, the two responses parse to **equal
values**, and the old bytes equal the new value re-emitted with keys sorted under
`jescape`'s classes — so **key order is the only byte change**.  22 responses
are byte-identical (every one-key `err` shape: free text, `kernel`, `dupId`,
`ambiguousDemotion`, `duplicatePath`, `itemCheck`); 57 moved by key order only:
every `ok` document (`path`, `lines`, then `grain`, `ix` — was `grain`, `ix`,
`lines`, `path`) and `badLine` (`path`, `line`, `why` — was `line`, `path`,
`why`).  Two theorems pin the new order at the builders the FFI calls:
`the_response_shapes_emit_in_build_order` (bytes, `decide`, small) and
`the_bad_line_diagnostic_keys_in_build_order` (every `badLine`, `rfl`).  Both
readers of these bytes — `kernel_bridge.rs`'s serde_json and the corpus
harness's hand-written codec — look keys up by name, so the shipped Rust is
untouched; three FFI tests compared or split bytes by key position and were
repaired to the new order, and a fourth was restated: `a_lone_demoted_line_round_trips` (an exact
`assert_eq!`), `which_line_is_the_tombstone_does_not_depend_on_the_document_order`
(split on `"lines":`, which with the new order attributed each document's lines
to its neighbour and failed), and
`a_close_stamps_the_copy_and_leaves_the_week_line_alone` (split on `{"grain"`,
which **still passed** under the new order — but over the whole response rather
than the week document, the separator no longer occurring — and is recorded
here because a test that silently weakened without failing is §9.2's disguise);
all three now split on `{"path":`, which opens
every document object.  The fourth, `the_response_carries_each_documents_horizon`,
was restated to the new order rather than loosened.

*A stack finding, and a proved twin rather than a gap.*  `jescape` is structural
and not tail-recursive, so compiled as written it takes a stack frame per
character.  Measured through the FFI (`examples/oneshot`, `ulimit -s`, 8 GB
memory cap): after the switch a single 100 000-character line **overflowed a
2 MiB stack** (a 60 000-character one did not; 8 MiB failed between 200 000 and
400 000), where `3c2621c` wrote a 1 000 000-character line on 2 MiB.  The fix is
`jescapeTR := List.flatMap escOf` (core's `flatMapTR` at runtime) with
**`jescape_eq_jescapeTR : @jescape = @jescapeTR` as a `@[csimp]` theorem**: the
compiler substitutes the twin and the substitution is proved, so R4's
`@[implemented_by]` ban is not touched, and every `decide` still reduces the
structural `jescape`.  After it, 1 000 000 plain characters and 1 000 000
characters of quote/backslash/tab/non-ASCII/control-byte mix both emit on 2 MiB.
Per-**line** depth did not move: base and new both return 20 000 prose lines and
both overflow at 22 500 on 2 MiB — that bound is the kernel's pipeline, not the
codec, and it predates this route (recorded under the request side's gap
paragraph, next commit, once the parser's own per-element recursion is measured
too).

Re-measured at this commit, from the committed harness (§5.11):
`kernel/check.sh` **7/7 ok**; axiom audit **1210 theorems** (was 1207; +3 under
a new `APPENDED 2026-09-12 (stage-3, J-route step 3 …)` banner), and §6.3's
three counts agree at 1210; every new theorem's axioms are within `propext`,
`Quot.sound`, `Classical.choice`; `Negative.lean`'s transcript is byte-identical
to `3c2621c`'s; corpus **33/37 files and 4/5 whole plans**, unchanged;
`Goals.lean` burn-down **41**, unchanged — the goal waits for the request side;
`cargo test --workspace` **983 passed / 0 failed / 0 ignored across 64
binaries**; the FFI suite **46 tests** (40 kernel + 6 corpus), four of them
edited as above.  Takes no gap and no cheat number.

**J5, the request side, and J6: the JSON edge is the kernel's both ways, and
`the_json_edge_round_trips` is discharged.**  Same 2026-09-12 session, J-route
step 3, second commit.  `call` now reads the request with `jparse` over
`input.toList` and every field through a new reader, `jget` (`Json.lean`, J5
section); `respond : List Char → JVal` is the response value and `call` is
`String.ofList ∘ jemit ∘ respond ∘ String.toList`.  The readers
`getStr`/`getNat`/`getArr`/`strLines`/`parseRegion`/`parseDoc`/`stampOf`/
`parseCmd`/`run` take a `JVal`, and field strings arrive as the `List Char`
`jparse` decoded (ids and titles no longer take a `String` hop).  **What is now
kernel-owned: the whole JSON edge** — scanning, un-escaping, numerals, the
value, field lookup, escaping and emission — each structural, each with its
round trip or refusal proved in `Json.lean`.

*Whether any `Lean.Json` survives on the wire path: none.*  `import
Lean.Data.Json` is gone from `Boundary.lean`, the only module that had it, so no
kernel module imports it (`grep -rn '^import ' kernel/TmKernel --include=*.lean`,
`.lake` excluded, shows only `import TmKernel…`).  The sites that used it, by name: `call` (was `Json.parse` and
`Json.compress`), `jsonErr`/`lerrJson`/`regionJson`/`loadPlan`/`runPlan` (were
`Json.mkObj`, previous commit), `getStr`/`getNat` (were `getObjValAs?`),
`getArr`/`strLines`/`parseRegion`/`parseDoc` (were `getObjVal?`/`getArr?`/
`getStr?`/`getNat?`), and the three witness theorems
`parseCmd_rejects_add_title_variants`, `parseCmd_rejects_edit_variants` and
`parseCmd_reads_the_keyed_edit_forms` (were stated over `Json.mkObj`; restated
over `JVal` literals with their names, conjuncts and expected values unchanged,
each probed under an 8 GB cap first).  What remains are doc-comment mentions
(`Json.lean`'s header and J5 notes, `Boundary.lean`'s gap-6 docstring and J5
sections), all historical.

*Three reading rules changed, each to a named refusal, and every message change
measured.*  The differential harness from the previous paragraph, extended to 91
requests with 12 hostile or non-serde requests, against `3c2621c`: 78 requests
— every corpus file and plan, every command, every `err` shape, and the
hand-written escape, whitespace and `null` cases — still parse to equal values
with key order the only byte change; 13 changed value, and every one is a
request `kernel_bridge.rs` never builds.  (1) **A duplicate key that is read is refused**, `duplicateKey <k>`:
`jparse` keeps both pairs, and `Lean.Json` (like serde_json's `Value`) had
silently kept the last — `{"op":"drop","id":"a","id":"b"}` used to read as a
drop of `b`.
Only the key being read is checked (`jget_ignores_a_duplicate_it_does_not_read`),
and it bites both orders (`jget_refuses_a_duplicate_key`,
`parseCmd_refuses_a_duplicate_field`).  This settles the duplicate-key question
step 2 left for J5, by §5.6 rather than by host imitation.  (2) **A `cmds` that
is present but not an array is refused**, `array expected`: the old reader's
`.error _ => pure #[]` read `"cmds":3` as a request with no commands and
answered `ok` (`run_refuses_cmds_that_are_not_an_array`); an absent `cmds` is
still a read.  (3) **A `grain` carried twice** on a document or a `demote` is
refused, where the old reader silently took the last (measured:
`"grain":1,"grain":2` loaded as grain 2).
Message changes, all on malformed input: an absent field is `property not found:
<k>` (was `String expected` / `Natural number expected`, `getObjValAs?` reading
a missing key as `null`); a parse refusal is `bad json: ` plus `jerrText`'s
constructor name (was Lean's offset text — `{ not json` is now `bad json:
expectedKey n`, `respond_names_a_parse_refusal`); a negative or fractional
number is refused at parse (`notAValue -`, `expectedCommaOrBrace .`) rather than
at the field (`Natural number expected`).  Gaps 42 and 43 became live here —
see the supersessions below.

*The host-agreement obligation — serde_json ≈ `jparse`/`jemit` — is evidenced,
not proved*, exactly the framing gap 12 took for Rust's `split('\n')` against
`Tm.splitOn`: nothing in Lean can mention serde_json.  The evidence, re-run at
this commit: the FFI suite's 45 kernel tests (five new —
`the_request_reads_every_escape_a_host_writes` sends a quote, a backslash,
serde's short `\t`/`\b`/`\f`, `\/`, a control byte as a lowercase quad, `é` as
an uppercase and a lowercase quad, raw two- and four-byte UTF-8, and pins the
kernel's spelling of the response byte for byte;
`a_duplicate_field_is_refused_by_name`, `cmds_that_are_not_an_array_are_refused`,
`a_parse_refusal_names_its_reason`, and
`a_million_character_line_does_not_exhaust_the_stack`); the corpus harness,
whose hand-written codec writes serde's short escapes over every corpus file;
`cargo test --workspace`, whose CLI suites drive every kernel-backed verb
through `kernel_bridge.rs`'s serde_json; the 91-request differential; and a
drive of the shipped `tm` binary — `init`, `add` of titles carrying quotes, a
backslash, `é` and U+2615, `edit est=`, `move`, `drop`, `check` — against a
tree whose `inbox.md` carried a tab, `DEL`, three control bytes, a quote, a
backslash, U+2028 and a 100 000-character line, which the kernel read on every
call and which stayed byte-identical (sha256).

*The escaping decisions step 1 took, now binding on real requests.*  Emit narrow
(Lean's printer's classes: `\"`, `\\`, `\n`, `\r`, a lowercase quad below
`0x20`, everything else verbatim), accept wide (serde's `\/`, `\t`, `\b`, `\f`,
either-case quads); a raw `"` or raw control byte inside a string is refused by
name; a surrogate-pair escape is refused (gap 42).  Numerals are `Text.lean`'s
`digitsOf`; leading zeros are accepted (gap 43).  **R10's stated width for
`JVal.num`**, owed since step 2: unbounded `Nat` on both sides of the kernel,
with no bound to enforce — the host writes and reads `u64` (`as_u64` in
`kernel_bridge.rs`), every number the kernel emits is either a `Fin 3` grain,
an echo of a host-sent `ix`, or a `badLine` index below a line count, so no
emitted number exceeds what the host can read; the one bounded field on the
way in, `grain`, keeps its smart constructor `Grain.ofNat?`.

*A stack finding, closed for characters and recorded for elements.*  The
request-side character recursions got the same treatment as `jescape`:
`junescapeTR`/`junescape_eq_junescapeTR` and `jscanTR`/`jscan_eq_jscanTR`,
`@[csimp]` theorems over accumulator twins, proved by strong induction on the
input length (`junescapeTR_go`, `jscanTR_go`).  Measured through the FFI on
2 MiB: 1 000 000 characters, plain or escape-dense, read and write back; `gdb`
on an element-depth overflow shows the twin (`junescapeTR.go`) as the running
frame, so the substitution is real in the linked archive.  The per-element
recursion is gap 44, next.

**Gap 44 — `jparse`'s and `jemit`'s per-element recursion has no runtime twin.**
(1) *What is not done*: `jarr`/`jtail`, `jobj`/`jotail` and
`jemitTail`/`jemitOTail` recurse once per array element or object pair, not in
tail position.  Measured through `examples/oneshot` (`ulimit -s`, 8 GB cap), on a
request refused right after parsing: 21 500 one-line strings in one array read
and 22 000 abort on a 2 MiB stack (`gdb`: `jtail` frames); 80 000 read and
90 000 abort on 8 MiB.  (2) *Why — a decision*: the character twins were single
functions provable by strong induction; the element twin is an accumulator
restatement of six mutually fuel-structural functions (one six-conjunct fuel
induction, the shape `jparser_fuel` already has) plus a well-founded emitter twin
proved against the four-motive `JVal.rec` — about a session — and for the
dimension that matters, lines per document, the bound is **one the kernel
already had**: `3c2621c` aborts in `splitDoc` (`gdb`) in exactly the same bands,
21 500 / 22 000 on 2 MiB and 80 000 / 90 000 on 8 MiB.  (3) *What it costs*: a
document of more than ~21 500 lines on a 2 MiB thread, or ~80 000 on tm's 8 MiB
main thread, aborts the process loudly (a stack-overflow abort, never a wrong
answer) — unchanged; **newly**, so does a request with that many *documents*:
25 000 one-line documents abort on 2 MiB where `3c2621c` answered (in 16.6 s).
No real plan tree is within two orders of magnitude of either.  (4) *Which
stage clears it*: whichever makes the kernel's per-line recursions tail-recursive
(`splitDoc` first); the codec's element twin alone moves no user-visible bound.

**Goal discharged: `the_json_edge_round_trips` → `the_response_call_emits_parses_back`.**
`theorem the_response_call_emits_parses_back (input : String) : jparse (call
input).toList = .ok (respond input.toList)` — in `Boundary.lean`, audited in
`Check.lean`, and the goal is **deleted from `Goals.lean`**, whose section note
now records the rename.  Whatever bytes `call` returns, for any input, the
kernel's own parser reads back to exactly the value `respond` built; with
`jparse_jemit` (every `JVal`, unconditionally) it is the route the goal's own doc
comment named — "a kernel-owned emitter and fuel-structural parser over the
emitted fragment, round-tripped unconditionally, put on the wire in `call`, with
serde_json agreement … staying corpus evidence".  §7.4, answered: the one binder
is used and there is no hypothesis; the name says what it states; it is about
`call`, which `callExport` is (item 5), and about the whole response string the
host receives (item 6); it is not vacuous — `respond` is not constant
(`respond_names_a_parse_refusal` gives two values) and
`call_refuses_the_real_duplicate_id_request` is the FFI test
`duplicate_ids_are_rejected_at_load` as a theorem: `call (String.ofList
demoRequestBytes) = String.ofList demoResponseBytes`, the parse by
`the_real_request_bytes_round_trip` (no parser run over a literal), the loader's
refusal evaluated by `rfl`, the emission by `the_real_response_bytes_round_trip`.
The honest limit, stated once more: the theorem cannot say that serde_json reads
what `jemit` writes; that is the evidence paragraph above.  I judge the goal
honestly discharged by this — the narrowing is the one licensed in writing, and
the unprovable original (over `partial def`s) quantified over code no kernel
path runs any more.

*Supersessions, by name.*  **"Gap 39 REPRICED"**: its conclusion that
`the_json_edge_round_trips` "can be neither proved nor refuted here" stands for
the `Lean.Json` statement, which is not restated; its residue — the goal
standing in `Goals.lean` "until J6", and every "`Boundary.lean` still builds
`Lean.Json`" in the J-route step 1 and step 2 paragraphs — is superseded: J5 and
J6 are landed and the goal is discharged under the rename above.  **Gap 42**,
part (3): "Today it costs nothing at all, because `Lean.Json` is still the reader
on the wire" is no longer true — `jparse` is the reader, and a surrogate-pair
escape that `Lean.Json` recombined is now refused, measured as `bad json:
badEscape surrogateEscape 55357` (FFI `a_parse_refusal_names_its_reason`); the
cost is otherwise as stated (serde_json never writes one).  **Gap 43**, parts
(3)–(4): the acceptance is now live — `"x":007` in a command, which
`Lean.Json` refused at parse, now reads (measured in the differential) — and J5
landed **without** the strict guard, by decision: no host this kernel has writes
a leading zero.  **The previous paragraph's** "recorded under the request side's
gap paragraph, next commit" is this gap 44.  **`Boundary.lean`'s gap-6
docstring** above `the_char_edge_round_trips` ("The JSON half … stay open in gap
12") was rewritten in place to point here, and `Json.lean`'s header now says the
module is on the wire both ways.  Line numbers: `Boundary.lean` is line-aligned
with `3c2621c` through `run`, so the ledger's citations (`ReqCmd.add` at 815,
`move_out_and_back_is_not_the_inverse`'s 925–931) are exact again.

Re-measured at this commit, from the committed harness (§5.11):
`kernel/check.sh` **7/7 ok**; axiom audit **1223 theorems** (was 1210; +13 under
the same `APPENDED 2026-09-12 (stage-3, J-route step 3 …)` banner: 8 in
`Json.lean`, 5 in `Boundary.lean`), and §6.3's three counts agree at 1223; every
new theorem's axioms are within `propext`, `Quot.sound`, `Classical.choice`;
`Negative.lean`'s transcript is byte-identical to `3c2621c`'s; corpus **33/37
files and 4/5 whole plans**, unchanged; **`Goals.lean` burn-down 40** (was 41;
one goal discharged, none added); `cargo test --workspace` **983 passed / 0
failed / 0 ignored across 64 binaries**; the FFI suite **51 tests** (45 kernel +
6 corpus; five new).  Gap 44 is taken; new gaps start at 45, new cheats at 48.

**A comment is prose — stage 3 step 4, the HTML-comment landmine, cleared
kernel-side (same 2026-09-12 session).**  Supersedes, by name, the kernel-side
"**owed by name**" sentence of the paragraph "The bare-`tm init` tree was
unloadable to the kernel" and the matching "recorded above, the kernel-side
HTML-comment awareness in `scanLines`/`splitDoc`" item of the panic-layers
paragraph's still-owed list; both are landed here.  That paragraph's claim that
the loader should read comments "the way the shipped Rust parser does" is
**corrected**: see the oracle, next.

*The oracle, read first.*  The fork-point `tm-core/src/grammar.rs` has **no
general comment awareness**.  `parse_file` treats exactly one comment form
specially — the generated range `<!-- tm:<name> start … -->` …
`<!-- tm:<name> end -->`, whose lines are `Verbatim` (an unterminated one is a
`Problem` and runs to end of file) — and `ItemLine::parse` demands `- ` at
column 0, so the starter templates' four-space-indented examples were prose to
it by indentation, not by comment.  `tm-spec-v1.md` §3 says only that "lines not
beginning with `- ` are prose/headings/comments and are kept verbatim".  This
kernel's `parseItem` accepts any run of leading spaces, which is how those
indented examples became live items to it.  So there is no shipped behaviour to
match: the kernel's comment reading is a **behaviour change** (§4's last row),
separated from the comment-blind reader it replaces by
`a_commented_item_line_loads_as_prose` — the example line `isItemLine`s `true`
and the splitter files it as prose.

*The rule (Plan.lean, `opensComment`/`closesComment`/`commentAfter`)* is
CommonMark's HTML block type 2 and nothing wider: a comment opens on a line
whose first non-space characters are `<!--`, and closes on the first line — the
opener included — that contains `-->` anywhere; every line from opener to closer
is prose, verbatim.  An inline `<!--` mid-line opens nothing
(`an_item_line_outside_a_comment_is_still_an_item`, second conjunct), so **an
item line can never open a comment** (`item_lines_open_no_comment`): an edit to
an item cannot change how any other line of its file reads.  The generated
markers (`<!-- tm:plan start 10:42 -->`) open and close on their own line, so
the corpus day files read exactly as before.  `commentAfter` is the one step
function; the splitter, the scan, the section derivation and the placement
check all read comments through it (§5.3).

*What changed, by name.*
- **`splitDoc`** is now `splitDocC false`, a splitter carrying the comment state:
  a line read while a comment is open is prose whatever its bytes.  The
  induction lemmas moved to `splitDocC` (`splitDocC_cons`, `_prose_ge`,
  `_items_ge`, `_prose_strict`, `_items_strict`, `_slots_separated`,
  `renderSplit_splitDocC`) and every old `splitDoc_*` name that is still true
  keeps its statement (`splitDoc_prose_ge`, `_items_ge`, `_nil`, `_cons_ok`,
  `_prose_sorted`, `_items_sorted`, `_prose_nodup`, `_items_nodup`,
  `_slots_separated`, `renderSplit_splitDoc`).  `splitDoc_cons_error` is
  **restated without a new hypothesis**: its tail is `splitDocC (commentAfter
  false l)`, which is `splitDoc` unless the line opened a comment.
- **`splitDocC_reads_comments`** is the bridge a `Doc` needs, since a `Doc` keeps
  only prose: read back off the prose alone (`commentOpenFrom`/`inComment`), a
  prose line with no comment open is not an item line, and no item sits where a
  comment is open.
- **`docWf`** is now `ranksAscend d.prose && prose.all (!isItemLine ∨ inComment)`.
  The second conjunct is the feature (a commented item line is admitted); the
  first is a strengthening, so that `inComment`'s list-order reading is the
  rendered file's order on every accepted document (`loadCore_docsWf` discharges
  it from `splitDoc_prose_strict`; `prose_ranks_ascend` reads it back).
- **Three proved theorems narrowed, renamed, and their old `Check.lean` lines
  removed** (the unconditional forms are false of a commented item line):
  `prose_is_never_an_item` → `prose_outside_a_comment_is_never_an_item`,
  `splitDoc_prose_not_item` → `splitDoc_prose_outside_a_comment_not_item`,
  `scanLines_prose` → `scanLines_prose_outside_a_comment`; each gained exactly
  the hypothesis `inComment … = false`.  The old reading is recovered exactly
  where no comment exists: `comment_free_prose_is_never_an_item`.
- **A heading inside a comment is no heading**: `liveHeading`, read by
  `headingsWf` and `lastHeadingBefore` (so by `sectionAt`/`sectionKindAt` and
  §4.2's derivation).  `a_demoted_section_is_a_month_section` and
  `a_pinned_section_is_a_day_section` keep their names and **gain the
  hypothesis** `inComment d.prose q.1 = false` — a `# Demoted` inside a week
  file's comment is not a misplaced section, and the unhypothesised statements
  are false of one.  Witness: `a_commented_heading_is_no_section`.
- **`placementSectionWf` gains `!commentAt p s`** — an item rendered inside a
  comment would read back as prose and vanish from the plan with the file still
  holding it.  Both directions (§5.8): `no_item_sits_in_a_comment` (every
  `WfPlan`, live and archive sites), `an_item_in_a_comment_is_rejected` (the
  bite), and `the_loader_places_no_item_in_a_comment` (the over-bite guard at
  the loader: the conjunct passes every placement `loadPlan` itself read, via
  `commentAt_loadCore_placement` and `entityUncommented_loadEntity`, the shape
  of `entityInRange_loadEntity`).  `firstItemFault` names it
  `sectionDiscipline`; see gap 47 for what that bite can reach.
- **`scanLines`** is `scanLinesFrom path none`: a line inside a comment is not
  scanned, so a broken example shape (`- [Z] …`, an id-less example) in a
  guidance comment is not `badLine`.

*The unterminated-comment decision: refused, by name.*  `LErr.unterminatedComment
path n`, on the wire `{"err":{"unterminatedComment":{"path":…,"line":n}}}`, `n` the
opener's 0-based index (`badLine`'s convention).  Why not CommonMark's
run-to-end-of-document: a stray `<!--` at the start of a line would silently
drop every item below it from the plan — the over-bite §5.8 warns is worse than
the bug — where a named refusal is loud and names the line to fix.  As a
theorem: `scanLines_accepts_only_closed_comments` (every accepted document
leaves `commentAfter`'s state closed); witnessed by
`an_unterminated_comment_is_refused` and the FFI test
`an_unterminated_comment_is_refused_by_name`.  The scan is linear, so a
`badLine` above the opener is reported first.  The host maps the refusal by
name (`kernel_bridge::refusal`, table test extended); driven on the shipped
binary: `tm add` on a tree whose `backlog.md` ended in an open comment exited 1
with `kernel refusal: unterminatedComment — the HTML comment opened at
backlog.md:17 …`, `--json` carrying `detail.refusal:"unterminatedComment"`, the
file's sha256 unchanged; closing the comment made the same `add` succeed.

*The decided witnesses* (Boundary.lean, "A comment is prose — the witnesses"),
each probed under an 8 GB cap first (the probe file ran all of them in 1.3 s,
800 MB peak): one seven-line week document whose comment holds an example
carrying the live item's **own id**, a broken shape and a `# Demoted` — each of
which would refuse the file if read — `a_commented_item_line_loads_as_prose`,
`the_commented_request_loads` (scan `rfl`, `loadsOk` by `decide`),
`the_commented_request_round_trips` (an instance of
`the_kernel_reads_back_what_it_writes`, whose statement is unchanged),
`a_commented_heading_is_no_section`, `an_item_line_outside_a_comment_is_still_an_item`
(the markers removed: `dupId` again), `an_unterminated_comment_is_refused`.

*Host side — the templates' natural bullets restored.*  `week-body.md`,
`month-body.md` and `backlog.md` carry their `- [ ]` examples again (exactly
`bd61f11^`'s bytes), superseding that paragraph's "Host-side fix, taken".  The
guard is `init_tree.rs`'s `every_kernel_backed_verb_works_on_a_bare_init_tree`:
a fresh `tm init`, asserting the landmine is armed (`@m2 after:^t4 ^t5` inside
the week comment), then `add` ×2, the keyed `edit est=`, `rank`, `move`,
`demote`, `readopt`, `drop` — every kernel-backed verb — each exit 0, every
guidance comment byte-identical after, and `tm check` clean.  Measured to bite:
with this step's two Lean files stashed (kernel at `b7f504d`), the test fails on
its first `add` with `kernel refusal: itemCheck — … (danglingDep)`.  FFI:
`an_item_line_inside_a_comment_is_prose` (load, byte-identical echo, an `est` on
`^m1` changes the live line and not the example, and the uncommented pair is
`dupId`).

*Cost, measured.*  A 3 800-line week document (200 headings, 2 000 items)
through `examples/oneshot` with one `est` command: 1.34 s at `b7f504d`, 1.37 s
here; with 200 three-line comments added, 1.42 s.

**Gap 45 — `tm-core`'s parser is comment-blind, so the host's old-path readers
disagree with the kernel about a column-0 item line inside a comment.**
(1) *What is not done*: `tm_core::grammar::parse_file` (and so `tm check`, the
planner, the TUI's today screen, every verb still on the old path) reads
`- [ ] … ^id` at column 0 inside `<!-- … -->` as a live item.  (2) *Why*: this
step's scope is the kernel; teaching the fork-point parser the same rule is
host work, and the templates no longer depend on it (their examples are
indented, which `ItemLine::parse` already reads as prose).  (3) *What it
costs*, driven: with `<!--`, `- [ ] 2 30m Hidden ^h1`, `-->` appended to a fresh
tree's `backlog.md`, `tm plan` schedules `Hidden` at 09:00 while `tm drop ^h1`
is refused `noSuchId`, and `tm check` reports no problems.  A commented id that
collides with a live one is a `tm check` dup-id while the kernel accepts the
tree.  Nothing is written wrongly — the kernel-backed verbs never see the
commented line — but the two readers answer differently.  (4) *Which stage
clears it*: whichever retires `parse_file` for kernel reads (stage 7's
cut-over), or a host change that calls `commentAfter`'s rule in Rust with a
differential test against the kernel.

**Gap 46 — the comment rule's edges, decided narrowly and not widened.**
(1) *What is not done*: the kernel does **not** read the lines *between* a
generated range's markers (`<!-- tm:plan start -->` … `<!-- tm:plan end -->`)
as verbatim, which the fork-point Rust does; each marker is a one-line comment
to it, so a `- [ ] … ^id` row inside a generated block is live.  The opener
accepts **any** number of leading spaces (CommonMark: at most three; four is an
indented code block) and no tabs (`isSp` is the space alone).  (2) *Why*: the
generated block's rows are timeline text (`emit.rs`'s `render_row`), never
`- [ ]` lines, so the range rule buys nothing today and would be a second state
machine; the indentation latitude matches `parseItem`'s own.  (3) *What it
costs*: a hand-edited item line pasted into a `tm:plan` block is read as an
item (in §4.3's day file, whose block precedes `# Pinned`, a
`sectionDiscipline` refusal — loud);
a four-space-indented `<!--` opens a comment a CommonMark renderer would show as
code.  (4) *Which stage*: stage 6, if the planner's block ever carries item
lines.

**Gap 47 — `placementSectionWf`'s comment conjunct is unreachable through
`run`; its bite is a proof, not a test.**  (1) *What is not done*: no wire
request can make it refuse.  (2) *Why*: prose never changes after load, and on a
loaded document the only free ranks are vacated item ranks (outside every
comment, by `splitDocC_reads_comments`) and ranks past the last line, where the
state is closed once `scanLines` has accepted the file — so a command ranking a
line into a comment is `rankCollision` first.  It stays because `planWf` is a
claim about `PlanCore`, not about `run`: `loadPlan` alone does not scan, and a
plan it accepts with a trailing open comment would take an append into it
(`an_item_in_a_comment_is_rejected` is that bite).  (3) *What it costs*: a
checker no wire input can fail, written down per §9.2; and when it does bite it
is named `sectionDiscipline`, not something more specific.  (4) *Which stage*:
none needed unless a command ever writes prose.

*Goals and ledger.*  No `Goals.lean` goal states this property, so none is
discharged and none is added; `Negative.lean` is untouched and its transcript
is byte-identical to `b7f504d`'s (compared by stashing the two Lean files and
rebuilding); no cheat is added.

Re-measured at this commit, from the committed harness (§5.11):
`kernel/check.sh` **7/7 ok**; axiom audit **1257 theorems** (was 1223; +37 names
under the new `APPENDED 2026-09-12 (stage-3, step 4: a comment is prose)` banner,
−3 renamed away), and §6.3's three counts agree at 1257; every new theorem's
axioms are within `propext`, `Quot.sound`, `Classical.choice`; corpus **33/37
files and 4/5 whole plans**, unchanged (no corpus file carries an item line
inside a comment; the four refusals are `plan-conflicts`' deliberate ones);
**`Goals.lean` burn-down 40**, unchanged; `cargo test --workspace` **984 passed
/ 0 failed / 0 ignored across 64 binaries** (was 983; +1,
`every_kernel_backed_verb_works_on_a_bare_init_tree`); the FFI suite **53
tests** (47 kernel + 6 corpus; two new).  Gaps 45–47 are taken; new gaps start
at 48, new cheats at 48.

**Gap 40's bridges — stage 3 step 5: eight more keys reach the wire (same
2026-09-12 session).**  Supersedes, by name, the list in "**Gap 40 (edit): nine
of the eighteen keys are deliberately not wired**" (`due`, `at`, `win`,
`every`, `on-event`, `after`, `loc`, `waiting` — every one of them is wired
now) and the edit-widening paragraph's "Wired keys … `est`, `dur`, `buffer`,
`pref`, `on-miss`, `after-done`, `min`, `max`, `ci`" as the complete set.  Its
**`demoted` exclusion stands unchanged**: `keyEditable .demoted` is still
`false`, the wire still answers `keyNotWired demoted`, and Negative.lean CHEAT
45 is still the door staying shut.  **Gap 40's status now: 17 of 18
`Field.Key`s are on the kernel's edit path; the one left is `demoted`, by
policy; no key is blocked by a missing bridge.**

*The shared fact (§5.3), proved once.*  `Field.readNat_lt_pow_length`: a
numeral `readNat` reads from `k` characters is below `10 ^ k` (by
`readNat_foldl_lt`, the fold's own induction, and `charDigit_lt`).
`parseDate` demands a four-character year and `mkDate?` a valid date
(`mkDate?_some`), and `Cal.ofDay_toDay` hands that year back, so
**`parseDate_dayWf`**: every parsed date is `dayWf`.  `due`
(`parseMoment_wf`, both forms), `waiting` (`parseDate_dayWf` itself) and both
ends of a long `at:` (`parseDT_wf`) inherit it; no second width argument
exists.

*The other bridges, one per parser the view binds* (Line.lean, end of file,
under "Parse ⇒ wf"): `parseRule_wf` (the six literal forms, `month:` in 1–31,
a non-zero `Nd`/`Nw`/`Nw:Day` period, a non-empty weekday list),
`parseOnEvent_wf`, `parseDep_wf` → `parseDeps_wf` (through `mapOpt_all`),
`parseLoc_wf`.  Each is an implication out of the parser, so the wire value is
bounded by the loader's grammar and nothing else.

*The one bridge that is false, and the decision.*  `parseEndShort` rolls a
short end that precedes the start onto the next day, and on 9999-12-31 that day
has a five-digit year `renderDate` cannot write back: the loader reads
`at:9999-12-31T23:00/01:00` and `intervalWf` refuses it.  Stated exactly
rather than weakened (§3.1 item 4): `parseInterval_spec` /
`parseInterval_wf_unless_rollover` say the rollover is the **only** way a parsed
interval fails `intervalWf`, and `parseWindow_wf_unless_rollover` carries it to
`win:`'s absolute form.  **Decision: the edit path refuses it, by name**
(`badValue at`), because writing it would put bytes on the line no loader reads
back.  Witness: `the_year_9999_rollover_parses_but_the_edit_refuses_it`
(`decide`; the day before, 9999-12-30, is accepted — the bite is exactly the
rollover).

*`loc:`'s word bound — the one value that is free text.*  `parseLoc` accepts
any non-empty word, so a wire value could carry a byte no loaded token can: a
space splits the token on re-read (`loc:a b` reads back as `loc:a` and a title
word), a newline splits the line, a tab is gap 32's.  `WordLoc` bounds it in the
type: `locOk c := c.wf && locWordOk (renderLoc c)`, `locWordOk` = no space and
no C0 control byte.  `editValOf_loc_refuses_only_a_bad_or_unworded_value` says
that is all it adds to `parseLoc` (via `renderLoc_parseLoc`: the parser hands
back the word it read), and `wordLoc_renders_a_word` discharges
`setKey_line_reparses`'s `wordWf` hypothesis for every written `loc:`.
Measured through `examples/oneshot`: `loc=café` writes `loc:café` and re-reads
byte-identically; a name carrying the byte U+0001 is `badValue loc`.

*The table (Cmd.lean).*  Eight `EditVal` constructors, each carrying the
wf-bounded subtype its setter's `view_set_*` needs (`WfMoment`, `WfInterval`,
`WfWindow`, `WfRule`, `WfOnEvent`, `WordLoc`, `WfDay`, `WfDeps`), built by one
R10 smart constructor, `guardWf` (the parser's answer kept only with its wf
proof).  That the guard is not a second grammar is a theorem per key, off the
bridges and `guardWf_isSome`: `editValOf_due_refuses_only_what_parseMoment_refuses`,
`editValOf_every_refuses_only_what_parseRule_refuses`,
`editValOf_onEvent_refuses_only_what_parseOnEvent_refuses`,
`editValOf_waiting_refuses_only_what_parseDate_refuses`,
`editValOf_after_refuses_only_what_parseDeps_refuses` (all exact), the `loc`
one above, and `editValOf_interval_refuses_only_a_bad_value_or_the_rollover` /
`editValOf_window_refuses_only_a_bad_value_or_the_rollover`.  Write side:
`setVal`'s eight new arms are `setDue`/`setAt`/`setWin`/`setEvery`/
`setOnEvent`/`setLoc`/`setWaiting`/`setAfter`, and
**`the_edit_path_writes_what_the_field_path_reads` keeps its name and gains
eight arms** (the `after` arm is stated on `Core.after` itself);
`setVal_writes_the_token_the_loader_reads` covered them with no change to its
proof.  Upward: `the_eight_bridged_keys_accept_their_spec_values`.

*`after` meets the plan tier, and its refusals are named.*  An `after:` edit
can dangle or cycle, and `mapAt`'s only name for a post-state failing `planWf`
was `badHorizon` — advice about relocation.  Two `KErr` constructors,
`danglingDep` and `depCycle`, and one renaming step: `applyCmd` routes `.edit`
(and the standing `.est` op, so `the_est_op_is_the_keyed_est_edit` is still
`rfl`) through `nameEditFault`, which rewrites `.error .badHorizon` into
`editFault` — `danglingDep` if `afterTotal` fails of `editPost` (exactly the
store `mapAt` re-checked), else `depCycle` if `afterAcyclic` does, else
`badHorizon` as before — and passes everything else through
(`nameEditFault_ok`: it never manufactures a success).  §5.8 both ways:
`edit_of_a_dangling_after_is_refused_by_name`,
`edit_of_a_cyclic_after_is_refused_by_name` (both through
`applyCmd_edit_names_the_plan_tier_fault` and `editFault_of_get`), and the
honest success form `applyCmd_after_succeeds` — the two dependency conjuncts of
the post-state as hypotheses, plus the four an edit can break by other means,
concluding the stored item's `Core.after` is the parsed list.  Not vacuous:
`the_after_refusals_are_named_on_a_loaded_plan` decides, on a loaded
two-item week, `^zz` → `danglingDep`, a two-item loop and a self-dependency →
`depCycle`, `event:visa` → success.  **Behaviour of the shipped ops is
unchanged**: `after` was `keyNotWired` before, and for every other key the
rename cannot fire on a well-formed plan, since a setter of another key leaves
the `after:` token — and so both dependency conjuncts — as they were (argued
from `setKey`'s per-key replace/insert, **not** a theorem; the FFI suite's 47
pre-existing kernel tests pass, one of them with its `keyNotWired` witness
moved from `due` to `demoted`).  Proof-side, the three existing theorems that
unfolded `applyCmd`'s edit arm (`edit_of_a_tabbed_line_is_refused`,
`applyCmd_edit_succeeds`, and the `est`/`edit` arms of
`move_has_no_inverse_command`) keep their statements and gained one step each.
Host side, `kernel_bridge::refusal` maps the two names (table test extended);
the `keyNotWired` message no longer points at deferred keys.

*Parse tier, by name (§5.7).*  `parseCmd_refuses_the_bridged_keys_bad_values`:
`due=2026-02-30`, `at=2026-09-07T13:50/2026-09-06T12:00` (an end before its
start), `at=9999-12-31T23:00/01:00` (the rollover), `win=25:00-13:00`,
`every=0d`, `on-event=re ply`, `loc=a b`, `waiting=2026-9-20`, `after=^` —
each `badValue <k>`, by `rfl`.  `parseCmd_reads_the_bridged_keys` is the
positive form.  `parseCmd_rejects_edit_variants` keeps its name; its
`keyNotWired` witness is now `demoted` (was `due`).

*FFI, end to end* (kernel.rs, "Gap 40's bridges" block; success bytes asserted
as the whole rewritten line): `edit_keyed_due_writes_both_forms`,
`edit_keyed_at_writes_the_short_end` (a same-day long end is written short),
`edit_keyed_win_writes_the_overnight_window`,
`edit_keyed_every_writes_the_canonical_rule` (`daily` → `every:day`),
`edit_keyed_on_event_replaces_in_place`, `edit_keyed_loc_writes_a_name_and_an_enum`,
`edit_keyed_waiting_replaces_in_place`,
`edit_keyed_after_writes_a_dependency_the_plan_holds`,
`edit_keyed_after_refuses_a_dangling_or_cyclic_dependency_by_name` (`^zz`,
`^t3` on `^t3`, and a two-command loop), and
`the_bridged_keys_refuse_bad_values_by_name` (the nine refusals above);
`edit_refusals_are_named` now asserts `keyNotWired demoted`.  Measured by hand
through `examples/oneshot`, each key's written line fed back with no commands
re-reads byte-identically (`due:2026-09-11T23:59`,
`at:2026-09-07T23:50/2026-09-08T00:10` — a rolled short end is written long —
`win:22:00-02:00`, `every:2w:Sun`, `on-event:reply/7d`, `loc:café`,
`waiting:2024-02-29`, `after:^b1,event:visa`).

*Negative.lean*, new banner "APPENDED 2026-09-12 (stage-3, step 5: gap 40's
bridges)": **CHEAT 48** (an empty `after:` payload, `rfl` against
`depsWf [] = true`) and **CHEAT 49** (a `WordLoc` with a space, `rfl` against
`locOk`), each with a compiling control checked first; the transcript is
`a4ccd9c`'s with exactly those two errors appended (diffed against the committed
file run on this build).

**Gap 48 — the host does not route the eight newly wired keys.**  (1) *What is
not done*: `tm/src/cli/items.rs`'s `KERNEL_EDIT_KEYS` still lists the nine; `tm
edit ^id due=…` (and `at`, `win`, `every`, `on-event`, `loc`, `waiting`,
`after`) still goes through the old Rust path.  (2) *Why*: this step's scope is
the kernel's edit path; routing changes shipped behaviour (canonical rendering —
`every=daily` would write `every:day`, a same-day long `at:` end would be
written short — and the named refusals), which wants its own `cli_items.rs`
coverage and the 30-minute drive (§5.13).  (3) *What it costs*: the shipped
binary's behaviour for those keys is the fork-point Rust's, unverified; the
kernel's answers are evidenced by the FFI suite only.  (4) *Which stage*: the
next stage-3 host step — add the eight to `KERNEL_EDIT_KEYS`, and extend
`edit_refuses_a_value_its_own_check_would_reject` (it already drives
`due=notadate` and `due=2026-09-11T23:59`).

**Gap 49 — the edit path is narrower than the loader in two named places.**
(1) *What is not done*: the edit refuses (a) an `at:`/`win:` value whose short
end rolls past 9999-12-31 and (b) a `loc:` name carrying a C0 control byte —
both values the loader reads from a file.  (2) *Why, a decision*: (a) no
four-digit year can write the rolled end back, so accepting it would write bytes
no loader re-reads; (b) the tokenizer cannot carry a newline and gap 32 refuses
tabs, and the bound was taken at "no control byte" rather than enumerating the
safe ones.  (3) *What it costs*: an item that already carries such a value
loads and round-trips verbatim, but `tm edit` cannot set that value; nothing is
misread.  (4) *Which stage*: none needed for (a) before year 9999; (b) widens
if a real `loc:` name ever needs a control byte.

**Gap 50 — every other plan-tier edit refusal is still `badHorizon`.**  (1)
*What is not done*: `editFault` names only the two dependency conjuncts; an
edit whose post-state fails `shapesWf` (or any other `itemsWf` conjunct) is
refused as `badHorizon`.  (2) *Why*: `after` is the key whose plan-tier failure
this step owed by name; `firstItemFault` could name them all, but the `KErr`
vocabulary for commands is a host-visible decision.  (3) *What it costs*,
measured through `examples/oneshot`: `{"op":"edit","id":"O1","key":"due",
"value":"2026-09-11"}` on a month outcome (§4.3: a month item has no shape)
answers `{"err":{"kernel":"badHorizon"}}`, and so does `at=…` — the refusal is
real and nothing is written, but the host's message ("a destination that is not
in the plan …") is advice about moves.  Pre-existing for `dur`/`after-done`.
(4) *Which stage*: the host step that clears gap 48, since `due`/`at`/`win` on
a month item is where users will meet it.

**Gap 51 — the edit path's re-read is a theorem for `loc:` only among the
wired values.**  (1) *What is not done*: `wordWf v.rendered` is proved for
`loc:` (`wordLoc_renders_a_word`) and for the `est:`/`ci:` renderings
(`wordWf_renderDur`, `wordWf_renderCi`), not for `due`/`at`/`win`/`every`/
`on-event`/`waiting`/`after` nor for the edit widening's `pref`/`on-miss`/
`after-done`/`min`/`max` renderings, so `setKey_line_reparses` is not
instantiated over every `EditVal`.  (2) *Why*: each is a character-class lemma
over its renderer (`renderDate_chars`, `renderClock_chars` and `isName_avoids`
already exist); time, not a decision.  (3) *What it costs*: "the line an edit
writes re-reads to the same tokens" is evidenced for those keys by the FFI
suite and the oneshot re-read above, not proved.  (4) *Which stage*: stage 3's
closing step, as one theorem `∀ v : EditVal, wordWf v.rendered = true`.

*Goals and ledger.*  No `Goals.lean` goal states a keyed-edit property, so none
is discharged and none is added.  Re-measured at this commit, from the committed
harness (§5.11): `kernel/check.sh` **7/7 ok**; axiom audit **1299 theorems**
(was 1257; +42 under `APPENDED 2026-09-12 (stage-3, step 5: gap 40's bridges)`:
18 in Line.lean, 16 in Cmd.lean, 8 in Boundary.lean), §6.3's three counts agree
at 1299, and every audited axiom is `propext`, `Quot.sound` or
`Classical.choice` (no `sorryAx`); corpus **33/37 files and 4/5 whole plans**,
unchanged; **`Goals.lean` burn-down 40**, unchanged; `cargo test --workspace`
**984 passed / 0 failed / 0 ignored across 64 binaries**, unchanged (the host's
refusal-table test grew two rows inside one test); the FFI suite **63 tests**
(57 kernel + 6 corpus; ten new).  Every new `decide` witness was probed first
under an 8 GB cap (each probe file ran in under a second).  Gaps 48–51 are
taken; new gaps start at 52, new cheats at 50.

**Stage 3 closes here — the handover (same 2026-09-12 session, step 6; a
documentation step: no Lean, no Rust, no gap or cheat numbers taken).**  Stage 3's
scope is landed and its ledger is at rest.  The shipped `tm` binary calls the
kernel for all seven verbs through one choke point, and the duplicate-id class is
dead there (A6's single-command reproduction is refused `occupied` with nothing
written); a kernel fault is a named `kernelFault` with the terminal restored,
never exit 0; three of the four integration countermeasures stand, the fourth
being stage 6's by PLAN's own row; the JSON edge is the kernel's own both ways
(`jparse` in, `jemit` out, `the_response_call_emits_parses_back`); a comment is
prose; seventeen of eighteen keys are on the kernel's edit path.  All twelve of
stage 3's `Goals.lean` goals are gone — eight proved as stated, one restated
over the kernel's own splitter and proved (the file split), two refuted under
renamed negations (L22; joining lines, at the char level), one narrowed as its
doc comment licensed (the JSON edge) — and no predicate was weakened for any of
them.  What stage 3 did
**not** do is as real, and is listed below.  Re-measured at `bf7cc63`, every
command under the 40 GB memory cap: `kernel/check.sh` **7/7 ok** (1.10–1.13 s
warm over four runs); axiom audit **1299 theorems**, §6.3's three counts agreeing
at 1299 with the same two cancelling off-by-ones; `Goals.lean` burn-down **40**
(0/11/14/15 across stages 3/4/5/6); corpus **33/37 files and 4/5 whole plans**,
unchanged through the stage; `cargo test --workspace` **984 passed / 0 failed /
0 ignored across 64 binaries** (4.9 s warm); the FFI suite **63 tests** (57
kernel + 6 corpus); ten modules, 20,902 lines (23,724 with the root, `Check`,
`Negative` and `Goals`); archive 3,704,386 bytes; `cargo build -p tm` into an
empty target directory, the archive already built, 18.1 s.  Gaps run to 51 (new
gaps start at 52) and cheats to 49 (new cheats start at 50).  `AGENTS.md` was
re-measured at this commit — its every number predated OpenCode's nine commits
and this session — with one lesson added (§5.10a, the memory cap), one
subsection (§7.5, both suites are acceptance), and the owner's 2026-09-12
decisions recorded in its §10.5, which this block had not carried: **D1** `close
day` targets the week containing *now* (stamp `demoted:D<dd>`, the 16-period
catch-up collapses to one step per grain); **D2** ids stay digits and spec §3.1's
width sentence is weakened (gap 13 closed); **D3** the close `report` is a
per-item list; **D4** `main` discarded (recorded above).  §10.5 q1's second half
is **withdrawn**: the week→month behaviour change it and AGENTS §8.2 trap (b)
describe does not exist — `horizon::close_week` already computes `closeTo week
now` — and `Cal.lean`'s header, this README's "month of today" row and its
week → month tie-break section frame it otherwise; stage 4's first step repairs
those sites.  One wording note on the new lesson: v4.33.1 does hand
`maxHeartbeats` to kernel checking (`addDeclCore`, `Lean/Environment.lean`), so
§5.10a states the rule as "heartbeats are not memory, and no budget stopped the
measured runs" rather than "the kernel has no budget".

**Still owed at stage 3's close, by name.**

- **Gap 48** — the host does not route the eight newly wired edit keys
  (`KERNEL_EDIT_KEYS`); the next host step, with **gap 50** (every other
  plan-tier edit refusal is `badHorizon`).
- **Gap 51** — `∀ v : EditVal, wordWf v.rendered = true`, proved today for `loc`,
  `est`, `ci` only; priced as stage 3's closing theorem.
- **Gap 44** — `jparse`/`jemit` per-element recursion has no runtime twin;
  cleared with `splitDoc`'s per-line recursion.
- **Gap 45** — `tm-core`'s parser is comment-blind, so the old-path readers
  disagree with the kernel; stage 7's cut-over or a host port of `commentAfter`.
- **Gap 46** — the comment rule's generated-block and indentation edges; stage 6
  if the planner's block ever carries item lines.
- **Gaps 41, 42, 43, 47, 49** — decisions recorded (unset clears one slot;
  surrogate pairs refused; leading zeros accepted; an unreachable `planWf`
  conjunct; two narrow edit refusals); no work owed unless a host or user needs
  it.
- **`add`'s command-shaped `itemsWf` bite** has no Lean theorem (Rust test only,
  `1a85e25`).
- **`now` in the request** — stage 3's schema item, not done; stage 4 adds it.
- **The differential oracle** still extracts `main` and fails; it must move to
  `4748911`, and stage 5's parity is against the fork point.
- **The depth-3 sweep harness** — `invariant_exhaustive.rs` was discarded with
  `main`; rebuild before PLAN §6.3's most consequential gate can be costed.
- **Housekeeping writes precede a kernel refusal** on a stale tree — stage 4,
  when `close`/`autoClose` enter the kernel.
- **Two newline conventions** (bridge versus legacy writers) — retire with
  stages 4 and 6 and gap 5.
- **Still-open inherited gaps**: 5 (id-less lines), 10 (the kernel believes any
  declared region), 12's remainder (a doc line carrying a literal newline is
  accepted), 22 (`parent`), 31 (a `[-]` anywhere is an archive copy; **§10.5
  q9**), 32 (`isSp`, narrowed on the edit path only), 33 (every `^` word is an
  id), 35, 36.
- **Ledger hygiene**: `Negative.lean`'s 27–30 renumber (AGENTS §6.5);
  `tm/DORMANT.md` and `Goals.lean`'s `# STAGE 3` header sentence, both stale
  (AGENTS §10.2); `check.sh`'s check-6 comment still credits it with the JSON
  escaping the kernel now proves.
- **Waiting on the human** (AGENTS §10.5): **q3** `parent` — blocks stage 5 and
  B3's firing in stage 4; **q4** which side replays the log; **q5** R7's
  `p_lounge` rounding; **q6** L24/L25 prove or keep the proptest; **q7**
  lifecycle commutation; **q9** the `[-]` placement rule; and the 30-minute drive
  of the stage-3 binary (AGENTS §5.13).  **Stage 4 is unblocked.**

**Verification repair — two narrowings renamed (same 2026-09-12 session).**
This supersedes, by name, step 4's sentence "`a_demoted_section_is_a_month_section`
and `a_pinned_section_is_a_day_section` keep their names and gain the hypothesis
`inComment d.prose q.1 = false`", and the §4.2 row of the "section discipline"
table, which cites the old names.  An independent read-only verification of stage
3's close found the names and the demoted docstring ("wherever it is written")
still describing the unhypothesised statement, which is false of a commented
heading (`a_commented_heading_is_no_section`), against AGENTS §7.4 item 3 ("does the name
match the statement?") and against the treatment of their three siblings
in the same commit.  Renamed, statements and proofs unchanged:
`a_demoted_section_is_a_month_section` →
`a_demoted_section_outside_a_comment_is_a_month_section`,
`a_pinned_section_is_a_day_section` →
`a_pinned_section_outside_a_comment_is_a_day_section`; both docstrings now name
the comment exclusion and the witness.  Old `Check.lean` lines removed, the new
ones appended under `APPENDED 2026-09-12 (stage-3, verification repair)`; nothing
else referenced them.  Re-measured: `check.sh` 7/7 — axiom audit **1299**
(unchanged: two removed, two added), corpus 33/37 files and 4/5 whole plans,
`Goals.lean` burn-down **40** (unchanged); `cargo test --workspace` **984
passed / 0 failed** across 64 binaries (unchanged).

<!-- ===================================================================
     APPENDED 2026-09-12 (stage-4 session, rebuild-on-lean).  Opens stage 4.
     Step 1 is documentation only: the owner's decisions D1–D4, the week→month contradiction repaired, the stage priced.  Takes gap 52; no cheat numbers.
     =================================================================== -->

## Stage 4 opens 2026-09-12: the owner's decisions, one contradiction repaired, the stage priced

Baseline re-measured at `a8bb800` before this block, every command under the 40 GB
memory cap (AGENTS §5.10a): `kernel/check.sh` **7/7 ok** — axiom audit **1299
theorems**, corpus **33/37 files and 4/5 whole plans**, `Goals.lean` burn-down
**40** (0/11/14/15 across stages 3–6); `cargo test --workspace` **984 passed / 0
failed / 0 ignored across 64 binaries**.

**The owner's decisions, taken 2026-09-12 after driving stale trees with the
restored binary.**  Settled in the AGENTS §4 sense: build on them, and changing
one needs the owner again.  The stage-3 handover paragraph above named them in
one sentence each; this is their record, with the evidence.

- **D1 — `close day` targets the week containing *now*.**  The kernel's derived
  `closeTo day now`, not `targetContaining day closedDay` (the week the closed day
  belonged to, which is what fork-point `horizon::close_day` does via
  `IsoWeek::from_date(date)`).  Decided on four driven scenarios; the owner drove
  them, and the mechanism given for each is read off the fork-point
  `close_day` / `close_week` / `auto_close` (`4748911`, identical to the restored
  `tm-core/src/horizon.rs`), not re-driven in this step:
  1. *Skipping a weekend double-stamps the leftovers.*  Monday's first command
     closes Saturday and Sunday one day at a time, each moving still-open
     `# Pinned` items into the week containing *that* day with `demoted:D<dd>`, and
     the week close in the same sweep demotes them again with `demoted:W<nn>` — two
     stamps, which is `/plan-month`'s "≥ 2 stamps" cut list.
  2. *…and drops them off Monday's plan.*  The same leftovers end in
     `month/<current>#Demoted`, and §6.2 says month items are not day-planner
     candidates, so work that was pinned on Friday is invisible on Monday.
  3. *An item whose parent is in the closing week is deleted, its minutes silently
     absorbed.*  A pinned child moved by `close_day` into the week being closed is,
     at `close_week`, an "unfinished child of a demoted item", so it is removed
     from the week file and its remaining folded into the parent's `est:` with no
     line left to say it existed.
  4. *A day closed more than 16 days late strands work in a sealed file.*
     `catch_up` returns only the most recent `AUTO_CLOSE_CATCHUP = 16` days; older
     days are recorded closed in `state.json` without running, so their pinned items
     stay in a day file the planner never reads again.

  **What D1 settles.**  (i) The target is `closeTo` at every grain, so
  `closeTo_target_is_open` is the argument L16 gets (AGENTS §8.2's "if assent is
  refused" trap is moot).  (ii) The stamp stays `demoted:D<dd>` — the day is the
  fact; the week was only the destination — so `close_day_stamps_a_day_stamp`
  keeps its statement.  (iii) `AUTO_CLOSE_CATCHUP = 16`'s period-by-period
  iteration collapses to one step per grain (`autoClose_is_each_grain_once`), which
  is what removes scenarios 1 and 4 at the root; scenario 3 goes because the child
  lands in the open current week, never in the week being closed.  (iv) It is the
  precondition for L16.
- **D2 — ids stay digits.**  `freshId` is proved and ships `^9`, `^10`; the recorded
  resolution of gap 13 was always "weaken the spec, not the data", and digits are a
  subset of `[a-z0-9]`.  **Settles:** gap 13 **CLOSED** (supersedes, by name, "Gap
  13 stands open." in the 2026-09-12 stage-3 continuation block) and AGENTS §10.5 q2.  **Owed, not
  done here:** the spec text itself still says "4 chars" at `tm-spec-v1.md` §3.1's
  `Item` listing and §17.2's "Ids:" bullet; weakening those sentences is a
  one-line spec edit nobody has made.
- **D3 — the close `report` carries a per-item list.**  For each item: its id, what
  happened to it (the disposition), where it went (the destination), which stamp it
  gained, and its minutes as an integer numerator/denominator pair.  Decided
  against *counts only*, because the month review would then re-derive per-item
  history from the files — a second reader of one fact, the defect class this
  rebuild removes — and against stage 6's full diagnostics surface, which is not
  due yet.  **Settles:** AGENTS §10.5 q8.  AGENTS §8.2's four report rules (under
  `ok`, bounded fields with smart constructors, named entries, no division) still
  govern the shape.  No code exists.
- **D4 — `main` is discarded** (`f386c56`; recorded in full in the stage-3 block
  above).  The oracle is the in-clone fork point `4748911`; the restored Rust is
  pre-stage-0 in `move_to` only.

**The week→month "behaviour change" does not exist — the contradiction repaired.**
Four sites disagreed about `horizon::close_week`, all landed in `6f67873`:
AGENTS §8.2's named trap (b) and §10.5 q1's second half called it a pending
behaviour change needing assent; the cheat table's row 24 ("declare
`horizon.rs:1543`'s 'month of today' stable") and this README's section "The
week → month tie-break, which is a choice" ("**Rejected:** 'the month of today',
which is what `horizon.rs:1543` does"), with `Cal.lean`'s header, framed that Rust
line as the rejected alternative; and `Grain.lean`'s
`closeTo_week_is_not_monthOfWeek` docstring ("The tie-break is not the close rule,
and must not be confused with it") said the opposite.  **`Grain.lean` is right.**
Checked in this step, writing nothing into the repo:

- fork-point `horizon::close_week` sets `let month = YearMonth::from_date(cx.today())`
  and hands it to `demote_one`, which is where the `# Demoted` copy goes — spec
  §6.3's `month/<current>#Demoted`;
- a scratch file importing the built `TmKernel.Grain` proved, by `decide` under an
  8 GB cap (well under a second), `closeTo week now = ⟨month, 12·(y−1) + (m−1)⟩` —
  the Rust's `(year, month)` of `now` as a month ordinal — at `now` = 2026-09-07
  (closing W36, Aug 31–Sep 6), 2026-08-31 (the straddle's own Monday), 2027-01-04
  (closing 2026-W53) and 2026-10-15 (a late close);
- and `(closeTo week now).ix = Cal.monthOfWeekByToday w now` holds by **`rfl`**.
  The "rejected alternative" *is* the close rule's month: one function in two
  roles, right as a destination (a close happens at a time) and wrong as a *name*
  for a week's month (a name must not depend on when you asked).  The
  `#eval`s show the two roles differ exactly where `Grain.lean` says: at `now` =
  2026-08-31 `closeTo` gives August while `monthOfWeek` names W36 September; at
  2027-01-04 `closeTo` gives January 2027 while `monthOfWeek` names 2026-W53
  December 2026.

So the Rust already computes `closeTo week now`, no behaviour change is pending at
the week grain, and §10.5 q1's second half is **withdrawn**.  Repaired sites:
AGENTS §8.2's trap (rewritten to state the above) and §10.5 q1 and §10.2's row;
`Cal.lean`'s module header and `monthOfWeekByToday`'s docstring (comments only —
no statement, definition or proof changed).  **Superseded here, by name, and not
edited:** the cheat table's row 24 — cheat 24 still fails to compile and still
stands as a cheat against the tie-break, but its attribution to `horizon.rs:1543`
is wrong; the "**Rejected:**" paragraph of "The week → month tie-break, which is a
choice", whose first sentence is wrong for the same reason (its closing paragraph,
`closeTo_week_is_not_monthOfWeek`, was right all along); and `Negative.lean`'s
`CHEAT 24` banner, which carries the same attribution and stays unedited under
AGENTS §6.2.  The origin is **`PLAN-lean-kernel.md` §3.2(b)** ("horizon.rs:1543
breaks it silently by taking the month of *today*"), which contradicts PLAN's own
§2.1 ("`close_week` the block containing now (:1543)"), and PLAN §6.2 q1 and its
stage-4 acceptance row ("the two behaviour changes landed with assent", quoted
again in `Goals.lean`'s `# STAGE 4` header); PLAN is plan-tier and is left as
history.  Read "the two behaviour changes" there as **one**, D1.

**Gap 52 — which month file a week's `# Demoted` record belongs in is not
decided; DEFERRED out of stage 4.**  (1) *Not done:* when a week is closed after
its month has ended, its archive record is filed by the close rule into
`month/<month of now>#Demoted` (spec §6.3's `<current>`, the Rust's, and
`closeTo`'s), while the tie-break would name the week's own month
(`monthOfIsoWeek`, the Thursday's); nothing says whether a *record about* week `w`
should instead sit in the month `w` belongs to.  (2) *Why deferred:* it has **no
consumer** — `monthOfIsoWeek` / `monthOfWeek` is defined, proved
(`monthOfIsoWeek_is_met`, `_mono`, `_W35`, `_W36`) and used by nothing in the
kernel, the FFI or the host; stage 4's fold needs only a destination, and
`closeTo` is it.  (3) *Cost:* none to the close fold or its theorems; a
per-month history reader (the month review, or a report grouped by month) would
find a late-closed week's record under the month it was closed in, not the month
it belongs to.  (4) *Clears:* whenever a consumer appears — stage 6's review
surface at the earliest — and it is a product decision for the owner, not a
proof.

**Pricing stage 4 against AGENTS §8.2's eleven goals.**  Read against spec §6.3's
three rows and the goals' statements as they stand in `Goals.lean`; each price is
an expectation, to be confirmed or corrected by the step that takes it.  Four of
the eleven are stated *stronger than §6.3 allows*, and the §3.2 protocol for that
is refute-and-rename — prove the negation of the as-stated form under a renamed
name, prove the narrowed statement beside it, record both — never a silently
weakened predicate.

*Expected to discharge as stated (4):*
- `close_is_idempotent` (L16) — the second run's candidate set is empty; the
  engine is `closeTo_target_is_open`, which D1 makes the argument.
- `autoClose_is_each_grain_once` (L19a) — close to definitional once `autoClose`
  is written as day, week, month.
- `autoClose_catches_up_in_one_step` (L19b) — from L16 per grain plus "a later
  grain's close adds nothing to an earlier grain's closed regions" (its targets are
  month regions, open by `closeTo_target_is_open`).
- `close_day_stamps_a_day_stamp` — D1 keeps `demoted:D<dd>`; `Field.Stamp` already
  separates `D07` from `W37`.

*Expected to discharge only through a recorded refute-and-rename (4):*
- `close_leaves_no_live_line_in_a_closed_region` and
  `autoClose_runs_every_period_it_passes` quantify over **every** entity whose live
  site is in a closed region, but §6.3 leaves settled lines ("the week file becomes
  an archive"), recurring items and calendar intervals where they are.  `live` is a
  `Core` field, so a `[x]` line in a closed week is a counterexample to any `close`
  that succeeds on that plan — and a `close` that *refused* such plans would
  satisfy both vacuously, which is a cheat.  Expected: the negation on a one-`[x]`
  witness, and the narrowed statement over open, non-exempt entities (which is what
  L16's argument actually uses).
- `close_writes_every_estimate_through_demoteEst` equates the whole `line` with
  `demoteEst`'s, but `demoteEst` writes only `est:` while §6.3 appends a `demoted:`
  stamp to the same token vector (`Core.stamps` is `viewDemoted c.line`) — so as
  stated it forbids the stamp `close_day_stamps_a_day_stamp` requires.  Expected:
  restated over the estimate view (`remainingOf`), or over the line modulo the one
  `demoted:` token.
- `close_never_demotes_a_wall` concludes `f.val = e.val`, which forbids moving the
  wall; fork-point `close_week` *carries* walls and their prep into the current
  week.  Whether the kernel leaves them in place (the goal holds, and they are
  exempt from the narrowed goals above) or carries them (the goal is restated over
  status and line, and `live` changes) is a `ClosePolicy` row stage 4 must choose
  and record with a separating theorem (AGENTS §4's last row).

*Expected refutations (2):*
- `close_week_and_close_month_commute` (L17) — a caution on the price: the
  expected reason was destinations, and with `closeTo` both orders file week and
  month leftovers into the *same* open month (month close adds no stamp), so a
  refutation, if it comes, is through rank or placement order in the shared
  destination.  If no witness exists it is proved as stated, and that is recorded
  as the finding.  Any witness is built from proved lemmas, not a `decide` over a
  whole plan (AGENTS §5.10a).
- `lifecycle_commands_commute` (L27) — independent of `close`: `applyAll` over two
  existing `ReqCmd`s already refutes it (e.g. a demote/readopt pair, where
  `readopt` first answers `notDemoted`), again from proved lemmas rather than
  evaluation.  The deliverable after the negation is §10.5 q7's *decision*, which
  stays the owner's (stage 6).

*Expected to stand (1):*
- `close_week_folds_a_dropped_child_into_its_parent` (B3).  Its hypothesis
  `parentStep p.val j = some i` reads `Core.parent`, which every loader-built plan
  sets to `none` (gap 22).  A proof over hand-built parents would satisfy check 7
  while no plan that reaches the disk could fire it — AGENTS §5.9's question, and
  §9.2's "a precondition nothing can satisfy".  It waits on §10.5 q3, an owner
  decision due before stage 5; **stage 4 does not take it.**  §6.3's child-folding
  clause is therefore scoped out of stage 4's close by name, alongside §6.3's
  "dated items past due with `persist` → `backlog.md#Overdue`" (needs §5.3's
  `on_miss`, stage 5) and F3 (the day file's review section, stage 6).

Two further prices the goals do not show.  **The day row's first clause** —
`[>]` → `[ ]` with `est:` = remaining **in the week file** — is not "a live site in
a closed *day* region", so the one-fold-at-three-grains shape does not reach it;
`ClosePolicy`'s day row has to say where it lives.  **The month row** — fork-point
`close_month` carries into `month.next()`, the successor, not `closeTo month now`;
the two agree for an on-time close and, because a month close adds no stamp, the
Rust's month-by-month catch-up ends at the same file as one `closeTo` step.  That
is the one-step-per-grain collapse D1's package names, not a further behaviour
change — read off the code here, to be confirmed by the stage's drive.

So stage 4 expects to take **10 of its 11** goals out of `Goals.lean` (4 as stated,
4 by refute-and-rename with a narrowed theorem beside each, 2 as refutations — one
of which may instead prove), leaving **B3** and a burn-down of **30** if nothing
new is admitted; plus the two provisional `def … := sorry`s (`close`, `autoClose`)
replaced by real definitions.

Re-measured after this block (documentation and comments only): see the commit
message.  Gaps run to 52 (new gaps start at 53); cheats to 49 (new cheats start at
50).

<!-- ===================================================================
     APPENDED 2026-09-12 (stage-4 session, rebuild-on-lean).  Step 2: `close` is one fold at three grains — new module `Close.lean`.
     Takes gaps 53–57 and cheats 50–51.  Supersedes nothing above; gaps 20 and 31 get status paragraphs below, not edits.
     =================================================================== -->

## Stage 4 step 2, 2026-09-12: `close` is one fold at three grains

Baseline re-measured at `d615bd1` before this step, every command under the 40 GB
cap: `check.sh` **7/7** — audit **1299**, corpus **33/37 files and 4/5 whole
plans**, burn-down **40**; `cargo test --workspace` **984 passed / 0 failed / 0
ignored across 64 binaries**.

**What landed.**  `TmKernel/Close.lean`, a new module of 1,291 lines, imported
in the same commit by `TmKernel.lean` (between `Cmd` and `Boundary`) and by
`Boundary.lean` (in place of its `Cmd` import, which `Close` re-exports), so the
step that puts `close` on the wire can reach it.  A module rather than an
extension of `Cmd.lean`: `Cmd` is the algebra of one command at one id, and a
close is a fold over many ids that brings its own table, its own rank-shift and
57 theorems; it consumes `Cmd` (`lift`, `moveTo`, `demote`, `WfPlan.mapAt`) and
nothing in `Cmd` consumes it.

- **`ClosePolicy`, one row per `Grain`** — §6.3's residue, tabulated (AGENTS
  §5.5).  What is derived is not in the table: the target region (`closeTo g
  now`, D1), a grain's file kind (`kindOfGrain`), and a stamp's number (the civil
  day of month, the ISO week of the closed region's index).

  | column | day | week | month |
  |---|---|---|---|
  | `takes` | `[ ]` `[>]` | `[ ]` `[>]` | every unsettled box, `[-]` included |
  | `disposition` | `moveReopening` (`[>]`→`[ ]`) | `copy` (`demote`) | `move` (`moveTo`) |
  | `landing` | `fileEnd` | `demotedSection` | `sameSection` |
  | `stamp` | `dayOfMonth` (`D04`) | `isoWeek` (`W36`) | `none` |
  | `recurring` | `stays` | `stays` | `stays` |
  | `walls` | `carried` | `carried` | `carried` |
  | `overdue` | `nothing` | **`stage5OnMiss`** | `nothing` |
  | `children` | `nothing` | **`gap22Parent`** | `nothing` |

  Each row is pinned by a bridge that says something the row does not:
  `closeStamp_names_the_closed_grain` (a stamp names the grain it closed —
  `Field.Stamp` has no month), `close_never_takes_a_settled_line`,
  `closePolicy_takes_the_demoted_record_only_at_month`,
  `closePolicy_demoted_landing_is_in_a_month_file` (the landing and `closeTo`
  agree), `closePolicy_copies_only_below_month`, `closePolicy_copy_stamps`,
  `closePolicy_move_is_unstamped`, `closePolicy_exemptions`, `closePolicy_owes`.
  **CHEAT 50** (a day row stamping `W`) and **CHEAT 51** (a month row that
  copies) corrupt one row each and restate the bridge over the corrupted table;
  both fail as "`decide` proved that the proposition … is false", and the controls
  are the bridges themselves.
- **`close g now`** folds `closeOne` over `closeCands g now` — the ids whose live
  line is in a file of the grain's own kind whose region has grain `g` and is
  `Closed` at `now` (`closedRegionOf`), and whose `closeAct` is not `stay`.
  `closeAct` reads the row: a box the row does not take stays; a recurring line
  gets `recurring`; a wall gets `walls` (carried only when still ahead); anything
  else is filed.  A filed line goes to the first document of kind `kindOfGrain
  (coarsen g)` whose region is `closeTo g now` (`closeTarget`), through the row's
  disposition — `moveTo`, `lift` with the box reopened and the stamp set, or
  `demote` — at the row's landing.  A carried wall goes to the week file whose
  region is `regionOf week now` (`carryTarget`) through `moveTo`.  **Landing
  inside a section** that another heading follows shifts every rank of the
  destination file at or after that heading up by one (`PlanCore.shiftIn`) and
  takes the freed rank; ranks come from line numbers, so a section that is not
  the file's last has no free rank otherwise.  The shift and the relocation each
  re-run `planWf` by computation (`WfPlan.shiftAt`, `WfPlan.mapAt`).
  `endRank_is_freshRank` (Boundary.lean) says the close's end-of-file rank and
  the verbs' `freshRank` are one number.
- **Two named refusals**, `KErr.noTarget` (no document of the kind and region a
  line must go to — the kernel has regions and no path grammar, gap 10, so it
  cannot create the file) and `KErr.noSection` (no `# Demoted`, or no heading
  matching the one the line stood under); `kerrName` names both.  Neither reaches
  the wire yet: `close` is not a wire op, and the Rust bridge's refusal map would
  print either as "an unlisted kernel refusal".

**How it is proved.**  A shift moves ranks and nothing else, so the statements
are made over a rank-free skeleton of each entity (`Skel`: its file, its
tombstone's file and bytes, its box, its bytes) and over the files' kinds and
regions (`Frame`), which no step changes.  `closeOne_spec` is one step;
`foldlM_closeOne_spec` is the induction; **`close_spec` is the denotation** —
after a successful close every id's skeleton is `stepSkel` of what it was, and
no line is one the same close would take again, because the file it now sits in
is `closeTo g now` or the live week and neither is closed
(`closeTo_target_is_open`, `regionOf_is_open`).  The three standard axioms only.

**Discharged from `Goals.lean`: `close_day_stamps_a_day_stamp`**, proved as
stated.  The provisional `def close … := sorry` is replaced by `Tm.close` with
the signature it declared (§3.2's same move).  Burn-down **40 → 39**.

**Proved beside three goals whose refute-and-rename is owed (step 3).**  Each is
stated stronger than §6.3 allows, exactly as the step-1 pricing said; the
narrowed theorem is proved now, the negation of the goal as written is not, and
the goal stays in `Goals.lean` with a status note naming its neighbour.

| goal, as written | why it is expected false | proved beside it |
|---|---|---|
| `close_leaves_no_live_line_in_a_closed_region` | a `[x]` line §6.3 leaves in the archive | `close_leaves_no_line_it_would_take`, `close_leaves_no_unfinished_line_in_a_closed_region` |
| `close_never_demotes_a_wall` (`f.val = e.val`) | a carried wall's `live` changes, and a landing shift moves other lines' ranks | `close_never_demotes_a_wall_but_may_carry_it` (box, bytes, tombstone kept), `close_carries_a_wall_that_is_still_ahead` |
| `close_writes_every_estimate_through_demoteEst` (whole line) | the `demoted:` stamp | `close_rewrites_a_line_only_by_stamping_it` |

The witness each refutation needs is already decided below
(`the_week_close_copies_carries_and_leaves_the_rest` holds a `[x]`, a carried
wall and a stamped record).  **Not proved, and needed for the estimate half:**
that setting the `demoted:` token leaves `remainingOf` unchanged — the
line-shape theorem says the stamp is the only rewrite, not that the estimate
reading survives it.

**D1 as theorems.**  `close_files_a_taken_line_into_closeTo`: a filed line lands
in `closeTo g now`, in a file of kind `kindOfGrain (coarsen g)`, with the row's
skeleton.  `close_day_files_into_the_week_of_now`: whenever the closed day's week
is not now's, that region is not `targetContaining day` of the closed day — the
separating theorem D1 owed, over `impl_rule_disagrees_iff`.

**Both directions (AGENTS §5.8).**  *It succeeds:* `close_without_candidates_is_the_identity`,
and three decided witnesses on **loaded** plans, closed at Monday 2026-09-07 —
`the_week_close_copies_carries_and_leaves_the_rest` (the open line stays behind
`[-]` in its own bytes, its record `…tests demoted:W36 ^m2` lands at the end of
`# Demoted` ahead of `# Notes` by a shift, the done and recurring lines stay, the
future `at:` wall is carried into 2026-W37), `the_day_close_files_into_the_week_of_now`
(a pinned `[>]` of Friday 2026-09-04, in W36, reopens with `demoted:D04` and lands
in **W37**, with W36's file handed over too), and
`the_month_close_moves_each_line_into_its_section` (an open outcome into the next
month's `# Outcomes` by a shift, keeping `!1`; the `[-]` record into `# Demoted`
keeping `est:3b demoted:W33`; the done outcome stays).  *It bites:*
`closeOne_refuses_a_missing_target`, `closeOne_refuses_a_carry_with_no_live_week`,
`closeOne_refuses_a_missing_section`, `closeOne_refuses_an_ill_formed_post_state`,
`closeOne_week_refuses_a_standing_tombstone`, `close_refuses_what_its_first_step_refuses`,
and decided on loaded plans `the_close_refusals_are_named_on_loaded_plans` —
`badHorizon`, `noTarget` twice, `noSection`, `alreadyDemoted`.  The witnesses
observe each file's lines in rank order (the two lists `renderDocAt` weaves,
merged by rank), not `renderDocAt`'s output: `weave` is well-founded and does not
reduce under `decide`, which stuck the first attempt.  Every witness was probed
under an 8 GB cap first; together they decide in about 3 s at a 1.2 GB peak.

**Choices this step took, each with the theorem that separates it (AGENTS §4's
last row).**  None relitigates D1–D4; the first two differ from fork-point
behaviour and are flagged for the owner's drive rather than settled here.

1. **Walls are carried at every grain, the day row included, and only while
   still ahead.**  Fork-point `close_day` moves a pinned interval into the week
   *with* `demoted:D<dd>`; the kernel carries it unstamped (§6.3's last
   paragraph: intervals are never demoted), and a pinned or week wall that is
   already over stays in the closed file.  `close_never_demotes_a_wall_but_may_carry_it`,
   `close_carries_a_wall_that_is_still_ahead`.  "Ahead" is day resolution — gap 57.
2. **The month row does not take a settled line under `# Demoted`.**  Fork-point
   `close_month` carries every `# Demoted` line whatever its box; the kernel's
   rows never take `[x]`/`[~]` (`close_never_takes_a_settled_line`), box first as
   everywhere else in this kernel.
3. **A section that is not a file's last is landed in by a rank shift, not
   refused.**  The alternative made the month row unusable on §4.3's own month
   file (`# Outcomes` before `# Demoted`); `the_month_close_moves_each_line_into_its_section`
   and the week witness exercise the shift.
4. **The destination is the first document of the right kind and region.**  Two
   files of one kind claiming one region are distinct paths the loader accepts;
   the close picks by index, deterministically, and says so here.

**Gap 20 — landed for `close`; not for the `demote` verb; `sectionsWf` unchanged.**
§6.3's week row now files its record into `month/<current>#Demoted` by
computation (`Landing.demotedSection`, the shift), which is what gap 20 said a
§6.2 "outcome with an estimate" warning needs.  Not changed, and why: (a) the
standalone `demote` wire verb still lands at `freshRank` — its request carries a
document and no section, and moving a shipped verb's landing is a wire behaviour
change that belongs with the step that puts `close` (and `now`) on the wire;
(b) `sectionsWf` does not demand that a `[-]` record sit under `# Demoted` —
that is AGENTS §10.5 q9, an owner decision still open, and refusing loads on it
is a behaviour change this step does not take; (c) the §6.2 warning itself is
still unimplementable, because "an estimate **and no children**" needs
`Core.parent` (gap 22).

**Gap 31 — the named fix is subsumed; nothing on `Core` changes.**  The "second
`RawItem` on `Core`, set by `demote`, cleared by `readopt`, read by `renderCore`
at the archive site" is `Tomb.line` (`Core.archive : Option Tomb`, since
`8eea3d6`): `demote` freezes the line it leaves there, `readopt` discards the
tombstone, `renderCore` writes `t.line` at `t.site`.  This step is the first code
that *writes* the differing pair through a close — the week witness shows the
week line kept byte for byte beside the stamped record — and it does so through
`demote`, so `orientPair`'s glyph clause and `demotionsOriented` are untouched.

**Scoped out, by name, with the stage that clears each (brief item 7).**
§6.3's week-row "dated items past due with `persist` → `backlog.md#Overdue`" is
the table's `overdue := .stage5OnMiss` — it needs §5.3's `on_miss` evaluated
against `due:`, stage 5.  Its "unfinished children are dropped, their remaining
folded into the parent's `est:`" is `children := .gap22Parent` — it needs
`Core.parent`, always `none` (gap 22, AGENTS §10.5 q3, owner, before stage 5);
with it goes fork-point `close_week`'s carrying of a wall's prep children, which
the kernel demotes as ordinary lines.  The day file's review section (F3) is
stage 6.  B3 (`close_week_folds_a_dropped_child_into_its_parent`) stays in
`Goals.lean` on the same precondition.

**Owed by the stage and not attempted in this step (sequencing, not gaps):**
`close` on the wire — `now` in the request, the close op, D3's per-item report
with its four AGENTS §8.2 rules; `autoClose` (still a provisional `sorry`); L16,
L17, L19a–c, L27 and the three refute-and-renames above; the CLI-level
acceptance and the 30-minute drive (AGENTS §5.13); the proof-to-definition ratio
AGENTS §8.2 asks for at the stage's end.

**Gap 53 — `close week` refuses an item that already carries a tombstone.**  (1)
*Not done:* §4.3's own pre-close pair — a `[ ]` record in a week beside its `[-]`
copy under a month's `# Demoted` — makes the week close answer `alreadyDemoted`
(`closeOne_week_refuses_a_standing_tombstone`, decided on a loaded plan).
Fork-point `demote_one` rewrites the standing copy with merged stamps and takes
its recorded `est:` as a floor.  (2) *Why:* doing that is `demoteEst bm userSet
rec` — the block length, whether the user set an estimate since, and the
standing copy's remaining — and none of the three is in `close g now`'s
signature; replacing the copy without the floor is exactly B2's "supersede"
defect.  (3) *Cost:* a whole week close refuses on any tree holding that shape,
which the corpus's `plan-basic`-shaped trees do once their week is closed.
(4) *Clears:* when `close` gains its measurement inputs — the wire step, where
the host supplies them, or stage 5's log replay.

**Gap 54 — `close` writes no `est:`.**  (1) *Not done:* §6.3's "`est:` =
remaining" on the day row's reopened `[>]` and on the week row's record; the line
carries the estimate it had (`close_rewrites_a_line_only_by_stamping_it`).
(2) *Why:* remaining beyond the line's own reading is the log's minutes (F6,
`done_minutes`, stage 5) and the rollup's children (gap 22); the kernel has
neither, and writing the line's own reading back as a token would only change
bytes.  (3) *Cost:* a `[>]` item worked on during the closed day keeps its
pre-work estimate; `close_writes_every_estimate_through_demoteEst` stays a goal.
(4) *Clears:* stage 5, with the log; its refute-and-rename is step 3's.

**Gap 55 — a dated line refuses the week close.**  (1) *Not done:* a week line
with `due:` (a point shape) is filed like any other, and its record then
violates `shapesWf`'s month rule ("an outcome carries no date"), so the close is
`badHorizon` (decided in `the_close_refusals_are_named_on_loaded_plans`).
(2) *Why:* half of it is the scoped-out overdue routing (stage 5); the other half
— a dated line not yet past due — has a record §6.3 says goes to `# Demoted` and
a month rule that refuses it, and exempting `# Demoted` placements from the rule
is a change to what a plan is, for the owner.  (3) *Cost:* §4.3's own
`week/2026-W37.md` (`^d1 due:2026-09-11T23:59`) cannot be closed whole.
(4) *Clears:* stage 5 for the past-due half; an owner decision for the rest.

**Gap 56 — the kernel cannot create the file or the section a close needs.**
(1) *Not done:* a close whose `month/<current>` (or live week, for a carry) is not
in the request is `noTarget`; one whose month file has no `# Demoted` (or no
heading matching the section a month-row line came from) is `noSection`.
Fork-point `ensure_horizon_file` and `insert_line` create both.  (2) *Why:* a
document here is a path, prose and a region, and there is no path grammar for a
region (gap 10); a heading could be inserted as prose, but the kernel choosing
where is the loader-picks-a-reading defect (§5.6).  (3) *Cost:* the host must
hand over every destination file with its sections before calling `close`, or
the close refuses whole.  (4) *Clears:* the wire step (host precondition) or
gap 10's grammar.

**Gap 57 — "still ahead" is day resolution.**  (1) *Not done:* a wall is carried
when its end's day is on or after `now`, so a wall that ended at 10:00 on the day
a close runs at 15:00 is carried although it is over.  (2) *Why:* `now` is a
`Day`; the kernel has no time of day (gap 10).  (3) *Cost:* an over wall can be
carried one day too long, into a week file the planner reads; never the other
way — a wall still ahead is never stranded.  (4) *Clears:* gap 10.

Re-measured after this step, every command under the 40 GB cap: `check.sh`
**7/7** — axiom audit **1362 theorems** (63 new: 57 in `Close.lean`, 6 in
`Boundary.lean`; the three counts of AGENTS §6.3 agree at 1362), corpus
**33/37 files and 4/5 whole plans** (unchanged), `Goals.lean` burn-down **39**;
`cargo test --workspace` **984 passed / 0 failed / 0 ignored across 64
binaries** (unchanged); FFI suite 63 (57 kernel + 6 corpus, unchanged).  A full
`lake build TmKernel:static` peaked at 1.8 GB.  Eleven modules, 22,400 lines.
Gaps run to 57 (new gaps start at 58); cheats to 51 (new cheats start at 52).

<!-- ===================================================================
     APPENDED 2026-09-12 (stage-4 session, rebuild-on-lean).  Step 3: L16 proved; L17 and L27 refuted and renamed.
     Takes no gap and no cheat numbers.  Supersedes nothing above by rewrite; corrects one framing of AGENTS §8.2 by name.
     =================================================================== -->

## Stage 4 step 3, 2026-09-12: closing twice is closing once; L17 and L27 refuted

Baseline re-measured at `50f11e3` before this step, every command under the 40 GB
cap: `check.sh` **7/7** — axiom audit **1362**, corpus **33/37 files and 4/5
whole plans**, burn-down **39**; `cargo test --workspace` **984 passed / 0 failed
/ 0 ignored across 64 binaries**.

**L16 — `close_is_idempotent`, discharged as stated** (`Close.lean`).  After a
successful `close g now`, the same close returns the plan unchanged.  The proof
is four lines on top of step 2: `close_leaves_no_line_it_would_take` (read off
`close_spec`) says no line of the output is one the close would take, so
`closeCands` is empty (`closeCands_eq_nil_of_stay`), and
`close_without_candidates_is_the_identity` finishes it.  The hypothesis is
satisfiable at all three grains by step 2's decided witnesses.  **Which
idempotence it is**, written in the theorem's own doc comment as AGENTS §8.2's
last trap asks: the fold on `WfPlan` with `g` and `now` fixed.  It is *not* §6.3's
"runs automatically on the first command after the period ends (idempotent;
recorded in `state.json`)", which is a Rust fact about the host's `closed` map
across invocations, and it is not a claim across instants — a later `now` closes
more regions (`closed_is_stable_in_time`).

**Where D1 is load-bearing for L16, stated precisely** (a correction of framing,
not of any decision).  AGENTS §8.2's trap says that with `targetContaining` "the
fold's own output can be back in scope and the proof does not go through".  Read
off the definitions — `closedRegionOf` demands the grain's *own file kind*, and
`coarsen month = month` — and **not proved here**: for a single grain that is
true at **month** only, where `targetContaining month d` is the closed month
itself (`containing_targets_a_closed_region_iff`), so the line would be retaken.
At day and week the output lands in a file of a coarser kind, which a close of
the same grain never takes, whatever its region.  Where the old rule breaks the
day and week rows is **across grains** — the day close's output landing in a
closed week that the week close then takes, the owner's scenario 1 (D1's first
evidence) — which is L19b's business, not L16's.  The proof as written runs on
openness at every grain (`closeOne_spec` uses `closeTo_target_is_open` and
`regionOf_is_open`), so nothing above changes what was proved.

**L17 — `close_week_and_close_month_commute` is false; renamed to
`close_week_and_close_month_do_not_commute` and proved** (`Boundary.lean`).  The
witness: `week/2026-W36.md` with one open line `^m2`, `month/2026-08.md` with one
`[-]` record `^m9` under `# Demoted`, and `month/2026-09.md` with an empty
`# Demoted`, closed at Monday 2026-09-07.  Week-then-month and month-then-week
both succeed and write the same lines into the same files; 2026-09's `# Demoted`
reads `^m2, ^m9` in one order and `^m9, ^m2` in the other
(`the_week_then_month_close_lands_the_week_record_first`,
`the_month_then_week_close_lands_the_month_record_first`,
`close_week_month_orders_both_succeed_and_differ`).  **Why they differ, in one
sentence: both closes file into the one open month containing *now*, and each
lands its line at the end of that month's `# Demoted`, so whichever runs second
lands below the other.**

**The goal's own reason was wrong, and the finding is the commuting half.**  The
goal expected the week close's output to become the month close's input in one
order and not the other.  Under D1 that cannot happen at one instant, and it is
proved: `stepSkel_lands_outside_every_closed_region` (wherever a step puts a
line, no close of *any* grain at that instant takes it from) and
`closeAct_of_another_grain` (a file is a closed region of at most one grain) give
`two_closes_at_one_instant_commute_on_skeletons` — for **any** two grains, when
both orders succeed, every id ends with the same skeleton: the same file, the
same tombstone file and bytes, the same box, the same bytes.  The orders differ
**only in rank**.  Step 1's pricing had cautioned exactly this ("a refutation, if
it comes, is through rank or placement order in the shared destination").
*Consequence for `autoClose`* (L19a, not yet written): the grain order it fixes
decides the order of lines inside a shared destination section and nothing else
— read off the table, the shared destinations are the open month's `# Demoted`
(week record, month leftover from `# Demoted`) and the live week's end (a day
close's line, any close's carried wall).  **Not proved, and nothing needs it
yet:** that one order succeeds exactly when the other does, or that two refusing
orders name the same refusal; `autoClose` runs one fixed order.  The witness is
decided, not built from lemmas as step 1 suggested: it was probed under an 8 GB
cap first (with the L27 witness, under 3 s at a 1.1 GB peak), and deriving a
rank inequality from `landAt_spec` would have been a proof about ranks that
`close_spec` deliberately does not track.

**L27 — `lifecycle_commands_commute` is false; renamed to
`lifecycle_commands_do_not_commute` and proved** (`Boundary.lean`).  On L22's
`undoWitnessPlan`, `demote ^m1` into the month then `readopt ^m1` into the week
succeeds; the reverse is refused `notDemoted` and the demote never runs
(`demote_then_readopt_succeeds_and_the_reverse_is_refused`).  **Why, in one
sentence: `readopt` reopens only a demoted record
(`readopt_of_a_live_record_is_refused`) and `demote` is what makes one, so a
demote/readopt pair's order is observable as success against a named refusal.**
This is about `applyAll`, the code the FFI runs, on a plan that loads.  It
refutes the law as written and **answers nothing about AGENTS §10.5 q7**: whether
lifecycle pairs that *both succeed* ought to commute — `inventory`'s R7, `demote
^m1 ; move ^m1 week` against its reverse — stays the owner's, at stage 6.

**One observation for every close witness.**  `closedFileLines` (step 2) now
reads through `fileLinesOf` and `closeResultLines`, which this step's witnesses
use too, so there is one definition of "each file's lines in rank order"; step
2's four decided witnesses re-decide unchanged.

**Goals.**  Three deleted from `Goals.lean`, each with a proof of what it states
or of its negation, each replaced by a status comment naming the theorem:
`close_is_idempotent` (as stated), `close_week_and_close_month_commute` (refuted),
`lifecycle_commands_commute` (refuted).  Burn-down **39 → 36**.  All five goals
ever flagged as expected refutations or narrowings in their doc comments have now
gone that way.  No goal added.  Seventeen theorems audited under the stage-4
banner in `Check.lean` (10 in `Close.lean`, 7 in `Boundary.lean`); no cheat added.

**Owed by the stage, not attempted in this step (sequencing, not gaps):**
`autoClose` and L19a–c; the refute-and-renames of
`close_leaves_no_live_line_in_a_closed_region`, `close_never_demotes_a_wall` and
`close_writes_every_estimate_through_demoteEst`, whose narrowed neighbours and
witnesses step 2 already proved; `close` on the wire with `now` and D3's report;
the CLI-level acceptance, the 30-minute drive (AGENTS §5.13) and the
proof-to-definition ratio.

Re-measured after this step, every command under the 40 GB cap: `check.sh`
**7/7** — axiom audit **1379 theorems** (17 new; the three counts of AGENTS §6.3
agree at 1379), corpus **33/37 files and 4/5 whole plans** (unchanged),
`Goals.lean` burn-down **36**; `cargo test --workspace` **984 passed / 0 failed /
0 ignored across 64 binaries** (unchanged); FFI suite 63 (57 kernel + 6 corpus,
unchanged).  A `lake build
TmKernel:static` rebuilding `Close` and `Boundary` peaked at 2.5 GB (max RSS of
one process); elaborating `Boundary.lean` alone takes 12.4 s at 2.2 GB against
9.2 s at 1.8 GB for `50f11e3`'s copy against the same `Close`, so this step's
witnesses cost about 3 s and 0.4 GB.  Gaps run to 57 (new gaps start at 58);
cheats to 51 (new cheats start at 52).

<!-- ===================================================================
     APPENDED 2026-09-12 (stage-4 session, rebuild-on-lean).  Step 4: `autoClose` is one step per grain; L19a and L19b proved, L19c refuted and renamed.
     Takes no gap and no cheat numbers.  Supersedes nothing above by rewrite.
     =================================================================== -->

## Stage 4 step 4, 2026-09-12: `autoClose` is one step per grain

Baseline re-measured at `b605bfe` before this step, every command under the 40 GB
cap: `check.sh` **7/7** — axiom audit **1379**, corpus **33/37 files and 4/5
whole plans**, burn-down **36**; `cargo test --workspace` **984 passed / 0 failed
/ 0 ignored across 64 binaries**.

**What landed (`Close.lean`).**  `autoCloseOrder := [day, week, month]`, pinned by
three decided facts — it is the containment chain walked up from `day`
(`autoCloseOrder_is_the_chain`), it names each grain exactly once
(`autoCloseOrder_names_each_grain_once`), and it is coarsest last
(`autoCloseOrder_is_coarsest_last`) — and `autoClose now := autoCloseOrder.foldlM
(close · now)`, replacing `Goals.lean`'s provisional `def autoClose … := sorry`
with the signature it declared.  There is no iteration count anywhere: each
`close g now` already folds over **every** closed region of grain `g`, whatever
its age, so the fork-point `AUTO_CLOSE_CATCHUP = 16` day-by-day loop
(`tm-core/src/horizon.rs:2003`) has nothing to do.

**Why one step per grain is enough, in one sentence: every close files into a
region containing *now*, and no close at that instant takes a line from such a
region** (`stepSkel_lands_outside_every_closed_region`, step 3).  Two
consequences, each a theorem: a close of any grain leaves nothing new for a close
of any other (`close_keeps_nothing_to_close`), so after the three closes no line
is one a close of **any** grain would take (`autoClose_leaves_nothing_to_close`);
and the three steps a line goes through collapse to one grain's step
(`stepSkel_three_is_one`), so a line is taken at most once per call
(`autoClose_takes_each_line_at_most_once`).  This is D1 doing the work: with
`targetContaining`, a day close's output lands in a closed week the week close
then takes — the owner's double stamp.

**Goals discharged from `Goals.lean`.**

- **`autoClose_is_each_grain_once` (L19a), as stated** — the fold unfolds to
  `(close day now p).bind (fun q => (close week now q).bind (close month now))`.
- **`autoClose_catches_up_in_one_step` (F1 / L19b), as stated** — a second
  `autoClose` at the same instant returns the plan unchanged: each grain's
  candidate set is empty (`closeCands_eq_nil_of_stay`) and an empty close is the
  identity.  Like L16, this is the fold on `WfPlan` at one `now`, not §6.3's
  host-side `state.json` idempotence; a later `now` closes more
  (`closed_is_stable_in_time`).
- **`autoClose_runs_every_period_it_passes` (F1 / L19c) — refuted, renamed to
  its negation `autoClose_leaves_lines_in_periods_it_passes` and proved**
  (`Boundary.lean`), exactly as AGENTS §8.2's trap priced it: it quantified over
  every live line, and §6.3 leaves `[x]` lines, recurring lines, done outcomes
  and walls already over in their closed files.  The witness is `^t1`, a `[x]` line of the
  closed 2026-W24, after a successful `autoClose` of the stale tree below.
  **The narrowing, proved:** `autoClose_strands_no_unfinished_line` — after
  `autoClose`, a line in a closed region of its file's own grain is not of a box
  that grain's row takes, or is recurring, or is a wall already over.  The wall
  clause is sharper than step 2's single-grain narrowing (a wall *still ahead*
  is excluded, because it is carried), and the grain is the region's own, not a
  parameter.

Burn-down **36 → 33**.  No goal added.

**The owner's two measured failures, as theorems and on one decided plan.**  On
the shipped Rust (D1's evidence): a tree **three months stale** ran zero day
closes — `catch_up` looked only at the sixteen most recent days, none of which
had a file — stranding every older pinned item under a clean `tm check`; a tree
**fourteen days stale** stamped every stale pinned item twice.  Here the first is
`autoClose_strands_no_unfinished_line` and the second is
`autoClose_stamps_each_line_at_most_once` (a line gains no stamp or exactly one
across one call, via `stepSkel_stamps`, which generalises step 2's day-only
`stepSkel_day_stamps` to every grain).

**The acceptance clause, library half: "a 3-month-stale tree catches up losing
nothing"** (`Boundary.lean`, closed at Saturday 2026-09-12).  `staleWitness`
loads (`the_stale_witness_loads`) and holds both failure shapes: a pinned `[>]`
of 2026-06-12 and one of 2026-08-29 (in 2026-W35), open lines in 2026-W24 and
2026-W35 beside a `[x]` and a recurring line, a wall still ahead in 2026-W35, a
June month file with an open outcome, a done outcome and a `[-]` record, and the
live week and month.  One call, decided:

- `the_stale_tree_catches_up_in_one_call` — both pinned items reopen and land in
  **2026-W37** with `demoted:D12` and `demoted:D29` (one stamp each; the fourteen-day
  item is *not* re-taken by the week close); both week lines leave `[-]` tombstones
  and land in 2026-09's `# Demoted` with `W24` and `W35`; the wall is carried
  into 2026-W37 unstamped; June's open outcome moves into 2026-09's `# Outcomes`
  by a shift, and its `[-]` record into `# Demoted`, both unchanged.
- `the_stale_ledger_before_catch_up` / `the_stale_ledger_after_catch_up` — the
  per-item ledger (id, file path, stamp count, estimate in minutes at a 50-minute
  block): thirteen ids before and after; four lines gain exactly one stamp
  (`p1`, `p3`, `m2`, `m3`), none gains two.
- `the_stale_tree_catches_up_losing_nothing` — the same ids in the same order,
  the summed estimate **875 minutes** before and after, no stamp count up by
  more than one.
- `the_stale_catch_up_leaves_only_settled_and_recurring_lines` — the ids still in
  closed files are exactly `O8` (done outcome), `r1` (recurring), `t1` (done),
  `p2` (done): the lines §6.3 leaves.

The three observations are decided **once**, as one `CatchUpView` value
(`the_stale_catch_up_observed`), and read off by `staleCaughtUp_map`: deciding
them separately closed the stale plan three times.  **Probed under an 8 GB cap
before committing** (AGENTS §5.10a): the scratch probe decided all three in 8 s
at a 1.7 GB peak, imports included.  **Not proved in general**, as step 2
already recorded: that setting `demoted:` leaves `remainingOf` unchanged — the
875 is a fact about this plan, and the general estimate half stays with gap 54.

**Both directions (AGENTS §5.8).**  *It succeeds:* the witness above; the
hypothesis of every `autoClose` theorem is satisfied by it.  *It bites:*
`autoClose_refuses_what_a_grain_refuses` (a refusal of any grain's close is the
call's refusal, with the earlier grains' successes named) and
`autoClose_refuses_a_refused_day_close`; decided on loaded plans,
`the_stale_catch_up_refusals_are_named` — the stale tree without
`week/2026-W37.md` is `noTarget` at the day grain, and without
`month/2026-09.md` it is `noTarget` at the week grain, after the day close
succeeded.  Every close step already re-runs `planWf` by computation
(`WfPlan.mapAt`, `WfPlan.shiftAt`); `autoClose` adds no write of its own.

**A choice this step took, with the theorem that separates it.**  A refusal at
any grain refuses the **whole** call (`autoClose_refuses_what_a_grain_refuses`):
the day close's successful work is not returned when the week close refuses.
The alternative — return what ran — is the fork-point shape in which a period
could be recorded as done while another stayed unrun, which is F1.  The cost,
priced: with gap 56 (the kernel cannot create a file or section), one missing
destination blocks the catch-up of every grain until the host hands it over.
The grain order is not a correctness choice (step 3: the grains commute on
skeletons and differ only in rank); coarsest last puts a closed week's records
ahead of an older month's carried ones in the open month's `# Demoted`.  Within
one grain, lines land in store order — `m3` (W35) above `m2` (W24) in the
witness — which no statement fixes and no consumer reads yet.

**What this step does not do, by name (sequencing, not gaps).**
(1) **The shipped binary still loops.**  The sixteen-period iteration is gone
from the kernel, not from `tm`: fork-point `auto_close` with `AUTO_CLOSE_CATCHUP
= 16` (`tm-core/src/horizon.rs:2003`) still runs as housekeeping ahead of every
command, and will until `close`/`autoClose` reach the wire with `now` in the
request (AGENTS §8.2 scope item 4) and the host calls them.  (2) **The FFI-level
witness** waits on the same wire step: `autoClose` is not a wire op, so the stale
tree is decided in `Boundary.lean`, not pushed through `String → String`.
(3) **The CLI half of the acceptance** ("a 3-month-stale tree catches up losing
nothing" through the binary) and the 30-minute drive (AGENTS §5.13) are step 6's.
(4) Still owed by the stage from step 3's list: the refute-and-renames of
`close_leaves_no_live_line_in_a_closed_region`, `close_never_demotes_a_wall` and
`close_writes_every_estimate_through_demoteEst`; D3's per-item report on the
wire; the proof-to-definition ratio.

Re-measured after this step, every command under the 40 GB cap: `check.sh`
**7/7** — axiom audit **1407 theorems** (28 new: 17 in `Close.lean`, 11 in
`Boundary.lean`; the three counts of AGENTS §6.3 agree at 1407), corpus **33/37
files and 4/5 whole plans** (unchanged), `Goals.lean` burn-down **33**;
`cargo test --workspace` **984 passed / 0 failed / 0 ignored across 64
binaries** (unchanged); FFI suite 63 (57 kernel + 6 corpus, unchanged).
Elaborating `Boundary.lean` alone now takes 27.5 s at a 2.9 GB peak, against
12.4 s at 2.2 GB at step 3 — this step's witnesses cost about 15 s and 0.7 GB
(4.1 GB before the observations were merged into one decision); a `lake build
TmKernel:static` rebuilding `Close` and `Boundary` peaked at 3.0 GB.  Gaps run to 57
(new gaps start at 58); cheats to 51 (new cheats start at 52).
