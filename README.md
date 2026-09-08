# tm

`tm` is a personal planner for people who think in plain text. You keep a small
tree of Markdown files — a month of outcomes, a week of milestones and tasks, a
backlog, your routines — and `tm` works out what to do next, an hour at a time,
from what is in those files and from what you tell it about your day.

It has a command for every moment of a working day (`tm wake`, `tm arrive`,
`tm start`, `tm done`), a terminal UI that shows the whole day at once
(`tm tui`), and a set of Claude Code skills for the parts of planning that are
writing rather than deciding.

Two ideas make it different from a to-do app.

**The Markdown files are the database.** There is no hidden store, no database
file, no import step. An item is a line in a file, and the file it sits in is
what makes it this week's work rather than next month's. Everything `tm` knows
about your intentions, you can read with `cat` and change with any editor. `tm`
rewrites lines byte-faithfully: your alignment, your spelling of an estimate,
your comments and prose all survive.

**The schedule is computed, never stored.** There is nothing in `tm` that moves
a task to 3pm. The timetable is recomputed from scratch every time you ask for
it, out of the facts you wrote down — estimates, deadlines, how much energy a
task needs, how much energy the model thinks you will have at 3pm. So you never
maintain a schedule. You maintain facts, and re-run the planner. When the day
goes wrong, you do not rearrange twelve rows; you tell `tm` one true thing
(`tm energy 3`, `tm interrupt`) and the rest follows.

`tm` is probably for you if you already keep plans in text files, want the
computer to do the arithmetic of deadlines and capacity, and are willing to
report a few facts about your day. It is probably not for you if you want a
shared team tracker, notifications, or a calendar you drag things around in.

---

## Contents

- [Install](#install)
- [Quick start](#quick-start)
- [The daily loop](#the-daily-loop)
- [Writing items: the line grammar](#writing-items-the-line-grammar)
  - [Anatomy of a line](#anatomy-of-a-line)
  - [The bullet, the state, and the two slots](#the-bullet-the-state-and-the-two-slots)
  - [Where the title ends](#where-the-title-ends)
  - [Every field](#every-field)
  - [Flags](#flags)
  - [Ids, parents and tags](#ids-parents-and-tags)
  - [Series](#series)
- [The files, and "horizon is the file"](#the-files-and-horizon-is-the-file)
- [Why the day came out that way](#why-the-day-came-out-that-way)
  - [Window and budget](#window-and-budget)
  - [What can be scheduled today](#what-can-be-scheduled-today)
  - [Priority](#priority)
  - [Energy, ci, and slots](#energy-ci-and-slots)
  - [Reading the timetable](#reading-the-timetable)
  - [The diagnostics](#the-diagnostics)
  - [What tm learns about you](#what-tm-learns-about-you)
  - [The week ahead](#the-week-ahead)
- [The terminal UI](#the-terminal-ui)
- [Command reference](#command-reference)
- [Claude Code integration](#claude-code-integration)
- [Configuration](#configuration)
- [Troubleshooting and surprises](#troubleshooting-and-surprises)

---

## Install

**If you already have a `tm` binary**, put it somewhere on your `PATH` and you
are done:

```sh
mkdir -p ~/.local/bin && cp ./tm ~/.local/bin/tm
```

**To build it from source** you need a Rust toolchain. `tm` is a Rust
workspace — a library (`tm-core`) and one binary (`tm`) — so run these from the
workspace root, the directory that holds `Cargo.toml` beside the `tm/` and
`tm-core/` folders:

```sh
cargo build --release          # binary at ./target/release/tm
cargo install --path tm        # or: install `tm` into ~/.cargo/bin
```

Either way, check it:

```console
$ tm --version
tm 0.1.0
```

Do put `tm` on your `PATH` rather than typing a path into `target/`. Both hooks
`tm init` writes give up when they cannot find it there: the Claude Code hook
exits 0 **silently**, and the git pre-commit hook prints `pre-commit: tm is not
on PATH — skipping tm check` on stderr and lets the commit through. Either way
your validation net is off.

### Finding your plan directory

Every command needs to know which plan directory to work on. It looks, in this
order:

1. `--dir <path>` (a global flag; it works before or after the verb)
2. `$TM_DIR`
3. by walking up from the working directory for a directory holding a
   `config.toml` **next to `.tm/`, `backlog.md`, `week/` or `month/`** — or one
   with a `plan/` child that does

A bare `config.toml` with none of those beside it is not a plan directory, so a
`config.toml` you keep for something else is never mistaken for one.

So in normal use you `cd` into your plan directory, anywhere under it, or
anywhere above a `plan/` folder, and type `tm now`. Outside one:

```console
$ tm now
tm: no plan directory found (looked for config.toml next to .tm/, here and in every parent); use --dir <path> or set TM_DIR
```

`tm init` is the one verb that also takes the directory as a plain argument, so
`tm init X`, `tm init --dir X` and `tm --dir X init` all create the tree at `X`.
Give it both and the positional wins: `tm init here --dir there` writes `here`.

---

## Quick start

From nothing to a planned day. Every block below is a real run.

**1. Make a plan directory.**

```console
$ tm init plan
created 20 file(s) in plan
enable the pre-commit hook with:
  git config core.hooksPath plan/.githooks
$ cd plan
```

The files are empty except for an HTML comment in each one showing what belongs
there. Nothing else is created until you run a command that needs it.

**2. Write down some work.** `tm add` takes a line in the item grammar and puts
it in a file; it assigns the `^id` and prints where the line landed. `--section`
says which heading to append under.

```console
$ tm add "- [ ] 5 6b Finish the ch.5 exercises ^m1" --to week --section Milestones
- [ ] 5 6b Finish the ch.5 exercises ^m1 → week/2026-W37.md
$ tm add "4 2b Draft the rollback tests" --to week --section Tasks
- [ ] 4 2b Draft the rollback tests ^vy69 → week/2026-W37.md
$ tm add "2 20m Call the bank about the card" --to week --section Tasks
- [ ] 2 20m Call the bank about the card ^exm2 → week/2026-W37.md
```

The `- [ ] ` prefix is optional, and you can give your own `^id` or let `tm`
make one. Reading a line: `5` is how much energy it needs (0–5), `6b` is six
blocks of an hour, the rest is the title.

**3. Write down the shape of your day.** Routines are the things that are not
work but take time. They have no checkbox — their instances live in the log, so
the line never changes.

```console
$ tm add "- sleep win:22:00-08:00 dur:8h30m every:day ci:0" --to routines
- sleep win:22:00-08:00 dur:8h30m every:day ci:0 → routines.md
$ tm add "- breakfast win:06:00-09:00 dur:30m every:day pref:wake+10m" --to routines
- breakfast win:06:00-09:00 dur:30m every:day pref:wake+10m → routines.md
$ tm add "- lunch win:11:30-13:30 dur:30m every:day" --to routines
- lunch win:11:30-13:30 dur:30m every:day → routines.md
```

**4. Check what you wrote.**

```console
$ tm check
no problems
```

**5. Start the day.** `tm wake` records when you got up; `tm arrive` says where
you are, works out the day's window and budget, and plans it.

```console
$ tm wake --slept 7h30m
wake 06:45 · slept 450m
$ tm arrive lounge
arrive lounge 07:10 · window 07:10–15:10 · budget 6 blocks
```

`lounge` is just a name for where you are — pick your own (`office`, `cafe`,
`library`). `tm` learns a separate energy curve per location, and the word is
not cosmetic: it decides the shape of the day. Two names are special. `lounge`
starts from a high curve that reaches energy 5, so demanding work gets
scheduled. `home` starts lower **and** is capped at energy 3, so ci-4 and ci-5
work is never planned there at all. A name `tm` has not met before starts from
the `home` curve, which peaks at 4, but takes no cap. See
[Configuration](#configuration) to give your own locations a curve.

**6. Look at the day.**

```console
$ tm plan
2026-09-07 · window 07:10–15:10 · budget 6 blocks
07:12  ·      breakfast 30m
07:42  4 p5   Draft the rollback tests          2b
08:42  5 p5   Finish the ch.5 exercises         6b
09:42  ·      break 20m
10:02  5 p5   Finish the ch.5 exercises         6b
11:30  ·      lunch 30m
12:00  4 p5   Draft the rollback tests          2b
13:00  4↓p5   Call the bank about the ca…       20m     ↓ slot 4, item 2
14:00  ·      break 20m
14:20  ·      rest 50m
15:10  ───    window ends 15:10
21:30  🌙     wind-down · bed 22:00
22:00  ·      sleep 8h30m
· 1 underused (4→2) · 0 ci-5 lost
· plan honesty 1.39 — planned above a realistic budget
```

Each row is `time · slot energy · p<priority> · title · estimate`. **The first
number is the energy the model predicts for that hour, not the item's own.** The
bank call needs energy 2 and got a 4-energy hour, which is exactly what the `↓`
complains about. `p5` is the priority, where **0 is the most urgent**; 5 is what
everything gets until you give it a deadline or an explicit `!1`–`!4`. The full
key is in [Reading the timetable](#reading-the-timetable).

So: six budgeted blocks of work, breaks between them, routines in their windows,
and two complaints at the bottom — one hour of good energy went on a small
errand (`↓`), and the work scheduled needs 1.39× the minutes the budget has.

**7. Work.** `tm now` is the live answer to "what am I doing"; it is recomputed
every time, so it is never stale.

```console
$ tm now
nothing running
· breakfast 30m  ci1  p0
  07:45–08:15 · elapsed 0m · left 30m
next
  08:15  Finish the ch.5 exercises  6b
  09:15  Finish the ch.5 exercises  6b
  10:15  · break 20m
0/6 blocks
```

Look at the times: breakfast has slid to 07:45, because `tm now` recomputes the
rest of the day from this moment. The timetable you printed at 07:12 was a
snapshot; `tm now` is the live one.

```console
$ tm start ^m1 --energy 5
▶ ^m1 Finish the ch.5 exercises · 07:50 · pred 5 rep 5
$ tm now
▶ ^m1 Finish the ch.5 exercises · started 07:50 · 40m of 360m
▶ Finish the ch.5 exercises  ci5  p5  6b
  08:30–08:50 · elapsed 0m · left 20m
next
  08:50  Finish the ch.5 exercises  6b
  09:50  · break 20m
  10:10  Finish the ch.5 exercises  6b
0/6 blocks
```

`pred 5` is the energy the model expected of you at that hour; `rep 5` is what
you reported.

**8. Finish the block.** A six-block item is not done after an hour, so finish
the *block* and keep the remainder:

```console
$ tm done --partial --went 1
✓ ^m1 Finish the ch.5 exercises · 65m/360m · 295m left
```

The line in `week/2026-W37.md` is now:

```markdown
- [ ] 5 6b Finish the ch.5 exercises est:4h55m ^m1
```

Still open, still estimated at 6 blocks originally, with 4h55m of work left.

**9. At the end of the day.**

```console
$ tm review day
 Day 2026-09-07 · lounge · 1/6 blocks · load 65.0 · window 07:10–15:10 · lost 0 · leak 0m · adherence 0%
 done      -    demoted  -    underused 0    replans 2 · drift 6m
 energy    pred 5   rep 5    MAE 0.0  bias 0.0
 estimates -
 breaks    planned none · actual - · rest debt 0
 sleep     7h30m
 tomorrow  first candidate vy69 (p5) · exm2 p5
```

Reading it: **`load`** is ci-weighted minutes of work logged — an hour at ci 5
is worth 60, an hour at ci 2 is worth 24. **`adherence`** is the share of the
blocks in your arrival plan you actually started within ten minutes of when they
were planned. **`replans`** counts how many times the day was recomputed, and
**`drift`** adds up the minutes your segments moved while it was. **`MAE`** is
how far the energy prediction was from what you reported; **`bias`** is the same
error with its sign kept, so a positive number means you run sharper than the
model expects. **`rest debt`** is break minutes you were owed and did not take.
**`lost`** is interrupted time and **`leak`** is time you could not account for.

You do not have to close the day. Closing happens by itself on the first command
of the next day.

If you would rather poke at a full tree than build one, `tm init demo --example`
writes a worked example — outcomes, milestones, tasks, routines, a meeting, a
deadline — that you can plan and replan against without inventing anything.

---

## The daily loop

The habit is a handful of commands spread over the day.

| when | command | what it is for |
|---|---|---|
| you get up | `tm wake --slept 7h30m` | sleep feeds the energy prediction; a short night lowers the whole curve |
| you sit down to work | `tm arrive lounge` | fixes the day's window and budget, syncs the calendar, plans the day |
| whenever you wonder | `tm now` | the live current block and the next three segments |
| starting work | `tm start ^id --energy 4` | begins a block and records the energy you actually have |
| finishing | `tm done --went 1` / `tm done --partial` / `tm stop` | finished the item / finished the block / gave up on the block |
| when it goes wrong | `tm energy 3`, `tm break`, `tm interrupt` … `tm resume` | tell `tm` one true thing; the plan follows |
| when you got it wrong | `tm undo` | reverses the last state change, 50 deep |
| end of day | `tm review day` | what actually happened, and the first candidate for tomorrow |

None of it is compulsory in the sense of blocking anything else: `tm plan`,
`tm start` and `tm now` all work on a bare tree with no `wake` and no `arrive`.
But skipping them costs you more than you would guess:

- With no `arrive`, the window just starts from now, and your location resolves
  to "anywhere" — which uses the **`home` energy curve**. That curve peaks at 4,
  so a ci-5 item is never scheduled at all until you run `tm arrive`. (It is not
  *capped* at 3 the way an explicit `tm arrive home` is, so ci-4 work still gets
  slots.)
- With no `wake`, the night is not "zero" — it is **unknown**, and an unknown
  night carries no sleep-debt penalty. A day with no `wake` is predicted exactly
  as if you had slept well. `tm wake --slept 0m` is what tells `tm` you did not.

So `arrive` is what makes the window, the budget and the energy curve honest,
and `wake` is what lets a short night show up in the plan.

### Finishing a block

This is the distinction people get wrong first.

| verb | the item becomes | the remaining time |
|---|---|---|
| `tm done` | `[x]` done | gone — you said the item is finished |
| `tm done --partial` | stays `[ ]`, gets `est:<remainder>` | kept on the item; counts as a finished block |
| `tm stop` | stays `[ ]`, gets `est:<remainder>` | back in the pool, re-competes with everything else |
| `tm extend 30m` | still running | the block gets longer, and `est:` grows to match |

`tm done` on a six-block item after one hour marks the whole thing done. Use
`--partial` unless you really finished it.

Already done it the wrong way? `tm undo` reverses the last state change and puts
the line back as it was:

```console
$ tm undo
undid done (done ^m1) · 2 file(s) restored · 9 left
```

The stack is 50 deep, and it works on nearly every verb — see
[What is undoable](#what-is-undoable).

### Interruptions, breaks and gaps

```console
$ tm break                 # start a break; the running block pauses
break 20m
$ tm break                 # the same command ends it
break ended · 6m of 20m
```

`tm break` and `tm pause` are toggles. A second `tm break 10m --where walk`
while a break is running just ends the break and ignores the arguments.

`tm interrupt` starts a stretch of lost time (it works even with nothing
running); `tm resume` ends it, replans the rest of the day, and tells you what
fell off:

```console
$ tm interrupt
interrupted
$ tm resume
resumed · lost 32m
```

If time went missing and you cannot say what happened, attribute it:

```console
$ tm idle i --min 60
60m attributed to interrupt
```

The kinds are `w` work, `b` break, `t` routine, `i` interruption, `l` leak.
Leaked time is counted, not judged; it turns up in the review as `leak 111m`.

### Capture

Anything you think of goes in the inbox first and becomes an item later.
`tm add` with no `--to` writes to `inbox.md`, as a raw line with no checkbox and
no id:

```console
$ tm add "renew the bike insurance before october"
- renew the bike insurance before october → inbox.md
```

When you come back to it, `tm triage` shows every inbox line and what the
grammar would make of it as it stands:

```console
$ tm triage
 11  - renew the bike insurance before october
     - [ ] renew the bike insurance before october
```

It does no interpreting — "before october" is still part of the title. Giving it
a ci, an estimate and a deadline is your job (or the `/triage` skill's):

```console
$ tm add "2 30m Renew the bike insurance due:2026-09-30" --to backlog --section Untied
- [ ] 2 30m Renew the bike insurance due:2026-09-30 ^xy9n → backlog.md
```

Then delete the raw inbox line. The TUI's Inbox screen does both halves in one
keystroke.

### Reviews

`tm review day`, `tm review week` and `tm review month` print what actually
happened. They are read-only unless you pass `--write`, which stores the text in
the period's file between `<!-- tm:review start -->` and
`<!-- tm:review end -->`. `--date` reviews an earlier period.

```console
$ tm review week --date 2026-W38
 Week 2026-W38 · 13 blocks · load 768.0 · planned 19.0b
 milestone hit - · demoted -
 blocks    Mon 3 · Tue 3 · Wed 3 · Thu 3 · Fri 1 · Sat 0 · Sun 0
 heat      7 days × 24h · block 17h40m · break 1h36m · routine 5h40m
 lounge    100% · streak 6 · wake 06 1.00 (5) · wake 07 1.00 (1)
 mix       ci4 11h · ci3 6h40m · ≥4 37%
 breaks    planned 1h20m · actual 1h36m · over 0 · - 4 (1h36m)
 sleep     Mon 7h (3b) · Tue 7h5m (3b) · Wed 7h5m (3b) · Thu 7h5m (3b) · Fri 6h30m (1b) · Sat - · Sun -
 latency   Mon -30/20 · Tue 50/20 · Wed 50/20 · Thu 50/20 · Fri 45/35
 energy    MAE Mon 0.8 · Tue 0.8 · Wed 0.8 · Thu 0.8 · Fri 0.0
 estimates lean ×1.34 (n=8)   soundcode ×1.21 (n=5)
 curve     home prior 3 4 4 4 3 3 3 3 2 2 2 2 · learned 3 4 4 4 3 3 3 3 2 2 2 2
 curve     lounge prior 4 5 5 5 5 4 4 4 3 3 2 2 · learned 4 5 5 4 5 4 4 3 3 3 2 2
 deadlines min slack -0.0d · hot 0 · impossible 1 · overdue 2
 churn     - · carry in 15.9b · out 0b
```

`heat` is where the week's hours went. `mix` is how much of your working time was
at ci 4 or 5. `energy MAE` is how far the model's prediction was from what you
reported. `latency` is two numbers a day — minutes from waking to arriving, then
from arriving to your first started block — so `Tue 50/20` is a fifty-minute
morning and a twenty-minute warm-up (a negative first number means you logged
`arrive` before `wake`). `streak` on the location line counts consecutive days
you worked at `lounge`. `estimates` and `curve … learned` are
the two lines that only appear once there is history to fit. `deadlines` counts
what is hot, impossible or overdue, and `carry in/out` is work that moved
between weeks.

```console
$ tm review month --date 2026-09
 Month 2026-09 · outcomes 0/3 · carry-over 29.8b
 outcomes  ○ !1 O1 163% · ○ !1 O2 111% · ○ !3 O3 11%
 churn     m1 (W37,W38) · m2 (W37,W38) · m3 (W37,W38)
 carry     2026-W37 15.9b · 2026-W38 13.9b
 cuts      m1 · m2 · m3
```

`churn` is work that has been demoted more than once, and `cuts` is the same list
stated as a recommendation. Progress can read over 100%: every block on a
descendant rolls up against the outcome's original estimate.

### Closing periods

You almost never run `tm close`. The first command after a period ends closes
the previous one, silently. Closing a **day** moves unfinished pinned items into
the week; closing a **week** demotes unfinished milestones into the month's
`# Demoted` section and files overdue dated items into `backlog.md` under
`# Overdue`; closing a **month** carries what is left forward.

Run it by hand only to close early, or to drop something as part of the close:

```console
$ tm close month --drop '^O3'
closed month 2026-09 · 6 moved · 4 demoted · 0 reopened · 1 dropped
```

It works after the month has ended too. The automatic close runs before the
verb body and carries everything forward, so by then the line is in the next
month's file; `--drop` fetches it back and drops it, leaving the same tree the
same command run on the last day of the month would have. Run the identical
command a second time and it is content: the item is already `[~]`, which is
what you asked for, so the close reports the drop and changes nothing. A
`--drop` that names something this close cannot act on — a typo, or a live item
that lives in `backlog.md` — is still an error, not a shrug:

```console
$ tm close month --drop '^a1'
tm: ^a1 is in backlog.md: --drop only names items of month/2026-09.md (or ones this close already carried into month/2026-10.md); drop it where it lives with `tm drop`
$ echo $?
1
```

`--drop` belongs to the month close alone; `tm close day` and `tm close week`
reject a drop list rather than ignore it.

---

## Writing items: the line grammar

This is the part of `tm` you will come back to. Everything you tell the planner
about your intentions is one line in one file.

There are two ways to write one. `tm add "…"` assigns the `^id`, validates the
grammar and tells you where the line landed — use it for a single item, and for
anything a script or Claude Code writes. Your editor is better for everything
else: aligning columns, reordering a section, pasting in ten lines at once,
writing a calendar file. `tm` re-reads the tree on every command, so hand edits
need nothing but a save; run `tm check` when you are done.

Calendar files are the one place to be careful. `tm add --to calendar` is
accepted and appends to `calendar/<this week>.md`, but every line in a calendar
file must be an `at:<start>/<end>` interval, so an ordinary `tm add` line lands
there happily and then fails the next `tm check`:

```console
$ tm add "- [ ] 1 1b thing" --to calendar
- [ ] 1 1b thing ^4bg6 → calendar/2026-W37.md
$ tm check
calendar/2026-W37.md:1: error[calendar-shape]: a calendar line must be an interval (`at:<start>/<end>`)
1 error, 0 warnings
```

Write calendar entries by hand instead, with the `manual` flag, so
`tm sync-cal` does not wipe them on the next sync.

### Anatomy of a line

```text
- [ ] 4 2b Exercises 5.3–5.5  @m1 #lean due:2026-09-11T23:59 max:2b/d est:1b ^t3
│ │   │ │  │                  └──────────────── tokens, any order ──────────────┘
│ │   │ │  └ title
│ │   │ └ estimate       (optional; must come right after the ci)
│ │   └ ci / min-energy 0–5  (optional; must come right after the state)
│ └ state
└ bullet
```

Read aloud: *an open task needing energy 4, estimated at two blocks, called
"Exercises 5.3–5.5", a child of milestone `m1`, tagged `lean`, due Friday night,
never more than two blocks of it a day, one block of it left, id `t3`.*

### The bullet, the state, and the two slots

An item is a line that **starts with `- ` at column 0**. Everything else in a
plan file — prose, headings, HTML comments, front matter — is kept verbatim and
ignored.

| line | is it an item? |
|---|---|
| `- [ ] 3 1b Task ^a1` | yes |
| `  - [ ] 3 1b Task` (indented) | **no** — indentation is not nesting; this is prose |
| `-[ ] 3 1b Task` (no space) | no |
| `* [ ] 3 1b Task` | no |
| `- Just a note` | **yes** — an item with no state. `tm check` complains, and `--fix-ids` will write an `^id` into your note |
| `- [ ]` | yes — an item with an empty title |

To write a bulleted note inside a plan file, indent it two spaces.

**States** — the character in the brackets:

| written | means | does the planner see it? |
|---|---|---|
| `[ ]` | to do | yes |
| `[>]` | in progress (written by `tm start`) | yes |
| `[x]` (or `[X]`) | done | no |
| `[-]` | demoted — archived by a week close or `tm demote` | no |
| `[~]` | dropped (`tm drop`) | no |
| `[?]` | waiting on someone or something; pairs with `waiting:<date>` | no — listed under `waiting:` in the diagnostics |

The state may be left out in `routines.md`, `optional.md` and `inbox.md`.
Anywhere else, a missing state is a `tm check` error.

**ci** (the first word after the state) is the item's *min-energy*: how sharp you
need to be to do it well, 0–5. **Estimate** (the next word) is `Nb` blocks, `Nm`
minutes, `Nh` hours, or `NhMm`. Both are positional — they only count in those
two slots.

| line | what actually happens |
|---|---|
| `- [ ] 7 2b Renew the permit` | `7` is not a ci, so `7` *and* `2b` fall into the title. `tm check` catches this one |
| `- [ ] 6 out of range ci` | title is `6 out of range ci`, ci falls back to the file default. **No warning** |
| `- [ ] 3 2d Days est` | `2d` is not a valid estimate; it becomes title text and the item has **no estimate**. No warning |
| `- [ ] Title with 2b in it` | `2b` is just a word — estimates only count in the slot |
| `- [ ] 30m walk the dog` | fine: no ci, estimate `30m`, title `walk the dog` |

> **The single most common silent failure: an item with no estimate anywhere is
> never scheduled, and `tm check` says nothing about it.**
>
> ```console
> $ tm add "3 Write the grant summary" --to week --section Tasks
> - [ ] 3 Write the grant summary ^4v9j → week/2026-W37.md
> $ tm check
> no problems
> $ tm plan
> 2026-09-07 · window 09:00–17:00 · budget 6 blocks
> 09:00  4 p5   Sort the photos                   1b
> 10:00  ·      rest 1h
> 11:20  ·      rest 1h
> 12:20  ·      rest 1h
> …
> · dropped: 4v9j
> ```
>
> Five free blocks, and the grant summary is in the `dropped:` line instead of
> any of them. An item with children is fine — it inherits the sum of theirs.

### Where the title ends

The title runs from the estimate up to the first word that starts with
`@ # ! ^` or that looks like `lowercase-word:`. After that, every word is
classified; anything that classifies as nothing is appended back onto the title.

| line | resulting title | why |
|---|---|---|
| `- [ ] Lean: through ch.8` | `Lean: through ch.8` | a capital letter means it is not a field |
| `- [ ] note: buy milk` | **`buy milk`** | `note:` is a lowercase word plus a colon, so it is read as a field |
| `- [ ] Call mum re: the trip` | **`Call mum the trip`** | same trap in the middle of a sentence |
| `- [ ] Ratio 3:1 improvement` | `Ratio 3:1 improvement` | `3` is not a lowercase letter |
| `- [ ] Meeting @ 10 with @e01` | `Meeting @ 10 with`, parent `e01` | a lone `@` is punctuation |

Rule of thumb: **a lowercase word ending in a colon starts a field.** Write
`Re:` with a capital, or rephrase.

### Every field

Fields are `key:value`, in any order, after the title. An unknown key is kept on
the line and reported as a warning. A known key with a value that does not parse
is kept and reported as an error — the field is simply absent until you fix it.

**Shape — where the item lives in time.** Only one shape wins, in the order
`at:` > `win:` > `due:`.

| field | what it does | accepted | example |
|---|---|---|---|
| `due:` | a deadline. Feeds the pressure calculation; a bare date means 23:59 that day | `YYYY-MM-DD`, `YYYY-MM-DDTHH:MM` — zero-padded, no seconds | `due:2026-09-11T23:59` |
| `at:` | a fixed appointment — a **wall**. Placed exactly there; nothing else is scheduled inside it | `…THH:MM/HH:MM` (same day; an earlier end rolls overnight) or `…THH:MM/YYYY-MM-DDTHH:MM` | `at:2026-10-20T10:00/12:00` |
| `win:` | a range the thing must happen inside. Needs `dur:` | `HH:MM-HH:MM` daily, or absolute `YYYY-MM-DDTHH:MM/HH:MM` | `win:11:30-13:30` |
| `dur:` | how long it takes. With `win:` it is the length to place; alone it is the estimate of last resort | `Nb Nm Nh NhMm` (**not** `Nd`) | `dur:30m` |
| `pref:` | preferred anchor inside the window | `HH:MM`, `wake`, `wake+<dur>` | `pref:wake+10m` |

**Recurrence.** Only one wins, in the order `every:` > `after-done:` >
`on-event:`.

| field | what it does | accepted | example |
|---|---|---|---|
| `every:` | a calendar rule | `day`/`daily`, `weekday(s)`, `week`/`weekly`, `Mon,Wed,Fri` (no spaces after commas), `3d`, `2w`, `2w:Sun`, `month:15` | `every:Mon,Wed,Fri` |
| `after-done:` | N after the last completion, optionally with a validity window | `<offset>` or `<offset>~<window>`; `d` allowed here | `after-done:2d~1d` |
| `on-event:` | wait for a named event, with an optional timeout | `<name>` or `<name>/<timeout>` | `on-event:reply/7d` |
| `on-miss:` | what happens to a missed occurrence | `expire`, `persist`, `next` (default: `expire` for windows, `persist` otherwise) | `on-miss:persist` |

**Budget.**

| field | what it does | accepted | example |
|---|---|---|---|
| `min:` | a floor — keep feeding this, at least this much per period. Raises priority pressure; does not gate | `<duration>/d\|w\|m` | `min:6b/w` |
| `max:` (alias `cap:`) | a ceiling. A real gate: once the logged minutes reach it, the item stops being schedulable that period | `<duration>/d\|w\|m` | `max:2b/d` |

**Dependencies, place, padding.**

| field | what it does | accepted | example |
|---|---|---|---|
| `after:` | not eligible until these are done | comma list of `^id`, `id`, `event:name` — **no spaces after the commas** | `after:^t4,event:visa` |
| `loc:` | only schedulable where you are | `lounge`, `home`, `out`, `any`, or any name you use | `loc:JCL` |
| `buffer:` | blocked time in front of an `at:` interval; also stretches the day's window | a duration, `d` allowed | `buffer:2h` |

**Estimate and energy.**

| field | what it does | accepted | example |
|---|---|---|---|
| `est:` | the *remaining* estimate. Overrides the leading estimate for everything the planner does. Usually written by `tm stop`, `tm done --partial`, `tm extend`, a close | `Nb Nm Nh NhMm` (**not** `Nd`) | `est:4h53m` |
| `ci:` | min-energy as a field — the only way to give a ci on a line with no state (routines, optionals). Beats a positional ci | `ci:0`–`ci:5` | `ci:0` |

**Stamps `tm` writes. Do not hand-edit these.**

| field | value | written by |
|---|---|---|
| `demoted:` | `W37`, `W37,W38`, `D07` | a week or day close, or `tm demote` |
| `waiting:` | a date | set with the `[?]` state when an `on-event:` item is completed |

Two `demoted:` stamps on one line is the signal that the work has failed twice
and should be cut or re-scoped.

One example of each, in one place:

```markdown
- [ ] 4 6b Pset 2                @O1 due:2026-09-11T23:59 max:2b/d est:4b ^d1
- [ ] 5 2h Midterm               @O1 at:2026-10-20T10:00/12:00 loc:JCL ^x1
- [ ] 1 Pick up package          win:2026-09-07T09:00/21:00 dur:20m ^a3
- lunch                          win:11:30-13:30 dur:30m every:day
- breakfast                      win:06:00-09:00 dur:30m every:day pref:wake+10m
- shower                         win:07:00-23:00 dur:20m after-done:2d~1d
- laundry                        win:09:00-21:00 dur:30m every:week on-miss:persist
- [?] 2 15m Ask about the group  on-event:reply/7d waiting:2026-09-05 ^a4
- [ ] 3 2b Lean practice         min:6b/w ^f1
- [ ] 3 1b Review the drafts     @m2 after:^t4,event:visa ^t5
- [ ] 1 ✈ ORD→SFO UA 1234        at:2026-09-12T08:15/10:40 buffer:2h travel-day ^g3
- [-] 4 3b Rollback path         @O2 est:3b demoted:W37 ^m2
- Factorio                       dur:2h max:4h/w
```

### Flags

Five bare words. They only count **after** a `@ # ! ^` or `key:` token has
already appeared on the line — otherwise they are title text.

| flag | what it does |
|---|---|
| `atomic` | must get contiguous slots; never split across a wall |
| `hot` | forces priority 0 — the row is marked `⚠` and `--explain` says `p = 0 (hot flag)` |
| `travel-day` | on an interval that lands today, the whole block budget goes to zero: routines, walls and optionals stay, no work is planned |
| `manual` | in a `calendar/` file, the line survives `tm sync-cal` (everything else there is rewritten from the feed) |
| `open` | parsed, preserved, and **completely inert** — nothing reads it |

**Write flags at the very end of the line, after the `^id`.** `tm check` only
half-catches a misplaced one. It warns when the flag word is the **last** word of
the title:

```console
$ tm check
week/2026-W37.md:3: warning[bad-value]: title ends with `hot`: flags count only after a `@ # ! ^ key:` token; move it after one if it was meant as a flag
0 errors, 1 warning
```

That came from `- [ ] 3 1b Do the thing hot ^z2`. But write
`- [ ] 3 1b hot Task ^h1` — the flag word anywhere earlier in the title — and
nothing warns at all. `tm check` says `no problems`, and the item is planned at
its ordinary priority:

```console
$ tm plan --explain ^h1
p = k(3) + 2 (no due, no floor) = 5; deps ok
```

A flag word that is not the last word of a title is a silent failure, like an
item with no estimate: nothing tells you, and the line just behaves as if you had
never written it.

### Ids, parents and tags

**`^id`** is the handle every command uses. It can be any run of letters,
digits, `_` and `-`; `tm` generates four characters from an alphabet with no
`l`, `o`, `0` or `1` in it, so you never squint at an id. Ids are global across
the whole tree, not per file. `tm add` assigns one and prints it;
`tm check --fix-ids` writes one onto every line that lacks one. Lines in
`routines.md`, `optional.md` and `inbox.md` get no id — those are addressed by
their title (`tm skip workout`).

**`@parent`** links an item to the item with that `^id` (or, for a routine, that
title). Parents may live in any file — hierarchy and horizon are independent.
What a parent actually does:

- **Priority comes from the root.** A `!k` on a non-root is ignored (with a
  warning); the whole branch takes the root's `k`.
- **ci is inherited** from the nearest ancestor that states one.
- **Tags are inherited**, all the way up.
- **Estimates roll up**: an item with no estimate of its own uses the sum of its
  children's remaining time.
- **Deadlines are derived**: a child with no shape of its own, under an ancestor
  that is an `at:` interval, is treated as due when that interval starts. This
  is how "revise for the midterm" gets a deadline without you writing one.

**`#tag`** is free-form. Tags are inherited, and they are what the learned
duration multiplier is keyed on (`#lean ×1.34` means your Lean work takes 34%
longer than you estimate). Tags do not affect priority or eligibility.

**`!k`** is explicit priority, `!1` (most important) to `!4`, and only on a root.

### Series

A reading list, a course, a set of volumes — things where only the next one
matters:

```markdown
## series:cell-bio
- [x] 4 4b Cell Biology vol. 1 ^c1
- [ ] 4 4b Cell Biology vol. 2 ^c2
- [ ] 4 4b Cell Biology vol. 3 ^c3
```

Only the **head** — the first member that is not `[x]` or `[~]` — is visible to
the planner. Finishing the head activates the next line. Asking about a later
one answers `^c3 is not a candidate today`. Adding a volume is adding a line.
Any `#`-level heading whose text starts with `series:` works; the natural home
is `backlog.md`.

---

## The files, and "horizon is the file"

```text
plan/
├── config.toml            # settings; `tm` finds a plan directory by this file sitting beside the rest
├── CLAUDE.md              # the rules for Claude Code
├── inbox.md               # capture, untriaged, any wording
├── backlog.md             # undated work, far-out dated work, series
├── routines.md            # recurring windows: sleep, meals, laundry
├── optional.md            # what may fill rest slots, and nothing else
├── month/2026-09.md       # outcomes
├── week/2026-W37.md       # milestones and tasks — the main working file
├── day/2026-09-07.md      # today's generated timetable, pinned items, log
├── calendar/2026-W37.md   # generated from your ICS feeds
├── .claude/  .githooks/  .gitignore
└── .tm/                   # log.jsonl, model.json, state.json — never hand-edit
```

**An item's horizon is decided purely by the path its line sits on.** There is no
`horizon:` field. Moving work between horizons means moving the line — with
`tm move ^id week`, or by cutting and pasting in your editor. That is the whole
mechanism, and it is why the tree is worth keeping tidy.

| file | horizon | default ci | candidate today? |
|---|---|---|---|
| `month/YYYY-MM.md` | month | 3 | **never** — outcomes are not work |
| `week/YYYY-Www.md` | week | 3 | yes, the current week's file |
| `day/YYYY-MM-DD.md` | day | 3 | only items under `# Pinned` |
| `backlog.md` | none | 3 | yes, always |
| `routines.md` | routine | 1 | instances due today |
| `optional.md` | optional | 0 | yes, but only for rest slots |
| `calendar/YYYY-Www.md` | calendar | 3 | intervals covering today |
| `inbox.md` | inbox | 3 | no |

What each is for:

- **`month/`** holds **outcomes, not work**: three to five statements of a
  finished state, each with an explicit `!1`–`!4`. Everything under an outcome
  inherits its `k`. An outcome with an estimate and no children is a warning —
  that is a milestone, and it belongs in `week/`. The `# Demoted` section here is
  where a week close files what you did not finish.
- **`week/`** is where you actually live: milestones (children of the outcomes),
  the tasks that serve them, and anything dated inside the week.
- **`day/`** is mostly generated. The one part that is yours is `# Pinned` —
  items you want today whatever the ranking says. It is the **only** section of a
  day file the planner reads.
- **`backlog.md`** is horizon-free: finite undated work, far-out dated work, and
  `## series:` sections. Its items compete for today, every day.
- **`routines.md`**: every line needs a window (`win:` + `dur:`) or an
  `after-done:` interval. No checkboxes — instances live in the log, so the file
  never changes.
- **`optional.md`**: ci 0, priority 5, rest slots only. An optional never
  displaces work. `max:4h/w` keeps it honest.
- **`calendar/`** is rewritten by `tm sync-cal`. Your own entries there need the
  `manual` flag or they are wiped on the next sync.

### The day file

```markdown
---
date: 2026-09-07
wake: 06:45
slept: 7h30m
loc: lounge
window: 07:10..15:10
budget: 6
---
![day](2026-09-07.svg)
<!-- tm:plan start 07:12 -->
07:12  ·      breakfast 30m
07:42  4 p5   Draft the rollback tests          2b
…
<!-- tm:plan end -->

# Pinned

## Log
06:45 wake slept=7h30m
07:10 arrive lounge
07:50 start ^m1 pred=5 rep=5
08:55 done ^m1 65m/360m went=1

## Notes
```

- The **front matter** is written for you to read, by `wake` and `arrive`.
- Everything between `<!-- tm:plan start … -->` and `<!-- tm:plan end -->` is
  **regenerated wholesale** on every replan. Anything you type in there is
  destroyed. The same goes for `<!-- tm:review start/end -->`.
- **`# Pinned`** is yours. Unfinished pinned items move to the week at day close.
- **`## Log`** is the readable mirror of `.tm/log.jsonl`, appended by the clock
  verbs. Do not edit it.
- **`## Notes`** is free text — the natural place for Claude Code to write prose.
- `## Log` and `## Notes` are protected from validation **only in a day file**.
  In a week or backlog file those are ordinary headings and their bullets are
  real, schedulable items.
- `day/<date>.svg` is a day bar picture, regenerated with the timetable; the
  `![day](…)` line renders it in a Markdown preview.

### Demotion: what happens to work you do not finish

When a week closes, the week file turns into an archive — `closed:` goes into its
front matter — and what was unfinished is dealt with in four different ways
depending on what it is.

**Unfinished roots become `[-]` in place**, and a stamped copy carrying the
remaining estimate lands in the month's `# Demoted` section:

```markdown
# Demoted
- [-] 5 6b Finish ch.5 exercises @O1 est:4h53m demoted:W37 ^m1
- [-] 4 6b Rollback path passes tests @O2 est:6b demoted:W37 ^m2
- [-] 5 3b Read ch.6 @O1 est:3b demoted:W37 ^m3
```

**Unfinished children are deleted from the week file outright.** They get no
`[-]` line, no copy in the month, no line anywhere. This is the one place `tm`
removes text you wrote, and it is worth seeing before it happens to you:

```console
$ tm close week
closed week 2026-W37 · 3 moved · 5 demoted · 0 reopened · 0 dropped
```

That was `tm init demo --example`, whose `# Tasks` section held `^t1 ^t3 ^t4
^t5`. Afterwards all four are gone — `grep` finds them nowhere in the tree but
the day file's `## Log`. The *work* is not lost, because it is carried as a
number in the parent's `est:`, but the breakdown is, and only version control
will get it back. If a subtask is worth keeping as a sentence, promote it to a
root of its own before the week closes, with
`tm move ^id week --section Milestones` or your editor.

What reaches the parent is `max(the parent's own remaining, the sum of the
deleted children's own estimates)` — **not** their sum on top of it. A subtask is
normally a decomposition of its parent, so a `6b` milestone with three `1b`
children still demotes as `est:6b`; the children's minutes only show up when they
add to more than the parent claimed, which is `tm` telling you the parent's
estimate was stale. A parent with no estimate of its own picks up the children's
total:

```markdown
- [-] 4 Parent with no estimate est:3b demoted:W37 ^pp        # children were 2b + 1b
- [-] 4 3b Parent with own estimate est:3b demoted:W37 ^qq    # child was 2b; 3b already covers it
```

**An item demoted twice keeps one record.** The stamps accumulate on the single
copy under `# Demoted` (`demoted:W36,W37`); a second demotion never writes a
second line, and neither does a close catching up on periods you were away for —
the record is moved into the month the close is running in, stamps and all. That
is what keeps `tm check` quiet: an `^id` may be on the `[-]` line in the archived
week and on its one archive copy, and nowhere else.

**Overdue dated items move to `backlog.md`** under a `# Overdue` heading, exactly
as written — they are not demoted. **Appointments still in the future**, and the
prep children hanging under them, move into next week's file so the planner can
still see them. Finished `[x]` lines and every routine stay exactly where they
are.

Bringing work back is one command, and it lands in this week's file:

```console
$ tm readopt ^m1
readopted ^m1 → week/2026-W38.md
```

The state goes back to `[ ]` and **the stamp is kept on purpose**. A line
carrying `demoted:W37,W38` has failed to happen twice; that is a decision you
have been avoiding, not a scheduling problem. `tm review month` lists those under
`cuts`.

`readopt` is the demoted line's verb, and it is the only one, so it holds to two
rules:

- **An item that was never demoted is refused**, because there is nothing to
  bring back: `` tm: ^t1 is in week 2026-W37: not demoted, so there is nothing to
  readopt (use `tm move`) ``, exit 1. Use `tm move ^t1 <horizon>` to move a live
  line.
- **An item that is still live somewhere gets its archive copy folded in**, not
  copied. Right after a week close the id is on two lines: the `[-]` record and
  the live line you carried forward. `tm readopt ^m2 --to week/2026-W38.md` then
  moves *the live line* into W38, adds the copy's `demoted:` stamps **and its
  `est:`** to it, and deletes the copy — one line, one id. Ids are global, so
  nothing else would leave the tree valid. The estimate comes across because the
  copy is where the remaining was recorded: the archived line still says what
  the item was estimated at before the demotion, so keeping that number instead
  would quietly hand you back work you had already done.

On the example tree, where `^m2` ships as exactly that pair:

```console
$ tm readopt ^m2
readopted ^m2 → week/2026-W37.md
$ grep '\^m2' week/2026-W37.md
- [ ] 4 6b Rollback path passes tests   @O2 est:3b demoted:W37 ^m2
```

The line still reads `6b` — the original estimate is never rewritten — and
`est:3b` is what is left of it.

### Two traps about file names

1. **A stray `.md` file in the plan directory is still parsed**, and its `- [ ]`
   lines become real candidates in `tm plan`. You get one warning
   (`` warning[bad-value]: unknown file kind `notes.md`; treated as backlog ``)
   and no validation of the lines themselves. Keep loose Markdown out of the
   plan directory.
2. **Only the last directory segment is matched.** `archive/week/2026-W37.md` is
   read as a live week file, with no warning at all, and its items compete for
   today's slots. Do not stash old plan files in subfolders.

---

## Why the day came out that way

Nothing about the timetable is arbitrary, and `tm` will explain any part of it.
The one command to remember is:

```console
$ tm plan --explain ^m1
p = k(1) + 2 (no due, no floor) = 3; deps ok
```

### Window and budget

`tm arrive` fixes two numbers for the day.

- **Window** — when you can work: `min(arrival + window_hours, window_cap)`,
  plus every appointment minute inside it. Meetings do not eat your working day;
  they stretch it. Arriving at 06:55 on a day with one hour-long meeting gives a
  window of `06:55–15:55` instead of `06:55–14:55`.
- **Budget** — how much work you can really do:
  `floor(window_hours × 60 / block_min × budget_ratio)`, which is
  `floor(8 × 60 / 60 × 0.75)` = **6 blocks** by default. The budget comes from
  the config, not from today's length. That is deliberate — the constraint is
  you, not the clock.

Both are stored when you arrive, and every replan reuses them.

The two rules pull apart on a late start, and this is worth knowing before it
bites. The window end moves later with your arrival, but only until it hits
`window_cap`; the budget does not move at all:

```console
$ tm arrive lounge
arrive lounge 16:00 · window 16:00–19:00 · budget 6 blocks
```

Three hours of window carrying a six-block budget. Nothing warns you — the plan
simply schedules more than the day can hold and the honesty ratio goes up. If
you often start late, either lower `budget_ratio` or push `window_cap` out.

### What can be scheduled today

Today's candidate set is exactly: everything in this week's file; everything
under `# Pinned` in today's file; everything in `backlog.md`; the head of every
`## series:` section; routine instances due today; calendar intervals covering
today; and `optional.md` (priority 5, rest slots only).

Month items are never candidates. Day-file items outside `# Pinned` are never
candidates. Non-head series members are never candidates.

**Instances.** A routine has no checkbox, so it cannot be "open" or "done" the
way a task is. Instead, its recurrence rule (`every:`, `after-done:`) decides
whether there is an **instance** of it today, and the instance has to be placed
inside its `win:` window — lunch between 11:30 and 13:30, not merely "some time
today". A window that closes with the instance unplaced is a miss, and `on-miss:`
says what happens: `expire` drops it and carries nothing, `persist` keeps it
pending and overdue (which makes it `p 0`), `next` counts it as skipped and
leaves the next occurrence alone. Instances live only in the log, which is why
`tm routine done lunch` and `tm skip workout` change no file.

Then four gates, checked in this order. A blocked item is **kept in the output
with its reason**, never silently dropped:

1. `[?]` waiting → reported as `waiting: a4`
2. state is not `[ ]` or `[>]`
3. an unsatisfied `after:` → reported as `t5 blocked by t4`
4. a `max:` cap already spent → `cap 2b/d reached (120m used)`

### Priority

Every candidate gets a priority `p`, where **0 is the most urgent**. The rule:

```text
p = k + bin(u)
```

- **`k`** is how much it matters: the `!1`–`!4` on the root of its branch, or
  `default_priority` (3) if nothing says otherwise.
- **`u`** is how much pressure the deadline is under: `need ÷ capacity`, where
  `need` is the remaining estimate × `safety` (1.3 — a 30% cushion) and
  `capacity` is the usable slot-time before the deadline, after earlier deadlines
  have taken theirs.
- **`bin(u)`** turns that ratio into a number: `u ≥ 0.5` adds 0, `≥ 0.25` adds 1,
  `≥ 0.1` adds 2, anything less adds 3.

The cases, in the order they are tried — the first that matches decides:

| case | p |
|---|---|
| an `at:` appointment | off the scale — walls are placed, not competed for |
| an `optional.md` line | 5 — never displaces work |
| overdue, with `on-miss:persist` | 0 |
| a mandatory routine instance due today | 0 |
| the `hot` flag | 0 |
| dated, and `u ≥ 1` | 0 — **HOT**, or **IMPOSSIBLE** when the need exceeds what is available |
| dated, and `u < 1` | `k + bin(u)` |
| a `min:` floor, and its `u ≥ 1` | 0 |
| a `min:` floor | `k + bin(u_floor)` |
| everything else | `k + 2` — pure rank |

Then priorities are clamped to 0–7, and **hysteresis** (on by default) lets an
item's `p` improve by at most one step a day, whatever put it there — not just
the binned cases. Getting worse is unlimited, and a jump straight to `p = 0` is
never held back. `optional.md` lines are exempt: they are pinned at 5. The point
is that the queue does not churn.

Four real explanations, all from the `tm init demo --example` tree, so you can
repeat them. On the Monday, a milestone under an `!1` outcome with no deadline:

```console
$ tm plan --explain ^m1
p = k(1) + 2 (no due, no floor) = 3; deps ok
```

And a problem set due Friday, four days out — dated, but not yet under pressure:

```console
$ tm plan --explain ^d1
p = k(3) + bin(u=0.26 → +1) = 4; need 7.8b, avail 30b by 2026-09-11; deps ok; cap 2b/d: 0b used
```

Run the same tree on the Friday instead. A weekly routine whose window has gone
by, and the same problem set on the day it is due with none of it done:

```console
$ tm plan --explain laundry
p = 0 (overdue, on-miss persist); deps ok
$ tm plan --explain ^d1
p = 0 (IMPOSSIBLE: needs 7.8b, 6b available by 2026-09-11); deps ok; cap 2b/d: 0b used
```

`IMPOSSIBLE` is `tm` telling you the deadline cannot be met with the days and
caps you have. It still schedules what it can; the decision is yours.

**Ties are broken by line order.** Rank is where the line sits in its section —
that is what `tm rank ^id 1` and the TUI's `J`/`K` rewrite. If you want the plan
to name a task rather than its parent milestone, move the task above it: **a
parent competes with its own children**, and a milestone that sits higher in the
file usually wins.

`tm rank` only reorders inside one heading, though. In the layout this manual
recommends — milestones under `# Milestones`, their tasks under `# Tasks` — a
task can never be ranked above its own parent:

```console
$ tm rank ^t1 1
^t1 already at position 1
```

`^t1` is already first in `# Tasks`, and its parent `^m3` is still up under
`# Milestones` where ranking cannot reach it, so nothing changed. Move the line
into the parent's section first, then rank it:

```console
$ tm move ^t1 week --section Milestones
^t1 week/2026-W37.md → week/2026-W37.md
$ tm rank ^t1 1
^t1 → position 1
```

**Pinning does not raise priority.** `# Pinned` only makes an item a candidate
for today. A pinned item with no `!k` computes `p = 5` like anything else, and
can be dropped off the end of the day.

### Energy, ci, and slots

This is the idea that makes `tm` different from a queue.

**Every item has a `ci`: the energy it needs.** Deep, difficult work is ci 4 or
5. Admin is ci 2. Watching a video is ci 0.

**Every hour of your day has a predicted energy, 0–5, too.** It comes from a
curve for where you are, indexed by hours since you woke, adjusted for sleep
debt and for anything you have reported today.

**An item is only placed in a slot whose energy is at least its ci.** That is
the whole mechanism, and everything else follows from it:

- Working at `home` caps slot energy at `home_max_ci` (3) — so ci 4 and 5 work is
  never scheduled there. `tm plan --allow-home` lifts the cap for one run. The
  cap is tied to the name `home`, not to the curve, so a location `tm` has not
  met before borrows the `home` curve without the cap.
- Reporting a low energy re-plans the rest of the day and drops the work you
  cannot do. `tm energy 4` on a morning full of ci-5 items pulls the ci-4 work
  forward and pushes the rest out; what it cost you shows up as the `deferred:`
  diagnostic.
- A slot whose energy is 2 or more above the item's ci is marked `↓` — a good
  hour spent on easy work: `13:00  4↓p5 Call the bank … ↓ slot 4, item 2`.
- The reverse is `ci-5 lost`: rest minutes at energy 4 or 5 on a day when a
  ci-5 item existed and none of those minutes could take it.

Report energy whenever it changes — mid-block is fine:

```console
$ tm energy 4
energy 4 (pred 5) at 08:00 · replanned
```

That one word rewrites the day. The same three afternoon rows, before the report
and after it:

```text
09:30  5 p3   Finish ch.5 exercises        @O1  6b
10:30  5 p3   Finish ch.5 exercises        @O1  6b
12:00  4 p3   Exercises 5.3-5.5            @m1  2b
```

```text
09:30  4 p3   Exercises 5.3-5.5            @m1  2b
10:30  4 p3   Exercises 5.3-5.5            @m1  2b
12:00  3 p3   Draft the rollback tests     @m2  1b
```

Saying "4" dropped every ci-5 item out of the rest of the day and pulled the
ci-4 work forward. The report fully corrects the next `posterior_full_hours` (3)
hours of slots and fades to nothing by `posterior_zero_hours` (6).

### Reading the timetable

A row is:

```text
HH:MM  <slot energy><↓> p<priority> <mark> <title> @<parent> <estimate> (<actual>) <note>
```

Five real rows, from a few different days:

```text
08:00  5 p1 ✓ Read ch.6 §3                 @m3  1b  (58m)
09:20  4 p1 ▶ Exercises 5.3–5.5            @m1  2b×1.6
09:20  5↓p3   Claude Code drafts tests     @m2  1b        ↓ slot 5, item 3
09:00  1 p0 ⚠ Pick up package                   20m       due today
12:50  ⏰     Meeting w/ host                   1h
```

| glyph | meaning |
|---|---|
| `✓` | finished |
| `▶` | running right now |
| `⚠` | priority 0 — due today, overdue, mandatory, `hot`, or a deadline that no longer fits |
| `↓` | the slot is under-used, next to the energy number |
| `·` | a routine, break, rest, sleep, or lost time |
| `⏰` | an appointment (a wall) |
| `○` | something from `optional.md` |
| `🌙` | the wind-down |
| `───` | the window-end divider — everything below it is outside the budgeted day |

Two things about the numbers:

- **The number in the second column is the slot's energy, not the item's ci.** A
  ci-2 item placed in a good hour shows a 3 or a 4. Only on finished rows, which
  have no slot, does it fall back to the item's ci.
- `2b×1.6` means "two blocks as written, scaled by the learned 1.6× multiplier".
  Once `tm` has learned that your estimates run long, the multiplied figure is
  what it actually budgets — and `tm done` measures you against it. The estimate
  column always shows the *original* estimate, not the remaining `est:`.

### The diagnostics

The `·` lines under a plan are not written into the day file; they are the
planner explaining itself.

```text
· 0 underused · 0 ci-5 lost
· plan honesty 1.33 — planned above a realistic budget
· t5 blocked by t4
· waiting: a4
· dropped: m3 · t1 · m2 · d2 · d1 · m4 · x2 · a1 · c2 · p1
```

They come out in a fixed order, and any of them can be missing on a given day:

| line | means |
|---|---|
| `N underused (4→2)` | N slots went to work well below their energy |
| `N ci-5 lost` | minutes of high energy that no ci-5 item could use |
| `plan honesty 1.33` | the work scheduled needs 1.33× the minutes your budget has. Only printed above 1.1 |
| `rest debt 20m` | break minutes today owed you that the log shows you skipped |
| `d1 CS 234 pset 2 impossible: 7.8b short by 2026-09-11` | the deadline cannot be met — this much work has nowhere left to go |
| `hot: d1` | the items now at `p 0` through deadline pressure |
| `<id> conflicts with <id>` | two appointments overlap; nothing is scheduled in the overlap until you move one |
| `t5 blocked by t4` | an `after:` dependency is not satisfied |
| `deferred: m2 · d1 · t3 · c2` | work that would have fitted at the *predicted* energy but not at the one you reported. This line is what a `tm energy 4` costs you |
| `waiting: a4` | a `[?]` item, waiting on an event |
| `dropped: …` | eligible work that did not fit today. Not `[~]` dropped — just not today |
| ``travel day: no blocks planned (`travel-day` wall today)`` | a `travel-day` interval landed today, so the block budget is zero |
| `groceries: no free 45m position in 10:42–20:00; not planned today` | a routine's `win:` window had no gap long enough for its `dur:`. Shorten the routine, widen the window, or accept the miss |

Two notes on that table. A routine that could not be placed is named by its
**title**, not by an id, because routines have no ids — so `groceries:` and
`breakfast:` are routine misses, not items. And an `impossible:` line is printed
a second time, after the `·` block, as an unprefixed banner, so that it is hard
to scroll past:

```text
· d1 CS 234 pset 2 impossible: 7.8b short by 2026-09-11
· hot: d1
…
IMPOSSIBLE d1 CS 234 pset 2: needs 7.8b, 0b available by 2026-09-11
```

`tm plan --diff` adds one more line, `diff: +0 −0 moved 2 · drift 8m`: what
changed since the last plan, and how far the day has slid.

### What tm learns about you

`tm` keeps an append-only log of everything you do (`.tm/log.jsonl`) and fits a
small model from it.

```console
$ tm model --fit
fitted from 22 observations
$ tm model --show
model  fitted 2026-09-18 · 22 obs
energy    hsw  0  1  2  3  4  5  6  7  8  9 10 11
  home         3  4  4  4  3  3  3  3  2  2  2  2
  lounge       4  5  5  4  5  4  4  3  3  3  2  2
sleep     debt shift - (config)
duration  _default ×1.31 · lean ×1.34 · soundcode ×1.24
weekday      Mon   Tue   Wed   Thu   Fri   Sat   Sun
p(lounge)   0.92  0.92  0.92  0.92     -     -     -
arrival    06:59 07:00 07:00 07:00     -     -     -
```

Three things are learned: the **energy curve** per location by hours since wake;
the **duration multiplier** per tag (how much longer things take than you say);
and your **habits** per weekday (when you start, where you are), which feed the
week-ahead capacity grid. Until there is data, the config priors are used —
`tm model` will say `not fitted (using config priors)`.

`tm model --compare` scores the stored model against a fresh fit and says which
it would keep.

One caveat: partial completions are fed into the duration fit as
`actual ÷ full estimate`, so a day spent doing an hour at a time on big items can
teach `tm` that you finish early when you did not.

### The week ahead

```console
$ tm plan --week
day          tot     5     4     3     2     1     0
Mon 09-07   6h50    4h    2h   50m     ·     ·     ·
Tue 09-08     6h    3h    3h     ·     ·     ·     ·
Wed 09-09     6h    3h    3h     ·     ·     ·     ·
Thu 09-10     6h    3h    3h     ·     ·     ·     ·
Fri 09-11     6h    3h    3h     ·     ·     ·     ·
Sat 09-12     6h    1h    3h    1h    1h     ·     ·
Sun 09-13     6h     ·     ·    4h    2h     ·     ·
total      42h50   17h   17h  5h50    3h     ·     ·
```

That is the capacity grid: how many hours at each energy level are left this
week. It is the `capacity` that deadline pressure `u` is divided by, and it is
what to look at before promising anything.

---

## The terminal UI

```sh
tm tui
```

Five screens over the same files, with every action running the same code as the
equivalent command. It watches the plan directory, so edits you make in your
editor show up within a second, and it replans on its own every minute.
`tm undo` works across everything it does.

It needs a real terminal:

```console
$ tm tui < /dev/null
tm: tm tui needs a terminal (stdout is not a tty) — every verb of §13 also works on its own
```

That message, and every `--help` screen, cites `§` numbers from the design
document `tm` was built to. You do not have it and you do not need it —
everything those sections say that affects you is in this manual. Read `(§7.1)`
as "there is a reason for this", not as a chapter you were meant to have read.

The message is nearly true: every planning and clock action has a command. Two
TUI keys have no command-line twin — `n`, which writes a note into the day
file's `## Log` (from the command line, type it into `## Notes` yourself), and
`l`, whose nearest equivalent is re-running `tm arrive <loc>`.

### The frame

```text
row 1        status line — date, clock, location, wake, predicted energy,
                           blocks done / budget, leak, adherence, window end, lost
rows 2–3     the day bar
rows 4…n-1   the body — the only part the 1–5 screens change
row n        hint line: message or open input on the left, keys on the right
```

Below `[tui] min_width` columns (110 by default), panes stack instead of sitting
side by side, and the week pane folds into the status line.

### The day bar

Two rows, both spanning **24 hours starting at today's wake time** — not the
working window, not midnight.

- **Top row: the day as it stands.** Logged time wins in the past, planned time
  in the future.
- **Bottom row: the ghost** — the plan exactly as it stood when you arrived,
  replayed from the record, never recomputed, drawn at half brightness. Where the
  top row has slid right of the ghost, you are behind the day you planned.

| character | what it is |
|---|---|
| `░` `▓` `█` | work — the shade is the item's ci (0–1 light, 2–3 medium, 4–5 full) |
| `▒` | a routine |
| `░` | also a break, and an unfilled rest slot |
| `█` | also sleep, and a wall (an appointment) |
| `╱` | lost or leaked time |
| `╳` | an interruption |
| `∙` | an optional |
| (blank) | nothing planned or logged |

**The shades repeat, so it is the colour that separates work from rest.** A long
`░` run in the evening is rest, not a stretch of ci-0 work; a solid `█` block at
midnight is sleep, not deep work. Hover it if you are unsure.

Colour carries two more facts: **hue is the project** (the root outcome an item
hangs under, hashed into the `[tui] palette`), and **brightness is the ci**. Two
blocks of the same colour are the same project.

The mouse does exactly two things, and only on these two rows: **hover** pops a
tooltip (`Claude Code drafts tests · 1h · ci3 · p3 · @O2`), and **left click**
moves the Timeline selection to that segment.

### Screen 1 — Today

```text
tm · Mon 2026-09-07 · 10:42 · lounge · wake 06:05 (7h) · pred 5 ·  ● 0/6 · leak 0m · adherence 17% · window → 16:00 · lost 0
                  █████▒▒ ▒▒▒▒▒▒██████████▓▓▓▓▓▓▒▒▒▒▒▒▒▒▒▒▒▒▒∙∙∙∙∙∙       █████████████                               ▲ 10:42
      ██████████████████████████████████████████                                                                      plan @07:00
┌ Timeline ─────────────────────────────────────┐┌ Now ──────────────────────────────────────┐┌ Week W37 · 0/25 ─────────────────┐
│09:50  5 p3   Finish ch.5 exerci…  @O1  6b    …││ci5 p3 Finish ch.5 exercises  @O1          ││  m1 Finish ch.5 e…     ░░░░░░ 0/6│
│10:42  5 p3 ▶ Finish ch.5 exerci…  @O1  6b    …││elapsed 52m ▐███░░░░░░░░░░░░▌ est 6b ×1.0  ││  m2 Rollback path…     ░░░░░░ 0/6│
│10:50  1 p0 ⚠ Pick up package           20m   …││next 10:50 Pick up package · 11:30 lunch ·…││  m3 Read ch.6          ░░░░░░ 0/3│
│11:30  ·      lunch 30m                        ││                                           ││  m4 Pick winter c…     ░░░░░░ 0/2│
│12:00  ·      laundry 30m                      ││d done  x extend  s stop  b break  i inter…││  d1 CS 234 pset 2      ░░░░░░ 0/6│
│12:50  ⏰     Meeting w/ host           1h     ││0-5 energy  l location  K skip  n note  Sp…││⚠ x1 Midterm            ░░░░░░ 0/2│
│13:50  4 p3   Exercises 5.3–5.5    @m1  2b     ││                                           ││──── HOT / overdue ───────────────│
│14:50  3 p3   Claude Code drafts…  @m2  1b     ││                                           ││⚠ x1 Midterm · wall               │
│16:00  ───    window ends 16:00                ││                                           ││⚠ a3 Pick up package · due today  │
│16:00  ·      workout 1h                       ││                                           ││⚠ lunch · due today               │
│17:00  ·      shower 20m                       ││                                           ││⚠ dinner · due today              │
│17:30  ·      dinner 30m                       ││                                           ││⚠ workout · due today             │
│18:00  ·      groceries 45m                    ││                                           ││⚠ laundry · overdue               │
│18:45  ○      Severance S3E4            1h     ││                                           ││⚠ g1 Meeting w/ host · wall       │
│21:30  🌙     wind-down · bed 22…              ││                                           ││──── Waiting ─────────────────────│
│22:00  ·      sleep 8h30m                      ││                                           ││? a4 Ask Prof. Lee about the read…│
│                                               ││                                           ││──── Diagnostics ─────────────────│
│                                               ││                                           ││0 underused · 0 ci-5 lost         │
│                                               ││                                           ││plan honesty 1.33 — planned above…│
│                                               ││                                           ││t5 blocked by t4                  │
│                                               ││                                           ││waiting: a4                       │
│                                               ││                                           ││dropped: m3 · t1 · m2 · d2 · d1 ·…│
│                                               │└───────────────────────────────────────────┘│                                  │
│                                               │┌ Energy today ─────────────────────────────┐│                                  │
│                                               ││pred  4  5  5  5  5  4  4  4  3  3         ││                                  │
│                                               ││rep   ·  ·  ·  ·  ·  ·  ·  ·  ·  ·         ││                                  │
│                                               ││     07 08 09 10 11 12 13 14 15 16         ││                                  │
└───────────────────────────────────────────────┘└───────────────────────────────────────────┘└──────────────────────────────────┘
:                                                                      j/k move · Enter open · e edit · r replan · R sync · ? help
```

The **Timeline** is today's plan, one row per segment, in exactly the format the
day file gets. The **Now** pane is the running block with a progress bar against
its planned minutes, and the next three segments. **Energy today** is what the
model predicts each hour (`pred`) against what you reported (`rep`). The **Week**
pane is your milestones with progress bars, then everything hot or overdue,
what is waiting, and the planner's complaints.

### Screen 2 — Queue

Month outcomes on the left, this week in the middle, the children of whatever is
selected on the right. This is where you groom: reorder lines (which *is* rank),
set estimates and ci, demote and readopt.

```text
┌ Month 2026-09 ────────────────┐┌ Week W37 · planned 20 / budget 25 ─────────────────────┐┌ Tasks @m1 ──────────────────────────┐
│!1 O1 Lean: through ch.8 o… ░░░││p3  5 6b m1 Finish ch.5 exercises             @O1 ░░░░░░││p3 4 1b Exercises 5.3–5.5            │
│!1 O2 Soundcode: end-to-en… ░░░││p3  4 6b m2 Rollback path passes tests        @O2 ░░░░░░││                                     │
│!3 O3 Winter course select… ░░░││p3  5 3b m3 Read ch.6                            @O1 ░░░││                                     │
│                               ││p5  2 2b m4 Pick winter courses                   @O3 ░░││                                     │
│Demoted (1)                    ││p4  4 6b d1 CS 234 pset 2   @O3 due Fri  u=0.3  fits 6/6││                                     │
│· m2 Rollback path passes … W37││⏰  5 2h x1 Midterm                       @O3 due Oct 20││                                     │
│                               ││p5  5 8b x2 Midterm rev… @x1 due Oct 20  u=0.1  fits 8/8││                                     │
│                               ││p3  5 1b t1 Read ch.6 §1–2                         @m3 ░││                                     │
│                               ││p3  4 1b t3 Exercises 5.3–5.5                      @m1 ░││                                     │
│                               ││p3  3 1b t4 Claude Code drafts tests               @m2 ░││                                     │
│                               ││p3  3 1b t5 Review the drafts                      @m2 ░││                                     │
│                               ││                                                        ││fits this week: 1b of 1b             │
└───────────────────────────────┘└────────────────────────────────────────────────────────┘└─────────────────────────────────────┘
 h/l pane · j/k · J/K reorder (rewrites line order) · Enter drill · a add · c ci · E estimate · P priority (roots) · D demote · A…
```

`u=0.3` is the deadline pressure; `fits 6/6` is how much of it the week can
actually absorb. `W37` on a demoted line is the stamp; two stamps mean the work
has failed twice.

### Screen 3 — Necessities

Everything that is not optional: the week's fixed shape on the left, and the
things with dates and dependencies on the right.

```text
┌ Week W37 · walls & windows ───┐┌ Deadlines · waiting · necessary ──────────────────────────────────────────────────────────────┐
│   Mon Tue Wed Thu Fri Sat Sun ││──── Dated ────────────────────────────────────────────────────────────────────────────────────│
│06 ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ███ ▒▒▒ ││  d1      CS 234 pset 2                                  need 7.8b  cap 26b  u=0.3  p4  due Fri│
│07 ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ███ ▒▒▒ ││  x2      Midterm review                           need 10.4b  cap 99.7b  u=0.1  p5  due Oct 20│
│08 ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ███ ▒▒▒ ││  d2      Workshop paper draft                     need 13b  cap 166.3b  u=0.08  p4  due Nov 20│
│09                     ███     ││──── Waiting ──────────────────────────────────────────────────────────────────────────────────│
│10                     ███     ││? a4      Ask Prof. Lee about the reading group                                     p5  2d / 7d│
│11 ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ││──── Necessary today ──────────────────────────────────────────────────────────────────────────│
│12 ███ ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ││! a3      Pick up package                     need 20m  p0  mandatory · window closes Mon 21:00│
│13 ███ ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ││! lunch   lunch                               need 30m  p0  mandatory · window closes Mon 13:30│
│14                             ││! dinner  dinner                              need 30m  p0  mandatory · window closes Mon 19:30│
│15         ███                 ││! workout workout                              need 1b  p0  mandatory · window closes Mon 19:00│
│16 ▒▒▒     ███     ▒▒▒         ││! laundry laundry                   need 30m  p0  overdue · mandatory · window closes Sun 21:00│
│17 ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ▒▒▒ ││                                                                                               │
└───────────────────────────────┘└───────────────────────────────────────────────────────────────────────────────────────────────┘
 ↑/↓ move · E estimate · e edit · t event arrived · k skip instance · 1-5 screens
```

On the left, one cell per hour per day: `▒▒▒` is a routine's *window* — when it
could happen, not when it will; `███` is a wall; red `▚▚▚` is two walls
overlapping, which is a conflict to resolve. On the right, three lists, and
every item is in exactly one: **Dated** (worst pressure first — `need` is the
remaining estimate with the safety factor, `cap` is what is available before the
deadline, `u` is their ratio), **Waiting** (days waited against the timeout), and
**Necessary today** (mandatory instances, with the hour their window shuts).

### Screen 4 — Review

The same text `tm review` prints, for the day, the week or the month; `h`/`l`
switch period. **Note that `w` ("write to the file") and `c` ("ask Claude Code
for prose") do not act** — they print the command into the hint line for you to
run yourself.

### Screen 5 — Inbox

A capture box that parses as you type, over the untriaged lines of `inbox.md`:

```text
 Inbox (4)   i capture · t triage line · C Claude Code triages all · x drop
     1  pset2 fri 6b ci4 max 2b/d
     2  ask Kun about the dinner place
     3  renew the bike insurance before October
     4  read the Lean 4 metaprogramming book
```

Press `t` (or `Enter`) on a line to load it into the capture box, or `i` to start
an empty one:

```text
┌ Capture ──────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│> pset2 fri 6b ci4 max 2b/d_                                                                                       │
│  parsed  - [ ] 4 6b pset2 due:2026-09-11T23:59 max:2b/d  → week/2026-W37.md #Milestones                           │
│  Enter save · Tab change file · Esc cancel                                                                        │
└───────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
```

Line 2 is the live preview — the exact line `tm add` would write and the file it
would go to — colour-coded green, yellow (a warning) or red (refused). `Tab`
cycles the destination: week `#Milestones` → week `#Tasks` → `backlog.md` →
today's `#Pinned` → `inbox.md`. `Enter` saves it and removes the inbox line it
came from.

> **The capture line never sees `1`–`5`, `?`, `:`, `q` or `R`.** The global keys
> take them first. Typing `pset2 fri 6b ci4 max 2b/d` jumps to the Review screen
> at the `4` and to the Queue screen at the `2`, and typing `q` **quits the TUI
> and throws the line away**. The buffer survives an accidental screen switch
> (press `5` to get back to it); it does not survive `q`. Safer routes: press `t`
> on a line already in `inbox.md` (it loads the whole text at once), use the `:`
> command line, or write the line in your editor.

### Keys

Resolution order, which is what causes the surprises: `Ctrl-C` always quits; then
an open input line takes every key; then an open prompt takes every key; then the
five reserved keys below, which no screen may take; then that screen's own row;
then the shared row below, for anything the screen did not want.

**Reserved — no screen can take these**

| key | does |
|---|---|
| `1` `2` `3` `4` `5` | Today · Queue · Necessities · Review · Inbox |
| `?` | the help overlay |
| `:` | command line — any `tm` verb with its flags, quoting supported |
| `q`, `Ctrl-C` | quit |
| `R` | sync the calendar, then replan |

**Shared — offered to the screen first**

| key | does |
|---|---|
| `e` | open the selected line in `[tui] editor` |
| `j`/`↓`, `k`/`↑` | move the selection |
| `Enter` | drill into the selection |
| `Esc` | leave the current mode |
| `r` | replan (on Today, resume first if an interruption is open) |

That second table is the reason `k` does not always move the selection: on
Necessities the screen claims `k` for "skip this instance", and the shared row
never sees it. Today's own keys and the shared row do not overlap, so on Today
the order between them never shows.

**Today only**

| key | does | runs |
|---|---|---|
| `d` | finish the running block | `tm done` |
| `x` | extend by one block | `tm extend` |
| `s` | stop; the remainder re-competes | `tm stop` |
| `b` then `w`/`s`/`b`/`p` | break: walk / seat / bed / phone | `tm break --where …` |
| `i` | an interruption began | `tm interrupt` |
| `0` then `0`–`5` | report your energy now | `tm energy N` |
| `l` | set your location | — |
| `K` | skip today's instance of the selected routine | `tm skip` |
| `n` | write a note into `## Log` | — |
| `Space` | pause / unpause the timer | `tm pause` |

Energy is `0` **then** a digit, because `1`–`5` alone are the screens. And note
the capital in `K`: **lowercase `k` moves the selection up, `K` skips a
routine.** The `?` overlay inside the TUI is the authority on this — an early
design note for the tool said `k` for skip, and the code went the other way.

None of the Today action keys work on screens 2–5. Some mean something else
there:

| key | Today | Queue | Necessities | Inbox list |
|---|---|---|---|---|
| `x` | extend | drop item | — | delete inbox line |
| `k` | move up | move up | **skip instance** | move up |
| `K` | skip routine | move line up | — | — |
| `l` | location | pane right | — | — |
| `t` | — | — | event arrived | triage the line |
| `a` | — | add | — | start capture |

Use `1` to get back to Today, or `:done`, `:break --where walk` and so on from
anywhere. The `:` line takes any verb with its flags, quoting included:
`:add "- [ ] 2 30m Call the bank" --to backlog.md`.

`?` shows the whole map at any time:

```text
┌ Keys — tm-spec §12.6 ───────────────────────────────────────────────────────────┐
│  1–5          screens: Today · Queue · Necessities · Review · Inbox             │
│  ?            this help  ·  :  command line (any tm verb)  ·  q  quit           │
│  e / Enter    open the selected line in the editor / drill into it              │
│  r / R        replan (resume, when interrupted) · sync calendar + replan        │
│  j / k        move the selection  ·  mouse: hover the day bar, click to select  │
│  d / x / s    done · extend one block · stop, the remainder re-competes         │
│  b + w/s/b/p  break: walk · seat · bed · phone                                  │
│  i / r        interruption starts / ends                                        │
│  0 then 0–5   report energy now (1–5 alone switch screens)                      │
│  l / K / n    location · skip the selected routine · note                       │
│  Space        pause or unpause the timer                                        │
│                                                                                 │
│  overtime     x extend · s stop · d done · anything else: ask again             │
│  idle         w work · b break · t routine · i interruption · l leak            │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### The two prompts

Both swallow every key while they are up, and neither is raised while an input
line is open.

**Overtime** fires when the minutes you have actually worked on a running block
(pauses, breaks and interruptions excluded) reach its planned minutes:

```text
┌ Overtime ──────────────────────────────────────────────┐
│Finish ch.5 exercises     est 6b = 6h · elapsed 6h15m   │
│  x  extend +1 block      → drops: nothing              │
│  s  stop, demote rest    → 5m stays in the week queue  │
│  d  done                                               │
│  any other key: ask again in 15m                       │
└────────────────────────────────────────────────────────┘
```

The consequence lines are computed by replanning the day both ways, so they are
promises, not guesses.

**Idle** fires after `idle_min` (12) minutes with nothing running, or once a
break overruns — but not while a wall, a routine or sleep covers the moment:

```text
┌ Nothing is running (25m) ─────────────────────────────────────┐
│  w  work (starts next block)   b  break   t  routine          │
│  i  interruption               l  leak (log it, no judgment)  │
└───────────────────────────────────────────────────────────────┘
```

Each key attributes the gap **and** makes the transition: `w` starts the next
block, `b` starts a break, `i` opens an interruption. `t` and `l` only record.

---

## Command reference

Global flags, usable before or after the verb: `--json` (machine-readable
output, on both paths: the result on stdout when the command works, one error
object on stderr when it does not — see [Scripting](#scripting)) and
`--dir <path>`. Without `--json`, errors stay `tm: <message>` on stderr.

Exit codes: **0** ok · **1** an ordinary error · **2** only from `tm check`, and
only when there is at least one *error* · **3** a write conflict, meaning a plan
file changed under `tm` and needs reconciling by hand.

Every verb has its own `tm <verb> --help` with the exact flags.

### Starting and finishing a day

| command | what it does |
|---|---|
| `tm init [DIR] [--example] [--force]` | create a plan directory: config, files, `CLAUDE.md`, skills, hooks. The directory is `DIR`, else `--dir`, else `./plan` — `DIR` wins when you give both. `--example` fills it with a worked example. Refuses a non-empty directory without `--force`. **Not undoable** |
| `tm wake [TIME] [--slept 7h] [--onset 20m]` | record when you woke. `TIME` is zero-padded `HH:MM` |
| `tm arrive [LOC] [--at HH:MM]` | set the location, sync the calendar, compute window and budget, plan the day |
| `tm plan [--week] [--diff] [--explain ^ID] [--allow-home]` | plan today and rewrite the day file's generated block. `--week` prints the capacity grid instead; `--explain` prints one item's priority and prints no timetable |
| `tm now` | the current block and the next three segments. Read-only, always live |
| `tm review <day\|week\|month> [--date D] [--write]` | the period's numbers. `--write` stores it in the file |
| `tm close <day\|week\|month> [--date D] [--drop ^ID]` | close a period early. Normally automatic. `--drop` is for the month close only |

### Working

| command | what it does |
|---|---|
| `tm start <ID> [--energy N]` | start a block. Asks for your energy on a terminal. Accepts a routine's name as well as an id |
| `tm done [ID] [--partial] [--went 1\|2\|3]` | finish the running block, or an item retrospectively. `--went` is 1 fine, 2 hard, 3 collapsed |
| `tm extend [BY]` | extend the running block; default one block. Rewrites the item's `est:` |
| `tm stop` | stop the running block; the remainder goes back in the pool |
| `tm pause` | pause / unpause the running timer (a toggle) |
| `tm break [DUR] [--where walk\|seat\|bed\|phone]` | start a break; **run it again to end it** |
| `tm interrupt` / `tm resume` | an interruption began / ended. `resume` replans |
| `tm energy <0-5> [--at HH:MM]` | report energy now; replans the rest of the day |
| `tm idle <w\|b\|t\|i\|l> [--min N]` | attribute a gap: work, break, routine, interruption, leak |
| `tm skip <NAME>` | skip today's instance of a routine |
| `tm routine done <NAME> [--min N]` | mark today's routine instance done |
| `tm event <NAME> [ID]` | record a named event; resolves `on-event:` and `after:event:` |

### Changing the tree

| command | what it does |
|---|---|
| `tm add <LINE> [--to WHERE] [--section S]` | add a line. `--to` takes `inbox` (default), `backlog` (alias `none`), `week`, `month`, `day`, `routines`, `optional`, `calendar`, or a path like `week/2026-W37.md`. A line put in `calendar` must be an `at:` interval or `tm check` will fail |
| `tm edit <ID> [K=V…] [--set K=V] [--unset KEY]` | edit fields byte-faithfully. `ci=`, `est=`, `due=`, `title=`, `p=`, or any `key=value` |
| `tm move <ID> <TO> [--section S]` | move an item to another horizon file |
| `tm rank <ID> <N>` | move an item to position N of its section |
| `tm demote <ID>` | demote a week item into the month's `# Demoted` |
| `tm readopt <ID> [--to WHERE]` | bring a demoted item back, into this week by default |
| `tm drop <ID>` | mark an item `[~]` |
| `tm sync-cal` | pull the ICS feeds into `calendar/` — last week, this week and next week, and nothing further out |
| `tm undo` | undo the last state change. A real stack, 50 deep |

### Looking and checking

| command | what it does |
|---|---|
| `tm check [--fix-ids]` | validate the tree. Exits 2 when there are errors; `--fix-ids` writes an `^id` onto every line that lacks one (**not undoable**) |
| `tm triage` | show every `inbox.md` line and what the grammar would make of it |
| `tm log [--tail N] [--since 7d] [--item ^ID]` | read the log. `tm add` shows up here as an `edit`, so `--item` gives an item's whole life |
| `tm model [--show] [--fit] [--compare]` | the learned model. `--fit` refits from the log (**not undoable**) |
| `tm tui` | the terminal UI |

### What is undoable

`tm undo` restores the files a verb touched and appends a compensating entry to
the log — it never erases history.

```console
$ tm undo
undid drop (drop ^a1) · 1 file(s) restored · 49 left
```

`49 left` is how deep the stack still goes; it keeps the last 50 commands. When
it runs out:

```console
$ tm undo
tm: nothing to undo
```

Almost every mutating verb is undoable. The exceptions, worth knowing before you
need them: **`tm plan`, `tm model --fit`, `tm check --fix-ids` and `tm init` are
not.**

---

## Claude Code integration

`tm init` writes a Claude Code project into the plan directory: a `CLAUDE.md`
with the rules, eight skills, a validating hook, and a git pre-commit hook. The
division of labour is that **Claude writes lines; you and `tm` decide and
record**.

Because `.claude/` lives inside the plan directory, start Claude Code with the
plan directory as its project — if your plan is a subfolder of a larger repo and
you run `claude` from the repo root, these settings are not the ones in play.

### The rules, verbatim

```markdown
# tm — rules for Claude Code
Files: month/ week/ day/ backlog.md routines.md optional.md calendar/ inbox.md. Horizon = file. Rank = line order.
Grammar: `- [ ] <ci 0-5> <est> Title @parent #tag key:value ^id`. Fields: due at win dur pref every after-done on-event on-miss min max after loc est. Flags: open atomic manual travel-day hot.
Always: add items with `tm add "..."` (or write the grammar exactly, then run `tm check`). Read `tm plan --json` before reasoning about today. Use `tm model --show` multipliers when estimating.
Never: edit between `<!-- tm:plan start/end -->`; edit `## Log`; mark blocks done; change an existing item's ci, est, or priority unless asked; reorder `month/` outcomes without confirmation; touch `.tm/`.
Demote, never delete. Explain the diff after `tm plan --diff`.
```

Claude may add items, write prose into `## Notes`, and propose milestones,
outcomes and cuts. Claude may never mark a block done, edit the generated
timetable or the log, silently change your estimates or priorities, or touch
`.tm/` — that last one is enforced twice, by the rule and by a `deny` rule in
`.claude/settings.json`.

### The skills

Each is invoked as `/<name>` in a Claude Code session. All of them read with
`--json` first, propose second, and write only what they are allowed to.

| skill | when | what it writes |
|---|---|---|
| `/capture <text>` | one sentence you want remembered — *"pset 2 is due Friday night, six blocks, two a day max"* | one `tm add` |
| `/triage` | `inbox.md` has lines waiting | one `tm add` per line, then removes the raw line; leaves anything ambiguous and says what it needs |
| `/replan` | after an interruption, a late start, a new meeting | nothing — two sentences on what moved and why |
| `/explain ^id` | *"why isn't this scheduled today?"* | nothing — it translates the priority arithmetic and says what you could change |
| `/review-day` | end of a day | 4–6 sentences into the day file's `## Notes`, and one thing to change tomorrow |
| `/review-week` | end of a week, before planning the next | two paragraphs into the week's `## Notes`, plus a cut list for anything demoted twice |
| `/plan-week` | Sunday planning | proposes 3–5 milestones with calibrated estimates and an honesty ratio; writes only after you confirm |
| `/plan-month` | a new month | proposes 3–5 outcomes with explicit `!1`–`!4` and a cut list; writes only after you confirm |

### The hooks

`.claude/hooks/tm-check.sh` runs after every file edit Claude makes. If the file
is inside the plan tree and `tm check` finds problems, it exits 2 with the
diagnostics on stderr, which blocks the turn and hands the errors back to Claude
to fix. Edits elsewhere in your repo, and edits under `.tm/`, cost nothing.

The git hook is the same check before every commit. `tm init` does not touch
your git config; it prints the one line for you to run:

```sh
git config core.hooksPath plan/.githooks
```

Bypass a single commit with `git commit --no-verify`. Note that `core.hooksPath`
is a whole-repository setting.

**Neither hook runs when `tm` is not on your `PATH`, and they say so
differently.** The Claude Code hook exits 0 **silently** — nothing at all in the
transcript. The git pre-commit hook prints `pre-commit: tm is not on PATH —
skipping tm check` on stderr and lets the commit through. If you rely on them,
install `tm` properly rather than pointing at a path inside `target/`.

### Upgrading

```console
$ tm init plan
tm: plan is not empty — refusing to overwrite it (use --force)
$ tm init plan --force
created 12 file(s) in plan
left alone, already there (8): config.toml, .gitignore, inbox.md, backlog.md, routines.md, optional.md, month/2026-09.md, week/2026-W37.md
enable the pre-commit hook with:
  git config core.hooksPath plan/.githooks
```

`--force` rewrites the generated integration — `CLAUDE.md`, the skills, the
settings, the hooks — and leaves your config and every content file untouched.

### Committing your plan

The `.gitignore` that `tm init` writes ignores the per-machine files
(`state.json`, `last_plan.json`, `arrival_plan.json`, `undo.json`) and
deliberately keeps `.tm/log.jsonl` and `.tm/model.json` — your observations and
what has been learned from them are worth having in history.

---

## Configuration

`config.toml` must exist — `tm` recognises a plan directory by this file sitting
next to `.tm/` or the plan files — but it may be empty; anything you leave out
takes its default. An **unknown or misplaced key is a hard error** that blocks
every command, so watch which section you put a key in:

```console
$ tm now
tm: invalid config plan/config.toml: TOML parse error at line 3, column 1
  |
3 | block_min = 60
  | ^^^^^^^^^
unknown field `block_min`, expected one of `palette`, `min_width`, `editor`
```

That was `block_min` put under `[tui]` instead of `[day]`; the "expected one of"
list tells you which section `tm` was reading when it tripped.

This is the file `tm init` writes, complete:

```toml
tz = "America/Chicago"

[day]
block_min             = 60
break_after_blocks    = 2
break_min             = 20
window_hours          = 8
window_cap            = "19:00"
budget_ratio          = 0.75
wind_down             = "21:30"
bed                   = "22:00"
overtime_reprompt_min = 15
idle_min              = 12
min_last_block_min    = 30

[week]
plan_ratio = 0.8                 # warn if planned > 0.8 × budget

[priority]
default_priority = 3             # k for roots without !k and for untied items
bins             = [0.5, 0.25, 0.1]
safety           = 1.3
hysteresis       = true
batch_max_min    = 20

[location]
home_max_ci = 3

[energy]
prior_weight          = 5
decay_days            = 30
duration_prior_weight = 5
posterior_full_hours  = 3
posterior_zero_hours  = 6
[energy.prior.lounge]            # by hours since wake
"0-1" = 4
"1-5" = 5
"5-8" = 4
"8-10" = 3
"10+" = 2
[energy.prior.home]
"0-1" = 3
"1-4" = 4
"4-8" = 3
"8+" = 2
[energy.sleep_debt]
under_hours = 7.0
shift       = 1

[expected]                       # used by the lookahead until learned
arrival = { Mon = "07:00", Tue = "07:00", Wed = "07:00", Thu = "07:00", Fri = "07:00", Sat = "10:00", Sun = "10:00" }
p_lounge = { Mon = 0.9, Tue = 0.9, Wed = 0.9, Thu = 0.9, Fri = 0.8, Sat = 0.5, Sun = 0.4 }

[calendar]
ics_urls       = []              # e.g. ["https://calendar.google.com/calendar/ical/<id>/private-<key>/basic.ics"]
sync_on_arrive = true
flight_regex   = "\\b[A-Z]{2} ?\\d{2,4}\\b"

[tui]
palette   = ["#e6194b","#3cb44b","#4363d8","#f58231","#911eb4","#42d4f4","#f032e6","#bfef45","#fabed4","#469990","#dcbeff","#9A6324"]
min_width = 110
editor    = "code -g {file}:{line}"
```

**`tz`** is the one key almost everyone must change. It is an IANA zone name and
it is validated. Every instant `tm` reasons about is in this zone, so daylight
saving comes out right.

| section | key | what it does |
|---|---|---|
| `[day]` | `block_min` | minutes in one block, and the slot length. Changing it changes what every `Nb` on every line is worth |
| | `break_after_blocks`, `break_min` | how often and how long you rest |
| | `window_hours`, `window_cap` | how long the working window runs from arrival, and the latest it may end |
| | `budget_ratio` | `budget = floor(window_hours × 60 / block_min × budget_ratio)`. Drop it to 0.6 if the plan is always too ambitious |
| | `wind_down`, `bed` | no work block is planned after `wind_down`; sleep starts at `bed` |
| | `overtime_reprompt_min`, `idle_min` | how the TUI's two prompts behave. `idle_min` is also the leak threshold in reviews |
| | `min_last_block_min` | the shortest block worth cutting at the end of a free stretch |
| `[week]` | `plan_ratio` | the weekly review warns when planned time exceeds this share of the budget |
| `[priority]` | `default_priority` | the `k` used when no root says `!k` |
| | `bins` | the utilization bin edges, descending |
| | `safety` | the cushion on every remaining estimate. Raise it to 1.5 if you routinely underestimate |
| | `hysteresis` | when true, an item's `p` may improve by at most one step a day, whatever put it there. Worsening is unlimited; a jump to `p = 0` is never held back; `optional.md` is exempt |
| | `batch_max_min` | small items of equal ci below this are swept into one block |
| `[location]` | `home_max_ci` | the highest slot energy allowed while you are at `home`. It applies to that one location name only — another name that *borrows* the `home` energy curve is not capped |
| `[energy]` | `prior_weight`, `decay_days` | how much the prior is worth, and how fast old observations fade |
| | `duration_prior_weight` | the same shrinkage, for the estimate-vs-actual multipliers |
| | `posterior_full_hours`, `posterior_zero_hours` | how long a reported energy keeps correcting the day |
| | `[energy.sleep_debt]` | a night shorter than `under_hours` drops the whole curve by `shift` |
| | `[energy.prior.<loc>]` | one step function per location, keyed by hours since wake (`"0-1"`, `"10+"`). Add curves for your own location names; a location with no curve of its own uses the `home` curve |
| `[expected]` | `arrival`, `p_lounge` | what the week lookahead assumes about future days until it has learned. All seven weekday keys are required, spelled `Mon`…`Sun` |
| `[calendar]` | `ics_urls` | your private ICS addresses — the "secret address in iCal format" your calendar offers. **Empty by default, so nothing is ever fetched until you add one** |
| | `sync_on_arrive` | pull the calendar during `tm arrive` |
| | `flight_regex` | an event matching this gets `buffer:2h travel-day` |
| `[tui]` | `palette` | the project hues on the day bar |
| | `min_width` | the column count below which panes stack |
| | `editor` | what the `e` key runs; `{file}` and `{line}` are substituted, e.g. `"nvim +{line} {file}"` |

### Hooking up your calendar

Paste your calendar's private ICS address into `ics_urls`. Then `tm sync-cal`
writes **last week, this week and next week** into `calendar/`, and `tm arrive`
does it for you as long as `sync_on_arrive` is true. Nothing further out is ever
fetched, so an appointment three weeks away has no `calendar/` file and will not
appear until that week comes round — if you need it in the plan now, write it by
hand with the `manual` flag. With nothing configured you get a warning rather
than an error:

```console
$ tm sync-cal
0 events · 0 files written
! no calendar feeds configured (config.toml [calendar] ics_urls)
```

Synced events become **walls**: they sit at a fixed time, nothing is scheduled
inside them, and their minutes stretch the end of your working window. Every
line in a calendar file must be an interval, and anything you write there by
hand needs the `manual` flag to survive the next sync.

---

## Troubleshooting and surprises

### "It didn't schedule my item"

Run `tm plan --explain ^id` first. Then work down this list:

1. **It has no estimate.** No leading estimate, no `est:`, no `dur:`, no children
   with estimates. It will never be scheduled and `tm check` will not tell you.
2. **Its ci is higher than any slot you will have today** — especially at home,
   where slot energy is capped at 3, and on a day with no `tm arrive` at all,
   which uses the `home` curve and so never reaches energy 5.
3. **Its `loc:` does not match where you are.**
4. **A `max:` cap for the period is spent.**
5. **It lives in `month/`,** or in a day file outside `# Pinned`, or it is a
   non-head series member. None of those are candidates.
6. **An `after:` dependency is unmet** — the plan says `t5 blocked by t4`.
7. **It simply did not fit.** It is in the `dropped:` line. Budget is six blocks.
8. **Its parent took the slots.** A milestone with an estimate — or with children
   whose estimates roll up into it — competes as a block in its own right, and
   usually wins, because it sits higher in the file. Move the task above it —
   but `tm rank` only reorders inside one heading, so if the milestone is under
   `# Milestones` and the task under `# Tasks`, first
   `tm move ^id week --section Milestones` (or move the line in your editor),
   then rank it. Or stop giving the milestone work of its own.
9. **You pinned it and expected that to be enough.** `# Pinned` makes an item a
   candidate; it does not change its priority.
10. **A typo in the id.** `tm plan --explain ^typo` answers
    `^typo is not a candidate today` and exits 0, which looks like an answer.
11. **A `hot` that is not a flag.** If `--explain` shows an ordinary `p` on an
    item you flagged `hot`, the word is sitting in the title. Move it to the end
    of the line, after the `^id`.

### "The day file shows the wrong plan"

`start`, `done`, `stop` and `extend` append to `## Log` but do **not** rewrite
the timetable in the day file. Only `plan`, `arrive`, `energy` and `resume` do.
So the file can show the morning's plan all afternoon. `tm now` is always
computed live; re-run `tm plan` to refresh the file.

### "The numbers don't agree"

- `tm now` prints raw wall-clock elapsed (`159m of 120m`); `tm done` subtracts
  pauses, breaks and interruptions (`152m/150m`). Both are right about different
  things.
- A `--partial` done leaves **no `✓` and no actual** in the timeline, because a
  past row is only marked finished when the *item* was closed that day. The
  minutes are in the log and in the reviews.
- `tm routine done <name>` without `--min` records the completion but produces a
  zero-length segment, so the routine vanishes from the timeline. Pass `--min`.
- `tm review month` can show progress over 100% — every block on a descendant
  rolls up against a fixed original estimate.

### Input formats

- **Durations need a unit**: `30m`, `1h`, `1h30m`, `1b`, `8h10m`. A bare `90` is
  `tm: invalid duration: "90"`. The exception is `--min`, which is a bare number
  of minutes.
- **Times must be zero-padded**: `06:05`, not `6:05`.
- **`Nd` is not a valid estimate** in the leading slot, in `est:` or in `dur:`
  (it is fine in `buffer:`, `after-done:`, `min:`/`max:` and `pref:wake+…`).
- **No spaces after commas** in `after:`, `every:` or `demoted:` lists.
- **Ids only** — `tm start "Read ch.6"` does not work; `tm start ^t1` and
  `tm start t1` do. Routine names work for `start`, `skip` and `routine done`.

### Commands that succeed when you expected an error

| you ran | what happened |
|---|---|
| `tm rank ^id 99` | clamped silently, and still prints `^id → position 99` |
| `tm plan --explain ^typo` | `^typo is not a candidate today`, exit 0 |
| `tm event <name>` matching nothing | `event <name> logged`, exit 0 |
| `tm drop` on an already-dropped item | exit 0 |
| `tm sync-cal` with no feeds | a `!` warning, exit 0 |
| `tm interrupt` with nothing running | exit 0; `stop`, `extend` and `pause` all fail |
| `tm done ^other` while a block runs | retro-dones `^other` and **leaves your block running** |
| `tm break` while a break runs | ends the break and ignores the arguments |
| `tm start` on an item already `[x]` | starts it |

### Where things land

- **`--to week`, `--to month` and `--to day` mean the period containing *now*.**
  Planning next week on Sunday evening silently writes into *this* week's file.
  Pass a path instead: `--to week/2026-W37.md`.
- **`tm add` with no `--section` appends to the end of the file**, i.e. under its
  last heading — which on a day file is `## Notes`, not `# Pinned`, and on a month
  file can be `# Demoted`. Always pass `--section` when it matters.
- **`tm init` names its month and week files from the real system clock.**

### Closing

- Closing is automatic and silent, on the first command after a period ends.
- **`tm close day` puts an empty `<!-- tm:review -->` block at the end of the day
  file, holding the text `review pending`** until `tm review day --write` fills
  it in. It never overwrites a review that is already there, so the two can run
  in either order.
- **`tm close <period>` with no `--date` closes the period the auto-close just
  ran — but only when that happened in this very command.** If some earlier
  command already triggered it, `tm close month` means "close the month I am in
  now", and closes it early. After the month has rolled over, name the month you
  mean: `tm close month --date 2026-09 --drop ^id`.
- **A catch-up sweep closes at most 16 periods of each kind.** Older ones are
  stamped closed without being run. Sixteen days is a fortnight and a bit, so a
  normal holiday is fine — but a tree left untouched for months can have its
  earliest days stamped closed without their pinned items ever being carried into
  a week. If you are coming back after a long absence, look at the old `day/` and
  `week/` files before you trust the sweep.

### Validation

```console
$ tm check
backlog.md:7: error[dup-id]: duplicate id ^m2; also at week/2026-W37.md:9
month/2026-09.md:8: warning[outcome-with-est]: outcome with an estimate (0.5b) and no children — did you mean a milestone in `week/`?
week/2026-W37.md:9: error[dup-id]: duplicate id ^m2; also at backlog.md:7
week/2026-W37.md:18: warning[priority-on-child]: priority on a non-root is ignored (§7.1); the root ^O2 sets `!1` for this branch
2 errors, 2 warnings
```

Each problem names the file, the line, whether it is an error or a warning, a
code you can look up, and what to do about it. A tree with real breakage:

```console
$ tm check
week/2026-W37.md:22: error[bad-ci]: `9` is not a ci: ci is one digit `0`..`5` (§4.1); `9 2b` stayed in the title, so the estimate was not read either
week/2026-W37.md:22: error[dangling-parent]: parent @nope does not exist
week/2026-W37.md:23: error[bad-value]: `due:not-a-date`: invalid date or date-time: "not-a-date"
week/2026-W37.md:23: warning[missing-id]: no `^id` on `Missing id`; run `tm check --fix-ids`
week/2026-W37.md:24: error[parent-cycle]: parent cycle: ^z2 -> ^z3 -> ^z2
week/2026-W37.md:26: warning[unknown-key]: unknown key `frobnicate:7`; it is preserved but ignored
4 errors, 2 warnings
```

`tm check` exits **2 only when there is at least one error**. Warnings alone
exit 0 — so a CI gate on the exit code will not catch a `missing-id`.

`tm check --fix-ids` appends an `^id` to every line that lacks one, including
plain prose bullets you never meant as items. It is not undoable.

The full set of problem codes: `dup-id`, `dangling-parent`, `parent-cycle`,
`dep-cycle`, `dangling-dep`, `bad-value`, `unknown-key`, `missing-id`,
`outcome-with-est`, `routine-shape`, `optional-shape`, `calendar-shape`,
`bad-ci`, `priority-on-child`, `series-order`, `wall-conflict`,
`unclassified-token`, `day-section`, `waiting-state`.

Eight of them are always errors: `dup-id`, `dangling-parent`, `parent-cycle`,
`dep-cycle`, `dangling-dep`, `bad-ci`, `routine-shape` and `calendar-shape`. Ten
are always warnings: everything on the list above except those eight and
`bad-value`.

**`bad-value` is the only code with both severities**, which matters if you gate
anything on the exit code. It is an **error** when a value cannot be parsed at
all (`due:not-a-date`) or a state is missing. It is a **warning** when the parser
resolved the line by rule and carried on — a duplicate key, two conflicting shape
keys, a flag word at the end of a title, an unknown file kind:

```console
$ tm check
week/2026-W37.md:2: warning[bad-value]: duplicate key `due:2026-09-12`
week/2026-W37.md:3: warning[bad-value]: conflicting shape keys (at: wins)
0 errors, 2 warnings
```

That run exits 0.

### When a file changed under tm

```console
$ tm undo
tm: conflict in week/2026-W37.md — the file changed under us
  ours:   20 lines
  theirs: 22 lines
  reconcile week/2026-W37.md in your editor, then try again
```

Exit 3. Nothing was written. Reconcile the file yourself and run the command
again — this is the price of the files being the database, and it only happens
when something edits a file underneath a command.

### Scripting

Every verb takes `--json`, and every segment in a plan carries both structured
fields and its rendered `text`, so a script never has to re-implement the layout.

Failures are JSON too. With `--json`, a command that fails prints **one JSON
object on stderr** — stdout stays empty — and exits non-zero:

```console
$ tm drop ^nope --json
{
  "ok": false,
  "kind": "not-found",
  "message": "no such item: ^nope",
  "exit_code": 1,
  "detail": {
    "id": "^nope"
  }
}
```

The four top-level fields are always there. `ok` is always `false`, so that is
the cheapest test for "is this a failure document". `kind` is a stable slug you
can branch on; `message` is the same sentence the human run prints after `tm: `;
`exit_code` is the code the process is about to exit with.

`detail` holds whatever the failure itself knows, and is `{}` when it knows
nothing extra — you never have to test whether the key exists:

| `kind` | when | `detail` |
|---|---|---|
| `not-found` | no line carries the `^id`, or a file the verb needs is missing | `id` or `path` |
| `conflict` | a write race (exit 3) | `file`, `ours`, `theirs`, and `id` for a single line |
| `invalid` | a value that does not parse (`est=zzz`, `due=…`) | `what`, `value` |
| `usage` | the command line itself does not parse | — |
| `parse` | text that cannot go into a plan file | `path`, `line` |
| `edit` | a byte-faithful line edit the grammar refused | `id`, or `word` / `flag` |
| `horizon` | the verb does not apply to that item's horizon | `id`, `horizon` |
| `io` | a file could not be read or written | `path` |
| `config`, `json`, `log`, `model`, `calendar` | `config.toml`, a `.tm/` sidecar, the log, `.tm/model.json`, a calendar feed | `path` or `url` |
| `error` | anything else ("nothing to undo", "no block running") | — |

The one non-zero exit that is *not* a failure document is `tm check`'s **2**: the
problems are the verb's result, so they stay on stdout in the usual shape with
the rest of `tm check --json`.

Without `--json` nothing changed: errors are `tm: <message>` on stderr, and a
conflict adds its `ours:` / `theirs:` lines.
