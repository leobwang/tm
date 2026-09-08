---
name: triage
description: Turn the raw lines in inbox.md into well-formed items — ci, estimate, parent, file — and add them with tm add. Use when the user says "triage the inbox", "clear my inbox", or when inbox.md has lines waiting.
---

# /triage

## 1. Read

```
tm triage --json               # every inbox line with its parse preview
tm plan --week --json          # what the week already holds, before adding to it
```

The preview shows what the grammar would make of the line as written. Your job
is the part it cannot guess.

<!-- json fields -->

```
tm triage --json → file lines[].line lines[].raw lines[].parsed lines[].problem
tm plan --week --json → week days[].date days[].total days[].minutes_at_level grid
```

## 2. Decide, per line

| Field | Question | Default |
|---|---|---|
| `ci` 0–5 | how much energy does this really need? | 3 (0 for chores, 5 for deep work) |
| estimate | `Nb` blocks, `Nm`, `Nh` — one block is 60m | ask if it could be 1b or 6b |
| `@parent` | which milestone or outcome does it serve? | none (an untied item is fine) |
| file | `week/<this week>.md` if it is this week's work; `backlog.md` if it is undated or far out; `routines.md` if it recurs on a window; `optional.md` if it must never displace work | `backlog.md` |
| dates | a deadline is `due:`, an appointment `at:`, a window `win:` + `dur:` | none |

Ask when the answer is ambiguous — a wrong `ci` or a wrong estimate quietly
distorts every plan afterwards. Never invent a deadline.

## 3. Write

One `tm add` per line — the bare line, **without** the `- [ ] ` prefix, which
would be read as a flag — then delete the raw line from `inbox.md`:

```
tm add "4 6b pset 2 @O3 due:2026-09-11T23:59 max:2b/d" --to week/2026-W37.md --section Milestones
```

`tm add` assigns the `^id`; never write one yourself. Finish with `tm check`
and a one-line summary per item (where it went and why). Lines you could not
resolve stay in `inbox.md` — say which, and what you need to know.
