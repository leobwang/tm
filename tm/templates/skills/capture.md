---
name: capture
description: Turn one sentence of natural language into a tm item line and add it with tm add. Use when the user throws something at you to remember — "pset 2 is due Friday night, six blocks, two a day max" — rather than asking for a plan.
---

# /capture `<text>`

Translate the sentence into the §4.1 grammar, show the line and the file, then
add it. One sentence in, one line out — no planning conversation.

## The grammar

```
- [ ] <ci 0-5> <est> Title @parent #tag key:value ^id
```

`ci` is the minimum energy the work needs; the estimate is `Nb` (blocks of
60m), `Nm` or `Nh`. Both are optional and both come before the title.

| The sentence says | Write |
|---|---|
| "due Friday night" | `due:2026-09-11T23:59` (resolve the weekday against today) |
| "meeting at 12:50 for an hour" | `at:2026-09-07T12:50/13:50` |
| "some time this afternoon, 20 minutes" | `win:14:00-18:00 dur:20m` |
| "every weekday", "every two days" | `every:weekday`, `after-done:2d~1d` |
| "after I hear back" | `on-event:reply/7d` |
| "at most two blocks a day", "at least 6 a week" | `max:2b/d`, `min:6b/w` |
| "only once the draft is done" | `after:^t4` |
| "at the office", "can't do it at home" | `loc:out` |
| "don't split it" | `atomic` |

## Where it goes

`week/<this week>.md` for this week's work, `backlog.md` for undated or far-out
work, `routines.md` for a recurring window (no checkbox there), `optional.md`
for what may only fill rest slots. When you are not sure, put it in
`inbox.md` verbatim and say so — `/triage` will finish the job.

## Add it

```
tm add "- [ ] 4 6b pset 2 due:2026-09-11T23:59 max:2b/d" --to week/2026-W37.md --section Milestones
```

`tm add` assigns the `^id` and validates the line; then run `tm check`. Print
the line you wrote and nothing else.
