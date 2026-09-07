---
name: replan
description: Replan the rest of the day and explain in two sentences what moved and why. Use after an interruption, a late start, a new meeting, an energy report or an estimate change — whenever the user asks "what does the day look like now?".
---

# /replan

## 1. Run

```
tm plan --diff --json          # replans from now and diffs against the last plan
```

Nothing else is needed. `tm plan` writes the generated section of
`day/<today>.md` and the day bar itself — you never write a timeline.

## 2. Say two sentences

The first names what moved: which item is running now, what starts next, and
what fell off the tail (`diagnostics.dropped_tail` — assignment is a
rank-ordered fill, so a loss of time always drops a *suffix* of the queue;
those items are untouched in their files).

The second names the cause, from the diagnostics: lost minutes from an
interruption, a new wall from `calendar/`, a lower energy prediction that made
a `ci`-5 item ineligible (`deferred`), a `max:` cap that is spent for today, or
a dependency that is still blocked.

## 3. Flag, do not fix

Report but never silently repair:

- `impossible` — the item, its shortfall ("needs 8b, 5b available by Fri"), and
  the two exits: a smaller `est:` or a later `due:`.
- `hot` — `u ≥ 1`, so it takes the next eligible slot.
- `underused` — slots with energy ≥ 2 above the item's `ci`.
- `a_capacity_lost` — a high-energy slot went to Rest while `ci`-5 work waited.

## Never

Do not edit anything between `<!-- tm:plan start -->` and `<!-- tm:plan end -->`,
do not mark blocks done, and do not change anyone's `est:`, `ci` or `due:` to
make the plan fit. Ask instead: `tm edit ^id est=1b` is the user's call.
