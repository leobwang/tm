---
name: review-week
description: Write the week review prose into the Notes section of week/<week>.md, from tm review week --json, and name the work that should be cut. Use at the end of a week, before /plan-week, or when the user asks "how did the week go?".
---

# /review-week

## 1. Run

```
tm review week --json          # add --date to review a week other than this one
tm model --compare             # only when the log is long enough to have a v2 fit
```

## 2. Write into `## Notes`

Append a short section to the `## Notes` of `week/<week>.md`:

- **Milestones** — hit, and demoted with their remaining estimate. Carry-over
  in blocks, week over week.
- **Shape of the week** — blocks per day, the heat grid's obvious holes,
  lounge rate and start latency (wake → arrive → first block).
- **Calibration** — estimate multipliers per tag and their trend; energy MAE
  and bias; plan honesty (planned ÷ budget, warn above 1.1).
- **Leak and rest** — leak minutes, break integrity, rest debt.

Two paragraphs at most, and every claim traceable to a number in the JSON.

## 3. Propose cuts

Name every item with two or more `demoted:` stamps and propose one of: cut it
(`tm drop ^id`), re-scope it (a smaller `est:` and a narrower title), or make
it the week's only milestone. A third demotion is a decision the user has been
avoiding — say so plainly, once.

Hand the result to `/plan-week`; do not write `week/<next>.md` here.

## 4. Never

Only `## Notes` is yours. Never touch `## Log`, the `<!-- tm:… -->` sections,
`.tm/`, or an item's `ci`, `est:` or `!k` without being asked.
