---
name: plan-month
description: Plan the coming month — propose outcomes with an explicit priority and a cut list for repeatedly demoted work, then write month/<next>.md after confirmation. Use when the user says "plan the month", "new month", or asks what this month is for.
---

# /plan-month

## 1. Read

```
tm review month --json         # outcomes hit, demotion churn, carry-over blocks
tm review week --json          # the last week, for the trend
```

Plus `month/<last month>.md`: the outcomes and everything under `# Demoted`.

## 2. Propose

- **Outcomes, not tasks.** Three to five lines, each a statement of a finished
  state ("Lean: through ch.8 of the tutorial"), each with an explicit priority
  `!1`–`!4` — only roots carry one, and `k` is what every descendant inherits.
  An outcome with an estimate and no children is a `tm check` warning: outcomes
  are outcomes, milestones live in `week/`.
- **A cut list.** Anything carrying two or more `demoted:` stamps (§11's
  demotion churn) is a candidate to cut or re-scope. Say what each cut costs
  and what it buys: the month has a fixed number of blocks, and last month's
  carry-over is already spent.
- **Capacity.** Compare the carry-over blocks from `tm review month --json`
  with a month of budget before proposing anything new.

## 3. Write — only after confirmation

Never create or edit `month/<next>.md` before the user says yes. Then:

```
tm close month --drop ^id …    # carries the rest forward; --drop for each cut
tm add "- [ ] 5 !1 Lean: through ch.9" --to month/<next month>.md --section Outcomes
tm check
```

`tm close month` moves unfinished outcomes and the `# Demoted` block into the
new file with their stamps intact — run it before adding new outcomes so the
carry-over is visible in the same file. Demote, never delete.
