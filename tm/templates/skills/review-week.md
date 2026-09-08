---
name: review-week
description: Write the week review prose into the Notes section of week/<week>.md, from tm review week --json, and name the work that should be cut. Use at the end of a week, before /plan-week, or when the user asks "how did the week go?".
---

# /review-week

## 1. Run

```
tm review week --json          # add --date to review a week other than this one
tm model --show --json         # the learned multipliers and the lounge rate
tm model --compare --json      # stored model vs a fresh fit, once the log is long enough
```

Every number you write comes from these documents; the carry-over comes from
the file itself (unfinished milestones and `# Demoted` in `week/<week>.md`).
Report nothing that is not here:

<!-- json fields -->

```
tm review week --json → period key blocks block_min leak_min lost_min energy_mae energy_bias days[].date days[].blocks days[].block_min days[].load days[].done estimates[].tag estimates[].n estimates[].multiplier churn
tm model --show --json → model.duration model.p_lounge model.expected_arrival model.n_obs
tm model --compare --json → comparison.n comparison.mae_a comparison.mae_b comparison.bias_a comparison.bias_b comparison.b_is_better
```

## 2. Write into `## Notes`

Append a short section to the `## Notes` of `week/<week>.md`:

- **Milestones** — what finished (`days[].done`), and what is still open in the
  file with its remaining `est:` — that is next week's carry-over.
- **Shape of the week** — `days[].blocks` day by day, the obvious holes, and
  the lounge rate (`model.p_lounge`) behind them.
- **Calibration** — `estimates[].multiplier` per tag with its `n`;
  `energy_mae` and `energy_bias`; and, when `comparison.b_is_better`, that a
  `tm model --fit` is due.
- **Leak and rest** — `leak_min` and `lost_min` against `block_min`.

Two paragraphs at most, and every claim traceable to a field above.

## 3. Propose cuts

Name every item in `churn` (two or more `demoted:` stamps) and propose one of:
cut it (`tm drop ^id`), re-scope it (a smaller `est:` and a narrower title), or
make it the week's only milestone. A third demotion is a decision the user has
been avoiding — say so plainly, once.

Hand the result to `/plan-week`; do not write `week/<next>.md` here.

## 4. Never

Only `## Notes` is yours. Never touch `## Log`, the `<!-- tm:… -->` sections,
`.tm/`, or an item's `ci`, `est:` or `!k` without being asked.
