---
name: explain
description: Explain in plain language why one item sits where it does — its priority, its deadline pressure, its slot — from tm plan --explain. Use when the user asks "why is this so low?", "why isn't this scheduled today?", or "why did that jump to the top?".
---

# /explain `^id`

## 1. Run

```
tm plan --explain ^id --json
```

`explain` answers in the model's own terms, e.g.
`p = k(3) + bin(u=0.31 → +1) = 4; slot 11:50 energy 4, ci 3, gap 1; deps ok;
cap 2b/d: 1b used`, and `priorities[]` carries the same numbers per item:

<!-- json fields -->

```
tm plan --explain ^id --json → explain priorities[].id priorities[].p priorities[].class priorities[].k priorities[].u priorities[].bin priorities[].need_min priorities[].avail_min priorities[].avail_min_exact priorities[].allocation_min priorities[].allocation_min_exact priorities[].shortfall_min priorities[].shortfall_min_exact priorities[].until segments[].item segments[].energy
```

## 2. Translate it

Priority is an integer where **0 is highest**, and it is computed, never
stored:

- `k` — the priority of the item's **root**, from `!1`–`!4` on the root line
  (default 3). Nothing on the item itself changes `k`.
- `u = need / capacity` — the deadline pressure. `need_min` is the remaining
  estimate × the safety factor (1.3); `avail_min` is the expected slot-minutes
  before the due date at an energy level the item can use, *after* earlier
  deadlines have reserved theirs. `u ≥ 1` means it does not fit: priority 0.
- **Minutes are floors.** Capacity is an exact mixture of the lounge day and
  the home day, so it is rarely a whole number of minutes. `avail_min`,
  `allocation_min` and `shortfall_min` are each **the floor** of the exact
  value beside it, `avail_min_exact` etc., a fraction `{"num": "…", "den": "…"}`
  of digit strings in lowest terms. Quote the integers, but reason from the
  exact values: `need_min − allocation_min` can exceed `shortfall_min` by one.
- `bin` — 0.5/0.25/0.1 turn `u` into `+0/+1/+2/+3`, so slack costs rank.
- Ties break by line order: the rank the user set by cut-and-paste.

Then say why it landed where it did in the day: the slot's predicted energy
versus the item's `ci` (a block is only offered when `ci ≤ slot`), a `max:` cap
already spent, an unsatisfied `after:`, a `loc:` mismatch, or simply that the
budget ran out before its turn.

## 3. Say what would change it

Concretely, in the user's hands: a smaller `est:`, a later `due:`, a different
`!k` on the root, moving the line up in its section, splitting an `atomic`
item, or accepting that something else has to go. Never make the change
yourself.
