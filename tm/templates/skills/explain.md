---
name: explain
description: Explain in plain language why one item sits where it does — its priority, its deadline pressure, its slot — from tm plan --explain. Use when the user asks "why is this so low?", "why isn't this scheduled today?", or "why did that jump to the top?".
---

# /explain `^id`

## 1. Run

```
tm plan --explain ^id --json
```

It answers in the model's own terms, e.g.
`p = k(3) + bin(u=0.31 → +1) = 4; slot 11:50 energy 4, ci 3, gap 1; deps ok;
cap 2b/d: 1b used`.

## 2. Translate it

Priority is an integer where **0 is highest**, and it is computed, never
stored:

- `k` — the priority of the item's **root**, from `!1`–`!4` on the root line
  (default 3). Nothing on the item itself changes `k`.
- `u = need / capacity` — the deadline pressure. `need` is the remaining
  estimate × the safety factor (1.3); `capacity` is the expected slot-minutes
  before the due date at an energy level the item can use, *after* earlier
  deadlines have reserved theirs. `u ≥ 1` means it does not fit: priority 0.
- `bin(u)` — 0.5/0.25/0.1 turn `u` into `+0/+1/+2/+3`, so slack costs rank.
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
