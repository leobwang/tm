# `kernel/corpus` — where these files came from

These are tm's own test fixtures, copied verbatim off the `main` branch, where
the Rust kernel still lives. They are test **data**, not Rust code, so they
belong on `rebuild-on-lean` even though the crate that used to read them does
not.

```
git archive --format=tar main tm-core/tests/fixtures -o fixtures.tar
tar -xf fixtures.tar && cp -R tm-core/tests/fixtures/. kernel/corpus/
```

The copy was taken from `main` at `557a3d2` ("horizon: one precondition for
every write that places a line"). Nothing was edited: `git show
main:tm-core/tests/fixtures/<path>` is byte-identical to `kernel/corpus/<path>`
for every file listed below.

## What is here

Five fixture plan trees and the shared inputs the Rust suite used:

| tree | what it is for |
|---|---|
| `plan-basic/` | a clean plan: every §4.3 file kind, one demoted item, front matter, a generated `<!-- tm:plan -->` block |
| `plan-conflicts/` | the `tm check` fixture — **deliberately malformed**: a duplicate id, two ids on one line, a bad priority `!9`, an odd token `^%`, an unknown key `foo:bar`, a repeated `due:`, an out-of-range ci `7`, an item with no id, a dangling `after:^t9`, a `@ghost` parent, a two-item `after:` cycle, a two-item `@parent` cycle, a calendar entry with no time, a day-file item outside `# Pinned` |
| `plan-home-day/` | `plan-basic` with a full day file, for the planner fixtures |
| `plan-recur/` | recurrence: `every:`, `after-done:`, `on-event:`, `on-miss:` |
| `plan-travel-day/` | the travel-day capacity case (`travel-day`, `buffer:`) |
| `logs/`, `model.json`, `sample.ics` | log, statistics and ICS inputs — **not** Markdown, and not read by the round-trip harness |

37 Markdown files in total, across the five plan trees.

`plan-conflicts/` is the reason the round-trip harness reports rejections rather
than asserting that everything loads: several of its lines exist precisely so
that a loader refuses them. A refusal there is the fixture doing its job. A
refusal anywhere else is a finding.

## Files added here that are not from `main`

* `PROVENANCE.md` — this file.
* `round-trip.expected` — the measured baseline the harness ratchets against.
  Generated, not hand-written; see `kernel/tm-kernel-ffi/tests/corpus.rs`.

## What reads them

`kernel/tm-kernel-ffi/tests/corpus.rs`, wired into `kernel/check.sh` as check 6.
Every `.md` file is pushed through the kernel's `String -> String` boundary with
no commands and the bytes that come back are compared with the bytes that went
in.
