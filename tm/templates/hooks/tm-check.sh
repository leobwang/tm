#!/bin/sh
# tm — the PostToolUse hook: validate the plan tree after an edit to it
# (tm-spec-v1.md §14, "a PostToolUse hook on Edit/Write under plan/ running
# tm check").
#
# Claude Code runs this with the tool payload on stdin. Two things it does that
# a bare `tm check` cannot:
#
#   * "under plan/" — it exits 0 without running anything when the edited file
#     is outside this plan tree (or inside `.tm/`, which is never Claude's to
#     edit), so editing the rest of the repository costs nothing and an
#     unrelated validation problem never blocks it.
#   * the diagnostics reach the model — `tm check` prints them on stdout, and
#     Claude Code feeds back only *stderr* on the blocking exit code 2, so the
#     output is re-emitted there. Without this the turn is blocked with an
#     empty message.

set -u

# The plan root is this script's grandparent: <plan>/.claude/hooks/tm-check.sh.
plan=$(CDPATH='' cd -- "$(dirname -- "$0")/../.." && pwd) || exit 0

# The edited file, from the payload's `file_path` (one key: sed, not jq).
file=$(tr -d '\n' | sed -n 's/.*"file_path"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p')
case "$file" in
	'') exit 0 ;;
	/*) ;;
	*) file="$PWD/$file" ;;
esac

case "$file" in
	"$plan"/.tm/*) exit 0 ;;
	"$plan"/*) ;;
	*) exit 0 ;;
esac

command -v tm >/dev/null 2>&1 || exit 0

out=$(tm check --dir "$plan" 2>&1) || {
	printf '%s\n' "$out" >&2
	exit 2
}
exit 0
