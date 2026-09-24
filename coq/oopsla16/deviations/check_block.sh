#!/usr/bin/env bash
# Checks that the restricted judgments in ctx_restriction.v are the reference's
# 32 rules (dot.v:219-393) with exactly one added line per rule, the premise
# `ctx_ok GH G1 ->`, and the suffix `_r` on the judgment and rule names.
#
# Usage: ./check_block.sh [path/to/dot.v]
# Without an argument the reference text is taken from
# ../packing/dot_spec.v, whose lines 25-410 are byte-identical to
# dot.v lines 14-399, so dot.v:219-393 is dot_spec.v:230-404.
set -euo pipefail
cd "$(dirname "$0")"

tmp=$(mktemp -d "${TMPDIR:-/tmp}/check_block.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

if [ $# -ge 1 ]; then
  sed -n '219,393p' "$1" > "$tmp/ref"
else
  sed -n '230,404p' ../packing/dot_spec.v > "$tmp/ref"
fi

# The block: from `Inductive has_type_r` to the end of `htp_sub_r`.
awk '/^Inductive has_type_r /{on=1} on{print} on && /^    htp_r GH G1 x T2 \(S \(n1\+n2\)\)\.$/{exit}' \
  ctx_restriction.v > "$tmp/blk"

# 1. No unrestricted judgment is mentioned inside the block.
if grep -nE '\b(has_type|dms_has_type|stp|htp)\b' "$tmp/blk"; then
  echo "FAIL: the block mentions an unrestricted judgment" >&2; exit 1
fi

# 2. Exactly 32 added premises, each directly after the line opening a rule.
n=$(grep -c '^ *ctx_ok GH G1 ->$' "$tmp/blk" || true)
[ "$n" -eq 32 ] || { echo "FAIL: $n ctx_ok premises, expected 32" >&2; exit 1; }
bad=$(awk '/^ *ctx_ok GH G1 ->$/ && prev !~ /: forall .*,$/ {print NR} {prev=$0}' "$tmp/blk")
[ -z "$bad" ] || { echo "FAIL: ctx_ok premise not first at block lines $bad" >&2; exit 1; }

# 3. Removing those lines and the `_r` suffixes gives the reference text.
grep -v '^ *ctx_ok GH G1 ->$' "$tmp/blk" \
  | perl -pe 's/\b(has_type|dms_has_type|stp|htp|T_\w+?|D_\w+?|stp_\w+?|htp_\w+?)_r\b/$1/g' \
  > "$tmp/stripped"
if diff "$tmp/ref" "$tmp/stripped"; then
  echo "OK: 32 rules identical to dot.v:219-393 except the added ctx_ok premise"
else
  echo "FAIL: the block differs from dot.v:219-393" >&2; exit 1
fi
