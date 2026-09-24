#!/usr/bin/env bash
# Builds this directory with Coq 8.19 and runs the rule-block check.
#
# Usage: ./build.sh          (uses `coqc` from PATH)
#        COQC=/path/to/coqc ./build.sh
#        ./build.sh clean
#
# dot_spec.v is not copied here: it is compiled from ../oopsla16-packing with
# its output written into this directory (`-o`), so nothing is written to
# ../oopsla16-packing.
set -euo pipefail
cd "$(dirname "$0")"
COQC=${COQC:-coqc}

if [ "${1:-}" = clean ]; then
  rm -f ./*.vo ./*.vos ./*.vok ./*.glob ./.*.aux .lia.cache
  exit 0
fi

"$COQC" -Q . "" -o dot_spec.vo ../oopsla16-packing/dot_spec.v
for f in regularity ctx_restriction store_restriction assumptions; do
  "$COQC" -Q . "" "$f.v"
done
./check_block.sh
