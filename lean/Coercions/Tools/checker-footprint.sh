#!/bin/sh
set -eu

# Reproducible physical footprint of the executable ManySortedFC checker.
#
# The list is deliberately explicit.  It includes the independently invoked
# evidence, term, theory-model, theory-map, theory-morphism, adapter, and modal
# theory-map checker modules.  It excludes separate syntax, example, and
# checker-completeness modules.  Adapter and modal-map syntax is co-located
# with validation and is therefore counted.  The result is a selected
# checker-bearing module footprint, not a dependency closure, a claim about
# Lean's trusted kernel, or a minimized TCB.

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
coercions_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)

files='ManySortedFC/EvidenceChecker.lean
ManySortedFC/TermChecker.lean
ManySortedFC/TheoryModelChecker.lean
ManySortedFC/TheoryMapChecker.lean
ManySortedFC/TheoryMorphismChecker.lean
ManySortedFC/Adapter.lean
ManySortedFC/ModalTheoryMap.lean'

total_lines=0
total_bytes=0

printf '%-52s %10s %10s\n' module lines bytes
printf '%-52s %10s %10s\n' ---------------------------------------------------- ---------- ----------

for relative in $files; do
  path="$coercions_dir/$relative"
  lines=$(wc -l < "$path" | tr -d ' ')
  bytes=$(wc -c < "$path" | tr -d ' ')
  total_lines=$((total_lines + lines))
  total_bytes=$((total_bytes + bytes))
  printf '%-52s %10s %10s\n' "$relative" "$lines" "$bytes"
done

printf '%-52s %10s %10s\n' ---------------------------------------------------- ---------- ----------
printf '%-52s %10s %10s\n' total "$total_lines" "$total_bytes"
