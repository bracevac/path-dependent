#!/usr/bin/env bash
# Checks that every lemma of regularity.v that bears the name of a dot.v lemma
# has the same statement, token for token (comments removed, whitespace
# normalised).  Needs the reference file:
#
#   curl -LO https://raw.githubusercontent.com/TiarkRompf/minidot/ef1143dc1875d389c47083cd324971b1b86686d1/oopsla16/dot.v
#   ./check_statements.sh dot.v
set -euo pipefail
cd "$(dirname "$0")"
[ $# -eq 1 ] || { echo "usage: $0 path/to/dot.v" >&2; exit 2; }
python3 - "$1" regularity.v <<'EOF'
import re, sys
def stmts(path):
    s = re.sub(r'\(\*.*?\*\)', '', open(path).read(), flags=re.S)
    return {m.group(2): ' '.join(m.group(3).split())
            for m in re.finditer(r'\b(Lemma|Theorem|Corollary)\s+(\w+)\s*(.*?)Proof\.', s, flags=re.S)}
ref, new = stmts(sys.argv[1]), stmts(sys.argv[2])
bad = 0
for k, v in new.items():
    if k not in ref:
        print(f'{k}: not a dot.v lemma')
    elif ref[k] == v:
        print(f'{k}: same statement as dot.v')
    else:
        bad += 1
        print(f'{k}: DIFFERENT\n  dot.v: {ref[k]}\n  here:  {v}')
sys.exit(1 if bad else 0)
EOF
