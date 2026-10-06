# OOPSLA 2016 DOT, in the reference's own definitions

Coq proofs about the DOT calculus of Rompf and Amin (OOPSLA 2016), stated in the definitions of
its Coq artifact: `oopsla16/dot.v` in `TiarkRompf/minidot` at commit `ef1143d`.  They back two
kinds of claim made by the Lean port in [`lean/Coercions/Oopsla16`](../../lean/Coercions/Oopsla16/README.md).
One is that packing in `htp` is unsound.  The other is that the port's restrictions on contexts
and stores cost what its README says they cost.  Proving these on the reference's own definitions
means they do not depend on the port's encoding.  The files build with Coq 8.19, separately from
the Rocq development in `../../rocq`.

## `packing/`

`dot_spec.v` is the reference's specification.  Its lines 25 to 410 are `dot.v` lines 14 to 399,
byte for byte.  Its lines 10 to 24 replace the reference's imports of `SfLib` and `Arith`, so that
the file builds with Coq 8.19.  `dot_packing.v` copies the four typing judgments, adds one rule
to `htp` that packs a variable into a recursive type, and changes nothing else.  `packing_unsound`
then exhibits a store and a closed program that the extended rules type at `⊤`, that is not a
value, and that cannot step.  So the progress half of the reference's `type_safety` fails once packing is added.

Build: `coqc dot_spec.v && coqc dot_packing.v` in `packing/`.

## `deviations/`

- `ctx_restriction.v`: the Lean port admits only contexts whose entry at a variable mentions that
  variable and older ones.  `restriction_harmless` shows that from such a context the reference's
  rules and the restricted rules derive the same judgments, and `restriction_harmless_empty` is the
  case of the empty context.  `ctx_restriction_is_real` shows that outside such contexts the
  reference derives judgments the restricted rules cannot.  `htp_closed_Sx` shows that every type
  `htp` gives a variable `x` mentions only `x` and older variables, which the port's typing of
  `htp` relies on.
- `store_restriction.v`: `store_restriction_is_real` shows that the reference types closed terms
  over stores the port cannot express.  In such a store a type member mentions a context variable,
  a location that does not exist, or an unbound variable.
- `regularity.v`: the reference's closedness lemmas (`all_closed` and the lemmas it needs), proved
  again in Coq 8.19 with the reference's statements.
- `check_block.sh` checks that the restricted rules in `ctx_restriction.v` are the reference's 32
  rules with one added premise each.  `check_statements.sh` checks, given a copy of `dot.v`, that
  every lemma of `regularity.v` named after a `dot.v` lemma has its statement token for token.
  `assumptions.v` prints the assumptions of every result, and each should be closed under the
  global context.
- `step_differential.py` runs the Lean step relation and the reference's side by side on random
  programs.  It is a test, not a proof.

Build: `./build.sh` in `deviations/`, which compiles `../packing/dot_spec.v` into this directory and
runs `check_block.sh`.  `COQC=/path/to/coqc ./build.sh` selects another `coqc`.
