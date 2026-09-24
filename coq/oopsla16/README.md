# Coq, in the reference's own definitions

Proofs about the Rompf–Amin OOPSLA'16 calculus, stated in its Coq artifact's
definitions (`TiarkRompf/minidot` at `ef1143d`, `oopsla16/dot.v`). They build
with Coq 8.19, separately from the project's Rocq development in `../../rocq`.

* `packing/`: `dot_spec.v` is the reference's specification (its lines
  25–410 are `dot.v:14-399` byte for byte; lines 10–24 replace old imports).
  `dot_packing.v` adds packing to `htp` and derives a well-typed stuck program.
  Build: `coqc dot_spec.v && coqc dot_packing.v`.
* `deviations/`: the facts behind the Lean port's restrictions.
  `restriction_harmless` shows contexts whose entries mention only themselves
  and older variables lose no judgment; `htp_closed_Sx` shows every type
  `htp` assigns to `x` is closed at `S x`; `store_restriction_is_real` shows
  the reference types terms over stores the port cannot express.
  `step_differential.py` tests the Lean step relation against the
  reference's. Build: `./build.sh`.
