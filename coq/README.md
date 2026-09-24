# Coq developments in the reference calculi's own definitions

These are separate from the project's Rocq development in `../rocq`: each one
works directly in a published artifact's Coq definitions and builds on its
own (Coq 8.19), not through the top-level `Makefile`.

| directory | contents |
|---|---|
| `oopsla16/packing` | the Rompf–Amin OOPSLA'16 specification (`dot_spec.v`) and the unsoundness of adding packing to `htp` |
| `oopsla16/deviations` | proofs about the reference behind the Lean port's restrictions, and a differential test of the step relation |
