# Frontend

The vanilla front end of plan V §7, specified in `plan-5e-frontend-stages.md`: a direct-style surface
syntax embedded in Lean, name resolution and let-insertion into DOT-MNF, a derivation-producing typer,
executable machines with agreement lemmas, and the pipeline through the FCdot checker to a run.  Not part
of the metatheory.

Stage F0 has landed: `Surface.lean`, `Notation.lean`, `Ann.lean` and `Resolve.lean`.  A program is written
in the paper's notation inside `dot%`, it becomes a value of the unindexed surface syntax, and
`resolve` turns that into an annotated DOT-MNF term in monadic normal form, inserting the `let` bindings
that direct-style application and projection need.  Resolution is total on scoped, well-labelled programs
and it is structural, so its results reduce in the kernel.  The rest of the stages are still to come.
