# Coercions

Lean formalizations of type-preserving translations from DOT fragments into
explicit-coercion calculi.

## Current development (Plan III, `plan-3-dot-mnf-to-fcdot.md`)

- `DotMNF` — the source: WadlerFest DOT in monadic normal form, with object
  literals that carry type members *and* term members, recursive self
  types, intersections of declarations, and bad bounds admitted.  Its
  machine erases step by step into the shared runtime (`erase_step`,
  `erase_reflect`).  It has no metatheory of its own; safety is transported
  from the target.
- `FCdot` — the target: an explicit-evidence coercion calculus whose
  evidence erases to nothing.  Checker with completeness, preservation,
  progress, both erasure simulations, canonical forms over inert stores,
  consistency of typed stores.  See `FCdot/README.md`.
- `DotToFCdot` — the bridge: the translation of derivations, typedness,
  erasure equality `⌊h.translate⌋ = ⌊t⌋`, coherence, `dot_safety`, and the
  consistency corollaries for translated programs.  See
  `DotToFCdot/README.md`.
- `Runtime` — the shared untyped runtime both calculi erase into: variables,
  lambdas, objects **with their term members**, application, projection,
  `let`.  For example E2 (`FCdot/Examples.lean`, `DotMNF/Examples.lean`),
  `let x = ν(x. {A = ∀(y : x.A) x.A} ∧ {a = λ(y : x.A). y}) in let f = x.a in f f`,
  erases on both sides to
  `let x = ν(x. {a = λy. y}) in let f = x.a in f f`, and the two erasures
  are equal by `rfl`.

Restrictions of the source relative to WadlerFest DOT, all stated in the
typing rules (`DotMNF/Typing.lean`) and in the plan's §13: intersections
and recursive-type bodies are declaration-shaped; type-member definitions
and field declarations inside a literal are not bare selections on the
literal's own self (`Defs.Guarded`, `Ty.Guarded`; the plan's §12 risk 2).
The last restriction is slated for removal by making the target's
resolution follow aliases within a block.

## Legacy (before this branch)

Kept for their theorems; not part of the current line.

- `FCsub` — System F-sub with explicit coercions, telescope-constrained
  quantifiers, head-guarded recursive projections; `progress`,
  `preservation`, a total checker with `checkTerm_iff`.
- `DOT/Acyclic` — the acyclic, variable-path, one-type-member-per-object
  DOT source and its explicitly coerced Stage A form.
- `Translation/Acyclic`, `Translation/StableRoots` — the old DOT-to-FCsub
  bridge; its source objects carry no term members and erase to a constant,
  which is the limitation Plan III was written to remove.
- `ManySortedFC` — the static layer of a two-sorted (type and capture)
  target; no operational semantics.

The legacy example files use `native_decide`; the current development does
not (`Examples` are decided in the kernel).  The core metatheory of every
part uses only `propext` and `Quot.sound`, with `Classical.choice` in the
FCdot `progress`/`erase_reflect'` line and what depends on it.

`All.lean` imports the legacy development; the current line is rooted at
`DotMNF.lean`, `FCdot.lean`, `DotToFCdot.lean`.
