# Lean developments

Two lines of work. Each directory is self-contained and depends on nothing beyond Lean's core.

**Paths through dependent pairs.** A minimal calculus where immutable dependent pairs are the only structured values and paths select through them. Every directory proves closed type safety.

- **`LambdaP/`**: the original calculus, with pair subtyping restricted to singleton-typed first components.
- **`LambdaPFC/`**: the general pair rule, proven by compiling subtyping to store-indexed coercions.
- **`LambdaPFCI/`**: `LambdaPFC` plus intersection and union types.
- **`LambdaPCC/`**: `LambdaPFC` plus capture checking, with use-set coverage and capture bounds.
- **`LambdaPCCI/`**: `LambdaPCC` plus intersection and union types.

**DOT into explicit evidence.**

- **`Coercions/`**: DOT translated into an FC-style coercion calculus with a decidable checker. DOT's type safety is a corollary. Its README is the map.

Axioms: `propext` and `Quot.sound`, plus `Classical.choice` in three theorems of `Coercions`. No `sorry`, `axiom`, `partial`, or `native_decide` outside example files. Rocq ports of `LambdaP`, `LambdaPFC`, and `LambdaPCC` are in `../rocq/`. `lake build` builds everything.
