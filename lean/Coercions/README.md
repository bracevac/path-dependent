# Coercions

| directory | what | README |
|---|---|---|
| `Runtime.lean` | the untyped runtime both `DotMNF` and `FCdot` erase into: `var`, `lam`, `obj` with fields, `app`, `proj`, `let`; store machine | — |
| `DotMNF/` | source: WadlerFest DOT in monadic normal form; syntax, typing, machine, erasure, examples | [`DotMNF/README.md`](DotMNF/README.md) |
| `FCdot/` | target: explicit-evidence coercion calculus; checker, preservation, progress, erasure simulations, canonical forms, consistency, examples | [`FCdot/README.md`](FCdot/README.md) |
| `DotToFCdot/` | the translation `DotMNF → FCdot`: typedness, erasure equality, `dot_safety`, consistency corollaries | [`DotToFCdot/README.md`](DotToFCdot/README.md) |
| `FCsub/` | System F-sub with explicit coercions; standalone | [`FCsub/README.md`](FCsub/README.md) |
| `ManySortedFC/` | static layer of a two-sorted (type and capture) target; standalone | [`ManySortedFC/README.md`](ManySortedFC/README.md) |

Roots: `DotMNF.lean`, `FCdot.lean`, `DotToFCdot.lean`, `Runtime.lean`, `FCsub.lean`, `ManySortedFC.lean`, `All.lean` (= `FCsub` + `ManySortedFC`).
