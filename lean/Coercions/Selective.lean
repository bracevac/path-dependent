import Coercions.Selective.Fsub
import Coercions.Selective.Dot
import Coercions.Selective.Dot.Vanilla

/-!
# Selective transitivity

The root of the `Selective` library: the coercive calculi for full System F-sub
(`Selective/Fsub`) and for WadlerFest DOT in monadic normal form (`Selective/Dot`), and the
correspondence of the DOT calculus with DOT-MNF (`Selective/Dot/Vanilla`). The coercions of
both are `step[S,T]` and `c ; d`. `README.md` in `Selective/` is the introduction.

The axiom audits are not imported here: `Selective/Fsub/Axioms.lean`,
`Selective/Dot/Axioms.lean` and `Selective/Dot/Vanilla/Axioms.lean`.
-/
