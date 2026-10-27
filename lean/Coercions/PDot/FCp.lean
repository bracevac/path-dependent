import Coercions.PDot.FCp.Syntax
import Coercions.PDot.FCp.RenameLemmas
import Coercions.PDot.FCp.Context
import Coercions.PDot.FCp.Typing
import Coercions.PDot.FCp.Store
import Coercions.PDot.FCp.Machine
import Coercions.PDot.FCp.Model
import Coercions.PDot.FCp.TypingRename
import Coercions.PDot.FCp.TypingSubst
import Coercions.PDot.FCp.Transparency
import Coercions.PDot.FCp.Examples
import Coercions.PDot.FCp.Erasure
import Coercions.PDot.FCp.Checker
import Coercions.PDot.FCp.CheckerCompleteness

/-!
Import root for the target of PDot: FCp, the coercion calculus of plan X, Part T, in
`PDot/FCp/`.  FCp keeps FCdot's discipline.  Every inclusion is an explicit cast, evidence is a
proof term whose endpoints typing assigns, object types are telescopes of propositions over a self,
and template morphisms prove one telescope from another.  A term is a path with its typing
evidence, and the machine is pDOT's.

The parts, in the order they land.  `Syntax` holds the families of T.1, renaming, path substitution
and evidence substitution, and the functions of T.2 that live in the syntax.  `RenameLemmas` holds
the composition laws of the three for every family.  `Context` holds contexts and the reading of
blocks.  `Typing` holds the typing rules of T.3 with their inversions.  `Store` holds store typing
and the shape of a typed store.  `Machine` holds continuation and state typing and the machine of
T.4, with the application view as a parameter.  `Model` holds the path models of a fixed context.
`TypingRename` holds the renaming of every judgment and the typing of a store's values.
`TypingSubst` holds the substitution of variables by path evidence in every judgment but store
typing, with its one-binder case.  `Transparency` holds the refinement of a context and the
monotonicity of every judgment.  `Examples` holds the negative examples N1 to N3, the binder
example and the adjusted let body.  `Erasure` holds the erasure into the runtime `PDot.Runtime`, the
simulation `erase_step` under a sound application view, and the shuffle steps that keep the
erasure.  `Checker` holds the checker of T.8, structural and sound, and `CheckerCompleteness` holds
its completeness with `checkTm_iff`.  `Examples` decides the binder example and the twins of N2 and
N3 with it.
-/
