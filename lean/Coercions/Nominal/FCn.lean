import Coercions.Nominal.FCn.Syntax
import Coercions.Nominal.FCn.RenameLemmas
import Coercions.Nominal.FCn.Context
import Coercions.Nominal.FCn.Typing
import Coercions.Nominal.FCn.Store
import Coercions.Nominal.FCn.Machine
import Coercions.Nominal.FCn.Model
import Coercions.Nominal.FCn.TypingRename
import Coercions.Nominal.FCn.TypingSubst
import Coercions.Nominal.FCn.Transparency
import Coercions.Nominal.FCn.Examples
import Coercions.Nominal.FCn.Erasure
import Coercions.Nominal.FCn.Checker
import Coercions.Nominal.FCn.CheckerCompleteness
import Coercions.Nominal.FCn.Canon
import Coercions.Nominal.FCn.Resolution
import Coercions.Nominal.FCn.CanonExamples
import Coercions.Nominal.FCn.Normalizer
import Coercions.Nominal.FCn.FormTyping
import Coercions.Nominal.FCn.FormAlgebra
import Coercions.Nominal.FCn.CanonicalForms
import Coercions.Nominal.FCn.LookupSafety
import Coercions.Nominal.FCn.Consistency
import Coercions.Nominal.FCn.CanonicalExamples
import Coercions.Nominal.FCn.Preservation
import Coercions.Nominal.FCn.Progress
import Coercions.Nominal.FCn.ErasureMetatheory

/-!
Import root for the target of PDot: FCn, the coercion calculus of plan X, Part T, in
`PDot/FCp/`.  FCn keeps FCdot's discipline.  Every inclusion is an explicit cast, evidence is a
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
