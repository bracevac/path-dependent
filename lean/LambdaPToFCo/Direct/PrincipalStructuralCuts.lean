import LambdaPToFCo.Direct.ContextRelation
import LambdaPToFCo.Direct.PairSubtyping

/-!
# Direct principal structural cuts

Structural transitivity must retain one exact representation of its middle
type.  Compiling the two source rules independently and then comparing their
existentially chosen middle Shapes would be unsound.  The functions in this
leaf are instead invoked inside the literal transitivity continuation, while
the three endpoint Shapes and the one shared middle representation are all
in scope.

The first bounded constructor is source-oriented `pair ; pair` for proper
members.  It invokes the two frozen, derivation-indexed pair callbacks with
the *same* middle first/member Shapes and Reps.  Their resulting outer middle
Shape is therefore definitionally identical, so ordinary `Relation.trans`
is sufficient.  This function neither builds a middle from a well-formedness
derivation nor accepts a Shape equality/coherence witness.

Target-oriented pair cuts require a sealed endpoint swap for
`ContextRelation.Scope`; that distinct boundary is intentionally absent.
-/

namespace LambdaPToFCo.Direct.Internal.PrincipalStructuralCuts

noncomputable section

open SystemFCo
open Representation
open ContextRelation

/-- Fuse two literal proper-member pair rules around one exact middle pair.

The middle first Shape and middle member Rep occur only once in the
signature.  Consequently both pair compilers construct exactly
`Pair.Proper.plan middleFirst middleMember` as their common outer endpoint.
The caller must invoke this function while recursive principal-cut CPS still
retains that middle; it is not an adapter for independently compiled pairs. -/
noncomputable def properProper
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType middleFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType middleMemberType targetMemberType :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {sourceFirst middleFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {middleMember : Shape middleFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (scope : Scope sourceContext targetContext .source base)
    {firstDerivation01 : LambdaPFC.Tau.Sub sourceContext
      (.ty sourceFirstType) (.ty middleFirstType)}
    (first01 : PairSubtyping.FirstCompilation base firstDerivation01
      sourceFirst middleFirst)
    {firstDerivation12 : LambdaPFC.Tau.Sub sourceContext
      (.ty middleFirstType) (.ty targetFirstType)}
    (first12 : PairSubtyping.FirstCompilation base firstDerivation12
      middleFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (middleMemberRep : Rep (middleFirst.context base)
      middleMemberType middleMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    {memberDerivation01 : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty middleMemberType)}
    (member01 : PairSubtyping.ProperMemberCompiler scope.endpointEnvs
      first01.relation sourceMemberRep middleMemberRep memberDerivation01)
    {memberDerivation12 : LambdaPFC.Tau.Sub
      (sourceContext.snoc middleFirstType)
      (.ty middleMemberType) (.ty targetMemberType)}
    (member12 : PairSubtyping.ProperMemberCompiler scope.endpointEnvs
      first12.relation middleMemberRep targetMemberRep memberDerivation12) :
    Relation base
      (.Pair sourceFirstType label (.ty sourceMemberType))
      (.Pair targetFirstType label (.ty targetMemberType))
      (.stable (Pair.Proper.plan sourceFirst sourceMember))
      (.stable (Pair.Proper.plan targetFirst targetMember)) :=
  let firstLeg := PairSubtyping.proper scope.endpointEnvs first01
    sourceMemberRep middleMemberRep member01
  let secondLeg := PairSubtyping.proper scope.endpointEnvs first12
    middleMemberRep targetMemberRep member12
  firstLeg.trans secondLeg

end

end LambdaPToFCo.Direct.Internal.PrincipalStructuralCuts
