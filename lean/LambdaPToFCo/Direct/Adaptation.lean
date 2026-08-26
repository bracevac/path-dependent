import LambdaPToFCo.Direct.Relation
import LambdaPToFCo.Direct.TermIntroduction

/-!
# Applying direct subtyping to compiled values

This leaf is the small junction between term compilation and subtyping.
Given an exact compiled source slot and a direct `Relation`, it runs the
relation's identity-preserving interface map and supplies the resulting exact
target slot to the term continuation.  Any target binders opened by the map
remain inside that continuation and are closed by `InterfaceMap.run`.

There is no intermediate source term, origin trace, model, or adapter input.
Both target programs stored by `Relation` were computed by the source rule;
only its interface map is needed at this use site.
-/

namespace LambdaPToFCo.Direct.Internal.TermAdaptation

open SystemFCo
open Representation
open TermIntroduction

private noncomputable def targetContinuation
    {sourceContext : LambdaPFC.Ctx n}
    {base : Ctx origin}
    {sourceType targetType : LambdaPFC.Ty n}
    {source target : Shape origin}
    (environment : Env sourceContext base)
    (relation : Relation base sourceType targetType source target)
    (answer : Ty origin)
    (consumer : ValueConsumer sourceContext base answer targetType) :
    InterfaceMap.Continuation base target answer where
  body mapping _finalContext typed targetInterface :=
    (consumer mapping typed
      (environment.targetRename mapping typed)
      { shape := target.rename mapping
        interface := targetInterface
        rep := relation.targetRep.targetRename mapping typed }).expression
  body_hasType mapping _finalContext typed targetInterface :=
    (consumer mapping typed
      (environment.targetRename mapping typed)
      { shape := target.rename mapping
        interface := targetInterface
        rep := relation.targetRep.targetRename mapping typed }).typing

/-- Apply one exact direct subtyping relation to one compiled source slot.

The source shape is definitionally the slot's shape.  This deliberately
avoids a shape-equality premise: derivation-directed rule compilation must
construct a relation at the value it is adapting. -/
noncomputable def adaptSlot
    {sourceContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceType targetType : LambdaPFC.Ty n}
    (environment : Env sourceContext base)
    (source : Slot base sourceType)
    {target : Shape sig}
    (relation : Relation base sourceType targetType source.shape target) :
    ValueComputation sourceContext base targetType :=
  fun answer consumer =>
    { expression := relation.interfaceMap.run source.interface answer
        (targetContinuation environment relation answer consumer)
      typing := relation.interfaceMap.run_hasType source.interface answer
        (targetContinuation environment relation answer consumer) }

end LambdaPToFCo.Direct.Internal.TermAdaptation
