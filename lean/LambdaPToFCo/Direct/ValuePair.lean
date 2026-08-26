import LambdaPToFCo.Direct.ArgumentCancellation
import LambdaPToFCo.Direct.TermIntroduction

/-!
# Direct value-member pair introduction

The source value-pair constructor names two paths already present in the
current environment.  This compiler forms singleton interfaces for those
exact values, weakens the member beneath the first singleton interface, and
packages the resulting dependent proper pair with ordinary System FCo Church
syntax.
-/

namespace LambdaPToFCo.Direct.Internal.ValuePair

open SystemFCo
open Representation
open TermIntroduction

private def memberShape
    {base : Ctx sig} {firstSource memberSource : LambdaPFC.Ty n}
    (first : Slot base firstSource) (member : Slot base memberSource) :
    Shape first.shape.scope :=
  member.shape.rename first.shape.binders.weaken

private theorem memberShape_subst
    {base : Ctx sig} {firstSource memberSource : LambdaPFC.Ty n}
    (first : Slot base firstSource) (member : Slot base memberSource) :
    (memberShape first member).subst first.interface.substitution =
      member.shape := by
  exact Shape.rename_subst_cancel member.shape first.shape.binders.weaken
    first.interface.substitution
    first.interface.arguments.weaken_comp_substitution

private theorem memberBinders_subst
    {base : Ctx sig} {firstSource memberSource : LambdaPFC.Ty n}
    (first : Slot base firstSource) (member : Slot base memberSource) :
    (memberShape first member).binders.subst
        first.interface.substitution = member.shape.binders := by
  rw [Shape.binders_subst, memberShape_subst]

private noncomputable def memberArguments
    {base : Ctx sig} {firstSource memberSource : LambdaPFC.Ty n}
    (first : Slot base firstSource) (member : Slot base memberSource) :
    Telescope.Args base
      ((memberShape first member).binders.subst
        first.interface.substitution) :=
  (memberBinders_subst first member).symm ▸ member.interface.arguments

private noncomputable def memberRep
    {base : Ctx sig}
    {firstIndex memberIndex : Fin n}
    (first : Slot base (.Single (.var firstIndex)))
    (member : Slot base (.Single (.var memberIndex))) :
    Rep (first.shape.context base)
      (.Single ((LambdaPFC.Path.var memberIndex).weaken))
      (memberShape first member) :=
  (member.rep.sourceRename LambdaPFC.FinFun.weaken).targetRename
    first.shape.binders.weaken
    (first.shape.binders.weaken_typed base)

/-- Exact direct slot for `Tm.pair y a (Def.val z)`. -/
noncomputable def slot
    {sourceContext : LambdaPFC.Ctx n} {base : Ctx sig}
    (environment : Env sourceContext base)
    (firstIndex memberIndex : Fin n) (label : LambdaPFC.Name) :
    Slot base
      (.Pair (.Single (.var firstIndex)) label
        (.ty (.Single ((LambdaPFC.Path.var memberIndex).weaken)))) :=
  let first := TermIntroduction.variableSlot environment firstIndex
  let member := TermIntroduction.variableSlot environment memberIndex
  let dependentMember := memberShape first member
  {
    shape := .stable (Pair.Proper.plan first.shape dependentMember)
    interface := {
      arguments := Pair.Proper.exactArguments first.shape dependentMember
        first.interface.arguments (memberArguments first member)
    }
    rep := .properPair first.rep (memberRep first member)
  }

/-- The constructor as a scope-closing term computation. -/
noncomputable def compile
    {sourceContext : LambdaPFC.Ctx n} {base : Ctx sig}
    (environment : Env sourceContext base)
    (firstIndex memberIndex : Fin n) (label : LambdaPFC.Name) :
    ValueComputation sourceContext base
      (.Pair (.Single (.var firstIndex)) label
        (.ty (.Single ((LambdaPFC.Path.var memberIndex).weaken)))) :=
  TermIntroduction.compileMaterial environment
    (slot environment firstIndex memberIndex label)

end LambdaPToFCo.Direct.Internal.ValuePair
