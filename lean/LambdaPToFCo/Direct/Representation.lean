import LambdaPToFCo.Direct.Atomic
import LambdaPToFCo.Direct.Structural
import LambdaPFC.Typing

/-!
# Minimal source representations for the direct compiler

This internal leaf is the single one-sided relation between a LambdaPFC type
and its target value shape. It retains only the structural children required
by well-formedness, path selection, and subtyping recursion. Runtime interval
views expose one genuinely opaque selected target type and two ordinary typed
endpoint functions; no selected source type or fabricated stable plan exists.

The opened environment stores the exact `Shape.Interface` already available
at each source variable. Looking up a variable therefore cannot reopen its
package into a deeper target scope. Source provenance continues to come from
the derivation being compiled; no auxiliary compiler-certificate hierarchy is
stored here.
-/

namespace LambdaPToFCo.Direct.Internal.Representation

open SystemFCo

inductive Rep : {n : Nat} -> {sig : Sig} ->
    SystemFCo.Ctx sig -> LambdaPFC.Ty n -> Shape sig -> Type where
| top (targetContext : SystemFCo.Ctx sig) :
    Rep targetContext .Top (.stable (Top.plan sig))
| bottom (targetContext : SystemFCo.Ctx sig) :
    Rep targetContext .Bot (.stable (Bot.plan sig))
| singleton (targetContext : SystemFCo.Ctx sig)
    (path : LambdaPFC.Path n) (referentIdentity : SystemFCo.Ty sig) :
    Rep targetContext (.Single path)
      (.stable (Single.plan referentIdentity))
| selection
    {targetContext : SystemFCo.Ctx sig}
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selectedType : SystemFCo.Ty sig}
    (lowerRep : Rep targetContext lowerSource lower)
    (upperRep : Rep targetContext upperSource upper)
    (lowerFunction : Exp sig)
    (lowerTyping : Exp.HasType targetContext lowerFunction
      (.arrow lower.inputTy selectedType))
    (upperFunction : Exp sig)
    (upperTyping : Exp.HasType targetContext upperFunction
      (.arrow selectedType upper.inputTy)) :
    Rep targetContext (.TSel path label) (.opaque selectedType)
| function
    {targetContext : SystemFCo.Ctx sig}
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    {domain : Shape sig} {codomain : Shape domain.scope}
    (domainRep : Rep targetContext domainSource domain)
    (codomainRep : Rep (domain.context targetContext)
      codomainSource codomain) :
    Rep targetContext (.Fun domainSource codomainSource)
      (.stable (Function.plan domain codomain))
| properPair
    {targetContext : SystemFCo.Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {memberSource : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {first : Shape sig} {member : Shape first.scope}
    (firstRep : Rep targetContext firstSource first)
    (memberRep : Rep (first.context targetContext)
      memberSource member) :
    Rep targetContext (.Pair firstSource label (.ty memberSource))
      (.stable (Pair.Proper.plan first member))
| intervalPair
    {targetContext : SystemFCo.Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {lowerSource upperSource : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {first : Shape sig} {lower upper : Shape first.scope}
    (firstRep : Rep targetContext firstSource first)
    (lowerRep : Rep (first.context targetContext) lowerSource lower)
    (upperRep : Rep (first.context targetContext) upperSource upper) :
    Rep targetContext
      (.Pair firstSource label (.intv lowerSource upperSource))
      (.stable (Pair.Interval.plan first lower upper))

noncomputable def Rep.sourceRename
    {targetContext : SystemFCo.Ctx sig}
    {sourceType : LambdaPFC.Ty n} {shape : Shape sig}
    (rep : Rep targetContext sourceType shape)
    (mapping : LambdaPFC.FinFun n m) :
    Rep targetContext (sourceType.rename mapping) shape := by
  induction rep generalizing m with
  | top => exact .top _
  | bottom => exact .bottom _
  | singleton _ path referentIdentity =>
      exact .singleton _ (path.rename mapping) referentIdentity
  | selection lowerRep upperRep lowerFunction lowerTyping upperFunction
      upperTyping lowerIH upperIH =>
      exact .selection (lowerIH mapping)
        (upperIH mapping) lowerFunction lowerTyping
        upperFunction upperTyping
  | function domainRep codomainRep domainIH codomainIH =>
      exact .function (domainIH mapping) (codomainIH mapping.ext)
  | properPair firstRep memberRep firstIH memberIH =>
      exact .properPair (firstIH mapping) (memberIH mapping.ext)
  | intervalPair firstRep lowerRep upperRep firstIH lowerIH upperIH =>
      exact .intervalPair (firstIH mapping) (lowerIH mapping.ext)
        (upperIH mapping.ext)

/-- Substitute source paths without changing the target representation. -/
noncomputable def Rep.sourceSubst
    {targetContext : SystemFCo.Ctx sig}
    {sourceType : LambdaPFC.Ty n} {shape : Shape sig}
    (rep : Rep targetContext sourceType shape)
    (substitution : LambdaPFC.PathSubst n m) :
    Rep targetContext (sourceType.subst substitution) shape := by
  induction rep generalizing m with
  | top => exact .top _
  | bottom => exact .bottom _
  | singleton _ path referentIdentity =>
      exact .singleton _ (path.subst substitution) referentIdentity
  | selection lowerRep upperRep lowerFunction lowerTyping upperFunction
      upperTyping lowerIH upperIH =>
      exact .selection (lowerIH substitution) (upperIH substitution)
        lowerFunction lowerTyping upperFunction upperTyping
  | function domainRep codomainRep domainIH codomainIH =>
      exact .function (domainIH substitution)
        (codomainIH substitution.lift)
  | properPair firstRep memberRep firstIH memberIH =>
      exact .properPair (firstIH substitution)
        (memberIH substitution.lift)
  | intervalPair firstRep lowerRep upperRep firstIH lowerIH upperIH =>
      exact .intervalPair (firstIH substitution)
        (lowerIH substitution.lift) (upperIH substitution.lift)

/-- Reindex one representation through a typed target renaming. -/
noncomputable def Rep.targetRename
    {sourceContext : SystemFCo.Ctx source}
    {targetContext : SystemFCo.Ctx target}
    {sourceType : LambdaPFC.Ty n} {shape : Shape source}
    (rep : Rep sourceContext sourceType shape)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Rep targetContext sourceType (shape.rename mapping) := by
  induction rep generalizing target with
  | top =>
      simpa only [Shape.rename, Top.plan_rename] using Rep.top targetContext
  | bottom =>
      simpa only [Shape.rename, Bot.plan_rename] using Rep.bottom targetContext
  | singleton _ path referentIdentity =>
      simpa only [Shape.rename, Single.plan_rename] using
        Rep.singleton targetContext path (referentIdentity.rename mapping)
  | selection lowerRep upperRep lowerFunction lowerTyping upperFunction
      upperTyping lowerIH upperIH =>
      refine .selection (lowerIH mapping typed) (upperIH mapping typed)
        (lowerFunction.rename mapping) ?_
        (upperFunction.rename mapping) ?_
      · simpa only [Ty.rename, Shape.inputTy_rename] using
          Exp.HasType.rename lowerTyping typed
      · simpa only [Ty.rename, Shape.inputTy_rename] using
          Exp.HasType.rename upperTyping typed
  | @function _ _ _ _ _ domain _ domainRep codomainRep domainIH
      codomainIH =>
      have lifted := domain.liftRename_typed typed
      have renamedDomain := domainIH mapping typed
      have renamedCodomain := codomainIH
        (domain.liftRename mapping) lifted
      simpa only [Shape.rename, Function.plan_rename,
        Function.renameCodomain] using
        Rep.function renamedDomain renamedCodomain
  | @properPair _ _ _ _ _ _ first _ firstRep memberRep firstIH memberIH =>
      have lifted := first.liftRename_typed typed
      have renamedFirst := firstIH mapping typed
      have renamedMember := memberIH
        (first.liftRename mapping) lifted
      simpa only [Shape.rename, Pair.Proper.plan_rename,
        Pair.Proper.renameMember] using
        Rep.properPair renamedFirst renamedMember
  | @intervalPair _ _ _ _ _ _ _ first _ _ firstRep lowerRep upperRep
      firstIH lowerIH upperIH =>
      have lifted := first.liftRename_typed typed
      have renamedFirst := firstIH mapping typed
      have renamedLower := lowerIH
        (first.liftRename mapping) lifted
      have renamedUpper := upperIH
        (first.liftRename mapping) lifted
      simpa only [Shape.rename, Pair.Interval.plan_rename] using
        Rep.intervalPair renamedFirst renamedLower renamedUpper

/-- Reindex one representation through a typed target substitution. -/
noncomputable def Rep.targetSubst
    {sourceContext : SystemFCo.Ctx source}
    {targetContext : SystemFCo.Ctx target}
    {sourceType : LambdaPFC.Ty n} {shape : Shape source}
    (rep : Rep sourceContext sourceType shape)
    (substitution : Subst source target)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    Rep targetContext sourceType (shape.subst substitution) := by
  induction rep generalizing target with
  | top =>
      simpa only [Shape.subst, Top.plan_subst] using Rep.top targetContext
  | bottom =>
      simpa only [Shape.subst, Bot.plan_subst] using Rep.bottom targetContext
  | singleton _ path referentIdentity =>
      simpa only [Shape.subst, Single.plan_subst] using
        Rep.singleton targetContext path
          (referentIdentity.subst substitution)
  | selection lowerRep upperRep lowerFunction lowerTyping upperFunction
      upperTyping lowerIH upperIH =>
      refine .selection (lowerIH substitution typed)
        (upperIH substitution typed) (lowerFunction.subst substitution) ?_
        (upperFunction.subst substitution) ?_
      · simpa only [Ty.subst, Shape.inputTy_subst] using
          Exp.HasType.subst lowerTyping typed
      · simpa only [Ty.subst, Shape.inputTy_subst] using
          Exp.HasType.subst upperTyping typed
  | @function _ _ _ _ _ domain _ domainRep codomainRep domainIH
      codomainIH =>
      have lifted := domain.liftSubst_typed typed
      have substitutedDomain := domainIH substitution typed
      have substitutedCodomain := codomainIH
        (domain.liftSubst substitution) lifted
      simpa only [Shape.subst, Function.plan_subst,
        Function.substCodomain] using
        Rep.function substitutedDomain substitutedCodomain
  | @properPair _ _ _ _ _ _ first _ firstRep memberRep firstIH memberIH =>
      have lifted := first.liftSubst_typed typed
      have substitutedFirst := firstIH substitution typed
      have substitutedMember := memberIH
        (first.liftSubst substitution) lifted
      simpa only [Shape.subst, Pair.Proper.plan_subst,
        Pair.Proper.substMember] using
        Rep.properPair substitutedFirst substitutedMember
  | @intervalPair _ _ _ _ _ _ _ first _ _ firstRep lowerRep upperRep
      firstIH lowerIH upperIH =>
      have lifted := first.liftSubst_typed typed
      have substitutedFirst := firstIH substitution typed
      have substitutedLower := lowerIH
        (first.liftSubst substitution) lifted
      have substitutedUpper := upperIH
        (first.liftSubst substitution) lifted
      simpa only [Shape.subst, Pair.Interval.plan_subst] using
        Rep.intervalPair substitutedFirst substitutedLower substitutedUpper

/-- Every stable representation produced by the source relation has a
term-only observation telescope. This is exactly the admissibility witness
used by unchanged-SystemFCo stable package adapters. -/
def Rep.termOnly
    {targetContext : SystemFCo.Ctx sig}
    {sourceType : LambdaPFC.Ty n} {plan : Package.Plan sig}
    (rep : Rep targetContext sourceType (.stable plan)) :
    plan.TermOnly := by
  cases rep with
  | top => exact Top.termOnly sig
  | bottom => exact Bot.termOnly sig
  | singleton _ _ referentIdentity =>
      exact Single.termOnly referentIdentity
  | function => exact .var .nil
  | properPair => exact .var .nil
  | intervalPair => exact .var .nil

/-- Instantiate a dependent representation with both its source-path
substitution and the concrete target interface arguments. -/
noncomputable def Rep.instantiate
    {base : SystemFCo.Ctx sig} {owner : Shape sig}
    {sourceType : LambdaPFC.Ty n} {member : Shape owner.scope}
    (rep : Rep (owner.context base) sourceType member)
    (interface : Shape.Interface base owner)
    (sourceSubstitution : LambdaPFC.PathSubst n m) :
    Rep base (sourceType.subst sourceSubstitution)
      (member.subst interface.substitution) :=
  (rep.sourceSubst sourceSubstitution).targetSubst
    interface.substitution interface.arguments.substitution_typed

/-- Runtime view exposed by one opened interval member. -/
structure IntervalRep
    {targetContext : SystemFCo.Ctx sig}
    (lowerSource upperSource : LambdaPFC.Ty n)
    (lower : Shape sig) (selectedType : SystemFCo.Ty sig)
    (upper : Shape sig) : Type where
  lowerRep : Rep targetContext lowerSource lower
  upperRep : Rep targetContext upperSource upper
  lowerFunction : Exp sig
  lowerTyping : Exp.HasType targetContext lowerFunction
    (.arrow lower.inputTy selectedType)
  upperFunction : Exp sig
  upperTyping : Exp.HasType targetContext upperFunction
    (.arrow selectedType upper.inputTy)

namespace IntervalRep

def selection {n : Nat} {sig : Sig}
    {targetContext : SystemFCo.Ctx sig}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selectedType : SystemFCo.Ty sig}
    (interval : IntervalRep (targetContext := targetContext)
    lowerSource upperSource lower selectedType upper)
    (path : LambdaPFC.Path n)
    (label : LambdaPFC.Name) :
    Rep targetContext (.TSel path label) (.opaque selectedType) :=
  .selection (lowerSource := lowerSource) (upperSource := upperSource)
    interval.lowerRep interval.upperRep interval.lowerFunction
    interval.lowerTyping interval.upperFunction interval.upperTyping

/-- The concrete interval view exposed by Structural's member telescope.
Its selected shape is the actual hidden raw type, while the endpoints are
the same endpoint representations weakened into that opened scope. -/
noncomputable def opened
    {n : Nat} {sig : Sig} {targetContext : SystemFCo.Ctx sig}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig}
    (lowerRep : Rep targetContext lowerSource lower)
    (upperRep : Rep targetContext upperSource upper) :
    IntervalRep
      (targetContext :=
        (Pair.Interval.memberTelescope lower upper).context targetContext)
      lowerSource upperSource
      (lower.rename (Pair.Interval.memberTelescope lower upper).weaken)
      (Pair.Interval.selectedTy lower upper)
      (upper.rename (Pair.Interval.memberTelescope lower upper).weaken) where
  lowerRep := lowerRep.targetRename
    (Pair.Interval.memberTelescope lower upper).weaken
    ((Pair.Interval.memberTelescope lower upper).weaken_typed targetContext)
  upperRep := upperRep.targetRename
    (Pair.Interval.memberTelescope lower upper).weaken
    ((Pair.Interval.memberTelescope lower upper).weaken_typed targetContext)
  lowerFunction := Pair.Interval.lowerFunction lower upper
  lowerTyping := by
    change Exp.HasType _ _ (.arrow
      (lower.rename (Pair.Interval.memberTelescope lower upper).weaken).inputTy
      (Pair.Interval.selectedTy lower upper))
    rw [← Shape.inputTy_rename]
    exact Pair.Interval.lowerFunction_hasType targetContext lower upper
  upperFunction := Pair.Interval.upperFunction lower upper
  upperTyping := by
    change Exp.HasType _ _ (.arrow (Pair.Interval.selectedTy lower upper)
      (upper.rename (Pair.Interval.memberTelescope lower upper).weaken).inputTy)
    rw [← Shape.inputTy_rename]
    exact Pair.Interval.upperFunction_hasType targetContext lower upper

noncomputable def sourceRename
    {n m : Nat} {sig : Sig}
    {targetContext : SystemFCo.Ctx sig}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selectedType : SystemFCo.Ty sig}
    (interval : IntervalRep (targetContext := targetContext)
      lowerSource upperSource lower selectedType upper)
    (mapping : LambdaPFC.FinFun n m) :
    IntervalRep (targetContext := targetContext) (lowerSource.rename mapping)
      (upperSource.rename mapping) lower selectedType upper where
  lowerRep := interval.lowerRep.sourceRename mapping
  upperRep := interval.upperRep.sourceRename mapping
  lowerFunction := interval.lowerFunction
  lowerTyping := interval.lowerTyping
  upperFunction := interval.upperFunction
  upperTyping := interval.upperTyping

noncomputable def sourceSubst
    {n m : Nat} {sig : Sig}
    {targetContext : SystemFCo.Ctx sig}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selectedType : SystemFCo.Ty sig}
    (interval : IntervalRep (targetContext := targetContext)
      lowerSource upperSource lower selectedType upper)
    (substitution : LambdaPFC.PathSubst n m) :
    IntervalRep (targetContext := targetContext)
      (lowerSource.subst substitution) (upperSource.subst substitution)
      lower selectedType upper where
  lowerRep := interval.lowerRep.sourceSubst substitution
  upperRep := interval.upperRep.sourceSubst substitution
  lowerFunction := interval.lowerFunction
  lowerTyping := interval.lowerTyping
  upperFunction := interval.upperFunction
  upperTyping := interval.upperTyping

noncomputable def targetRename
    {source target : Sig}
    {sourceContext : SystemFCo.Ctx source}
    {targetContext : SystemFCo.Ctx target}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape source} {selectedType : SystemFCo.Ty source}
    (interval : IntervalRep (targetContext := sourceContext)
      lowerSource upperSource lower selectedType upper)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    IntervalRep (targetContext := targetContext) lowerSource upperSource
      (lower.rename mapping) (selectedType.rename mapping)
      (upper.rename mapping) where
  lowerRep := interval.lowerRep.targetRename mapping typed
  upperRep := interval.upperRep.targetRename mapping typed
  lowerFunction := interval.lowerFunction.rename mapping
  lowerTyping := by
    simpa only [Ty.rename, Shape.inputTy_rename] using
      Exp.HasType.rename interval.lowerTyping typed
  upperFunction := interval.upperFunction.rename mapping
  upperTyping := by
    simpa only [Ty.rename, Shape.inputTy_rename] using
      Exp.HasType.rename interval.upperTyping typed

noncomputable def targetSubst
    {source target : Sig}
    {sourceContext : SystemFCo.Ctx source}
    {targetContext : SystemFCo.Ctx target}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape source} {selectedType : SystemFCo.Ty source}
    (interval : IntervalRep (targetContext := sourceContext)
      lowerSource upperSource lower selectedType upper)
    (substitution : Subst source target)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    IntervalRep (targetContext := targetContext) lowerSource upperSource
      (lower.subst substitution) (selectedType.subst substitution)
      (upper.subst substitution) where
  lowerRep := interval.lowerRep.targetSubst substitution typed
  upperRep := interval.upperRep.targetSubst substitution typed
  lowerFunction := interval.lowerFunction.subst substitution
  lowerTyping := by
    simpa only [Ty.subst, Shape.inputTy_subst] using
      Exp.HasType.subst interval.lowerTyping typed
  upperFunction := interval.upperFunction.subst substitution
  upperTyping := by
    simpa only [Ty.subst, Shape.inputTy_subst] using
      Exp.HasType.subst interval.upperTyping typed

end IntervalRep

/-! ## Already-open source environments -/

/-- One source type together with its currently available target interface.
The interface is retained so variable lookup never reopens the value and
accidentally creates a deeper, unclosable target scope. -/
structure Slot (targetContext : SystemFCo.Ctx sig)
    (sourceType : LambdaPFC.Ty n) : Type where
  shape : Shape sig
  interface : Shape.Interface targetContext shape
  rep : Rep targetContext sourceType shape

namespace Slot

noncomputable def expression {sig : Sig} {n : Nat}
    {targetContext : SystemFCo.Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (slot : Slot targetContext sourceType) : Exp sig :=
  slot.interface.package

noncomputable def expression_hasType
    {sig : Sig} {n : Nat}
    {targetContext : SystemFCo.Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (slot : Slot targetContext sourceType) :
    Exp.HasType targetContext slot.expression slot.shape.inputTy :=
  slot.interface.package_hasType

noncomputable def sourceRename
    {sig : Sig} {n m : Nat}
    {targetContext : SystemFCo.Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (slot : Slot targetContext sourceType)
    (mapping : LambdaPFC.FinFun n m) :
    Slot targetContext (sourceType.rename mapping) where
  shape := slot.shape
  interface := slot.interface
  rep := slot.rep.sourceRename mapping

noncomputable def targetRename
    {n : Nat} {sourceType : LambdaPFC.Ty n}
    {sourceContext : SystemFCo.Ctx source}
    {targetContext : SystemFCo.Ctx target}
    (slot : Slot sourceContext sourceType)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Slot targetContext sourceType where
  shape := slot.shape.rename mapping
  interface := slot.interface.rename mapping typed
  rep := slot.rep.targetRename mapping typed

end Slot

/-- A compact semantic environment indexed by the actual source lookup type.
Every slot is already open at the current target scope. -/
structure Env (sourceContext : LambdaPFC.Ctx n)
    (targetContext : SystemFCo.Ctx sig) : Type where
  lookup : (index : Fin n) ->
    Slot targetContext (sourceContext.lookup index)

namespace Env

def empty (targetContext : SystemFCo.Ctx sig) :
    Env .nil targetContext where
  lookup index := Fin.elim0 index

noncomputable def targetRename
    {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : SystemFCo.Ctx source}
    {targetTargetContext : SystemFCo.Ctx target}
    (environment : Env sourceContext sourceTargetContext)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    Env sourceContext targetTargetContext where
  lookup index := (environment.lookup index).targetRename mapping typed

/-- Extend through any target scope renaming and install an interface that is
already open in the resulting context. The caller supplies the bound
representation; target syntax alone cannot manufacture it. -/
noncomputable def extend
    {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : SystemFCo.Ctx source}
    {targetTargetContext : SystemFCo.Ctx target}
    (environment : Env sourceContext sourceTargetContext)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
    (sourceType : LambdaPFC.Ty n)
    {shape : Shape target}
    (interface : Shape.Interface targetTargetContext shape)
    (boundRep : Rep targetTargetContext sourceType.weaken shape) :
    Env (sourceContext.snoc sourceType) targetTargetContext where
  lookup := Fin.cases
    { shape := shape, interface := interface, rep := boundRep }
    (fun older =>
      ((environment.lookup older).targetRename mapping typed).sourceRename
        LambdaPFC.FinFun.weaken)

@[simp] theorem extend_here
    {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : SystemFCo.Ctx source}
    {targetTargetContext : SystemFCo.Ctx target}
    (environment : Env sourceContext sourceTargetContext)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
    (sourceType : LambdaPFC.Ty n)
    {shape : Shape target}
    (interface : Shape.Interface targetTargetContext shape)
    (boundRep : Rep targetTargetContext sourceType.weaken shape) :
    (environment.extend mapping typed sourceType interface boundRep).lookup 0 =
      { shape := shape, interface := interface, rep := boundRep } := by
  rfl

@[simp] theorem extend_there
    {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : SystemFCo.Ctx source}
    {targetTargetContext : SystemFCo.Ctx target}
    (environment : Env sourceContext sourceTargetContext)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
    (sourceType : LambdaPFC.Ty n)
    {shape : Shape target}
    (interface : Shape.Interface targetTargetContext shape)
    (boundRep : Rep targetTargetContext sourceType.weaken shape)
    (index : Fin n) :
    (environment.extend mapping typed sourceType interface boundRep).lookup
        index.succ =
      ((environment.lookup index).targetRename mapping typed).sourceRename
        LambdaPFC.FinFun.weaken := by
  rfl

/-- Canonically open one represented value and retain its exact repackaged
interface as the newest source slot. -/
noncomputable def enter
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    (environment : Env sourceContext targetContext)
    (sourceType : LambdaPFC.Ty n) (shape : Shape sig)
    (boundRep : Rep targetContext sourceType shape) :
    Env (sourceContext.snoc sourceType) (shape.context targetContext) :=
  let mapping := shape.binders.weaken
  let typed := shape.binders.weaken_typed targetContext
  let openedRep :=
    (boundRep.sourceRename LambdaPFC.FinFun.weaken).targetRename mapping typed
  environment.extend mapping typed sourceType
    (Shape.Interface.canonical targetContext shape) openedRep

end Env

end LambdaPToFCo.Direct.Internal.Representation
