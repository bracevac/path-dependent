import LambdaPToFCo.Direct.AtomicSubtyping
import LambdaPToFCo.Direct.ArgumentCancellation
import LambdaPToFCo.Direct.TermIntroduction
import LambdaPToFCo.Direct.ContextRelation

/-!
# Direct dependent-pair subtyping

This target-only implementation opens the source pair representation, maps
its exact first interface through the compiled first-component relation, and
repackages the dependent member in the resulting continuation scope.  The
runtime output is an ordinary unchanged-SystemFCo function.  Hidden interval
witnesses remain opaque and their stored lower/upper functions are mapped in
place; no selected identity is reconstructed.

The public constructors return a `Relation` indexed by their exact source and
target shapes.  All telescope and continuation plumbing below is private, so
callers neither supply shape equalities nor target-code callbacks.
-/

namespace LambdaPToFCo.Direct.Internal.PairSubtyping

open SystemFCo
open Representation

private def sourceFirstAtBinder (first : Shape sig) : Shape (sig ,, .var) :=
  first.rename (Rename.weaken .var)

private def sourceMemberAtBinder (first : Shape sig)
    (member : Shape first.scope) :
    Shape (sourceFirstAtBinder first).scope :=
  Pair.Proper.renameMember first member (Rename.weaken .var)

private def properRepresentationAtBinder (first : Shape sig)
    (member : Shape first.scope) : Telescope (sig ,, .var) :=
  Pair.Proper.representation (sourceFirstAtBinder first)
    (sourceMemberAtBinder first member)

private theorem properRepresentationAtBinder_eq (first : Shape sig)
    (member : Shape first.scope) :
    (Pair.Proper.representation first member).rename (Rename.weaken .var) =
      properRepresentationAtBinder first member :=
  Pair.Proper.representation_rename first member (Rename.weaken .var)

private def sourceOpening (first : Shape sig)
    (member : Shape first.scope) :
    Rename (sig ,, .var) (sourceMemberAtBinder first member).scope :=
  (sourceFirstAtBinder first).binders.weaken.comp
    (sourceMemberAtBinder first member).binders.weaken

private def sourceOpenedContext (base : Ctx sig)
    (first : Shape sig) (member : Shape first.scope) :
    Ctx (sourceMemberAtBinder first member).scope :=
  (sourceMemberAtBinder first member).context
    ((sourceFirstAtBinder first).context
      (base.bindVar (Pair.Proper.representation first member).existsTy))

private noncomputable def sourceFirstInterface (base : Ctx sig)
    (first : Shape sig) (member : Shape first.scope) :
    Shape.Interface (sourceOpenedContext base first member)
      (((sourceFirstAtBinder first).rename
        (sourceFirstAtBinder first).binders.weaken).rename
          (sourceMemberAtBinder first member).binders.weaken) :=
  (Shape.Interface.canonical
    (base.bindVar (Pair.Proper.representation first member).existsTy)
    (sourceFirstAtBinder first)).rename
      (sourceMemberAtBinder first member).binders.weaken
      ((sourceMemberAtBinder first member).binders.weaken_typed
        ((sourceFirstAtBinder first).context
          (base.bindVar
            (Pair.Proper.representation first member).existsTy)))

private noncomputable def sourceMemberInterface (base : Ctx sig)
    (first : Shape sig) (member : Shape first.scope) :
    Shape.Interface (sourceOpenedContext base first member)
      ((sourceMemberAtBinder first member).rename
        (sourceMemberAtBinder first member).binders.weaken) :=
  Shape.Interface.canonical
    ((sourceFirstAtBinder first).context
      (base.bindVar (Pair.Proper.representation first member).existsTy))
    (sourceMemberAtBinder first member)

private def properOpening (first : Shape sig) (member : Shape first.scope) :
    Rename sig (sourceMemberAtBinder first member).scope :=
  (Rename.weaken .var).comp (sourceOpening first member)

private noncomputable def properOpening_typed (base : Ctx sig)
    (first : Shape sig) (member : Shape first.scope) :
    Rename.Typed base (sourceOpenedContext base first member)
      (properOpening first member) :=
  TypedRename.comp
    (Rename.Typed.weaken base
      (.var (Pair.Proper.representation first member).existsTy))
    (TypedRename.comp
      ((sourceFirstAtBinder first).binders.weaken_typed
        (base.bindVar
          (Pair.Proper.representation first member).existsTy))
      ((sourceMemberAtBinder first member).binders.weaken_typed
        ((sourceFirstAtBinder first).context
          (base.bindVar
            (Pair.Proper.representation first member).existsTy))))

private noncomputable def openedSourceFirstInterface (base : Ctx sig)
    (first : Shape sig) (member : Shape first.scope) :
    Shape.Interface (sourceOpenedContext base first member)
      (first.rename (properOpening first member)) := by
  simpa only [properOpening, sourceOpening, sourceFirstAtBinder,
    Shape.rename_comp] using sourceFirstInterface base first member

private def sourceMemberActual (first : Shape sig) (member : Shape first.scope) :
    Shape (sourceMemberAtBinder first member).scope :=
  (sourceMemberAtBinder first member).rename
    (sourceMemberAtBinder first member).binders.weaken

private noncomputable def openedSourceMemberInterface
    (base : Ctx sig) (first : Shape sig) (member : Shape first.scope) :
    Shape.Interface (sourceOpenedContext base first member)
      (sourceMemberActual first member) :=
  sourceMemberInterface base first member

private def sourceMemberOpening (first : Shape sig)
    (member : Shape first.scope) :
    Rename first.scope (sourceMemberAtBinder first member).scope :=
  (first.liftRename (Rename.weaken .var)).comp
    (sourceMemberAtBinder first member).binders.weaken

private noncomputable def sourceMemberOpening_typed (base : Ctx sig)
    (first : Shape sig) (member : Shape first.scope) :
    Rename.Typed (first.context base) (sourceOpenedContext base first member)
      (sourceMemberOpening first member) :=
  TypedRename.comp
    (first.liftRename_typed
      (Rename.Typed.weaken base
        (.var (Pair.Proper.representation first member).existsTy)))
    ((sourceMemberAtBinder first member).binders.weaken_typed
      ((sourceFirstAtBinder first).context
        (base.bindVar
          (Pair.Proper.representation first member).existsTy)))

private noncomputable def openedSourceMemberRep
    {memberType : LambdaPFC.Ty (n + 1)}
    (base : Ctx sig) (first : Shape sig) (member : Shape first.scope)
    (memberRep : Rep (first.context base) memberType member) :
    Rep (sourceOpenedContext base first member) memberType
      (sourceMemberActual first member) := by
  let renamed := memberRep.targetRename (sourceMemberOpening first member)
    (sourceMemberOpening_typed base first member)
  unfold sourceMemberActual sourceMemberAtBinder
    Pair.Proper.renameMember
  change Rep _ _
    (member.rename ((first.liftRename (Rename.weaken .var)).comp
      (member.rename (first.liftRename (Rename.weaken .var))).binders.weaken))
      at renamed
  rw [← Shape.rename_comp] at renamed
  exact renamed

private def targetFirstAtSource (sourceFirst : Shape sig)
    (sourceMember : Shape sourceFirst.scope)
    (targetFirst : Shape sig) :
    Shape (sourceMemberAtBinder sourceFirst sourceMember).scope :=
  (sourceFirstAtBinder targetFirst).rename
    (sourceOpening sourceFirst sourceMember)

private def targetMemberAtSource (sourceFirst : Shape sig)
    (sourceMember : Shape sourceFirst.scope)
    (targetFirst : Shape sig) (targetMember : Shape targetFirst.scope) :
    Shape (targetFirstAtSource sourceFirst sourceMember targetFirst).scope :=
  Pair.Proper.renameMember
    (sourceFirstAtBinder targetFirst)
    (sourceMemberAtBinder targetFirst targetMember)
    (sourceOpening sourceFirst sourceMember)

private def targetProperRepresentationAtSource
    (sourceFirst : Shape sig) (sourceMember : Shape sourceFirst.scope)
    (targetFirst : Shape sig) (targetMember : Shape targetFirst.scope) :
    Telescope (sourceMemberAtBinder sourceFirst sourceMember).scope :=
  Pair.Proper.representation
    (targetFirstAtSource sourceFirst sourceMember targetFirst)
    (targetMemberAtSource sourceFirst sourceMember targetFirst targetMember)

private theorem targetProperRepresentationAtSource_eq
    (sourceFirst : Shape sig) (sourceMember : Shape sourceFirst.scope)
    (targetFirst : Shape sig) (targetMember : Shape targetFirst.scope) :
    (properRepresentationAtBinder targetFirst targetMember).rename
        (sourceOpening sourceFirst sourceMember) =
      targetProperRepresentationAtSource sourceFirst sourceMember
        targetFirst targetMember :=
  Pair.Proper.representation_rename
    (sourceFirstAtBinder targetFirst)
    (sourceMemberAtBinder targetFirst targetMember)
    (sourceOpening sourceFirst sourceMember)

private noncomputable def firstRelationAtSource
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {base : Ctx sig}
    (relation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst) :
    Relation (sourceOpenedContext base sourceFirst sourceMember)
      sourceFirstType targetFirstType
      (sourceFirst.rename (properOpening sourceFirst sourceMember))
      (targetFirst.rename (properOpening sourceFirst sourceMember)) :=
  relation.targetRename (properOpening sourceFirst sourceMember)
    (properOpening_typed base sourceFirst sourceMember)

private noncomputable def adjustedFirstRelationAtSource
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {base : Ctx sig}
    (relation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst) :
    Relation (sourceOpenedContext base sourceFirst sourceMember)
      sourceFirstType targetFirstType
      ((sourceFirstAtBinder sourceFirst).rename
        (sourceOpening sourceFirst sourceMember))
      (targetFirstAtSource sourceFirst sourceMember targetFirst) := by
  simpa only [properOpening, sourceFirstAtBinder, targetFirstAtSource,
    Shape.rename_comp] using firstRelationAtSource relation

private def topShape (sig : Sig) : Shape sig := .stable (Top.plan sig)

private def bottomShape (sig : Sig) : Shape sig := .stable (Bot.plan sig)

private theorem targetTopRepresentationAtSource_rename
    (sourceFirst : Shape sig) (sourceMember : Shape sourceFirst.scope)
    (targetFirst : Shape sig)
    (mapping : Rename (sourceMemberAtBinder sourceFirst sourceMember).scope
      target) :
    (targetProperRepresentationAtSource sourceFirst sourceMember targetFirst
      (topShape targetFirst.scope)).rename mapping =
      Pair.Proper.representation
        ((targetFirstAtSource sourceFirst sourceMember targetFirst).rename
          mapping)
        (topShape
          ((targetFirstAtSource sourceFirst sourceMember targetFirst).rename
            mapping).scope) := by
  unfold targetProperRepresentationAtSource
  rw [Pair.Proper.representation_rename]
  unfold targetMemberAtSource
    sourceMemberAtBinder sourceFirstAtBinder targetFirstAtSource topShape
    Pair.Proper.renameMember Shape.liftRename Shape.rename
  cases targetFirst <;> rfl

private noncomputable def topMemberArguments
    {base : Ctx sig} {first : Shape sig}
    (firstInterface : Shape.Interface base first)
    (memberInterface : Shape.Interface base (topShape sig)) :
    Telescope.Args base
      ((topShape first.scope).binders.subst
        firstInterface.arguments.substitution) := by
  simpa only [topShape, Shape.binders, Top.plan_subst] using
    memberInterface.arguments

private noncomputable def properTopPackageContinuation
    {base : Ctx sig} (first : Shape sig)
    (firstInterface : Shape.Interface base first) :
    InterfaceMap.Continuation base (topShape sig)
      (Pair.Proper.representation first (topShape first.scope)).existsTy where
  body mapping finalContext typed memberInterface :=
    let firstAt := first.rename mapping
    let memberAt := topShape firstAt.scope
    let firstAtInterface := firstInterface.rename mapping typed
    Telescope.pack (Pair.Proper.representationArguments firstAt memberAt
      firstAtInterface.arguments
      (topMemberArguments firstAtInterface memberInterface))
  body_hasType mapping finalContext typed memberInterface := by
    let firstAt := first.rename mapping
    let memberAt := topShape firstAt.scope
    let firstAtInterface := firstInterface.rename mapping typed
    have packed := Telescope.pack_hasType
      (Pair.Proper.representationArguments firstAt memberAt
        firstAtInterface.arguments
        (topMemberArguments firstAtInterface memberInterface))
    simpa only [Package.existsTy_rename, Pair.Proper.representation_rename,
      Pair.Proper.renameMember, topShape, Shape.rename,
      Top.plan_rename] using packed

private noncomputable def properTopFirstContinuation
    {sourceMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    (sourceFirst : Shape sig) (sourceMember : Shape sourceFirst.scope)
    (targetFirst : Shape sig)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember) :
    InterfaceMap.Continuation
      (sourceOpenedContext base sourceFirst sourceMember)
      (targetFirstAtSource sourceFirst sourceMember targetFirst)
      (targetProperRepresentationAtSource sourceFirst sourceMember
        targetFirst (topShape targetFirst.scope)).existsTy where
  body mapping finalContext typed targetFirstInterface :=
    let sourceMemberInterfaceAt :=
      (openedSourceMemberInterface base sourceFirst sourceMember).rename
        mapping typed
    let sourceMemberRepAt :=
      (openedSourceMemberRep base sourceFirst sourceMember
        sourceMemberRep).targetRename mapping typed
    let sourceProper : Wf.Proper finalContext sourceMemberType := {
      shape := (sourceMemberActual sourceFirst sourceMember).rename mapping
      rep := sourceMemberRepAt
    }
    let memberRelation := AtomicSubtyping.top sourceProper
    let targetFirstAt :=
      (targetFirstAtSource sourceFirst sourceMember targetFirst).rename mapping
    let targetMemberAt := topShape targetFirstAt.scope
    let answer :=
      (Pair.Proper.representation targetFirstAt targetMemberAt).existsTy
    let continuation : InterfaceMap.Continuation finalContext
        memberRelation.target answer := by
      simpa only [memberRelation, AtomicSubtyping.top, topShape] using
        properTopPackageContinuation targetFirstAt targetFirstInterface
    memberRelation.relation.interfaceMap.run sourceMemberInterfaceAt
      answer continuation
  body_hasType mapping finalContext typed targetFirstInterface := by
    let sourceMemberInterfaceAt :=
      (openedSourceMemberInterface base sourceFirst sourceMember).rename
        mapping typed
    let sourceMemberRepAt :=
      (openedSourceMemberRep base sourceFirst sourceMember
        sourceMemberRep).targetRename mapping typed
    let sourceProper : Wf.Proper finalContext sourceMemberType := {
      shape := (sourceMemberActual sourceFirst sourceMember).rename mapping
      rep := sourceMemberRepAt
    }
    let memberRelation := AtomicSubtyping.top sourceProper
    let targetFirstAt :=
      (targetFirstAtSource sourceFirst sourceMember targetFirst).rename mapping
    let targetMemberAt := topShape targetFirstAt.scope
    let answer :=
      (Pair.Proper.representation targetFirstAt targetMemberAt).existsTy
    let continuation : InterfaceMap.Continuation finalContext
        memberRelation.target answer := by
      simpa only [memberRelation, AtomicSubtyping.top, topShape] using
        properTopPackageContinuation targetFirstAt targetFirstInterface
    have result := memberRelation.relation.interfaceMap.run_hasType
      sourceMemberInterfaceAt answer continuation
    rw [Package.existsTy_rename]
    rw [targetTopRepresentationAtSource_rename]
    exact result

private noncomputable def properTopNestedBody
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember) :
    Path.Body (sourceOpenedContext base sourceFirst sourceMember)
      (targetProperRepresentationAtSource sourceFirst sourceMember
        targetFirst (topShape targetFirst.scope)).existsTy :=
  let relationAt := adjustedFirstRelationAtSource
    (sourceMember := sourceMember) firstRelation
  let sourceInterface : Shape.Interface
      (sourceOpenedContext base sourceFirst sourceMember)
      ((sourceFirstAtBinder sourceFirst).rename
        (sourceOpening sourceFirst sourceMember)) := by
    simpa only [properOpening, sourceFirstAtBinder,
      Shape.rename_comp] using
        openedSourceFirstInterface base sourceFirst sourceMember
  let continuation := properTopFirstContinuation sourceFirst sourceMember
    targetFirst sourceMemberRep
  {
    expression := relationAt.interfaceMap.run sourceInterface
      (targetProperRepresentationAtSource sourceFirst sourceMember
        targetFirst (topShape targetFirst.scope)).existsTy continuation
    typing := relationAt.interfaceMap.run_hasType sourceInterface
      (targetProperRepresentationAtSource sourceFirst sourceMember
        targetFirst (topShape targetFirst.scope)).existsTy continuation
  }

private noncomputable def fromSuffixExp_hasType
    (first : Telescope sig) (suffix : Telescope first.scope)
    {base : Ctx sig} {expression : Exp suffix.scope}
    {type : Ty suffix.scope}
    (typing : Exp.HasType (suffix.context (first.context base))
      expression type) :
    Exp.HasType ((first.append suffix).context base)
      (Pair.fromSuffixExp first suffix expression)
      (Pair.fromSuffixTy first suffix type) := by
  induction first with
  | nil => exact typing
  | var parameter tail ih => exact ih suffix typing
  | tvar tail ih => exact ih suffix typing
  | cvar source target tail ih => exact ih suffix typing

private theorem Ty.cast_rename_target
    {source firstTarget secondTarget : Sig}
    (equal : firstTarget = secondTarget) (type : Ty source)
    (mapping : Rename source firstTarget) :
    cast (congrArg Ty equal) (type.rename mapping) =
      type.rename (cast (congrArg (Rename source) equal) mapping) := by
  cases equal
  rfl

private theorem cast_symm_eq
    {index : Sort u} {family : index -> Sort v}
    {firstIndex secondIndex : index} (equal : firstIndex = secondIndex)
    {first : family firstIndex} {second : family secondIndex}
    (forward : cast (congrArg family equal) first = second) :
    cast (congrArg family equal.symm) second = first := by
  cases equal
  exact forward.symm

private theorem fromSuffixTy_weaken
    (first : Telescope sig) (suffix : Telescope first.scope)
    (type : Ty sig) :
    Pair.fromSuffixTy first suffix
        ((type.rename first.weaken).rename suffix.weaken) =
      type.rename ((first.append suffix).weaken) := by
  unfold Pair.fromSuffixTy
  rw [Ty.rename_comp]
  rw [Ty.cast_rename_target (first.appendScopeEq suffix).symm type
    (first.weaken.comp suffix.weaken)]
  exact congrArg (Ty.rename type)
    (cast_symm_eq (first.appendScopeEq suffix)
      (first.append_weaken suffix))

private noncomputable def properTopOpenedBody
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember) :
    Exp (properRepresentationAtBinder sourceFirst sourceMember).scope :=
  Pair.fromSuffixExp (sourceFirstAtBinder sourceFirst).binders
    (sourceMemberAtBinder sourceFirst sourceMember).binders
    (properTopNestedBody firstRelation sourceMemberRep).expression

private noncomputable def properTopOpenedBody_hasType
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember) :
    Exp.HasType
      ((properRepresentationAtBinder sourceFirst sourceMember).context
        (base.bindVar
          (Pair.Proper.representation sourceFirst sourceMember).existsTy))
      (properTopOpenedBody firstRelation sourceMemberRep)
      ((properRepresentationAtBinder targetFirst
        (topShape targetFirst.scope)).existsTy.rename
          (properRepresentationAtBinder sourceFirst sourceMember).weaken) := by
  let firstTele := (sourceFirstAtBinder sourceFirst).binders
  let memberTele := (sourceMemberAtBinder sourceFirst sourceMember).binders
  have nested := (properTopNestedBody firstRelation sourceMemberRep).typing
  have transported := fromSuffixExp_hasType firstTele memberTele nested
  have targetEq :
      (targetProperRepresentationAtSource sourceFirst sourceMember targetFirst
        (topShape targetFirst.scope)).existsTy =
      (((properRepresentationAtBinder targetFirst
        (topShape targetFirst.scope)).existsTy.rename firstTele.weaken).rename
          memberTele.weaken) := by
    rw [← targetProperRepresentationAtSource_eq]
    rw [← Package.existsTy_rename]
    unfold sourceOpening
    rw [Ty.rename_comp]
    rfl
  have finalTypeEq :
      Pair.fromSuffixTy firstTele memberTele
        (targetProperRepresentationAtSource sourceFirst sourceMember
          targetFirst (topShape targetFirst.scope)).existsTy =
      (properRepresentationAtBinder targetFirst
        (topShape targetFirst.scope)).existsTy.rename
          (properRepresentationAtBinder sourceFirst sourceMember).weaken := by
    calc
      Pair.fromSuffixTy firstTele memberTele
          (targetProperRepresentationAtSource sourceFirst sourceMember
            targetFirst (topShape targetFirst.scope)).existsTy =
        Pair.fromSuffixTy firstTele memberTele
          (((properRepresentationAtBinder targetFirst
            (topShape targetFirst.scope)).existsTy.rename
              firstTele.weaken).rename memberTele.weaken) :=
        congrArg (Pair.fromSuffixTy firstTele memberTele) targetEq
      _ = (properRepresentationAtBinder targetFirst
          (topShape targetFirst.scope)).existsTy.rename
            (firstTele.append memberTele).weaken :=
        fromSuffixTy_weaken firstTele memberTele _
      _ = _ := rfl
  exact finalTypeEq ▸ transported

private noncomputable def properRepresentationVariable_hasType
    (base : Ctx sig) (first : Shape sig) (member : Shape first.scope) :
    Exp.HasType
      (base.bindVar (Pair.Proper.representation first member).existsTy)
      (.var .here) (properRepresentationAtBinder first member).existsTy := by
  have variableTyping : Exp.HasType
      (base.bindVar (Pair.Proper.representation first member).existsTy)
      (.var .here)
      ((Pair.Proper.representation first member).existsTy.weaken .var) :=
    .var Ctx.Lookup.here
  rw [Ty.weaken, Package.existsTy_rename,
    properRepresentationAtBinder_eq] at variableTyping
  exact variableTyping

private noncomputable def properTopRepresentationBody
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember) : Exp (sig ,, .var) :=
  (properRepresentationAtBinder sourceFirst sourceMember).unpack (.var .here)
    (properRepresentationAtBinder targetFirst
      (topShape targetFirst.scope)).existsTy
    (properTopOpenedBody firstRelation sourceMemberRep)

private noncomputable def properTopRepresentationBody_hasType
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember) :
    Exp.HasType
      (base.bindVar (Pair.Proper.representation sourceFirst sourceMember).existsTy)
      (properTopRepresentationBody firstRelation sourceMemberRep)
      ((Pair.Proper.representation targetFirst
        (topShape targetFirst.scope)).existsTy.weaken .var) := by
  have result :=
    (properRepresentationAtBinder sourceFirst sourceMember).unpack_hasType
      (properRepresentationVariable_hasType base sourceFirst sourceMember)
      (properTopOpenedBody_hasType firstRelation sourceMemberRep)
  rw [Ty.weaken, Package.existsTy_rename,
    properRepresentationAtBinder_eq]
  exact result

private noncomputable def properTopRepresentationConversion
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember) :
    Conversion base
      (Pair.Proper.representation sourceFirst sourceMember).existsTy
      (Pair.Proper.representation targetFirst
        (topShape targetFirst.scope)).existsTy :=
  Conversion.ofFunction
    (Adapter.ofBody
      (Pair.Proper.representation sourceFirst sourceMember).existsTy
      (properTopRepresentationBody firstRelation sourceMemberRep))
    (Adapter.ofBody_hasType
      (properTopRepresentationBody_hasType firstRelation sourceMemberRep))

noncomputable def properTop
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember) :
    Relation base
      (.Pair sourceFirstType label (.ty sourceMemberType))
      (.Pair targetFirstType label (.ty .Top))
      (.stable (Pair.Proper.plan sourceFirst sourceMember))
      (.stable (Pair.Proper.plan targetFirst
        (topShape targetFirst.scope))) :=
  let sourceRepresentation :=
    Pair.Proper.representation sourceFirst sourceMember
  let targetMember := topShape targetFirst.scope
  let targetRepresentation :=
    Pair.Proper.representation targetFirst targetMember
  let representation := properTopRepresentationConversion
    firstRelation sourceMemberRep
  let conversion := Conversion.Pair.retarget base sourceRepresentation
    targetRepresentation representation
  Relation.ofConversion
    (.properPair firstRelation.sourceRep sourceMemberRep)
    (.properPair firstRelation.targetRep
      (.top (targetFirst.context base)))
    conversion

/-! ## Interval-member source opening -/

private def intervalLowerAtBinder (first : Shape sig)
    (lower : Shape first.scope) :
    Shape (sourceFirstAtBinder first).scope :=
  lower.rename (first.liftRename (Rename.weaken .var))

private def intervalUpperAtBinder (first : Shape sig)
    (upper : Shape first.scope) :
    Shape (sourceFirstAtBinder first).scope :=
  upper.rename (first.liftRename (Rename.weaken .var))

private def intervalMemberAtBinder (first : Shape sig)
    (lower upper : Shape first.scope) :
    Telescope (sourceFirstAtBinder first).scope :=
  Pair.Interval.memberTelescope
    (intervalLowerAtBinder first lower)
    (intervalUpperAtBinder first upper)

private def intervalRepresentationAtBinder (first : Shape sig)
    (lower upper : Shape first.scope) : Telescope (sig ,, .var) :=
  Pair.Interval.representation (sourceFirstAtBinder first)
    (intervalLowerAtBinder first lower)
    (intervalUpperAtBinder first upper)

private theorem intervalRepresentationAtBinder_eq (first : Shape sig)
    (lower upper : Shape first.scope) :
    (Pair.Interval.representation first lower upper).rename
        (Rename.weaken .var) =
      intervalRepresentationAtBinder first lower upper :=
  Pair.Interval.representation_rename first lower upper
    (Rename.weaken .var)

private def intervalSourceOpening (first : Shape sig)
    (lower upper : Shape first.scope) :
    Rename (sig ,, .var) (intervalMemberAtBinder first lower upper).scope :=
  (sourceFirstAtBinder first).binders.weaken.comp
    (intervalMemberAtBinder first lower upper).weaken

private def intervalOpening (first : Shape sig)
    (lower upper : Shape first.scope) :
    Rename sig (intervalMemberAtBinder first lower upper).scope :=
  (Rename.weaken .var).comp (intervalSourceOpening first lower upper)

private def intervalSourceOpenedContext (base : Ctx sig)
    (first : Shape sig) (lower upper : Shape first.scope) :
    Ctx (intervalMemberAtBinder first lower upper).scope :=
  (intervalMemberAtBinder first lower upper).context
    ((sourceFirstAtBinder first).context
      (base.bindVar
        (Pair.Interval.representation first lower upper).existsTy))

private noncomputable def intervalOpening_typed (base : Ctx sig)
    (first : Shape sig) (lower upper : Shape first.scope) :
    Rename.Typed base (intervalSourceOpenedContext base first lower upper)
      (intervalOpening first lower upper) :=
  TypedRename.comp
    (Rename.Typed.weaken base
      (.var (Pair.Interval.representation first lower upper).existsTy))
    (TypedRename.comp
      ((sourceFirstAtBinder first).binders.weaken_typed
        (base.bindVar
          (Pair.Interval.representation first lower upper).existsTy))
      ((intervalMemberAtBinder first lower upper).weaken_typed
        ((sourceFirstAtBinder first).context
          (base.bindVar
            (Pair.Interval.representation first lower upper).existsTy))))

private noncomputable def intervalSourceOpening_typed (base : Ctx sig)
    (first : Shape sig) (lower upper : Shape first.scope) :
    Rename.Typed
      (base.bindVar (Pair.Interval.representation first lower upper).existsTy)
      (intervalSourceOpenedContext base first lower upper)
      (intervalSourceOpening first lower upper) :=
  TypedRename.comp
    ((sourceFirstAtBinder first).binders.weaken_typed
      (base.bindVar
        (Pair.Interval.representation first lower upper).existsTy))
    ((intervalMemberAtBinder first lower upper).weaken_typed
      ((sourceFirstAtBinder first).context
        (base.bindVar
          (Pair.Interval.representation first lower upper).existsTy)))

private noncomputable def intervalSourceFirstInterface (base : Ctx sig)
    (first : Shape sig) (lower upper : Shape first.scope) :
    Shape.Interface (intervalSourceOpenedContext base first lower upper)
      ((sourceFirstAtBinder first).rename
        (intervalSourceOpening first lower upper)) := by
  let immediate := Shape.Interface.canonical
    (base.bindVar
      (Pair.Interval.representation first lower upper).existsTy)
    (sourceFirstAtBinder first)
  have renamed := immediate.rename
    (intervalMemberAtBinder first lower upper).weaken
    ((intervalMemberAtBinder first lower upper).weaken_typed
      ((sourceFirstAtBinder first).context
        (base.bindVar
          (Pair.Interval.representation first lower upper).existsTy)))
  simpa only [intervalSourceOpening, Shape.rename_comp] using renamed

private def intervalLowerActual (first : Shape sig)
    (lower upper : Shape first.scope) :
    Shape (intervalMemberAtBinder first lower upper).scope :=
  (intervalLowerAtBinder first lower).rename
    (intervalMemberAtBinder first lower upper).weaken

private def intervalUpperActual (first : Shape sig)
    (lower upper : Shape first.scope) :
    Shape (intervalMemberAtBinder first lower upper).scope :=
  (intervalUpperAtBinder first upper).rename
    (intervalMemberAtBinder first lower upper).weaken

private def intervalSelectedActual (first : Shape sig)
    (lower upper : Shape first.scope) :
    Shape (intervalMemberAtBinder first lower upper).scope :=
  .opaque (Pair.Interval.selectedTy
    (intervalLowerAtBinder first lower)
    (intervalUpperAtBinder first upper))

private noncomputable def openedIntervalWitness (base : Ctx sig)
    (first : Shape sig) (lower upper : Shape first.scope) :
    Conversion.Interval.Witness
      (intervalSourceOpenedContext base first lower upper)
      (intervalLowerActual first lower upper)
      (intervalUpperActual first lower upper) where
  selected := intervalSelectedActual first lower upper
  lowerFunction := Pair.Interval.lowerFunction
    (intervalLowerAtBinder first lower)
    (intervalUpperAtBinder first upper)
  lowerTyping := by
    simpa only [intervalSourceOpenedContext, intervalMemberAtBinder,
      intervalLowerActual, intervalSelectedActual,
      Shape.inputTy_rename,
      Pair.Interval.lowerTy, Pair.Interval.selectedShape,
      Pair.Interval.selectedTy] using
      Pair.Interval.lowerFunction_hasType
        ((sourceFirstAtBinder first).context
          (base.bindVar
            (Pair.Interval.representation first lower upper).existsTy))
        (intervalLowerAtBinder first lower)
        (intervalUpperAtBinder first upper)
  upperFunction := Pair.Interval.upperFunction
    (intervalLowerAtBinder first lower)
    (intervalUpperAtBinder first upper)
  upperTyping := by
    simpa only [intervalSourceOpenedContext, intervalMemberAtBinder,
      intervalUpperActual, intervalSelectedActual,
      Shape.inputTy_rename,
      Pair.Interval.upperTy, Pair.Interval.selectedShape,
      Pair.Interval.selectedTy] using
      Pair.Interval.upperFunction_hasType
        ((sourceFirstAtBinder first).context
          (base.bindVar
            (Pair.Interval.representation first lower upper).existsTy))
        (intervalLowerAtBinder first lower)
        (intervalUpperAtBinder first upper)

private def targetIntervalFirstAtSource
    (sourceFirst : Shape sig) (sourceLower sourceUpper : Shape sourceFirst.scope)
    (targetFirst : Shape sig) :
    Shape (intervalMemberAtBinder sourceFirst sourceLower sourceUpper).scope :=
  (sourceFirstAtBinder targetFirst).rename
    (intervalSourceOpening sourceFirst sourceLower sourceUpper)

private def targetIntervalLowerAtSource
    (sourceFirst : Shape sig) (sourceLower sourceUpper : Shape sourceFirst.scope)
  (targetFirst : Shape sig) (targetLower : Shape targetFirst.scope) :
    Shape (targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).scope :=
  (intervalLowerAtBinder targetFirst targetLower).rename
    ((sourceFirstAtBinder targetFirst).liftRename
      (intervalSourceOpening sourceFirst sourceLower sourceUpper))

private def targetIntervalUpperAtSource
    (sourceFirst : Shape sig) (sourceLower sourceUpper : Shape sourceFirst.scope)
    (targetFirst : Shape sig) (targetUpper : Shape targetFirst.scope) :
    Shape (targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).scope :=
  (intervalUpperAtBinder targetFirst targetUpper).rename
    ((sourceFirstAtBinder targetFirst).liftRename
      (intervalSourceOpening sourceFirst sourceLower sourceUpper))

/-! Public callback indices for delayed interval members.  As above, only
the callback's already-computed types are named. -/

namespace IntervalMemberCompiler

abbrev CallbackSig (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope) : Sig :=
  (intervalMemberAtBinder sourceFirst sourceLower sourceUpper).scope

abbrev CallbackContext (base : Ctx sig) (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope) :
    Ctx (CallbackSig sourceFirst sourceLower sourceUpper) :=
  intervalSourceOpenedContext base sourceFirst sourceLower sourceUpper

abbrev SourceFirstAt (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope) {final : Sig}
    (mapping : Rename
      (CallbackSig sourceFirst sourceLower sourceUpper) final) : Shape final :=
  ((sourceFirstAtBinder sourceFirst).rename
    (intervalSourceOpening sourceFirst sourceLower sourceUpper)).rename mapping

abbrev TargetFirstAt (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope)
    (targetFirst : Shape sig) {final : Sig}
    (mapping : Rename
      (CallbackSig sourceFirst sourceLower sourceUpper) final) : Shape final :=
  (targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
    targetFirst).rename mapping

end IntervalMemberCompiler

private def targetIntervalRepresentationAtSource
    (sourceFirst : Shape sig) (sourceLower sourceUpper : Shape sourceFirst.scope)
    (targetFirst : Shape sig)
    (targetLower targetUpper : Shape targetFirst.scope) :
    Telescope (intervalMemberAtBinder sourceFirst sourceLower sourceUpper).scope :=
  Pair.Interval.representation
    (targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst)
    (targetIntervalLowerAtSource sourceFirst sourceLower sourceUpper
      targetFirst targetLower)
    (targetIntervalUpperAtSource sourceFirst sourceLower sourceUpper
      targetFirst targetUpper)

private theorem targetIntervalRepresentationAtSource_eq
    (sourceFirst : Shape sig) (sourceLower sourceUpper : Shape sourceFirst.scope)
    (targetFirst : Shape sig)
    (targetLower targetUpper : Shape targetFirst.scope) :
    (intervalRepresentationAtBinder targetFirst targetLower targetUpper).rename
        (intervalSourceOpening sourceFirst sourceLower sourceUpper) =
      targetIntervalRepresentationAtSource sourceFirst sourceLower sourceUpper
        targetFirst targetLower targetUpper :=
  Pair.Interval.representation_rename
    (sourceFirstAtBinder targetFirst)
    (intervalLowerAtBinder targetFirst targetLower)
    (intervalUpperAtBinder targetFirst targetUpper)
    (intervalSourceOpening sourceFirst sourceLower sourceUpper)

private noncomputable def adjustedIntervalFirstRelationAtSource
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {base : Ctx sig}
    (relation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst) :
    Relation (intervalSourceOpenedContext base sourceFirst sourceLower sourceUpper)
      sourceFirstType targetFirstType
      ((sourceFirstAtBinder sourceFirst).rename
        (intervalSourceOpening sourceFirst sourceLower sourceUpper))
      (targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst) := by
  let renamed := relation.targetRename
    (intervalOpening sourceFirst sourceLower sourceUpper)
    (intervalOpening_typed base sourceFirst sourceLower sourceUpper)
  simpa only [intervalOpening, sourceFirstAtBinder,
    targetIntervalFirstAtSource, Shape.rename_comp] using renamed

private def intervalEndpointOpening (first : Shape sig)
    (lower upper : Shape first.scope) :
    Rename first.scope (intervalMemberAtBinder first lower upper).scope :=
  (first.liftRename (Rename.weaken .var)).comp
    (intervalMemberAtBinder first lower upper).weaken

private noncomputable def intervalEndpointOpening_typed (base : Ctx sig)
    (first : Shape sig) (lower upper : Shape first.scope) :
    Rename.Typed (first.context base)
      (intervalSourceOpenedContext base first lower upper)
      (intervalEndpointOpening first lower upper) :=
  TypedRename.comp
    (first.liftRename_typed
      (Rename.Typed.weaken base
        (.var (Pair.Interval.representation first lower upper).existsTy)))
    ((intervalMemberAtBinder first lower upper).weaken_typed
      ((sourceFirstAtBinder first).context
        (base.bindVar
          (Pair.Interval.representation first lower upper).existsTy)))

private noncomputable def openedIntervalLowerRep
    {lowerType : LambdaPFC.Ty (n + 1)}
    (base : Ctx sig) (first : Shape sig)
    (lower upper : Shape first.scope)
    (lowerRep : Rep (first.context base) lowerType lower) :
    Rep (intervalSourceOpenedContext base first lower upper) lowerType
      (intervalLowerActual first lower upper) := by
  let renamed := lowerRep.targetRename
    (intervalEndpointOpening first lower upper)
    (intervalEndpointOpening_typed base first lower upper)
  unfold intervalLowerActual intervalLowerAtBinder
  change Rep _ _
    (lower.rename ((first.liftRename (Rename.weaken .var)).comp
      (Pair.Interval.memberTelescope
        (lower.rename (first.liftRename (Rename.weaken .var)))
        (upper.rename (first.liftRename (Rename.weaken .var)))).weaken))
      at renamed
  rw [← Shape.rename_comp] at renamed
  exact renamed

private noncomputable def openedIntervalUpperRep
    {upperType : LambdaPFC.Ty (n + 1)}
    (base : Ctx sig) (first : Shape sig)
    (lower upper : Shape first.scope)
    (upperRep : Rep (first.context base) upperType upper) :
    Rep (intervalSourceOpenedContext base first lower upper) upperType
      (intervalUpperActual first lower upper) := by
  let renamed := upperRep.targetRename
    (intervalEndpointOpening first lower upper)
    (intervalEndpointOpening_typed base first lower upper)
  unfold intervalUpperActual intervalUpperAtBinder
  change Rep _ _
    (upper.rename ((first.liftRename (Rename.weaken .var)).comp
      (Pair.Interval.memberTelescope
        (lower.rename (first.liftRename (Rename.weaken .var)))
        (upper.rename (first.liftRename (Rename.weaken .var)))).weaken))
      at renamed
  rw [← Shape.rename_comp] at renamed
  exact renamed

private noncomputable def renameIntervalWitness
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {lower upper : Shape source}
    (witness : Conversion.Interval.Witness sourceContext lower upper)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Conversion.Interval.Witness targetContext
      (lower.rename mapping) (upper.rename mapping) where
  selected := witness.selected.rename mapping
  lowerFunction := witness.lowerFunction.rename mapping
  lowerTyping := by
    simpa only [Ty.rename, Shape.inputTy_rename] using
      witness.lowerTyping.rename typed
  upperFunction := witness.upperFunction.rename mapping
  upperTyping := by
    simpa only [Ty.rename, Shape.inputTy_rename] using
      witness.upperTyping.rename typed

private noncomputable def targetIntervalEndpointRepAt
    {endpointType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst : Shape sig} {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetFirst : Shape sig} {targetEndpoint : Shape targetFirst.scope}
    (endpointRep : Rep (targetFirst.context base)
      endpointType targetEndpoint)
    {final : Sig} (mapping : Rename
      (intervalMemberAtBinder sourceFirst sourceLower sourceUpper).scope final)
    {finalContext : Ctx final}
    (typed : Rename.Typed
      (intervalSourceOpenedContext base sourceFirst sourceLower sourceUpper)
      finalContext mapping)
    (targetFirstInterface : Shape.Interface finalContext
      ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).rename mapping)) :
    Rep finalContext endpointType
      (((targetIntervalLowerAtSource sourceFirst sourceLower sourceUpper
        targetFirst targetEndpoint).rename
          ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
            targetFirst).liftRename mapping)).subst
        targetFirstInterface.substitution) := by
  let atBinder := endpointRep.targetRename
    (targetFirst.liftRename (Rename.weaken .var))
    (targetFirst.liftRename_typed
      (Rename.Typed.weaken base
        (.var (Pair.Interval.representation sourceFirst sourceLower
          sourceUpper).existsTy)))
  let atSource := atBinder.targetRename
    ((sourceFirstAtBinder targetFirst).liftRename
      (intervalSourceOpening sourceFirst sourceLower sourceUpper))
    ((sourceFirstAtBinder targetFirst).liftRename_typed
      (intervalSourceOpening_typed base sourceFirst sourceLower sourceUpper))
  let atFinal := atSource.targetRename
    ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).liftRename mapping)
    ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).liftRename_typed typed)
  exact atFinal.targetSubst targetFirstInterface.substitution
    targetFirstInterface.arguments.substitution_typed

private noncomputable def sourceIntervalAt
    {lowerType upperType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {first : Shape sig} {lower upper : Shape first.scope}
    (lowerRep : Rep (first.context base) lowerType lower)
    (upperRep : Rep (first.context base) upperType upper)
    {final : Sig}
    (mapping : Rename (intervalMemberAtBinder first lower upper).scope final)
    {finalContext : Ctx final}
    (typed : Rename.Typed
      (intervalSourceOpenedContext base first lower upper)
      finalContext mapping) :
    Wf.Interval finalContext lowerType upperType :=
  let opened : Wf.Interval
      (intervalSourceOpenedContext base first lower upper)
      lowerType upperType := {
    lower := intervalLowerActual first lower upper
    upper := intervalUpperActual first lower upper
    lowerRep := openedIntervalLowerRep base first lower upper lowerRep
    upperRep := openedIntervalUpperRep base first lower upper upperRep
  }
  opened.targetRename mapping typed

private theorem targetBotTopIntervalRepresentationAtSource_rename
    (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope)
    (targetFirst : Shape sig)
    (mapping : Rename
      (intervalMemberAtBinder sourceFirst sourceLower sourceUpper).scope
      target) :
    (targetIntervalRepresentationAtSource sourceFirst sourceLower sourceUpper
      targetFirst (bottomShape targetFirst.scope)
      (topShape targetFirst.scope)).rename mapping =
      Pair.Interval.representation
        ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
          targetFirst).rename mapping)
        (bottomShape
          ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
            targetFirst).rename mapping).scope)
        (topShape
          ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
            targetFirst).rename mapping).scope) := by
  unfold targetIntervalRepresentationAtSource
  rw [Pair.Interval.representation_rename]
  unfold targetIntervalLowerAtSource targetIntervalUpperAtSource
    intervalLowerAtBinder intervalUpperAtBinder sourceFirstAtBinder
    targetIntervalFirstAtSource bottomShape topShape
    Shape.liftRename Shape.rename
  cases targetFirst <;> rfl

private noncomputable def intervalBotTopFirstContinuation
    {sourceLowerType sourceUpperType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope)
    (targetFirst : Shape sig)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper) :
    InterfaceMap.Continuation
      (intervalSourceOpenedContext base sourceFirst sourceLower sourceUpper)
      (targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst)
      (targetIntervalRepresentationAtSource sourceFirst sourceLower sourceUpper
        targetFirst (bottomShape targetFirst.scope)
        (topShape targetFirst.scope)).existsTy where
  body mapping finalContext typed targetFirstInterface :=
    let source := sourceIntervalAt sourceLowerRep sourceUpperRep mapping typed
    let targetFirstAt :=
      (targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).rename mapping
    let lowerResult := AtomicSubtyping.bot {
      shape := source.lower
      rep := source.lowerRep
    }
    let upperResult := AtomicSubtyping.top {
      shape := source.upper
      rep := source.upperRep
    }
    let target : Wf.Interval finalContext (.Bot : LambdaPFC.Ty (n + 1))
        (.Top : LambdaPFC.Ty (n + 1)) := {
      lower := lowerResult.source
      upper := upperResult.target
      lowerRep := lowerResult.relation.sourceRep
      upperRep := upperResult.relation.targetRep
    }
    let relation : AtomicSubtyping.IntervalRelation source target := {
      lower := lowerResult.relation
      upper := upperResult.relation
    }
    let witnessAt := renameIntervalWitness
      (openedIntervalWitness base sourceFirst sourceLower sourceUpper)
      mapping typed
    let mapped := relation.mapWitness witnessAt
    let targetLowerFamily := bottomShape targetFirstAt.scope
    let targetUpperFamily := topShape targetFirstAt.scope
    Telescope.pack (Pair.Interval.representationArguments targetFirstAt
      targetLowerFamily targetUpperFamily targetFirstInterface mapped.selected
      mapped.lowerFunction (by
        simpa only [targetLowerFamily, target, lowerResult,
          AtomicSubtyping.bot, bottomShape, Shape.subst,
          Bot.plan_subst] using mapped.lowerTyping)
      mapped.upperFunction (by
        simpa only [targetUpperFamily, target, upperResult,
          AtomicSubtyping.top, topShape, Shape.subst,
          Top.plan_subst] using mapped.upperTyping))
  body_hasType mapping finalContext typed targetFirstInterface := by
    let source := sourceIntervalAt sourceLowerRep sourceUpperRep mapping typed
    let targetFirstAt :=
      (targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).rename mapping
    let lowerResult := AtomicSubtyping.bot {
      shape := source.lower
      rep := source.lowerRep
    }
    let upperResult := AtomicSubtyping.top {
      shape := source.upper
      rep := source.upperRep
    }
    let target : Wf.Interval finalContext (.Bot : LambdaPFC.Ty (n + 1))
        (.Top : LambdaPFC.Ty (n + 1)) := {
      lower := lowerResult.source
      upper := upperResult.target
      lowerRep := lowerResult.relation.sourceRep
      upperRep := upperResult.relation.targetRep
    }
    let relation : AtomicSubtyping.IntervalRelation source target := {
      lower := lowerResult.relation
      upper := upperResult.relation
    }
    let witnessAt := renameIntervalWitness
      (openedIntervalWitness base sourceFirst sourceLower sourceUpper)
      mapping typed
    let mapped := relation.mapWitness witnessAt
    let targetLowerFamily := bottomShape targetFirstAt.scope
    let targetUpperFamily := topShape targetFirstAt.scope
    have packed := Telescope.pack_hasType
      (Pair.Interval.representationArguments targetFirstAt
        targetLowerFamily targetUpperFamily targetFirstInterface
        mapped.selected mapped.lowerFunction (by
          simpa only [targetLowerFamily, target, lowerResult,
            AtomicSubtyping.bot, bottomShape, Shape.subst,
            Bot.plan_subst] using mapped.lowerTyping)
        mapped.upperFunction (by
          simpa only [targetUpperFamily, target, upperResult,
            AtomicSubtyping.top, topShape, Shape.subst,
            Top.plan_subst] using mapped.upperTyping))
    rw [Package.existsTy_rename]
    rw [targetBotTopIntervalRepresentationAtSource_rename]
    exact packed

private noncomputable def intervalBotTopNestedBody
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper) :
    Path.Body
      (intervalSourceOpenedContext base sourceFirst sourceLower sourceUpper)
      (targetIntervalRepresentationAtSource sourceFirst sourceLower sourceUpper
        targetFirst (bottomShape targetFirst.scope)
        (topShape targetFirst.scope)).existsTy :=
  let relationAt := adjustedIntervalFirstRelationAtSource firstRelation
  let sourceInterface := intervalSourceFirstInterface base sourceFirst
    sourceLower sourceUpper
  let continuation := intervalBotTopFirstContinuation sourceFirst sourceLower
    sourceUpper targetFirst sourceLowerRep sourceUpperRep
  {
    expression := relationAt.interfaceMap.run sourceInterface
      (targetIntervalRepresentationAtSource sourceFirst sourceLower sourceUpper
        targetFirst (bottomShape targetFirst.scope)
        (topShape targetFirst.scope)).existsTy continuation
    typing := relationAt.interfaceMap.run_hasType sourceInterface
      (targetIntervalRepresentationAtSource sourceFirst sourceLower sourceUpper
        targetFirst (bottomShape targetFirst.scope)
        (topShape targetFirst.scope)).existsTy continuation
  }

private noncomputable def intervalBotTopOpenedBody
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper) :
    Exp (intervalRepresentationAtBinder sourceFirst sourceLower
      sourceUpper).scope :=
  Pair.fromSuffixExp (sourceFirstAtBinder sourceFirst).binders
    (intervalMemberAtBinder sourceFirst sourceLower sourceUpper)
    (intervalBotTopNestedBody firstRelation sourceLowerRep
      sourceUpperRep).expression

private noncomputable def intervalBotTopOpenedBody_hasType
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper) :
    Exp.HasType
      ((intervalRepresentationAtBinder sourceFirst sourceLower
        sourceUpper).context
          (base.bindVar
            (Pair.Interval.representation sourceFirst sourceLower
              sourceUpper).existsTy))
      (intervalBotTopOpenedBody firstRelation sourceLowerRep sourceUpperRep)
      ((intervalRepresentationAtBinder targetFirst
        (bottomShape targetFirst.scope)
        (topShape targetFirst.scope)).existsTy.rename
          (intervalRepresentationAtBinder sourceFirst sourceLower
            sourceUpper).weaken) := by
  let firstTele := (sourceFirstAtBinder sourceFirst).binders
  let memberTele := intervalMemberAtBinder sourceFirst sourceLower sourceUpper
  have nested := (intervalBotTopNestedBody firstRelation sourceLowerRep
    sourceUpperRep).typing
  have transported := fromSuffixExp_hasType firstTele memberTele nested
  have targetEq :
      (targetIntervalRepresentationAtSource sourceFirst sourceLower sourceUpper
        targetFirst (bottomShape targetFirst.scope)
        (topShape targetFirst.scope)).existsTy =
      (((intervalRepresentationAtBinder targetFirst
        (bottomShape targetFirst.scope)
        (topShape targetFirst.scope)).existsTy.rename firstTele.weaken).rename
          memberTele.weaken) := by
    rw [← targetIntervalRepresentationAtSource_eq]
    rw [← Package.existsTy_rename]
    unfold intervalSourceOpening
    rw [Ty.rename_comp]
  have finalTypeEq :
      Pair.fromSuffixTy firstTele memberTele
        (targetIntervalRepresentationAtSource sourceFirst sourceLower
          sourceUpper targetFirst (bottomShape targetFirst.scope)
          (topShape targetFirst.scope)).existsTy =
      (intervalRepresentationAtBinder targetFirst
        (bottomShape targetFirst.scope)
        (topShape targetFirst.scope)).existsTy.rename
          (intervalRepresentationAtBinder sourceFirst sourceLower
            sourceUpper).weaken := by
    calc
      Pair.fromSuffixTy firstTele memberTele
          (targetIntervalRepresentationAtSource sourceFirst sourceLower
            sourceUpper targetFirst (bottomShape targetFirst.scope)
            (topShape targetFirst.scope)).existsTy =
        Pair.fromSuffixTy firstTele memberTele
          (((intervalRepresentationAtBinder targetFirst
            (bottomShape targetFirst.scope)
            (topShape targetFirst.scope)).existsTy.rename
              firstTele.weaken).rename memberTele.weaken) :=
        congrArg (Pair.fromSuffixTy firstTele memberTele) targetEq
      _ = (intervalRepresentationAtBinder targetFirst
          (bottomShape targetFirst.scope)
          (topShape targetFirst.scope)).existsTy.rename
            (firstTele.append memberTele).weaken :=
        fromSuffixTy_weaken firstTele memberTele _
      _ = _ := rfl
  exact finalTypeEq ▸ transported

private noncomputable def intervalRepresentationVariable_hasType
    (base : Ctx sig) (first : Shape sig)
    (lower upper : Shape first.scope) :
    Exp.HasType
      (base.bindVar (Pair.Interval.representation first lower upper).existsTy)
      (.var .here) (intervalRepresentationAtBinder first lower upper).existsTy := by
  have variableTyping : Exp.HasType
      (base.bindVar (Pair.Interval.representation first lower upper).existsTy)
      (.var .here)
      ((Pair.Interval.representation first lower upper).existsTy.weaken .var) :=
    .var Ctx.Lookup.here
  rw [Ty.weaken, Package.existsTy_rename,
    intervalRepresentationAtBinder_eq] at variableTyping
  exact variableTyping

private noncomputable def intervalBotTopRepresentationBody
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper) : Exp (sig ,, .var) :=
  (intervalRepresentationAtBinder sourceFirst sourceLower sourceUpper).unpack
    (.var .here)
    (intervalRepresentationAtBinder targetFirst
      (bottomShape targetFirst.scope) (topShape targetFirst.scope)).existsTy
    (intervalBotTopOpenedBody firstRelation sourceLowerRep sourceUpperRep)

private noncomputable def intervalBotTopRepresentationBody_hasType
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper) :
    Exp.HasType
      (base.bindVar
        (Pair.Interval.representation sourceFirst sourceLower
          sourceUpper).existsTy)
      (intervalBotTopRepresentationBody firstRelation sourceLowerRep
        sourceUpperRep)
      ((Pair.Interval.representation targetFirst
        (bottomShape targetFirst.scope)
        (topShape targetFirst.scope)).existsTy.weaken .var) := by
  have result :=
    (intervalRepresentationAtBinder sourceFirst sourceLower sourceUpper).unpack_hasType
      (intervalRepresentationVariable_hasType base sourceFirst sourceLower
        sourceUpper)
      (intervalBotTopOpenedBody_hasType firstRelation sourceLowerRep
        sourceUpperRep)
  rw [Ty.weaken, Package.existsTy_rename,
    intervalRepresentationAtBinder_eq]
  exact result

private noncomputable def intervalBotTopRepresentationConversion
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper) :
    Conversion base
      (Pair.Interval.representation sourceFirst sourceLower sourceUpper).existsTy
      (Pair.Interval.representation targetFirst
        (bottomShape targetFirst.scope)
        (topShape targetFirst.scope)).existsTy :=
  Conversion.ofFunction
    (Adapter.ofBody
      (Pair.Interval.representation sourceFirst sourceLower sourceUpper).existsTy
      (intervalBotTopRepresentationBody firstRelation sourceLowerRep
        sourceUpperRep))
    (Adapter.ofBody_hasType
      (intervalBotTopRepresentationBody_hasType firstRelation sourceLowerRep
        sourceUpperRep))

noncomputable def intervalBotTop
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper) :
    Relation base
      (.Pair sourceFirstType label (.intv sourceLowerType sourceUpperType))
      (.Pair targetFirstType label (.intv .Bot .Top))
      (.stable (Pair.Interval.plan sourceFirst sourceLower sourceUpper))
      (.stable (Pair.Interval.plan targetFirst
        (bottomShape targetFirst.scope) (topShape targetFirst.scope))) :=
  let sourceRepresentation := Pair.Interval.representation sourceFirst
    sourceLower sourceUpper
  let targetLower := bottomShape targetFirst.scope
  let targetUpper := topShape targetFirst.scope
  let targetRepresentation := Pair.Interval.representation targetFirst
    targetLower targetUpper
  let representation := intervalBotTopRepresentationConversion firstRelation
    sourceLowerRep sourceUpperRep
  let conversion := Conversion.Pair.retarget base sourceRepresentation
    targetRepresentation representation
  Relation.ofConversion
    (.intervalPair firstRelation.sourceRep sourceLowerRep sourceUpperRep)
    (.intervalPair firstRelation.targetRep
      (.bottom (targetFirst.context base))
      (.top (targetFirst.context base)))
    conversion

/-! ## Exact singleton-member covariance -/

/-- The exact source member family: the source first shape lifted into its
own opened scope. -/
def liftedFirstFamily (first : Shape sig) : Shape first.scope :=
  first.rename first.binders.weaken

private noncomputable def liftedFirstFamilyRep
    {sourcePath : LambdaPFC.Path n} {base : Ctx sig}
    (first : Shape sig)
    (rep : Rep base (.Single sourcePath) first) :
    Rep (first.context base) (.Single sourcePath.weaken)
      (liftedFirstFamily first) :=
  (rep.sourceRename LambdaPFC.FinFun.weaken).targetRename
    first.binders.weaken (first.binders.weaken_typed base)

/-- The target member family naming the package at the newest first slot. -/
def newestSingletonFamily (first : Shape sig) : Shape first.scope :=
  .stable (Single.plan (first.inputTy.rename first.binders.weaken))

private noncomputable def newestSingletonFamilyRep
    {n : Nat} {base : Ctx sig} (first : Shape sig) :
    Rep (first.context base)
      (.Single (.var (0 : Fin (n + 1))))
      (newestSingletonFamily first) :=
  .singleton (first.context base) (.var 0)
    (first.inputTy.rename first.binders.weaken)

private theorem newestSingletonFamily_rename (first : Shape source)
    (mapping : Rename source target) :
    (newestSingletonFamily first).rename (first.liftRename mapping) =
      newestSingletonFamily (first.rename mapping) := by
  unfold newestSingletonFamily
  rw [Shape.rename, Single.plan_rename]
  congr 2
  cases first with
  | stable plan =>
      simpa only [Shape.inputTy, Shape.rename, Shape.binders,
        Shape.liftRename, Package.Plan.inputTy_rename] using
        plan.telescope.weakenType_liftRename plan.inputTy mapping
  | «opaque» type =>
      simpa only [Shape.inputTy, Shape.rename, Shape.binders,
        Shape.liftRename] using
        (Telescope.var type .nil).weakenType_liftRename type mapping

private theorem newestSingletonFamily_rename3 (first : Shape source)
    (firstMapping : Rename source middle)
    (secondMapping : Rename middle next)
    (thirdMapping : Rename next target) :
    ((((newestSingletonFamily first).rename
        (first.liftRename firstMapping)).rename
          ((first.rename firstMapping).liftRename secondMapping)).rename
            (((first.rename firstMapping).rename secondMapping).liftRename
              thirdMapping)) =
      newestSingletonFamily
        (((first.rename firstMapping).rename secondMapping).rename
          thirdMapping) := by
  calc
    _ = ((newestSingletonFamily (first.rename firstMapping)).rename
          ((first.rename firstMapping).liftRename secondMapping)).rename
            (((first.rename firstMapping).rename secondMapping).liftRename
              thirdMapping) :=
      congrArg (fun current =>
        (current.rename
          ((first.rename firstMapping).liftRename secondMapping)).rename
            (((first.rename firstMapping).rename secondMapping).liftRename
              thirdMapping))
        (newestSingletonFamily_rename first firstMapping)
    _ = (newestSingletonFamily
          ((first.rename firstMapping).rename secondMapping)).rename
            (((first.rename firstMapping).rename secondMapping).liftRename
              thirdMapping) :=
      congrArg (fun current => current.rename
        (((first.rename firstMapping).rename secondMapping).liftRename
          thirdMapping))
        (newestSingletonFamily_rename (first.rename firstMapping)
          secondMapping)
    _ = _ := newestSingletonFamily_rename
      ((first.rename firstMapping).rename secondMapping) thirdMapping

private theorem newestSingletonFamily_subst_interface
    {base : Ctx sig} (first : Shape sig)
    (interface : Shape.Interface base first) :
    (newestSingletonFamily first).subst interface.substitution =
      .stable (Single.plan first.inputTy) := by
  unfold newestSingletonFamily
  rw [Shape.subst, Single.plan_subst]
  congr 2
  have instantiated :=
    interface.arguments.instantiate_weaken first.inputTy
  rw [Telescope.Args.instantiate_eq_subst] at instantiated
  simpa only [Shape.Interface.arguments_substitution] using instantiated

private noncomputable def constantConversion
    {base : Ctx sig} {shape : Shape sig}
    (interface : Shape.Interface base shape) (source : Ty sig) :
    Conversion base source shape.inputTy :=
  let typed := Rename.Typed.weaken base (.var source)
  Conversion.ofFunction
    (Adapter.ofBody source
      (interface.package.rename (Rename.weaken .var)))
    (Adapter.ofBody_hasType (by
      simpa only [Ty.weaken, Shape.inputTy_rename] using
        interface.package_hasType.rename typed))

private theorem liftedFirstActual_eq (first : Shape sig) :
    intervalLowerActual first (liftedFirstFamily first)
        (liftedFirstFamily first) =
      (sourceFirstAtBinder first).rename
        (intervalSourceOpening first (liftedFirstFamily first)
          (liftedFirstFamily first)) := by
  unfold intervalLowerActual intervalLowerAtBinder liftedFirstFamily
    sourceFirstAtBinder intervalSourceOpening
  rw [Shape.rename_comp, Shape.rename_comp, Shape.rename_comp]
  congr 1
  cases first with
  | stable plan =>
      simp only [Shape.binders, Shape.liftRename, Shape.rename,
        sourceFirstAtBinder]
      let suffix := (intervalMemberAtBinder (Shape.stable plan)
        (Shape.stable (plan.rename plan.telescope.weaken))
        (Shape.stable (plan.rename plan.telescope.weaken))).weaken
      calc
        (plan.telescope.weaken.comp
            (plan.telescope.liftRename (Rename.weaken .var))).comp suffix =
          ((Rename.weaken .var).comp
            (plan.telescope.rename (Rename.weaken .var)).weaken).comp
              suffix := congrArg (fun current => current.comp suffix)
                (plan.telescope.weaken_liftRename (Rename.weaken .var))
        _ = (Rename.weaken .var).comp
            ((plan.rename (Rename.weaken .var)).telescope.weaken.comp
              suffix) := by
                simpa only [Package.Plan.telescope_rename] using
                  Rename.comp_assoc (Rename.weaken .var)
                    (plan.telescope.rename (Rename.weaken .var)).weaken suffix
  | «opaque» type =>
      simp only [Shape.binders, Shape.liftRename, Shape.rename,
        sourceFirstAtBinder]
      let tele : Telescope sig := .var type .nil
      let suffix := (intervalMemberAtBinder (Shape.opaque type)
        (Shape.opaque (type.rename tele.weaken))
        (Shape.opaque (type.rename tele.weaken))).weaken
      calc
        (tele.weaken.comp
            (tele.liftRename (Rename.weaken .var))).comp suffix =
          ((Rename.weaken .var).comp
            (tele.rename (Rename.weaken .var)).weaken).comp suffix :=
              congrArg (fun current => current.comp suffix)
                (tele.weaken_liftRename (Rename.weaken .var))
        _ = (Rename.weaken .var).comp
            ((Telescope.var (type.rename (Rename.weaken .var)) .nil).weaken.comp
              suffix) := by
                simpa only [Telescope.rename] using
                  Rename.comp_assoc (Rename.weaken .var)
                    (tele.rename (Rename.weaken .var)).weaken suffix

private theorem liftedFirstUpperActual_eq (first : Shape sig) :
    intervalUpperActual first (liftedFirstFamily first)
        (liftedFirstFamily first) =
      (sourceFirstAtBinder first).rename
        (intervalSourceOpening first (liftedFirstFamily first)
          (liftedFirstFamily first)) := by
  simpa only [intervalUpperActual, intervalLowerActual,
    intervalUpperAtBinder, intervalLowerAtBinder] using
    liftedFirstActual_eq first

private theorem targetSingletonIntervalRepresentationAtSource_rename
    (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope)
    (targetFirst : Shape sig)
    (mapping : Rename
      (intervalMemberAtBinder sourceFirst sourceLower sourceUpper).scope
      target) :
    (targetIntervalRepresentationAtSource sourceFirst sourceLower sourceUpper
      targetFirst (newestSingletonFamily targetFirst)
      (newestSingletonFamily targetFirst)).rename mapping =
      Pair.Interval.representation
        ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
          targetFirst).rename mapping)
        (newestSingletonFamily
          ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
            targetFirst).rename mapping))
        (newestSingletonFamily
          ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
            targetFirst).rename mapping)) := by
  unfold targetIntervalRepresentationAtSource
  rw [Pair.Interval.representation_rename]
  unfold targetIntervalLowerAtSource targetIntervalUpperAtSource
    intervalLowerAtBinder intervalUpperAtBinder
    targetIntervalFirstAtSource sourceFirstAtBinder
  congr 1 <;>
    exact newestSingletonFamily_rename3 targetFirst (Rename.weaken .var)
      (intervalSourceOpening sourceFirst sourceLower sourceUpper) mapping

private noncomputable def singletonSourceWitnessAt
    (base : Ctx sig) (sourceFirst : Shape sig)
    {final : Sig}
    (mapping : Rename
      (intervalMemberAtBinder sourceFirst (liftedFirstFamily sourceFirst)
        (liftedFirstFamily sourceFirst)).scope final)
    {finalContext : Ctx final}
    (typed : Rename.Typed
      (intervalSourceOpenedContext base sourceFirst
        (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst))
      finalContext mapping) :
    Conversion.Interval.Witness finalContext
      (((sourceFirstAtBinder sourceFirst).rename
        (intervalSourceOpening sourceFirst (liftedFirstFamily sourceFirst)
          (liftedFirstFamily sourceFirst))).rename mapping)
      (((sourceFirstAtBinder sourceFirst).rename
        (intervalSourceOpening sourceFirst (liftedFirstFamily sourceFirst)
          (liftedFirstFamily sourceFirst))).rename mapping) := by
  let raw := renameIntervalWitness
    (openedIntervalWitness base sourceFirst (liftedFirstFamily sourceFirst)
      (liftedFirstFamily sourceFirst)) mapping typed
  rw [liftedFirstActual_eq, liftedFirstUpperActual_eq] at raw
  exact raw

private noncomputable def exactWidenRelation
    {sourcePath : LambdaPFC.Path n} {base : Ctx sig}
    {source : Shape sig}
    (newest : LambdaPFC.Path n)
    (sourceRep : Rep base (.Single sourcePath) source) :
    Relation base (.Single newest) (.Single sourcePath)
      (.stable (Single.plan source.inputTy)) source :=
  Relation.ofConversion
    (.singleton base newest source.inputTy) sourceRep
    (Conversion.Singleton.unwrap base source.inputTy)

private noncomputable def exactSymmetryRelation
    {sourcePath : LambdaPFC.Path n} {base : Ctx sig}
    {source : Shape sig}
    (newest : LambdaPFC.Path n)
    (sourceRep : Rep base (.Single sourcePath) source) :
    Relation base (.Single sourcePath) (.Single newest) source
      (.stable (Single.plan source.inputTy)) := by
  cases source with
  | stable plan =>
      cases sourceRep with
      | singleton _ _ referent =>
        exact Relation.ofConversion
          (.singleton base sourcePath referent)
          (.singleton base newest (Single.plan referent).inputTy)
          (Conversion.Singleton.retarget base referent
            (Single.plan referent).inputTy
            (Conversion.Singleton.selfBridge base referent))
  | «opaque» type =>
      exact Relation.ofConversion
        sourceRep (.singleton base newest type)
        (Conversion.Singleton.wrap base type)

private noncomputable def singletonTargetPackageAt
    {sourcePath : LambdaPFC.Path n}
    {targetFirstType : LambdaPFC.Ty n}
    {base : Ctx sig}
    (sourceFirst targetFirst : Shape sig)
    (firstRelation : Relation base (.Single sourcePath) targetFirstType
      sourceFirst targetFirst)
    {final : Sig}
    (mapping : Rename
      (intervalMemberAtBinder sourceFirst (liftedFirstFamily sourceFirst)
        (liftedFirstFamily sourceFirst)).scope final)
    {finalContext : Ctx final}
    (typed : Rename.Typed
      (intervalSourceOpenedContext base sourceFirst
        (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst))
      finalContext mapping)
    (targetFirstInterface : Shape.Interface finalContext
      ((targetIntervalFirstAtSource sourceFirst
        (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst)
        targetFirst).rename mapping)) :
    Path.Body finalContext
      ((targetIntervalRepresentationAtSource sourceFirst
        (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst)
        targetFirst (newestSingletonFamily targetFirst)
        (newestSingletonFamily targetFirst)).existsTy.rename mapping) := by
  let sourceLower := liftedFirstFamily sourceFirst
  let sourceOpeningAt := intervalSourceOpening sourceFirst sourceLower
    sourceLower
  let sourceFirstAt := ((sourceFirstAtBinder sourceFirst).rename
    sourceOpeningAt).rename mapping
  let targetFirstAt := (targetIntervalFirstAtSource sourceFirst sourceLower
    sourceLower targetFirst).rename mapping
  let relationAt := (adjustedIntervalFirstRelationAtSource
    (sourceLower := sourceLower) (sourceUpper := sourceLower)
    firstRelation).targetRename mapping typed
  let sourceInterfaceRaw :=
    (intervalSourceFirstInterface base sourceFirst sourceLower
      sourceLower).rename mapping typed
  let sourceInterface : Shape.Interface finalContext sourceFirstAt := by
    simpa only [sourceFirstAt, sourceOpeningAt] using sourceInterfaceRaw
  let sourceRep : Rep finalContext (.Single sourcePath.weaken)
      sourceFirstAt := relationAt.sourceRep.sourceRename
        LambdaPFC.FinFun.weaken
  let targetSlot : Slot finalContext targetFirstType.weaken := {
    shape := targetFirstAt
    interface := targetFirstInterface
    rep := relationAt.targetRep.sourceRename LambdaPFC.FinFun.weaken
  }
  let targetEndpoint := Wf.Proper.singletonFromSlot
    (.var (0 : Fin (n + 1))) targetSlot
  let sourceToTarget : Conversion finalContext sourceFirstAt.inputTy
      targetFirstAt.inputTy := relationAt.conversion
  let targetToSource : Conversion finalContext targetFirstAt.inputTy
      sourceFirstAt.inputTy :=
    constantConversion sourceInterface targetFirstAt.inputTy
  let bridge : Conversion.Bridge finalContext sourceFirstAt.inputTy
      targetFirstAt.inputTy := {
    leftToRight := sourceToTarget
    rightToLeft := targetToSource
  }
  let widenRelation := exactWidenRelation
    (.var (0 : Fin (n + 1))) sourceRep
  let symmetryRelation := exactSymmetryRelation
    (.var (0 : Fin (n + 1))) sourceRep
  let backward : Relation finalContext
      (.Single (.var (0 : Fin (n + 1))))
      (.Single (.var (0 : Fin (n + 1))))
      targetEndpoint.shape (.stable (Single.plan sourceFirstAt.inputTy)) :=
    Relation.ofConversion targetEndpoint.rep widenRelation.sourceRep
      (Conversion.Singleton.retarget finalContext targetFirstAt.inputTy
        sourceFirstAt.inputTy bridge.symm)
  let forwardFromSymmetry : Relation finalContext
      (.Single (.var (0 : Fin (n + 1))))
      (.Single (.var (0 : Fin (n + 1))))
      (.stable (Single.plan sourceFirstAt.inputTy)) targetEndpoint.shape :=
    Relation.ofConversion symmetryRelation.targetRep targetEndpoint.rep
      (Conversion.Singleton.retarget finalContext sourceFirstAt.inputTy
        targetFirstAt.inputTy bridge)
  let source : Wf.Interval finalContext (.Single sourcePath.weaken)
      (.Single sourcePath.weaken) := {
    lower := sourceFirstAt
    upper := sourceFirstAt
    lowerRep := sourceRep
    upperRep := sourceRep
  }
  let target : Wf.Interval finalContext
      (.Single (.var (0 : Fin (n + 1))))
      (.Single (.var (0 : Fin (n + 1)))) :=
    Wf.Interval.bounds targetEndpoint targetEndpoint
  let intervalRelation : AtomicSubtyping.IntervalRelation source target := {
    lower := backward.trans widenRelation
    upper := symmetryRelation.trans forwardFromSymmetry
  }
  let witness := singletonSourceWitnessAt base sourceFirst mapping typed
  let mapped := intervalRelation.mapWitness witness
  let targetMember := newestSingletonFamily targetFirstAt
  have lowerTyping : Exp.HasType finalContext mapped.lowerFunction
      (.arrow
        (targetMember.subst targetFirstInterface.substitution).inputTy
        mapped.selected.inputTy) := by
    rw [newestSingletonFamily_subst_interface]
    exact mapped.lowerTyping
  have upperTyping : Exp.HasType finalContext mapped.upperFunction
      (.arrow mapped.selected.inputTy
        (targetMember.subst targetFirstInterface.substitution).inputTy) := by
    rw [newestSingletonFamily_subst_interface]
    exact mapped.upperTyping
  let arguments := Pair.Interval.representationArguments targetFirstAt
    targetMember targetMember targetFirstInterface mapped.selected
    mapped.lowerFunction lowerTyping mapped.upperFunction upperTyping
  exact {
    expression := Telescope.pack arguments
    typing := by
      have packed := Telescope.pack_hasType arguments
      simpa only [Package.existsTy_rename,
        targetSingletonIntervalRepresentationAtSource_rename] using packed
  }

private noncomputable def singletonFirstContinuation
    {sourcePath : LambdaPFC.Path n}
    {targetFirstType : LambdaPFC.Ty n}
    {base : Ctx sig}
    (sourceFirst targetFirst : Shape sig)
    (firstRelation : Relation base (.Single sourcePath) targetFirstType
      sourceFirst targetFirst) :
    InterfaceMap.Continuation
      (intervalSourceOpenedContext base sourceFirst
        (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst))
      (targetIntervalFirstAtSource sourceFirst
        (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst)
        targetFirst)
      (targetIntervalRepresentationAtSource sourceFirst
        (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst)
        targetFirst (newestSingletonFamily targetFirst)
        (newestSingletonFamily targetFirst)).existsTy where
  body mapping _finalContext typed targetFirstInterface :=
    (singletonTargetPackageAt sourceFirst targetFirst firstRelation mapping
      typed targetFirstInterface).expression
  body_hasType mapping _finalContext typed targetFirstInterface :=
    (singletonTargetPackageAt sourceFirst targetFirst firstRelation mapping
      typed targetFirstInterface).typing

private noncomputable def singletonNestedBody
    {sourcePath : LambdaPFC.Path n}
    {targetFirstType : LambdaPFC.Ty n}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    (firstRelation : Relation base (.Single sourcePath) targetFirstType
      sourceFirst targetFirst) :
    Path.Body
      (intervalSourceOpenedContext base sourceFirst
        (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst))
      (targetIntervalRepresentationAtSource sourceFirst
        (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst)
        targetFirst (newestSingletonFamily targetFirst)
        (newestSingletonFamily targetFirst)).existsTy :=
  let relationAt := adjustedIntervalFirstRelationAtSource
    (sourceLower := liftedFirstFamily sourceFirst)
    (sourceUpper := liftedFirstFamily sourceFirst) firstRelation
  let sourceInterface := intervalSourceFirstInterface base sourceFirst
    (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst)
  let continuation := singletonFirstContinuation sourceFirst targetFirst
    firstRelation
  {
    expression := relationAt.interfaceMap.run sourceInterface
      (targetIntervalRepresentationAtSource sourceFirst
        (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst)
        targetFirst (newestSingletonFamily targetFirst)
        (newestSingletonFamily targetFirst)).existsTy continuation
    typing := relationAt.interfaceMap.run_hasType sourceInterface
      (targetIntervalRepresentationAtSource sourceFirst
        (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst)
        targetFirst (newestSingletonFamily targetFirst)
        (newestSingletonFamily targetFirst)).existsTy continuation
  }

private noncomputable def singletonOpenedBody
    {sourcePath : LambdaPFC.Path n}
    {targetFirstType : LambdaPFC.Ty n}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    (firstRelation : Relation base (.Single sourcePath) targetFirstType
      sourceFirst targetFirst) :
    Exp (intervalRepresentationAtBinder sourceFirst
      (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst)).scope :=
  Pair.fromSuffixExp (sourceFirstAtBinder sourceFirst).binders
    (intervalMemberAtBinder sourceFirst (liftedFirstFamily sourceFirst)
      (liftedFirstFamily sourceFirst))
    (singletonNestedBody firstRelation).expression

private noncomputable def singletonOpenedBody_hasType
    {sourcePath : LambdaPFC.Path n}
    {targetFirstType : LambdaPFC.Ty n}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    (firstRelation : Relation base (.Single sourcePath) targetFirstType
      sourceFirst targetFirst) :
    Exp.HasType
      ((intervalRepresentationAtBinder sourceFirst
        (liftedFirstFamily sourceFirst)
        (liftedFirstFamily sourceFirst)).context
          (base.bindVar
            (Pair.Interval.representation sourceFirst
              (liftedFirstFamily sourceFirst)
              (liftedFirstFamily sourceFirst)).existsTy))
      (singletonOpenedBody firstRelation)
      ((intervalRepresentationAtBinder targetFirst
        (newestSingletonFamily targetFirst)
        (newestSingletonFamily targetFirst)).existsTy.rename
          (intervalRepresentationAtBinder sourceFirst
            (liftedFirstFamily sourceFirst)
            (liftedFirstFamily sourceFirst)).weaken) := by
  let sourceLower := liftedFirstFamily sourceFirst
  let sourceTele := (sourceFirstAtBinder sourceFirst).binders
  let memberTele := intervalMemberAtBinder sourceFirst sourceLower sourceLower
  have nested := (singletonNestedBody firstRelation).typing
  have transported := fromSuffixExp_hasType sourceTele memberTele nested
  have targetEq :
      (targetIntervalRepresentationAtSource sourceFirst sourceLower sourceLower
        targetFirst (newestSingletonFamily targetFirst)
        (newestSingletonFamily targetFirst)).existsTy =
      (((intervalRepresentationAtBinder targetFirst
        (newestSingletonFamily targetFirst)
        (newestSingletonFamily targetFirst)).existsTy.rename
          sourceTele.weaken).rename memberTele.weaken) := by
    rw [← targetIntervalRepresentationAtSource_eq]
    rw [← Package.existsTy_rename]
    unfold intervalSourceOpening
    rw [Ty.rename_comp]
  have finalTypeEq :
      Pair.fromSuffixTy sourceTele memberTele
        (targetIntervalRepresentationAtSource sourceFirst sourceLower
          sourceLower targetFirst (newestSingletonFamily targetFirst)
          (newestSingletonFamily targetFirst)).existsTy =
      (intervalRepresentationAtBinder targetFirst
        (newestSingletonFamily targetFirst)
        (newestSingletonFamily targetFirst)).existsTy.rename
          (intervalRepresentationAtBinder sourceFirst sourceLower
            sourceLower).weaken := by
    calc
      Pair.fromSuffixTy sourceTele memberTele
          (targetIntervalRepresentationAtSource sourceFirst sourceLower
            sourceLower targetFirst (newestSingletonFamily targetFirst)
            (newestSingletonFamily targetFirst)).existsTy =
        Pair.fromSuffixTy sourceTele memberTele
          (((intervalRepresentationAtBinder targetFirst
            (newestSingletonFamily targetFirst)
            (newestSingletonFamily targetFirst)).existsTy.rename
              sourceTele.weaken).rename memberTele.weaken) :=
        congrArg (Pair.fromSuffixTy sourceTele memberTele) targetEq
      _ = (intervalRepresentationAtBinder targetFirst
          (newestSingletonFamily targetFirst)
          (newestSingletonFamily targetFirst)).existsTy.rename
            (sourceTele.append memberTele).weaken :=
        fromSuffixTy_weaken sourceTele memberTele _
      _ = _ := rfl
  exact finalTypeEq ▸ transported

private noncomputable def singletonRepresentationBody
    {sourcePath : LambdaPFC.Path n}
    {targetFirstType : LambdaPFC.Ty n}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    (firstRelation : Relation base (.Single sourcePath) targetFirstType
      sourceFirst targetFirst) : Exp (sig ,, .var) :=
  (intervalRepresentationAtBinder sourceFirst
    (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst)).unpack
      (.var .here)
      (intervalRepresentationAtBinder targetFirst
        (newestSingletonFamily targetFirst)
        (newestSingletonFamily targetFirst)).existsTy
      (singletonOpenedBody firstRelation)

private noncomputable def singletonRepresentationBody_hasType
    {sourcePath : LambdaPFC.Path n}
    {targetFirstType : LambdaPFC.Ty n}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    (firstRelation : Relation base (.Single sourcePath) targetFirstType
      sourceFirst targetFirst) :
    Exp.HasType
      (base.bindVar
        (Pair.Interval.representation sourceFirst
          (liftedFirstFamily sourceFirst)
          (liftedFirstFamily sourceFirst)).existsTy)
      (singletonRepresentationBody firstRelation)
      ((Pair.Interval.representation targetFirst
        (newestSingletonFamily targetFirst)
        (newestSingletonFamily targetFirst)).existsTy.weaken .var) := by
  have result :=
    (intervalRepresentationAtBinder sourceFirst
      (liftedFirstFamily sourceFirst)
      (liftedFirstFamily sourceFirst)).unpack_hasType
        (intervalRepresentationVariable_hasType base sourceFirst
          (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst))
        (singletonOpenedBody_hasType firstRelation)
  rw [Ty.weaken, Package.existsTy_rename,
    intervalRepresentationAtBinder_eq]
  exact result

private noncomputable def singletonRepresentationConversion
    {sourcePath : LambdaPFC.Path n}
    {targetFirstType : LambdaPFC.Ty n}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    (firstRelation : Relation base (.Single sourcePath) targetFirstType
      sourceFirst targetFirst) :
    Conversion base
      (Pair.Interval.representation sourceFirst
        (liftedFirstFamily sourceFirst)
        (liftedFirstFamily sourceFirst)).existsTy
      (Pair.Interval.representation targetFirst
        (newestSingletonFamily targetFirst)
        (newestSingletonFamily targetFirst)).existsTy :=
  Conversion.ofFunction
    (Adapter.ofBody
      (Pair.Interval.representation sourceFirst
        (liftedFirstFamily sourceFirst)
        (liftedFirstFamily sourceFirst)).existsTy
      (singletonRepresentationBody firstRelation))
    (Adapter.ofBody_hasType
      (singletonRepresentationBody_hasType firstRelation))

/-- Exact direct compilation of the GeneralPair member premise
`.bounds (.widen .var) (.symm .var) .refl`.

Both endpoint families are computed from the two first-component shapes.
The source family is the weakened source singleton itself; the target family
is the singleton of the mapped first package.  No caller-supplied shape
equation reconnects an existential result. -/
noncomputable def exactSingletonInterval
    {sourcePath : LambdaPFC.Path n}
    {targetFirstType : LambdaPFC.Ty n}
    {label : LambdaPFC.Name}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    (firstRelation : Relation base (.Single sourcePath) targetFirstType
      sourceFirst targetFirst) :
    Relation base
      (.Pair (.Single sourcePath) label
        (.intv (.Single sourcePath.weaken) (.Single sourcePath.weaken)))
      (.Pair targetFirstType label
        (.intv (.Single (.var (0 : Fin (n + 1))))
          (.Single (.var (0 : Fin (n + 1))))))
      (.stable (Pair.Interval.plan sourceFirst
        (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst)))
      (.stable (Pair.Interval.plan targetFirst
        (newestSingletonFamily targetFirst)
        (newestSingletonFamily targetFirst))) :=
  let sourceRepresentation := Pair.Interval.representation sourceFirst
    (liftedFirstFamily sourceFirst) (liftedFirstFamily sourceFirst)
  let targetRepresentation := Pair.Interval.representation targetFirst
    (newestSingletonFamily targetFirst) (newestSingletonFamily targetFirst)
  let representation := singletonRepresentationConversion firstRelation
  let conversion := Conversion.Pair.retarget base sourceRepresentation
    targetRepresentation representation
  let sourceEndpointRep := liftedFirstFamilyRep sourceFirst
    firstRelation.sourceRep
  let targetEndpointRep := newestSingletonFamilyRep (n := n) targetFirst
  Relation.ofConversion
    (.intervalPair firstRelation.sourceRep sourceEndpointRep sourceEndpointRep)
    (.intervalPair firstRelation.targetRep targetEndpointRep targetEndpointRep)
    conversion

/-- Smart constructor specialized to an exact source type-pair Slot. Its
indices expose the literal source Slot shape and the target Wf shape, so term
adaptation consumes it without an equality premise. -/
noncomputable def exactTypePair
    {sourceContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (environment : Env sourceContext base)
    (index : Fin n) (label : LambdaPFC.Name)
    {targetFirstType : LambdaPFC.Ty n}
    (targetFirst : Wf.Proper base targetFirstType)
    (firstRelation : Relation base (.Single (.var index)) targetFirstType
      (TermIntroduction.variableSlot environment index).shape
      targetFirst.shape) :
    let sourceEndpoint := Wf.Proper.singletonVariable environment index
    let source := TermIntroduction.typePairSlot environment index label
      sourceEndpoint
    let targetEnvironment := environment.enter targetFirstType
      targetFirst.shape targetFirst.rep
    let targetEndpoint := Wf.Proper.singletonVariable targetEnvironment 0
    let target := Wf.Proper.intervalPair label targetFirst
      (Wf.Interval.bounds targetEndpoint targetEndpoint)
    Relation base
      (.Pair (.Single (.var index)) label
        (.intv
          ((.Single (.var index) : LambdaPFC.Ty n).weaken)
          ((.Single (.var index) : LambdaPFC.Ty n).weaken)))
      (.Pair targetFirstType label
        (.intv (.Single (.var (0 : Fin (n + 1))))
          (.Single (.var (0 : Fin (n + 1))))))
      source.shape target.shape := by
  let sourceEndpoint := Wf.Proper.singletonVariable environment index
  let source := TermIntroduction.typePairSlot environment index label
    sourceEndpoint
  let targetEnvironment := environment.enter targetFirstType
    targetFirst.shape targetFirst.rep
  let targetEndpoint := Wf.Proper.singletonVariable targetEnvironment 0
  let target := Wf.Proper.intervalPair label targetFirst
    (Wf.Interval.bounds targetEndpoint targetEndpoint)
  dsimp only [sourceEndpoint, source, targetEnvironment, targetEndpoint,
    target]
  simpa only [TermIntroduction.typePairSlot,
    TermIntroduction.liftEndpoint, TermIntroduction.variableSlot,
    TermIntroduction.singletonSlot, Wf.Proper.intervalPair,
    Wf.Proper.singletonVariable, Wf.Proper.singletonFromSlot,
    Wf.Proper.referentType, Wf.Interval.bounds, liftedFirstFamily,
    newestSingletonFamily, Representation.Env.enter,
    Representation.Env.extend, Fin.cases_zero, Shape.inputTy_rename] using
      exactSingletonInterval (label := label) firstRelation

/-! ## Generic derivation-indexed proper-member covariance -/

/-- Compiled first premise, indexed by the literal first premise of the
source pair rule. -/
structure FirstCompilation
    {sourceContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    (base : Ctx sig)
    (_derivation : LambdaPFC.Tau.Sub sourceContext
      (.ty sourceFirstType) (.ty targetFirstType))
    (sourceFirst targetFirst : Shape sig) : Type where
  relation : Relation base sourceFirstType targetFirstType
    sourceFirst targetFirst

private def genericTargetFirstAtSource
    (sourceFirst : Shape sig) (sourceMember : Shape sourceFirst.scope)
    (targetFirst : Shape sig) :
    Shape (sourceMemberAtBinder sourceFirst sourceMember).scope :=
  targetFirst.rename (properOpening sourceFirst sourceMember)

private def genericTargetMemberAtSource
    (sourceFirst : Shape sig) (sourceMember : Shape sourceFirst.scope)
    (targetFirst : Shape sig) (targetMember : Shape targetFirst.scope) :
    Shape (genericTargetFirstAtSource sourceFirst sourceMember
      targetFirst).scope :=
  Pair.Proper.renameMember targetFirst targetMember
    (properOpening sourceFirst sourceMember)

/-! Public callback indices.  These aliases expose only the types already
present at the delayed proper-member boundary; the target-program opening
maps and their implementations remain private. -/

namespace ProperMemberCompiler

abbrev CallbackSig (sourceFirst : Shape sig)
    (sourceMember : Shape sourceFirst.scope) : Sig :=
  (sourceMemberAtBinder sourceFirst sourceMember).scope

abbrev CallbackContext (base : Ctx sig) (sourceFirst : Shape sig)
    (sourceMember : Shape sourceFirst.scope) :
    Ctx (CallbackSig sourceFirst sourceMember) :=
  sourceOpenedContext base sourceFirst sourceMember

abbrev SourceFirstAt (sourceFirst : Shape sig)
    (sourceMember : Shape sourceFirst.scope) {final : Sig}
    (mapping : Rename (CallbackSig sourceFirst sourceMember) final) :
    Shape final :=
  (sourceFirst.rename (properOpening sourceFirst sourceMember)).rename mapping

abbrev TargetFirstAt (sourceFirst : Shape sig)
    (sourceMember : Shape sourceFirst.scope) (targetFirst : Shape sig)
    {final : Sig}
    (mapping : Rename (CallbackSig sourceFirst sourceMember) final) :
    Shape final :=
  (genericTargetFirstAtSource sourceFirst sourceMember targetFirst).rename
    mapping

end ProperMemberCompiler

private def genericTargetProperRepresentationAtSource
    (sourceFirst : Shape sig) (sourceMember : Shape sourceFirst.scope)
    (targetFirst : Shape sig) (targetMember : Shape targetFirst.scope) :
    Telescope (sourceMemberAtBinder sourceFirst sourceMember).scope :=
  Pair.Proper.representation
    (genericTargetFirstAtSource sourceFirst sourceMember targetFirst)
    (genericTargetMemberAtSource sourceFirst sourceMember targetFirst
      targetMember)

/-- Exact recursive scope reached after opening a source proper-pair
representation and mapping its first component.  The source member is the
actual interface already present in the opened representation; the target
member is instantiated by the mapped target-first interface. -/
noncomputable def properMemberScopeAt
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    (mapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) final)
    (typed : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      finalContext mapping)
    (sourceFirstInterface : Shape.Interface finalContext
      (ProperMemberCompiler.SourceFirstAt sourceFirst sourceMember mapping))
    (targetFirstInterface : Shape.Interface finalContext
      (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        mapping)) :
    MemberScope sourceContext targetContext sourceFirstType targetFirstType
      sourceMemberType targetMemberType finalContext :=
  let openedMapping := properOpening sourceFirst sourceMember
  let openedTyped := properOpening_typed base sourceFirst sourceMember
  let sourceFirstRepOpened := firstRelation.sourceRep.targetRename
    openedMapping openedTyped
  let targetFirstRepOpened := firstRelation.targetRep.targetRename
    openedMapping openedTyped
  let sourceFirstRepAt := sourceFirstRepOpened.targetRename mapping typed
  let targetFirstRepAt := targetFirstRepOpened.targetRename mapping typed
  let sourceEnvironmentAt :=
    (environments.source.targetRename openedMapping openedTyped).targetRename
      mapping typed
  let targetEnvironmentAt :=
    (environments.target.targetRename openedMapping openedTyped).targetRename
      mapping typed
  let sourceMemberRepAt :=
    (openedSourceMemberRep base sourceFirst sourceMember
      sourceMemberRep).targetRename mapping typed
  let targetMemberRepOpened := targetMemberRep.targetRename
    (targetFirst.liftRename openedMapping)
    (targetFirst.liftRename_typed openedTyped)
  let targetMemberRepAt := targetMemberRepOpened.targetRename
    ((targetFirst.rename openedMapping).liftRename mapping)
    ((targetFirst.rename openedMapping).liftRename_typed typed)
  let targetMemberInstantiated := targetMemberRepAt.targetSubst
    targetFirstInterface.substitution
    targetFirstInterface.arguments.substitution_typed
  {
    source := {
      environment := extendAtInterface
        sourceEnvironmentAt
        sourceFirstType sourceFirstInterface sourceFirstRepAt
      memberShape :=
        (sourceMemberActual sourceFirst sourceMember).rename mapping
      memberRep := sourceMemberRepAt
    }
    target := {
      environment := extendAtInterface
        targetEnvironmentAt
        targetFirstType targetFirstInterface targetFirstRepAt
      memberShape :=
        (Pair.Proper.renameMember (targetFirst.rename openedMapping)
          (Pair.Proper.renameMember targetFirst targetMember openedMapping)
          mapping).subst
          targetFirstInterface.substitution
      memberRep := targetMemberInstantiated
    }
  }

/-- The exact contextual scope present at a delayed proper-member callback.

This is the target analogue of instantiating a semantic pair-member closure
at its concrete first value.  All package-opening maps remain private; the
only exported observation is the already-computed scope containing the two
actual first interfaces and their frozen relation. -/
noncomputable def properActionScopeAt
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    (root : ContextRelation.Scope sourceContext targetContext .source base)
    (first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (mapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) final)
    (typed : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      finalContext mapping)
    (sourceFirstInterface : Shape.Interface finalContext
      (ProperMemberCompiler.SourceFirstAt sourceFirst sourceMember mapping))
    (targetFirstInterface : Shape.Interface finalContext
      (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        mapping)) :
    ContextRelation.Scope (sourceContext.snoc sourceFirstType)
      (targetContext.snoc targetFirstType) .source finalContext := by
  let opening := properOpening sourceFirst sourceMember
  let openingTyped := properOpening_typed base sourceFirst sourceMember
  let rootAt := (root.targetRename opening openingTyped).targetRename
    mapping typed
  let firstAt := (first.targetRename opening openingTyped).targetRename
    mapping typed
  let adjustedTargetInterface : Shape.Interface finalContext
      ((targetFirst.rename opening).rename mapping) := by
    simpa only [ProperMemberCompiler.TargetFirstAt,
      genericTargetFirstAtSource, targetFirstAtSource,
      sourceFirstAtBinder, properOpening, Shape.rename_comp] using
      targetFirstInterface
  exact rootAt.extendPair sourceFirstInterface firstAt.sourceRep
    adjustedTargetInterface firstAt.targetRep firstAt

/-- Recursive compilation of the literal proper-member premise.  Its only
higher-order field is indexed by that premise and receives the two exact
first interfaces in the continuation scope chosen by the first relation. -/
structure ProperMemberCompiler
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    (_derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)) : Type where
  compile : {final : Sig} -> {finalContext : Ctx final} ->
    (mapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) final) ->
    (typed : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      finalContext mapping) ->
    (sourceFirstInterface : Shape.Interface finalContext
      (ProperMemberCompiler.SourceFirstAt sourceFirst sourceMember mapping)) ->
    (targetFirstInterface : Shape.Interface finalContext
      (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        mapping)) ->
    let scope := properMemberScopeAt environments firstRelation
      sourceMemberRep targetMemberRep mapping typed sourceFirstInterface
      targetFirstInterface
    Relation finalContext sourceMemberType targetMemberType
      scope.source.memberShape scope.target.memberShape

/-- A delayed proper-member compiler with one proof-only payload retained at
the exact relation returned by each callback.  `PairSubtyping` remains
independent of the payload (in production it is the recursive `Action`) and
erases it definitionally before generating target code. -/
structure ProperMemberCompiler.Enriched
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (root : ContextRelation.Scope sourceContext targetContext .source base)
    (first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    (_derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)) : Type 1 where
  Retained : {final : Sig} -> {finalContext : Ctx final} ->
    (mapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) final) ->
    (typed : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      finalContext mapping) ->
    (sourceFirstInterface : Shape.Interface finalContext
      (ProperMemberCompiler.SourceFirstAt sourceFirst sourceMember mapping)) ->
    (targetFirstInterface : Shape.Interface finalContext
      (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        mapping)) ->
    let scope := properMemberScopeAt root.endpointEnvs first sourceMemberRep
      targetMemberRep mapping typed sourceFirstInterface targetFirstInterface
    Relation finalContext sourceMemberType targetMemberType
      scope.source.memberShape scope.target.memberShape -> Type
  compile : {final : Sig} -> {finalContext : Ctx final} ->
    (mapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) final) ->
    (typed : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      finalContext mapping) ->
    (sourceFirstInterface : Shape.Interface finalContext
      (ProperMemberCompiler.SourceFirstAt sourceFirst sourceMember mapping)) ->
    (targetFirstInterface : Shape.Interface finalContext
      (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        mapping)) ->
    let scope := properMemberScopeAt root.endpointEnvs first sourceMemberRep
      targetMemberRep mapping typed sourceFirstInterface targetFirstInterface
    Sigma fun relation : Relation finalContext sourceMemberType
        targetMemberType scope.source.memberShape scope.target.memberShape =>
      Retained mapping typed sourceFirstInterface targetFirstInterface relation

/-- Forget only the proof payload.  The generated pair program consumes the
same relation at projection `.1`; no conversion, interface map, or endpoint
equality is supplied independently. -/
noncomputable def ProperMemberCompiler.Enriched.erase
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember}
    {targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (compiler : ProperMemberCompiler.Enriched root first sourceMemberRep
      targetMemberRep derivation) :
    ProperMemberCompiler root.endpointEnvs first sourceMemberRep
      targetMemberRep derivation where
  compile mapping typed sourceFirstInterface targetFirstInterface :=
    (compiler.compile mapping typed sourceFirstInterface
      targetFirstInterface).1

/-! ## Same-run material proper-pair callbacks -/

section ProperMaterial

variable {sourceContext targetContext : LambdaPFC.Ctx n}
variable {base : Ctx sig}
variable {sourceFirstType targetFirstType : LambdaPFC.Ty n}
variable {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
variable {sourceFirst targetFirst : Shape sig}
variable {sourceMember : Shape sourceFirst.scope}
variable {targetMember : Shape targetFirst.scope}
variable {root : ContextRelation.Scope sourceContext targetContext .source base}
variable {first : Relation base sourceFirstType targetFirstType
  sourceFirst targetFirst}
variable {sourceMemberRep : Rep (sourceFirst.context base)
  sourceMemberType sourceMember}
variable {targetMemberRep : Rep (targetFirst.context base)
  targetMemberType targetMember}
variable {memberDerivation : LambdaPFC.Tau.Sub
  (sourceContext.snoc sourceFirstType)
  (.ty sourceMemberType) (.ty targetMemberType)}

/-- Root mapping after opening the source proper representation and running
the first and member interface maps exactly once. -/
abbrev ProperMaterialRootAt
    {firstFinal final : Sig}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal)
    (memberMapping : Rename firstFinal final) : Rename sig final :=
  ((properOpening sourceFirst sourceMember).comp firstMapping).comp
    memberMapping

noncomputable def properMaterialRootAt_typed
    {firstFinal final : Sig}
    {firstContext : Ctx firstFinal} {finalContext : Ctx final}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal)
    (firstTyped : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      firstContext firstMapping)
    (memberMapping : Rename firstFinal final)
    (memberTyped : Rename.Typed firstContext finalContext memberMapping) :
    Rename.Typed base finalContext
      (ProperMaterialRootAt firstMapping memberMapping) :=
  TypedRename.comp
    (TypedRename.comp
      (properOpening_typed base sourceFirst sourceMember) firstTyped)
    memberTyped

/-- Canonical source-first interface manufactured by the one representation
opening.  Callers cannot replace it with an unrelated package. -/
noncomputable def properMaterialSourceFirstInterface
    {firstFinal : Sig} {firstContext : Ctx firstFinal}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal)
    (firstTyped : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      firstContext firstMapping) :
    Shape.Interface firstContext
      (ProperMemberCompiler.SourceFirstAt sourceFirst sourceMember
        firstMapping) :=
  (openedSourceFirstInterface base sourceFirst sourceMember).rename
    firstMapping firstTyped

/-- Canonical source-member interface opened beside the source first value. -/
noncomputable def properMaterialSourceMemberInterface
    {firstFinal : Sig} {firstContext : Ctx firstFinal}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal)
    (firstTyped : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      firstContext firstMapping) :
    Shape.Interface firstContext
      ((sourceMemberActual sourceFirst sourceMember).rename firstMapping) :=
  (openedSourceMemberInterface base sourceFirst sourceMember).rename
    firstMapping firstTyped

abbrev ProperMaterialSourceMemberAt
    {firstFinal : Sig}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal) :
    Shape firstFinal :=
  (sourceMemberActual sourceFirst sourceMember).rename firstMapping

/-- Target environment before extending it with either mapped pair field. -/
noncomputable def properMaterialTargetEnvironment
    {firstFinal final : Sig}
    {firstContext : Ctx firstFinal} {finalContext : Ctx final}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal)
    (firstTyped : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      firstContext firstMapping)
    (memberMapping : Rename firstFinal final)
    (memberTyped : Rename.Typed firstContext finalContext memberMapping) :
    Env targetContext finalContext :=
  ((((root.endpointEnvs.targetRename
      (properOpening sourceFirst sourceMember)
      (properOpening_typed base sourceFirst sourceMember)).targetRename
        firstMapping firstTyped).target).targetRename memberMapping
          memberTyped)

/-- Target first representation at the final member-map callback scope. -/
noncomputable def properMaterialTargetFirstRep
    {firstFinal final : Sig}
    {firstContext : Ctx firstFinal} {finalContext : Ctx final}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal)
    (firstTyped : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      firstContext firstMapping)
    (memberMapping : Rename firstFinal final)
    (memberTyped : Rename.Typed firstContext finalContext memberMapping) :
    Rep finalContext targetFirstType
      ((ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        firstMapping).rename memberMapping) :=
  (((first.targetRep.targetRename
      (properOpening sourceFirst sourceMember)
      (properOpening_typed base sourceFirst sourceMember)).targetRename
        firstMapping firstTyped).targetRename memberMapping memberTyped)

/-- Target member family at the final target-first scope, before substituting
the actual target-first interface. -/
abbrev ProperMaterialTargetMemberAt
    {firstFinal final : Sig}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal)
    (memberMapping : Rename firstFinal final) :
    Shape
      ((ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        firstMapping).rename memberMapping).scope :=
  Pair.Proper.renameMember
    (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
      firstMapping)
    (Pair.Proper.renameMember
      (genericTargetFirstAtSource sourceFirst sourceMember targetFirst)
      (genericTargetMemberAtSource sourceFirst sourceMember targetFirst
        targetMember)
      firstMapping)
    memberMapping

abbrev ProperMaterialTargetMemberAtFirst
    {firstFinal : Sig}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal) :
    Shape
      (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        firstMapping).scope :=
  Pair.Proper.renameMember
    (genericTargetFirstAtSource sourceFirst sourceMember targetFirst)
    (genericTargetMemberAtSource sourceFirst sourceMember targetFirst
      targetMember)
    firstMapping

abbrev ProperMaterialTargetMemberInstantiatedAt
    {firstFinal : Sig} {firstContext : Ctx firstFinal}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal)
    (targetFirstInterface : Shape.Interface firstContext
      (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        firstMapping)) : Shape firstFinal :=
  (ProperMaterialTargetMemberAtFirst (targetMember := targetMember)
    firstMapping).subst targetFirstInterface.substitution

noncomputable def properMaterialTargetFirstInterface
    {firstFinal final : Sig}
    {firstContext : Ctx firstFinal} {finalContext : Ctx final}
    {firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal}
    (targetFirstInterface : Shape.Interface firstContext
      (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        firstMapping))
    (memberMapping : Rename firstFinal final)
    (memberTyped : Rename.Typed firstContext finalContext memberMapping) :
    Shape.Interface finalContext
      ((ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        firstMapping).rename memberMapping) :=
  targetFirstInterface.rename memberMapping memberTyped

theorem properMaterialTargetMemberInstantiatedAt_rename
    {firstFinal final : Sig}
    {firstContext : Ctx firstFinal} {finalContext : Ctx final}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal)
    (targetFirstInterface : Shape.Interface firstContext
      (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        firstMapping))
    (memberMapping : Rename firstFinal final)
    (memberTyped : Rename.Typed firstContext finalContext memberMapping) :
    (ProperMaterialTargetMemberInstantiatedAt
      (targetMember := targetMember) firstMapping
        targetFirstInterface).rename memberMapping =
      (ProperMaterialTargetMemberAt (targetMember := targetMember)
        firstMapping memberMapping).subst
        (properMaterialTargetFirstInterface targetFirstInterface memberMapping
          memberTyped).substitution := by
  simpa only [ProperMaterialTargetMemberInstantiatedAt,
    ProperMaterialTargetMemberAt, ProperMaterialTargetMemberAtFirst,
    properMaterialTargetFirstInterface, Pair.Proper.renameMember] using
    Shape.subst_interface_rename
      (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        firstMapping)
      (ProperMaterialTargetMemberAtFirst (targetMember := targetMember)
        firstMapping)
      targetFirstInterface memberMapping memberTyped

/-- Target member representation at the final target-first scope, before the
actual target-first substitution. -/
noncomputable def properMaterialTargetMemberRep
    {firstFinal final : Sig}
    {firstContext : Ctx firstFinal} {finalContext : Ctx final}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal)
    (firstTyped : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      firstContext firstMapping)
    (memberMapping : Rename firstFinal final)
    (memberTyped : Rename.Typed firstContext finalContext memberMapping) :
    Rep
      (((ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        firstMapping).rename memberMapping).context finalContext)
      targetMemberType
      (ProperMaterialTargetMemberAt (targetMember := targetMember)
        firstMapping memberMapping) := by
  let opened := targetMemberRep.targetRename
    (targetFirst.liftRename (properOpening sourceFirst sourceMember))
    (targetFirst.liftRename_typed
      (properOpening_typed base sourceFirst sourceMember))
  let atFirst := opened.targetRename
    ((targetFirst.rename (properOpening sourceFirst sourceMember)).liftRename
      firstMapping)
    ((targetFirst.rename (properOpening sourceFirst sourceMember)).liftRename_typed
      firstTyped)
  exact atFirst.targetRename
    ((ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
      firstMapping).liftRename memberMapping)
    ((ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
      firstMapping).liftRename_typed memberTyped)

/-- Exact member scope selected by the canonical source-first interface and
the target-first interface returned by the first map. -/
noncomputable abbrev ProperMaterialMembersAt
    {firstFinal : Sig} {firstContext : Ctx firstFinal}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal)
    (firstTyped : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      firstContext firstMapping)
    (targetFirstInterface : Shape.Interface firstContext
      (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        firstMapping)) :=
  properMemberScopeAt root.endpointEnvs first sourceMemberRep targetMemberRep
    firstMapping firstTyped
    (properMaterialSourceFirstInterface firstMapping firstTyped)
    targetFirstInterface

/-- Ephemeral output of the one member-interface map.  The retained payload
is still indexed at the first callback, while both actual member interfaces
are available at the final callback chosen by that relation. -/
structure ProperMaterialView
    (compiler : ProperMemberCompiler.Enriched root first sourceMemberRep
      targetMemberRep memberDerivation)
    {firstFinal : Sig} {firstContext : Ctx firstFinal}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal)
    (firstTyped : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      firstContext firstMapping)
    (targetFirstInterface : Shape.Interface firstContext
      (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        firstMapping))
    (relation : Relation firstContext sourceMemberType targetMemberType
      (ProperMaterialSourceMemberAt firstMapping)
      (ProperMaterialTargetMemberInstantiatedAt
        (targetMember := targetMember) firstMapping targetFirstInterface))
    {final : Sig} {finalContext : Ctx final}
    (memberMapping : Rename firstFinal final)
    (memberTyped : Rename.Typed firstContext finalContext memberMapping) where
  retained : compiler.Retained firstMapping firstTyped
    (properMaterialSourceFirstInterface firstMapping firstTyped)
    targetFirstInterface relation
  sourceMemberInterface : Shape.Interface finalContext
    ((ProperMaterialSourceMemberAt firstMapping).rename memberMapping)
  targetMemberInterface : Shape.Interface finalContext
    ((ProperMaterialTargetMemberAt (targetMember := targetMember)
      firstMapping memberMapping).subst
        (properMaterialTargetFirstInterface targetFirstInterface memberMapping
          memberTyped).substitution)

/-- Result-polymorphic consumer invoked after the actual first and member
interface maps, while their exact relation and retained proof payload remain
in scope. -/
structure ProperMaterialContinuation
    (compiler : ProperMemberCompiler.Enriched root first sourceMemberRep
      targetMemberRep memberDerivation)
    (answer : Ty sig) : Type 1 where
  body : {firstFinal final : Sig} ->
    {firstContext : Ctx firstFinal} -> {finalContext : Ctx final} ->
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal) ->
    (firstTyped : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      firstContext firstMapping) ->
    (targetFirstInterface : Shape.Interface firstContext
      (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        firstMapping)) ->
    (relation : Relation firstContext sourceMemberType targetMemberType
      (ProperMaterialSourceMemberAt firstMapping)
      (ProperMaterialTargetMemberInstantiatedAt
        (targetMember := targetMember) firstMapping targetFirstInterface)) ->
    (memberMapping : Rename firstFinal final) ->
    (memberTyped : Rename.Typed firstContext finalContext memberMapping) ->
    Rename.Typed base finalContext
      (ProperMaterialRootAt firstMapping memberMapping) ->
    ProperMaterialView compiler firstMapping firstTyped targetFirstInterface
      relation memberMapping memberTyped ->
    Path.Body finalContext
      (answer.rename (ProperMaterialRootAt firstMapping memberMapping))

end ProperMaterial

private noncomputable def properRepresentationPackage
    {targetContext : Ctx sig}
    {first : Shape sig} {member : Shape first.scope}
    (interface : Shape.Interface targetContext
      (.stable (Pair.Proper.plan first member))) : Exp sig :=
  (Pair.asRepresentation
    (Pair.Proper.representation first member)).subst interface.substitution

private noncomputable def properRepresentationPackage_hasType
    {targetContext : Ctx sig}
    {first : Shape sig} {member : Shape first.scope}
    (interface : Shape.Interface targetContext
      (.stable (Pair.Proper.plan first member))) :
    Exp.HasType targetContext (properRepresentationPackage interface)
      (Pair.Proper.representation first member).existsTy := by
  let representation := Pair.Proper.representation first member
  have opened :=
    (Pair.asRepresentation_hasType targetContext representation).subst
      interface.arguments.substitution_typed
  have resultType :
      (Pair.finalRepresentationTy representation).subst
          interface.arguments.substitution =
        representation.existsTy := by
    calc
      _ = interface.arguments.instantiate
          (representation.existsTy.rename
            (Pair.Proper.plan first member).telescope.weaken) :=
        (interface.arguments.instantiate_eq_subst _).symm
      _ = representation.existsTy :=
        interface.arguments.instantiate_weaken representation.existsTy
  rw [resultType] at opened
  exact opened

section ProperMaterialRun

variable {sourceContext targetContext : LambdaPFC.Ctx n}
variable {base : Ctx sig}
variable {sourceFirstType targetFirstType : LambdaPFC.Ty n}
variable {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
variable {sourceFirst targetFirst : Shape sig}
variable {sourceMember : Shape sourceFirst.scope}
variable {targetMember : Shape targetFirst.scope}
variable {root : ContextRelation.Scope sourceContext targetContext .source base}
variable {first : Relation base sourceFirstType targetFirstType
  sourceFirst targetFirst}
variable {sourceMemberRep : Rep (sourceFirst.context base)
  sourceMemberType sourceMember}
variable {targetMemberRep : Rep (targetFirst.context base)
  targetMemberType targetMember}
variable {memberDerivation : LambdaPFC.Tau.Sub
  (sourceContext.snoc sourceFirstType)
  (.ty sourceMemberType) (.ty targetMemberType)}

private noncomputable def properMaterialMemberContinuation
    (compiler : ProperMemberCompiler.Enriched root first sourceMemberRep
      targetMemberRep memberDerivation)
    (answer : Ty sig)
    (continuation : ProperMaterialContinuation compiler answer)
    {firstFinal : Sig} {firstContext : Ctx firstFinal}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal)
    (firstTyped : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      firstContext firstMapping)
    (targetFirstInterface : Shape.Interface firstContext
      (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        firstMapping))
    (relation : Relation firstContext sourceMemberType targetMemberType
      (ProperMaterialSourceMemberAt firstMapping)
      (ProperMaterialTargetMemberInstantiatedAt
        (targetMember := targetMember) firstMapping targetFirstInterface))
    (retained : compiler.Retained firstMapping firstTyped
      (properMaterialSourceFirstInterface firstMapping firstTyped)
      targetFirstInterface relation) :
    InterfaceMap.Continuation firstContext
      (ProperMaterialTargetMemberInstantiatedAt
        (targetMember := targetMember) firstMapping targetFirstInterface)
      (answer.rename
        ((properOpening sourceFirst sourceMember).comp firstMapping)) where
  body memberMapping _finalContext memberTyped targetMemberInterface :=
    let sourceMemberInterface :=
      (properMaterialSourceMemberInterface firstMapping firstTyped).rename
        memberMapping memberTyped
    let normalizedTargetMemberInterface : Shape.Interface _
        ((ProperMaterialTargetMemberAt (targetMember := targetMember)
          firstMapping memberMapping).subst
          (properMaterialTargetFirstInterface targetFirstInterface
            memberMapping memberTyped).substitution) := by
      rw [← properMaterialTargetMemberInstantiatedAt_rename firstMapping
        targetFirstInterface memberMapping memberTyped]
      exact targetMemberInterface
    let view : ProperMaterialView compiler firstMapping firstTyped
        targetFirstInterface relation memberMapping memberTyped := {
      retained := retained
      sourceMemberInterface := sourceMemberInterface
      targetMemberInterface := normalizedTargetMemberInterface
    }
    (continuation.body firstMapping firstTyped targetFirstInterface relation
      memberMapping memberTyped
      (properMaterialRootAt_typed firstMapping firstTyped memberMapping
        memberTyped)
      view).expression
  body_hasType memberMapping _finalContext memberTyped
      targetMemberInterface := by
    let sourceMemberInterface :=
      (properMaterialSourceMemberInterface firstMapping firstTyped).rename
        memberMapping memberTyped
    let normalizedTargetMemberInterface : Shape.Interface _
        ((ProperMaterialTargetMemberAt (targetMember := targetMember)
          firstMapping memberMapping).subst
          (properMaterialTargetFirstInterface targetFirstInterface
            memberMapping memberTyped).substitution) := by
      rw [← properMaterialTargetMemberInstantiatedAt_rename firstMapping
        targetFirstInterface memberMapping memberTyped]
      exact targetMemberInterface
    let view : ProperMaterialView compiler firstMapping firstTyped
        targetFirstInterface relation memberMapping memberTyped := {
      retained := retained
      sourceMemberInterface := sourceMemberInterface
      targetMemberInterface := normalizedTargetMemberInterface
    }
    simpa only [Ty.rename_comp] using
      (continuation.body firstMapping firstTyped targetFirstInterface relation
        memberMapping memberTyped
        (properMaterialRootAt_typed firstMapping firstTyped memberMapping
          memberTyped)
        view).typing

private noncomputable def properMaterialFirstBody
    (compiler : ProperMemberCompiler.Enriched root first sourceMemberRep
      targetMemberRep memberDerivation)
    (answer : Ty sig)
    (continuation : ProperMaterialContinuation compiler answer)
    {firstFinal : Sig} {firstContext : Ctx firstFinal}
    (firstMapping : Rename
      (ProperMemberCompiler.CallbackSig sourceFirst sourceMember) firstFinal)
    (firstTyped : Rename.Typed
      (ProperMemberCompiler.CallbackContext base sourceFirst sourceMember)
      firstContext firstMapping)
    (targetFirstInterfaceAtSource : Shape.Interface firstContext
      ((targetFirstAtSource sourceFirst sourceMember targetFirst).rename
        firstMapping)) :
    Path.Body firstContext
      (answer.rename
        ((properOpening sourceFirst sourceMember).comp firstMapping)) := by
  let sourceFirstInterface :=
    properMaterialSourceFirstInterface firstMapping firstTyped
  let targetFirstInterface : Shape.Interface firstContext
      (ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember targetFirst
        firstMapping) := by
    simpa only [ProperMemberCompiler.TargetFirstAt,
      genericTargetFirstAtSource, properOpening, targetFirstAtSource,
      sourceFirstAtBinder, Shape.rename_comp] using
        targetFirstInterfaceAtSource
  let compiled := compiler.compile firstMapping firstTyped
    sourceFirstInterface targetFirstInterface
  let relation := compiled.1
  let retained := compiled.2
  let sourceMemberInterface :=
    properMaterialSourceMemberInterface firstMapping firstTyped
  let next := properMaterialMemberContinuation compiler answer continuation
    firstMapping firstTyped targetFirstInterface relation retained
  exact {
    expression := relation.interfaceMap.run sourceMemberInterface
      (answer.rename
        ((properOpening sourceFirst sourceMember).comp firstMapping)) next
    typing := relation.interfaceMap.run_hasType sourceMemberInterface
      (answer.rename
        ((properOpening sourceFirst sourceMember).comp firstMapping)) next
  }

private noncomputable def properMaterialFirstContinuation
    (compiler : ProperMemberCompiler.Enriched root first sourceMemberRep
      targetMemberRep memberDerivation)
    (answer : Ty sig)
    (continuation : ProperMaterialContinuation compiler answer) :
    InterfaceMap.Continuation
      (sourceOpenedContext base sourceFirst sourceMember)
      (targetFirstAtSource sourceFirst sourceMember targetFirst)
      (answer.rename (properOpening sourceFirst sourceMember)) where
  body firstMapping _firstContext firstTyped targetFirstInterface :=
    (properMaterialFirstBody compiler answer continuation firstMapping
      firstTyped targetFirstInterface).expression
  body_hasType firstMapping _firstContext firstTyped
      targetFirstInterface := by
    simpa only [Ty.rename_comp] using
      (properMaterialFirstBody compiler answer continuation firstMapping
        firstTyped targetFirstInterface).typing

private noncomputable def properMaterialNestedBody
    (compiler : ProperMemberCompiler.Enriched root first sourceMemberRep
      targetMemberRep memberDerivation)
    (answer : Ty sig)
    (continuation : ProperMaterialContinuation compiler answer) :
    Path.Body (sourceOpenedContext base sourceFirst sourceMember)
      (answer.rename (properOpening sourceFirst sourceMember)) :=
  let relationAt := adjustedFirstRelationAtSource
    (sourceMember := sourceMember) first
  let sourceInterface : Shape.Interface
      (sourceOpenedContext base sourceFirst sourceMember)
      ((sourceFirstAtBinder sourceFirst).rename
        (sourceOpening sourceFirst sourceMember)) := by
    simpa only [properOpening, sourceFirstAtBinder,
      Shape.rename_comp] using
        openedSourceFirstInterface base sourceFirst sourceMember
  let next := properMaterialFirstContinuation compiler answer continuation
  {
    expression := relationAt.interfaceMap.run sourceInterface
      (answer.rename (properOpening sourceFirst sourceMember)) next
    typing := relationAt.interfaceMap.run_hasType sourceInterface
      (answer.rename (properOpening sourceFirst sourceMember)) next
  }

private noncomputable def properMaterialOpenedBody
    (compiler : ProperMemberCompiler.Enriched root first sourceMemberRep
      targetMemberRep memberDerivation)
    (answer : Ty sig)
    (continuation : ProperMaterialContinuation compiler answer) :
    Exp (properRepresentationAtBinder sourceFirst sourceMember).scope :=
  Pair.fromSuffixExp (sourceFirstAtBinder sourceFirst).binders
    (sourceMemberAtBinder sourceFirst sourceMember).binders
    (properMaterialNestedBody compiler answer continuation).expression

private noncomputable def properMaterialOpenedBody_hasType
    (compiler : ProperMemberCompiler.Enriched root first sourceMemberRep
      targetMemberRep memberDerivation)
    (answer : Ty sig)
    (continuation : ProperMaterialContinuation compiler answer) :
    Exp.HasType
      ((properRepresentationAtBinder sourceFirst sourceMember).context
        (base.bindVar
          (Pair.Proper.representation sourceFirst sourceMember).existsTy))
      (properMaterialOpenedBody compiler answer continuation)
      ((answer.weaken .var).rename
        (properRepresentationAtBinder sourceFirst sourceMember).weaken) := by
  let firstTele := (sourceFirstAtBinder sourceFirst).binders
  let memberTele := (sourceMemberAtBinder sourceFirst sourceMember).binders
  have nested := (properMaterialNestedBody compiler answer continuation).typing
  have transported := fromSuffixExp_hasType firstTele memberTele nested
  have openingTypeEq :
      answer.rename (properOpening sourceFirst sourceMember) =
      (((answer.rename (Rename.weaken .var)).rename firstTele.weaken).rename
        memberTele.weaken) := by
    unfold properOpening sourceOpening firstTele memberTele
    rw [Ty.rename_comp, Ty.rename_comp]
    rfl
  have finalTypeEq :
      Pair.fromSuffixTy firstTele memberTele
          (answer.rename (properOpening sourceFirst sourceMember)) =
      (answer.weaken .var).rename
        (properRepresentationAtBinder sourceFirst sourceMember).weaken := by
    calc
      _ = Pair.fromSuffixTy firstTele memberTele
          (((answer.rename (Rename.weaken .var)).rename firstTele.weaken).rename
            memberTele.weaken) :=
        congrArg (Pair.fromSuffixTy firstTele memberTele) openingTypeEq
      _ = (answer.rename (Rename.weaken .var)).rename
          (firstTele.append memberTele).weaken :=
        fromSuffixTy_weaken firstTele memberTele _
      _ = _ := rfl
  exact finalTypeEq ▸ transported

private noncomputable def properMaterialRepresentationBody
    (compiler : ProperMemberCompiler.Enriched root first sourceMemberRep
      targetMemberRep memberDerivation)
    (answer : Ty sig)
    (continuation : ProperMaterialContinuation compiler answer) :
    Exp (sig ,, .var) :=
  (properRepresentationAtBinder sourceFirst sourceMember).unpack (.var .here)
    (answer.weaken .var)
    (properMaterialOpenedBody compiler answer continuation)

private noncomputable def properMaterialRepresentationBody_hasType
    (compiler : ProperMemberCompiler.Enriched root first sourceMemberRep
      targetMemberRep memberDerivation)
    (answer : Ty sig)
    (continuation : ProperMaterialContinuation compiler answer) :
    Exp.HasType
      (base.bindVar
        (Pair.Proper.representation sourceFirst sourceMember).existsTy)
      (properMaterialRepresentationBody compiler answer continuation)
      (answer.weaken .var) :=
  (properRepresentationAtBinder sourceFirst sourceMember).unpack_hasType
    (properRepresentationVariable_hasType base sourceFirst sourceMember)
    (properMaterialOpenedBody_hasType compiler answer continuation)

/-- Open one actual proper-pair interface, run its first and member maps once,
and immediately reclose a result-polymorphic continuation carrying the exact
retained child payload and both actual member interfaces. -/
noncomputable def runProperMaterial
    (compiler : ProperMemberCompiler.Enriched root first sourceMemberRep
      targetMemberRep memberDerivation)
    (sourceInterface : Shape.Interface base
      (.stable (Pair.Proper.plan sourceFirst sourceMember)))
    (answer : Ty sig)
    (continuation : ProperMaterialContinuation compiler answer) :
    Path.Body base answer :=
  let package := properRepresentationPackage sourceInterface
  let packageTyping := properRepresentationPackage_hasType sourceInterface
  let body := properMaterialRepresentationBody compiler answer continuation
  let bodyTyping := properMaterialRepresentationBody_hasType compiler answer
    continuation
  {
    expression := Adapter.apply
      (Adapter.ofBody
        (Pair.Proper.representation sourceFirst sourceMember).existsTy body)
      package
    typing := Adapter.apply_hasType (Adapter.ofBody_hasType bodyTyping)
      packageTyping
  }

end ProperMaterialRun

private noncomputable def properMemberArguments
    {base : Ctx sig} {first : Shape sig} {member : Shape first.scope}
    (firstInterface : Shape.Interface base first)
    {final : Sig} {finalContext : Ctx final}
    (mapping : Rename sig final)
    (typed : Rename.Typed base finalContext mapping)
    (memberInterface : Shape.Interface finalContext
      ((member.subst firstInterface.substitution).rename mapping)) :
    Telescope.Args finalContext
      ((Pair.Proper.renameMember first member mapping).binders.subst
        (firstInterface.rename mapping typed).substitution) := by
  rw [Shape.binders_subst]
  unfold Pair.Proper.renameMember
  rw [← Shape.subst_interface_rename first member firstInterface
    mapping typed]
  exact memberInterface.arguments

private noncomputable def properPackageContinuation
    {base : Ctx sig} (first : Shape sig) (member : Shape first.scope)
    (firstInterface : Shape.Interface base first) :
    InterfaceMap.Continuation base
      (member.subst firstInterface.substitution)
      (Pair.Proper.representation first member).existsTy where
  body mapping finalContext typed memberInterface :=
    let firstAt := first.rename mapping
    let memberAt := Pair.Proper.renameMember first member mapping
    let firstAtInterface := firstInterface.rename mapping typed
    Telescope.pack (Pair.Proper.representationArguments firstAt memberAt
      firstAtInterface.arguments
      (properMemberArguments firstInterface mapping typed memberInterface))
  body_hasType mapping finalContext typed memberInterface := by
    let firstAt := first.rename mapping
    let memberAt := Pair.Proper.renameMember first member mapping
    let firstAtInterface := firstInterface.rename mapping typed
    have packed := Telescope.pack_hasType
      (Pair.Proper.representationArguments firstAt memberAt
        firstAtInterface.arguments
        (properMemberArguments firstInterface mapping typed memberInterface))
    simpa only [Package.existsTy_rename,
      Pair.Proper.representation_rename] using packed

private noncomputable def genericProperMemberBody
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (compiler : ProperMemberCompiler environments firstRelation
      sourceMemberRep targetMemberRep memberDerivation)
    (mapping : Rename (sourceMemberAtBinder sourceFirst sourceMember).scope
      final)
    (typed : Rename.Typed (sourceOpenedContext base sourceFirst sourceMember)
      finalContext mapping)
    (targetFirstInterfaceAtSource : Shape.Interface finalContext
      ((targetFirstAtSource sourceFirst sourceMember targetFirst).rename
        mapping)) :
    Path.Body finalContext
      ((genericTargetProperRepresentationAtSource sourceFirst sourceMember
        targetFirst targetMember).existsTy.rename mapping) := by
  let sourceFirstInterface : Shape.Interface finalContext
      ((sourceFirst.rename (properOpening sourceFirst sourceMember)).rename
        mapping) :=
    (openedSourceFirstInterface base sourceFirst sourceMember).rename
      mapping typed
  let targetFirstInterface : Shape.Interface finalContext
      ((genericTargetFirstAtSource sourceFirst sourceMember
        targetFirst).rename mapping) := by
    simpa only [genericTargetFirstAtSource, properOpening,
      targetFirstAtSource,
      sourceFirstAtBinder, Shape.rename_comp] using
        targetFirstInterfaceAtSource
  let scope := properMemberScopeAt environments firstRelation
    sourceMemberRep targetMemberRep mapping typed sourceFirstInterface
    targetFirstInterface
  let memberRelation := compiler.compile mapping typed
    sourceFirstInterface targetFirstInterface
  let sourceMemberInterface : Shape.Interface finalContext
      scope.source.memberShape := by
    exact (openedSourceMemberInterface base sourceFirst sourceMember).rename
      mapping typed
  let targetFirstAt :=
    (genericTargetFirstAtSource sourceFirst sourceMember targetFirst).rename
      mapping
  let targetMemberAt :=
    Pair.Proper.renameMember
      (genericTargetFirstAtSource sourceFirst sourceMember targetFirst)
      (genericTargetMemberAtSource sourceFirst sourceMember targetFirst
        targetMember) mapping
  let answer := (Pair.Proper.representation targetFirstAt
    targetMemberAt).existsTy
  let continuation := properPackageContinuation targetFirstAt targetMemberAt
    targetFirstInterface
  let result := memberRelation.interfaceMap.run sourceMemberInterface
    answer continuation
  have resultTyping := memberRelation.interfaceMap.run_hasType
    sourceMemberInterface answer continuation
  have answerEq :
      answer =
        (genericTargetProperRepresentationAtSource sourceFirst sourceMember
          targetFirst targetMember).existsTy.rename mapping := by
    dsimp only [answer, targetFirstAt, targetMemberAt]
    rw [Package.existsTy_rename]
    unfold genericTargetProperRepresentationAtSource
    rw [Pair.Proper.representation_rename]
  exact {
    expression := result
    typing := answerEq ▸ resultTyping
  }

private noncomputable def genericProperFirstContinuation
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (compiler : ProperMemberCompiler environments firstRelation
      sourceMemberRep targetMemberRep memberDerivation) :
    InterfaceMap.Continuation
      (sourceOpenedContext base sourceFirst sourceMember)
      (targetFirstAtSource sourceFirst sourceMember targetFirst)
      (genericTargetProperRepresentationAtSource sourceFirst sourceMember
        targetFirst targetMember).existsTy where
  body mapping _finalContext typed targetFirstInterface :=
    (genericProperMemberBody environments firstRelation sourceMemberRep
      targetMemberRep compiler mapping typed targetFirstInterface).expression
  body_hasType mapping _finalContext typed targetFirstInterface :=
    (genericProperMemberBody environments firstRelation sourceMemberRep
      targetMemberRep compiler mapping typed targetFirstInterface).typing

private theorem genericTargetProperRepresentationAtSource_eq
    (sourceFirst : Shape sig) (sourceMember : Shape sourceFirst.scope)
    (targetFirst : Shape sig) (targetMember : Shape targetFirst.scope) :
    (properRepresentationAtBinder targetFirst targetMember).rename
        (sourceOpening sourceFirst sourceMember) =
      genericTargetProperRepresentationAtSource sourceFirst sourceMember
        targetFirst targetMember := by
  rw [← properRepresentationAtBinder_eq]
  unfold genericTargetProperRepresentationAtSource
    genericTargetFirstAtSource genericTargetMemberAtSource
  unfold properOpening
  calc
    ((Pair.Proper.representation targetFirst targetMember).rename
        (Rename.weaken .var)).rename
        (sourceOpening sourceFirst sourceMember) =
      (Pair.Proper.representation targetFirst targetMember).rename
        ((Rename.weaken .var).comp
          (sourceOpening sourceFirst sourceMember)) :=
      Telescope.rename_comp _ _ _
    _ = Pair.Proper.representation
        (targetFirst.rename ((Rename.weaken .var).comp
          (sourceOpening sourceFirst sourceMember)))
        (Pair.Proper.renameMember targetFirst targetMember
          ((Rename.weaken .var).comp
            (sourceOpening sourceFirst sourceMember))) :=
      Pair.Proper.representation_rename targetFirst targetMember _

private noncomputable def genericProperNestedBody
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (compiler : ProperMemberCompiler environments firstRelation
      sourceMemberRep targetMemberRep memberDerivation) :
    Path.Body (sourceOpenedContext base sourceFirst sourceMember)
      (genericTargetProperRepresentationAtSource sourceFirst sourceMember
        targetFirst targetMember).existsTy :=
  let relationAt := adjustedFirstRelationAtSource
    (sourceMember := sourceMember) firstRelation
  let sourceInterface : Shape.Interface
      (sourceOpenedContext base sourceFirst sourceMember)
      ((sourceFirstAtBinder sourceFirst).rename
        (sourceOpening sourceFirst sourceMember)) := by
    simpa only [properOpening, sourceFirstAtBinder,
      Shape.rename_comp] using
        openedSourceFirstInterface base sourceFirst sourceMember
  let continuation := genericProperFirstContinuation environments
    firstRelation sourceMemberRep targetMemberRep compiler
  {
    expression := relationAt.interfaceMap.run sourceInterface
      (genericTargetProperRepresentationAtSource sourceFirst sourceMember
        targetFirst targetMember).existsTy continuation
    typing := relationAt.interfaceMap.run_hasType sourceInterface
      (genericTargetProperRepresentationAtSource sourceFirst sourceMember
        targetFirst targetMember).existsTy continuation
  }

private noncomputable def genericProperOpenedBody
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (compiler : ProperMemberCompiler environments firstRelation
      sourceMemberRep targetMemberRep memberDerivation) :
    Exp (properRepresentationAtBinder sourceFirst sourceMember).scope :=
  Pair.fromSuffixExp (sourceFirstAtBinder sourceFirst).binders
    (sourceMemberAtBinder sourceFirst sourceMember).binders
    (genericProperNestedBody environments firstRelation sourceMemberRep
      targetMemberRep compiler).expression

private noncomputable def genericProperOpenedBody_hasType
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (compiler : ProperMemberCompiler environments firstRelation
      sourceMemberRep targetMemberRep memberDerivation) :
    Exp.HasType
      ((properRepresentationAtBinder sourceFirst sourceMember).context
        (base.bindVar
          (Pair.Proper.representation sourceFirst sourceMember).existsTy))
      (genericProperOpenedBody environments firstRelation sourceMemberRep
        targetMemberRep compiler)
      ((properRepresentationAtBinder targetFirst targetMember).existsTy.rename
        (properRepresentationAtBinder sourceFirst sourceMember).weaken) := by
  let firstTele := (sourceFirstAtBinder sourceFirst).binders
  let memberTele := (sourceMemberAtBinder sourceFirst sourceMember).binders
  have nested := (genericProperNestedBody environments firstRelation
    sourceMemberRep targetMemberRep compiler).typing
  have transported := fromSuffixExp_hasType firstTele memberTele nested
  have targetEq :
      (genericTargetProperRepresentationAtSource sourceFirst sourceMember
        targetFirst targetMember).existsTy =
      (((properRepresentationAtBinder targetFirst targetMember).existsTy.rename
        firstTele.weaken).rename memberTele.weaken) := by
    rw [← genericTargetProperRepresentationAtSource_eq]
    rw [← Package.existsTy_rename]
    unfold sourceOpening
    rw [Ty.rename_comp]
    rfl
  have finalTypeEq :
      Pair.fromSuffixTy firstTele memberTele
        (genericTargetProperRepresentationAtSource sourceFirst sourceMember
          targetFirst targetMember).existsTy =
      (properRepresentationAtBinder targetFirst targetMember).existsTy.rename
        (properRepresentationAtBinder sourceFirst sourceMember).weaken := by
    calc
      Pair.fromSuffixTy firstTele memberTele
          (genericTargetProperRepresentationAtSource sourceFirst sourceMember
            targetFirst targetMember).existsTy =
        Pair.fromSuffixTy firstTele memberTele
          (((properRepresentationAtBinder targetFirst targetMember).existsTy.rename
            firstTele.weaken).rename memberTele.weaken) :=
        congrArg (Pair.fromSuffixTy firstTele memberTele) targetEq
      _ = (properRepresentationAtBinder targetFirst targetMember).existsTy.rename
          (firstTele.append memberTele).weaken :=
        fromSuffixTy_weaken firstTele memberTele _
      _ = _ := rfl
  exact finalTypeEq ▸ transported

private noncomputable def genericProperRepresentationBody
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (compiler : ProperMemberCompiler environments firstRelation
      sourceMemberRep targetMemberRep memberDerivation) : Exp (sig ,, .var) :=
  (properRepresentationAtBinder sourceFirst sourceMember).unpack (.var .here)
    (properRepresentationAtBinder targetFirst targetMember).existsTy
    (genericProperOpenedBody environments firstRelation sourceMemberRep
      targetMemberRep compiler)

private noncomputable def genericProperRepresentationBody_hasType
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (compiler : ProperMemberCompiler environments firstRelation
      sourceMemberRep targetMemberRep memberDerivation) :
    Exp.HasType
      (base.bindVar
        (Pair.Proper.representation sourceFirst sourceMember).existsTy)
      (genericProperRepresentationBody environments firstRelation
        sourceMemberRep targetMemberRep compiler)
      ((Pair.Proper.representation targetFirst targetMember).existsTy.weaken
        .var) := by
  have result :=
    (properRepresentationAtBinder sourceFirst sourceMember).unpack_hasType
      (properRepresentationVariable_hasType base sourceFirst sourceMember)
      (genericProperOpenedBody_hasType environments firstRelation
        sourceMemberRep targetMemberRep compiler)
  rw [Ty.weaken, Package.existsTy_rename,
    properRepresentationAtBinder_eq]
  exact result

private noncomputable def genericProperRepresentationConversion
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (compiler : ProperMemberCompiler environments firstRelation
      sourceMemberRep targetMemberRep memberDerivation) :
    Conversion base
      (Pair.Proper.representation sourceFirst sourceMember).existsTy
      (Pair.Proper.representation targetFirst targetMember).existsTy :=
  Conversion.ofFunction
    (Adapter.ofBody
      (Pair.Proper.representation sourceFirst sourceMember).existsTy
      (genericProperRepresentationBody environments firstRelation
        sourceMemberRep targetMemberRep compiler))
    (Adapter.ofBody_hasType
      (genericProperRepresentationBody_hasType environments firstRelation
        sourceMemberRep targetMemberRep compiler))

/-- Compile the literal proper-member dependent-pair covariance rule. -/
noncomputable def proper
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    {firstDerivation : LambdaPFC.Tau.Sub sourceContext
      (.ty sourceFirstType) (.ty targetFirstType)}
    (first : FirstCompilation base firstDerivation sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (member : ProperMemberCompiler environments first.relation
      sourceMemberRep targetMemberRep memberDerivation) :
    Relation base
      (.Pair sourceFirstType label (.ty sourceMemberType))
      (.Pair targetFirstType label (.ty targetMemberType))
      (.stable (Pair.Proper.plan sourceFirst sourceMember))
      (.stable (Pair.Proper.plan targetFirst targetMember)) :=
  let sourceRepresentation :=
    Pair.Proper.representation sourceFirst sourceMember
  let targetRepresentation :=
    Pair.Proper.representation targetFirst targetMember
  let representation := genericProperRepresentationConversion environments
    first.relation sourceMemberRep targetMemberRep member
  let conversion := Conversion.Pair.retarget base sourceRepresentation
    targetRepresentation representation
  Relation.ofConversion
    (.properPair first.relation.sourceRep sourceMemberRep)
    (.properPair first.relation.targetRep targetMemberRep)
    conversion

/-! ## Generic derivation-indexed interval-member covariance -/

private def genericTargetIntervalEndpointAt
    (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope)
    (targetFirst : Shape sig) (targetEndpoint : Shape targetFirst.scope)
    {final : Sig}
    (mapping : Rename
      (intervalMemberAtBinder sourceFirst sourceLower sourceUpper).scope final)
    {finalContext : Ctx final}
    (targetFirstInterface : Shape.Interface finalContext
      ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).rename mapping)) : Shape final :=
  ((targetIntervalLowerAtSource sourceFirst sourceLower sourceUpper
    targetFirst targetEndpoint).rename
      ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).liftRename mapping)).subst
    targetFirstInterface.substitution

/-- Exact interval endpoints and endpoint environments reached after opening
the source representation and mapping its first component.  The selected
runtime shape is intentionally absent here: it comes from the actual opened
witness and is preserved by `IntervalRelation.mapWitness`. -/
structure IntervalMemberScope
    (sourceContext targetContext : LambdaPFC.Ctx n)
    (sourceFirstType targetFirstType : LambdaPFC.Ty n)
    (sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1))
    (base : Ctx sig) : Type where
  environments : EndpointEnvs (sourceContext.snoc sourceFirstType)
    (targetContext.snoc targetFirstType) base
  source : Wf.Interval base sourceLowerType sourceUpperType
  target : Wf.Interval base targetLowerType targetUpperType

/-- Build the exact recursive interval scope in the continuation selected by
the first-component interface map. -/
noncomputable def intervalMemberScopeAt
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper)
    (mapping : Rename
      (IntervalMemberCompiler.CallbackSig sourceFirst sourceLower sourceUpper)
      final)
    (typed : Rename.Typed
      (IntervalMemberCompiler.CallbackContext base sourceFirst sourceLower
        sourceUpper)
      finalContext mapping)
    (sourceFirstInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.SourceFirstAt sourceFirst sourceLower sourceUpper
        mapping))
    (targetFirstInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.TargetFirstAt sourceFirst sourceLower sourceUpper
        targetFirst mapping)) :
    IntervalMemberScope sourceContext targetContext sourceFirstType
      targetFirstType sourceLowerType sourceUpperType targetLowerType
      targetUpperType finalContext :=
  let opening := intervalOpening sourceFirst sourceLower sourceUpper
  let openingTyped := intervalOpening_typed base sourceFirst sourceLower
    sourceUpper
  let firstAt := (adjustedIntervalFirstRelationAtSource
    (sourceLower := sourceLower) (sourceUpper := sourceUpper)
    firstRelation).targetRename mapping typed
  let environmentsAt := (environments.targetRename opening
    openingTyped).targetRename mapping typed
  let source := sourceIntervalAt sourceLowerRep sourceUpperRep mapping typed
  let targetLowerRepAt := targetIntervalEndpointRepAt targetLowerRep mapping
    typed targetFirstInterface
  let targetUpperRepAt := targetIntervalEndpointRepAt targetUpperRep mapping
    typed targetFirstInterface
  {
    environments := {
      source := extendAtInterface environmentsAt.source sourceFirstType
        sourceFirstInterface firstAt.sourceRep
      target := extendAtInterface environmentsAt.target targetFirstType
        targetFirstInterface firstAt.targetRep
    }
    source := source
    target := {
      lower := genericTargetIntervalEndpointAt sourceFirst sourceLower
        sourceUpper targetFirst targetLower mapping targetFirstInterface
      upper := genericTargetIntervalEndpointAt sourceFirst sourceLower
        sourceUpper targetFirst targetUpper mapping targetFirstInterface
      lowerRep := targetLowerRepAt
      upperRep := targetUpperRepAt
    }
  }

/-- The exact contextual scope present at a delayed interval-member callback.
The source interval's hidden selected witness remains target-only; this scope
contains only the concrete first values needed to instantiate the literal
member derivation. -/
noncomputable def intervalActionScopeAt
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    (root : ContextRelation.Scope sourceContext targetContext .source base)
    (first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (mapping : Rename
      (IntervalMemberCompiler.CallbackSig sourceFirst sourceLower sourceUpper)
      final)
    (typed : Rename.Typed
      (IntervalMemberCompiler.CallbackContext base sourceFirst sourceLower
        sourceUpper)
      finalContext mapping)
    (sourceFirstInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.SourceFirstAt sourceFirst sourceLower sourceUpper
        mapping))
    (targetFirstInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.TargetFirstAt sourceFirst sourceLower sourceUpper
        targetFirst mapping)) :
    ContextRelation.Scope (sourceContext.snoc sourceFirstType)
      (targetContext.snoc targetFirstType) .source finalContext := by
  let opening := intervalOpening sourceFirst sourceLower sourceUpper
  let openingTyped := intervalOpening_typed base sourceFirst sourceLower
    sourceUpper
  let rootAt := (root.targetRename opening openingTyped).targetRename
    mapping typed
  let firstAt := (adjustedIntervalFirstRelationAtSource
    (sourceLower := sourceLower) (sourceUpper := sourceUpper)
    first).targetRename mapping typed
  exact rootAt.extendPair sourceFirstInterface firstAt.sourceRep
    targetFirstInterface firstAt.targetRep firstAt

/-- Recursive compilation of the literal interval-member premise.  The
compiler receives both exact first interfaces and the computed two-endpoint
scope; it returns only the contravariant-lower/covariant-upper relations. -/
structure IntervalMemberCompiler
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper)
    (_derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)) : Type where
  compile : {final : Sig} -> {finalContext : Ctx final} ->
    (mapping : Rename
      (IntervalMemberCompiler.CallbackSig sourceFirst sourceLower sourceUpper)
      final) ->
    (typed : Rename.Typed
      (IntervalMemberCompiler.CallbackContext base sourceFirst sourceLower
        sourceUpper)
      finalContext mapping) ->
    (sourceFirstInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.SourceFirstAt sourceFirst sourceLower sourceUpper
        mapping)) ->
    (targetFirstInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.TargetFirstAt sourceFirst sourceLower sourceUpper
        targetFirst mapping)) ->
    let scope := intervalMemberScopeAt environments firstRelation
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep mapping typed
      sourceFirstInterface targetFirstInterface
    AtomicSubtyping.IntervalRelation scope.source scope.target

/-- An interval-member compiler retaining one proof-only payload at the exact
contravariant-lower/covariant-upper relation returned by its callback. -/
structure IntervalMemberCompiler.Enriched
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (root : ContextRelation.Scope sourceContext targetContext .source base)
    (first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper)
    (_derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)) : Type 1 where
  Retained : {final : Sig} -> {finalContext : Ctx final} ->
    (mapping : Rename
      (IntervalMemberCompiler.CallbackSig sourceFirst sourceLower sourceUpper)
      final) ->
    (typed : Rename.Typed
      (IntervalMemberCompiler.CallbackContext base sourceFirst sourceLower
        sourceUpper)
      finalContext mapping) ->
    (sourceFirstInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.SourceFirstAt sourceFirst sourceLower sourceUpper
        mapping)) ->
    (targetFirstInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.TargetFirstAt sourceFirst sourceLower sourceUpper
        targetFirst mapping)) ->
    let scope := intervalMemberScopeAt root.endpointEnvs first sourceLowerRep
      sourceUpperRep targetLowerRep targetUpperRep mapping typed
      sourceFirstInterface targetFirstInterface
    AtomicSubtyping.IntervalRelation scope.source scope.target -> Type
  compile : {final : Sig} -> {finalContext : Ctx final} ->
    (mapping : Rename
      (IntervalMemberCompiler.CallbackSig sourceFirst sourceLower sourceUpper)
      final) ->
    (typed : Rename.Typed
      (IntervalMemberCompiler.CallbackContext base sourceFirst sourceLower
        sourceUpper)
      finalContext mapping) ->
    (sourceFirstInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.SourceFirstAt sourceFirst sourceLower sourceUpper
        mapping)) ->
    (targetFirstInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.TargetFirstAt sourceFirst sourceLower sourceUpper
        targetFirst mapping)) ->
    let scope := intervalMemberScopeAt root.endpointEnvs first sourceLowerRep
      sourceUpperRep targetLowerRep targetUpperRep mapping typed
      sourceFirstInterface targetFirstInterface
    Sigma fun relation : AtomicSubtyping.IntervalRelation scope.source
        scope.target =>
      Retained mapping typed sourceFirstInterface targetFirstInterface relation

/-- Erase only the retained proof payload. -/
noncomputable def IntervalMemberCompiler.Enriched.erase
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : IntervalMemberCompiler.Enriched root first sourceLowerRep
      sourceUpperRep targetLowerRep targetUpperRep derivation) :
    IntervalMemberCompiler root.endpointEnvs first sourceLowerRep
      sourceUpperRep targetLowerRep targetUpperRep derivation where
  compile mapping typed sourceFirstInterface targetFirstInterface :=
    (compiler.compile mapping typed sourceFirstInterface
      targetFirstInterface).1

/-- Instantiate the enriched interval callback at one actual source witness.
The returned witness is mapped by the very relation whose proof payload is
retained in the same dependent pair. -/
noncomputable def IntervalMemberCompiler.Enriched.mapAt
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : IntervalMemberCompiler.Enriched root first sourceLowerRep
      sourceUpperRep targetLowerRep targetUpperRep derivation)
    {final : Sig} {finalContext : Ctx final}
    (mapping : Rename
      (IntervalMemberCompiler.CallbackSig sourceFirst sourceLower sourceUpper)
      final)
    (typed : Rename.Typed
      (IntervalMemberCompiler.CallbackContext base sourceFirst sourceLower
        sourceUpper)
      finalContext mapping)
    (sourceFirstInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.SourceFirstAt sourceFirst sourceLower sourceUpper
        mapping))
    (targetFirstInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.TargetFirstAt sourceFirst sourceLower sourceUpper
        targetFirst mapping))
    (sourceWitness :
      let scope := intervalMemberScopeAt root.endpointEnvs first sourceLowerRep
        sourceUpperRep targetLowerRep targetUpperRep mapping typed
        sourceFirstInterface targetFirstInterface
      Conversion.Interval.Witness finalContext scope.source.lower
        scope.source.upper) :
    let scope := intervalMemberScopeAt root.endpointEnvs first sourceLowerRep
      sourceUpperRep targetLowerRep targetUpperRep mapping typed
      sourceFirstInterface targetFirstInterface
    Sigma fun relation : AtomicSubtyping.IntervalRelation scope.source
        scope.target =>
      compiler.Retained mapping typed sourceFirstInterface
          targetFirstInterface relation ×
        Conversion.Interval.Witness finalContext scope.target.lower
          scope.target.upper :=
  let compiled := compiler.compile mapping typed sourceFirstInterface
    targetFirstInterface
  ⟨compiled.1, compiled.2, compiled.1.mapWitness sourceWitness⟩

/-- Mapping interval bounds preserves the exact selected identity. -/
@[simp] theorem IntervalMemberCompiler.Enriched.mapAt_selected
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : IntervalMemberCompiler.Enriched root first sourceLowerRep
      sourceUpperRep targetLowerRep targetUpperRep derivation)
    {final : Sig} {finalContext : Ctx final}
    (mapping : Rename
      (IntervalMemberCompiler.CallbackSig sourceFirst sourceLower sourceUpper)
      final)
    (typed : Rename.Typed
      (IntervalMemberCompiler.CallbackContext base sourceFirst sourceLower
        sourceUpper)
      finalContext mapping)
    (sourceFirstInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.SourceFirstAt sourceFirst sourceLower sourceUpper
        mapping))
    (targetFirstInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.TargetFirstAt sourceFirst sourceLower sourceUpper
        targetFirst mapping))
    (sourceWitness :
      let scope := intervalMemberScopeAt root.endpointEnvs first sourceLowerRep
        sourceUpperRep targetLowerRep targetUpperRep mapping typed
        sourceFirstInterface targetFirstInterface
      Conversion.Interval.Witness finalContext scope.source.lower
        scope.source.upper) :
    (compiler.mapAt mapping typed sourceFirstInterface targetFirstInterface
      sourceWitness).2.2.selected = sourceWitness.selected := by
  rfl

private noncomputable def intervalRepresentationPackage
    {targetContext : Ctx sig}
    {first : Shape sig} {lower upper : Shape first.scope}
    (interface : Shape.Interface targetContext
      (.stable (Pair.Interval.plan first lower upper))) : Exp sig :=
  (Pair.asRepresentation
    (Pair.Interval.representation first lower upper)).subst
      interface.substitution

private noncomputable def intervalRepresentationPackage_hasType
    {targetContext : Ctx sig}
    {first : Shape sig} {lower upper : Shape first.scope}
    (interface : Shape.Interface targetContext
      (.stable (Pair.Interval.plan first lower upper))) :
    Exp.HasType targetContext (intervalRepresentationPackage interface)
      (Pair.Interval.representation first lower upper).existsTy := by
  let representation := Pair.Interval.representation first lower upper
  have opened :=
    (Pair.asRepresentation_hasType targetContext representation).subst
      interface.arguments.substitution_typed
  have resultType :
      (Pair.finalRepresentationTy representation).subst
          interface.arguments.substitution =
        representation.existsTy := by
    calc
      _ = interface.arguments.instantiate
          (representation.existsTy.rename
            (Pair.Interval.plan first lower upper).telescope.weaken) :=
        (interface.arguments.instantiate_eq_subst _).symm
      _ = representation.existsTy :=
        interface.arguments.instantiate_weaken representation.existsTy
  rw [resultType] at opened
  exact opened

/-- Exact root-to-callback mapping.  This names only the already-computed
public callback index; the representation-opening implementation remains
private. -/
abbrev MaterialRootAt
    (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope)
    {final : Sig}
    (mapping : Rename
      (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst
        sourceLower sourceUpper) final) : Rename sig final :=
  (intervalOpening sourceFirst sourceLower sourceUpper).comp mapping

noncomputable def materialRootAt_typed
    {base : Ctx sig}
    (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope)
    {final : Sig} {finalContext : Ctx final}
    (mapping : Rename
      (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst
        sourceLower sourceUpper) final)
    (typed : Rename.Typed
      (PairSubtyping.IntervalMemberCompiler.CallbackContext base sourceFirst
        sourceLower sourceUpper) finalContext mapping) :
    Rename.Typed base finalContext
      (MaterialRootAt sourceFirst sourceLower sourceUpper mapping) :=
  TypedRename.comp
    (intervalOpening_typed base sourceFirst sourceLower sourceUpper) typed

/-- The unique source-first interface opened from the actual source
representation package.  It is a definition, not a caller-supplied witness. -/
noncomputable def materialSourceFirstInterface
    {base : Ctx sig}
    (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope)
    {final : Sig} {finalContext : Ctx final}
    (mapping : Rename
      (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst
        sourceLower sourceUpper) final)
    (typed : Rename.Typed
      (PairSubtyping.IntervalMemberCompiler.CallbackContext base sourceFirst
        sourceLower sourceUpper) finalContext mapping) :
    Shape.Interface finalContext
      (PairSubtyping.IntervalMemberCompiler.SourceFirstAt sourceFirst
        sourceLower sourceUpper mapping) :=
  (intervalSourceFirstInterface base sourceFirst sourceLower sourceUpper).rename
    mapping typed

/-- Pre-extension target environment in the literal staged callback. -/
noncomputable def materialTargetEnvironment
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (root : ContextRelation.Scope sourceContext targetContext .source base)
    (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope)
    {final : Sig} {finalContext : Ctx final}
    (mapping : Rename
      (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst
        sourceLower sourceUpper) final)
    (typed : Rename.Typed
      (PairSubtyping.IntervalMemberCompiler.CallbackContext base sourceFirst
        sourceLower sourceUpper) finalContext mapping) :
    Env targetContext finalContext :=
  (((root.endpointEnvs.targetRename
      (intervalOpening sourceFirst sourceLower sourceUpper)
      (intervalOpening_typed base sourceFirst sourceLower sourceUpper))
    ).targetRename mapping typed).target

/-- First target representation before extending the callback environment. -/
noncomputable def materialTargetFirstRep
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    (_root : ContextRelation.Scope sourceContext targetContext .source base)
    (first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    {final : Sig} {finalContext : Ctx final}
    (mapping : Rename
      (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst
        sourceLower sourceUpper) final)
    (typed : Rename.Typed
      (PairSubtyping.IntervalMemberCompiler.CallbackContext base sourceFirst
        sourceLower sourceUpper) finalContext mapping) :
    Rep finalContext targetFirstType
      (PairSubtyping.IntervalMemberCompiler.TargetFirstAt sourceFirst
        sourceLower sourceUpper targetFirst mapping) :=
  ((adjustedIntervalFirstRelationAtSource
      (sourceLower := sourceLower) (sourceUpper := sourceUpper) first
    ).targetRename mapping typed).targetRep

/-- Target endpoint family before substitution by the actual first
interface. -/
abbrev MaterialTargetEndpointAt
    (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope)
    (targetFirst : Shape sig)
    (targetEndpoint : Shape targetFirst.scope)
    {final : Sig}
    (mapping : Rename
      (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst
        sourceLower sourceUpper) final) :
    Shape
      (PairSubtyping.IntervalMemberCompiler.TargetFirstAt sourceFirst
        sourceLower sourceUpper targetFirst mapping).scope :=
  (targetIntervalLowerAtSource sourceFirst sourceLower sourceUpper targetFirst
    targetEndpoint).rename
      ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).liftRename mapping)

/-- Target endpoint representation at the callback first scope, before the
actual first-interface target substitution. -/
noncomputable def materialTargetEndpointRep
    {base : Ctx sig}
    {endpointType : LambdaPFC.Ty (n + 1)}
    {sourceFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetFirst : Shape sig}
    {targetEndpoint : Shape targetFirst.scope}
    (endpointRep : Rep (targetFirst.context base)
      endpointType targetEndpoint)
    {final : Sig}
    (mapping : Rename
      (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst
        sourceLower sourceUpper) final)
    {finalContext : Ctx final}
    (typed : Rename.Typed
      (PairSubtyping.IntervalMemberCompiler.CallbackContext base sourceFirst
        sourceLower sourceUpper) finalContext mapping) :
    Rep
      ((PairSubtyping.IntervalMemberCompiler.TargetFirstAt sourceFirst
        sourceLower sourceUpper targetFirst mapping).context finalContext)
      endpointType
      (MaterialTargetEndpointAt sourceFirst sourceLower sourceUpper targetFirst
        targetEndpoint mapping) := by
  let atBinder := endpointRep.targetRename
    (targetFirst.liftRename (Rename.weaken .var))
    (targetFirst.liftRename_typed
      (Rename.Typed.weaken base
        (.var (Pair.Interval.representation sourceFirst sourceLower
          sourceUpper).existsTy)))
  let atSource := atBinder.targetRename
    ((sourceFirstAtBinder targetFirst).liftRename
      (intervalSourceOpening sourceFirst sourceLower sourceUpper))
    ((sourceFirstAtBinder targetFirst).liftRename_typed
      (intervalSourceOpening_typed base sourceFirst sourceLower sourceUpper))
  exact atSource.targetRename
    ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).liftRename mapping)
    ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).liftRename_typed typed)

/-- The exact member scope selected by the manufactured source-first
interface and the actual target-first interface returned by the first map. -/
noncomputable abbrev MaterialMembersAt
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (root : ContextRelation.Scope sourceContext targetContext .source base)
    (first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper)
    {final : Sig} {finalContext : Ctx final}
    (mapping : Rename
      (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst
        sourceLower sourceUpper) final)
    (typed : Rename.Typed
      (PairSubtyping.IntervalMemberCompiler.CallbackContext base sourceFirst
        sourceLower sourceUpper) finalContext mapping)
    (targetFirstInterface : Shape.Interface finalContext
      (PairSubtyping.IntervalMemberCompiler.TargetFirstAt sourceFirst
        sourceLower sourceUpper targetFirst mapping)) :=
  PairSubtyping.intervalMemberScopeAt root.endpointEnvs first sourceLowerRep
    sourceUpperRep targetLowerRep targetUpperRep mapping typed
    (materialSourceFirstInterface sourceFirst sourceLower sourceUpper mapping
      typed)
    targetFirstInterface

/-- One ephemeral same-callback result.  Its source interface is not a field:
all indices mention the unique interface manufactured by `runMaterial`. -/
structure MaterialView
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : PairSubtyping.IntervalMemberCompiler.Enriched root first
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep derivation)
    {final : Sig} {finalContext : Ctx final}
    (mapping : Rename
      (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst
        sourceLower sourceUpper) final)
    (typed : Rename.Typed
      (PairSubtyping.IntervalMemberCompiler.CallbackContext base sourceFirst
        sourceLower sourceUpper) finalContext mapping)
    (targetFirstInterface : Shape.Interface finalContext
      (PairSubtyping.IntervalMemberCompiler.TargetFirstAt sourceFirst
        sourceLower sourceUpper targetFirst mapping)) where
  sourceWitness :
    let members := MaterialMembersAt root first sourceLowerRep sourceUpperRep
      targetLowerRep targetUpperRep mapping typed targetFirstInterface
    Conversion.Interval.Witness finalContext members.source.lower
      members.source.upper
  relation :
    let members := MaterialMembersAt root first sourceLowerRep sourceUpperRep
      targetLowerRep targetUpperRep mapping typed targetFirstInterface
    AtomicSubtyping.IntervalRelation members.source members.target
  retained : compiler.Retained mapping typed
    (materialSourceFirstInterface sourceFirst sourceLower sourceUpper mapping
      typed)
    targetFirstInterface relation
  targetWitness :
    let members := MaterialMembersAt root first sourceLowerRep sourceUpperRep
      targetLowerRep targetUpperRep mapping typed targetFirstInterface
    Conversion.Interval.Witness finalContext members.target.lower
      members.target.upper
  selectedBridge : Conversion.Bridge finalContext
    sourceWitness.selected.inputTy targetWitness.selected.inputTy

/-- A result-polymorphic consumer invoked at the one callback scope produced
by the actual interval-pair opening and first-component interface map. -/
structure MaterialContinuation
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : PairSubtyping.IntervalMemberCompiler.Enriched root first
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep derivation)
    (answer : Ty sig) : Type 1 where
  body : {final : Sig} -> {finalContext : Ctx final} ->
    (mapping : Rename
      (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst
        sourceLower sourceUpper) final) ->
    (typed : Rename.Typed
      (PairSubtyping.IntervalMemberCompiler.CallbackContext base sourceFirst
        sourceLower sourceUpper) finalContext mapping) ->
    Rename.Typed base finalContext
      (MaterialRootAt sourceFirst sourceLower sourceUpper mapping) ->
    (targetFirstInterface : Shape.Interface finalContext
      (PairSubtyping.IntervalMemberCompiler.TargetFirstAt sourceFirst
        sourceLower sourceUpper targetFirst mapping)) ->
    MaterialView compiler mapping typed targetFirstInterface ->
    Path.Body finalContext
      (answer.rename
        (MaterialRootAt sourceFirst sourceLower sourceUpper mapping))

private noncomputable def materialMemberBody
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : PairSubtyping.IntervalMemberCompiler.Enriched root first
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep derivation)
    (answer : Ty sig)
    (continuation : MaterialContinuation compiler answer)
    (mapping : Rename
      (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst
        sourceLower sourceUpper) final)
    (typed : Rename.Typed
      (PairSubtyping.IntervalMemberCompiler.CallbackContext base sourceFirst
        sourceLower sourceUpper) finalContext mapping)
    (targetFirstInterface : Shape.Interface finalContext
      (PairSubtyping.IntervalMemberCompiler.TargetFirstAt sourceFirst
        sourceLower sourceUpper targetFirst mapping)) :
    Path.Body finalContext
      (answer.rename (intervalOpening sourceFirst sourceLower sourceUpper |>.comp
        mapping)) := by
  let sourceFirstInterface : Shape.Interface finalContext
      (PairSubtyping.IntervalMemberCompiler.SourceFirstAt sourceFirst
        sourceLower sourceUpper mapping) := by
    exact materialSourceFirstInterface sourceFirst sourceLower sourceUpper
      mapping typed
  let scope := MaterialMembersAt root first sourceLowerRep sourceUpperRep
    targetLowerRep targetUpperRep mapping typed targetFirstInterface
  let sourceWitnessRaw := renameIntervalWitness
    (openedIntervalWitness base sourceFirst sourceLower sourceUpper)
    mapping typed
  let sourceWitness : Conversion.Interval.Witness finalContext
      scope.source.lower scope.source.upper := by
    exact sourceWitnessRaw
  let mapped := compiler.mapAt mapping typed sourceFirstInterface
    targetFirstInterface sourceWitness
  let selectedBridge : Conversion.Bridge finalContext
      sourceWitness.selected.inputTy mapped.2.2.selected.inputTy := {
    leftToRight := Conversion.refl finalContext sourceWitness.selected.inputTy
    rightToLeft := Conversion.refl finalContext sourceWitness.selected.inputTy
  }
  let view : MaterialView compiler mapping typed targetFirstInterface := {
    sourceWitness := sourceWitness
    relation := mapped.1
    retained := mapped.2.1
    targetWitness := mapped.2.2
    selectedBridge := selectedBridge
  }
  exact continuation.body mapping typed
    (materialRootAt_typed sourceFirst sourceLower sourceUpper mapping typed)
    targetFirstInterface view

private noncomputable def materialFirstContinuation
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : PairSubtyping.IntervalMemberCompiler.Enriched root first
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep derivation)
    (answer : Ty sig)
    (continuation : MaterialContinuation compiler answer) :
    InterfaceMap.Continuation
      (intervalSourceOpenedContext base sourceFirst sourceLower sourceUpper)
      (targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst)
      (answer.rename (intervalOpening sourceFirst sourceLower sourceUpper)) where
  body mapping _finalContext typed targetFirstInterface :=
    (materialMemberBody compiler answer continuation mapping typed
      targetFirstInterface).expression
  body_hasType mapping _finalContext typed targetFirstInterface := by
    simpa only [Ty.rename_comp] using
      (materialMemberBody compiler answer continuation mapping typed
        targetFirstInterface).typing

private noncomputable def materialNestedBody
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : PairSubtyping.IntervalMemberCompiler.Enriched root first
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep derivation)
    (answer : Ty sig)
    (continuation : MaterialContinuation compiler answer) :
    Path.Body
      (intervalSourceOpenedContext base sourceFirst sourceLower sourceUpper)
      (answer.rename (intervalOpening sourceFirst sourceLower sourceUpper)) :=
  let relationAt := adjustedIntervalFirstRelationAtSource
    (sourceLower := sourceLower) (sourceUpper := sourceUpper) first
  let sourceInterface := intervalSourceFirstInterface base sourceFirst
    sourceLower sourceUpper
  let next := materialFirstContinuation compiler answer continuation
  {
    expression := relationAt.interfaceMap.run sourceInterface
      (answer.rename (intervalOpening sourceFirst sourceLower sourceUpper)) next
    typing := relationAt.interfaceMap.run_hasType sourceInterface
      (answer.rename (intervalOpening sourceFirst sourceLower sourceUpper)) next
  }

private noncomputable def materialOpenedBody
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : PairSubtyping.IntervalMemberCompiler.Enriched root first
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep derivation)
    (answer : Ty sig)
    (continuation : MaterialContinuation compiler answer) :
    Exp (intervalRepresentationAtBinder sourceFirst sourceLower
      sourceUpper).scope :=
  Pair.fromSuffixExp (sourceFirstAtBinder sourceFirst).binders
    (intervalMemberAtBinder sourceFirst sourceLower sourceUpper)
    (materialNestedBody compiler answer continuation).expression

private noncomputable def materialOpenedBody_hasType
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : PairSubtyping.IntervalMemberCompiler.Enriched root first
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep derivation)
    (answer : Ty sig)
    (continuation : MaterialContinuation compiler answer) :
    Exp.HasType
      ((intervalRepresentationAtBinder sourceFirst sourceLower
        sourceUpper).context
          (base.bindVar
            (Pair.Interval.representation sourceFirst sourceLower
              sourceUpper).existsTy))
      (materialOpenedBody compiler answer continuation)
      ((answer.weaken .var).rename
        (intervalRepresentationAtBinder sourceFirst sourceLower
          sourceUpper).weaken) := by
  let firstTele := (sourceFirstAtBinder sourceFirst).binders
  let memberTele := intervalMemberAtBinder sourceFirst sourceLower sourceUpper
  have nested := (materialNestedBody compiler answer continuation).typing
  have transported := fromSuffixExp_hasType firstTele memberTele nested
  have openingTypeEq :
      answer.rename (intervalOpening sourceFirst sourceLower sourceUpper) =
      (((answer.rename (Rename.weaken .var)).rename firstTele.weaken).rename
        memberTele.weaken) := by
    unfold intervalOpening intervalSourceOpening firstTele memberTele
    rw [Ty.rename_comp, Ty.rename_comp]
  have finalTypeEq :
      Pair.fromSuffixTy firstTele memberTele
          (answer.rename
            (intervalOpening sourceFirst sourceLower sourceUpper)) =
      (answer.weaken .var).rename
        (intervalRepresentationAtBinder sourceFirst sourceLower
          sourceUpper).weaken := by
    calc
      _ = Pair.fromSuffixTy firstTele memberTele
          (((answer.rename (Rename.weaken .var)).rename firstTele.weaken).rename
            memberTele.weaken) :=
        congrArg (Pair.fromSuffixTy firstTele memberTele) openingTypeEq
      _ = (answer.rename (Rename.weaken .var)).rename
          (firstTele.append memberTele).weaken :=
        fromSuffixTy_weaken firstTele memberTele _
      _ = _ := rfl
  exact finalTypeEq ▸ transported

private noncomputable def materialRepresentationBody
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : PairSubtyping.IntervalMemberCompiler.Enriched root first
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep derivation)
    (answer : Ty sig)
    (continuation : MaterialContinuation compiler answer) : Exp (sig ,, .var) :=
  (intervalRepresentationAtBinder sourceFirst sourceLower sourceUpper).unpack
    (.var .here) (answer.weaken .var)
    (materialOpenedBody compiler answer continuation)

private noncomputable def materialRepresentationBody_hasType
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : PairSubtyping.IntervalMemberCompiler.Enriched root first
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep derivation)
    (answer : Ty sig)
    (continuation : MaterialContinuation compiler answer) :
    Exp.HasType
      (base.bindVar
        (Pair.Interval.representation sourceFirst sourceLower
          sourceUpper).existsTy)
      (materialRepresentationBody compiler answer continuation)
      (answer.weaken .var) :=
  (intervalRepresentationAtBinder sourceFirst sourceLower sourceUpper).unpack_hasType
    (intervalRepresentationVariable_hasType base sourceFirst sourceLower
      sourceUpper)
    (materialOpenedBody_hasType compiler answer continuation)

/-- Open one actual interval-pair interface, map its actual first interface,
instantiate one enriched member callback at the opened source witness, and
reclose a typed result-polymorphic consumer. -/
noncomputable def runMaterial
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : PairSubtyping.IntervalMemberCompiler.Enriched root first
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep derivation)
    (sourceInterface : Shape.Interface base
      (.stable (Pair.Interval.plan sourceFirst sourceLower sourceUpper)))
    (answer : Ty sig)
    (continuation : MaterialContinuation compiler answer) :
    Path.Body base answer :=
  let package := intervalRepresentationPackage sourceInterface
  let packageTyping := intervalRepresentationPackage_hasType sourceInterface
  let body := materialRepresentationBody compiler answer continuation
  let bodyTyping := materialRepresentationBody_hasType compiler answer
    continuation
  {
    expression := Adapter.apply
      (Adapter.ofBody
        (Pair.Interval.representation sourceFirst sourceLower
          sourceUpper).existsTy body)
      package
    typing := Adapter.apply_hasType (Adapter.ofBody_hasType bodyTyping)
      packageTyping
  }

private theorem targetIntervalRepresentationAtSource_rename
    (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope)
    (targetFirst : Shape sig)
    (targetLower targetUpper : Shape targetFirst.scope)
    (mapping : Rename
      (intervalMemberAtBinder sourceFirst sourceLower sourceUpper).scope
      final) :
    (targetIntervalRepresentationAtSource sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper).rename mapping =
      Pair.Interval.representation
        ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
          targetFirst).rename mapping)
        ((targetIntervalLowerAtSource sourceFirst sourceLower sourceUpper
          targetFirst targetLower).rename
            ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
              targetFirst).liftRename mapping))
        ((targetIntervalUpperAtSource sourceFirst sourceLower sourceUpper
          targetFirst targetUpper).rename
            ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
              targetFirst).liftRename mapping)) :=
  Pair.Interval.representation_rename _ _ _ mapping

private noncomputable def genericIntervalMemberBody
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : IntervalMemberCompiler environments firstRelation
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
      memberDerivation)
    (mapping : Rename
      (intervalMemberAtBinder sourceFirst sourceLower sourceUpper).scope final)
    (typed : Rename.Typed
      (intervalSourceOpenedContext base sourceFirst sourceLower sourceUpper)
      finalContext mapping)
    (targetFirstInterface : Shape.Interface finalContext
      ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).rename mapping)) :
    Path.Body finalContext
      ((targetIntervalRepresentationAtSource sourceFirst sourceLower
        sourceUpper targetFirst targetLower targetUpper).existsTy.rename
          mapping) := by
  let sourceFirstInterface : Shape.Interface finalContext
      (((sourceFirstAtBinder sourceFirst).rename
        (intervalSourceOpening sourceFirst sourceLower sourceUpper)).rename
          mapping) :=
    (intervalSourceFirstInterface base sourceFirst sourceLower
      sourceUpper).rename mapping typed
  let scope := intervalMemberScopeAt environments firstRelation
    sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep mapping typed
    sourceFirstInterface targetFirstInterface
  let intervalRelation := compiler.compile mapping typed sourceFirstInterface
    targetFirstInterface
  let witnessAt := renameIntervalWitness
    (openedIntervalWitness base sourceFirst sourceLower sourceUpper)
    mapping typed
  let mapped := intervalRelation.mapWitness witnessAt
  let targetFirstAt :=
    (targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).rename mapping
  let targetLowerAt :=
    (targetIntervalLowerAtSource sourceFirst sourceLower sourceUpper
      targetFirst targetLower).rename
        ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
          targetFirst).liftRename mapping)
  let targetUpperAt :=
    (targetIntervalUpperAtSource sourceFirst sourceLower sourceUpper
      targetFirst targetUpper).rename
        ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
          targetFirst).liftRename mapping)
  let arguments := Pair.Interval.representationArguments targetFirstAt
    targetLowerAt targetUpperAt targetFirstInterface mapped.selected
    mapped.lowerFunction (by
      exact mapped.lowerTyping)
    mapped.upperFunction (by
      exact mapped.upperTyping)
  exact {
    expression := Telescope.pack arguments
    typing := by
      have packed := Telescope.pack_hasType arguments
      simpa only [Package.existsTy_rename,
        targetIntervalRepresentationAtSource_rename] using packed
  }

private noncomputable def genericIntervalFirstContinuation
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : IntervalMemberCompiler environments firstRelation
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
      memberDerivation) :
    InterfaceMap.Continuation
      (intervalSourceOpenedContext base sourceFirst sourceLower sourceUpper)
      (targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst)
      (targetIntervalRepresentationAtSource sourceFirst sourceLower sourceUpper
        targetFirst targetLower targetUpper).existsTy where
  body mapping _finalContext typed targetFirstInterface :=
    (genericIntervalMemberBody environments firstRelation sourceLowerRep
      sourceUpperRep targetLowerRep targetUpperRep compiler mapping typed
      targetFirstInterface).expression
  body_hasType mapping _finalContext typed targetFirstInterface :=
    (genericIntervalMemberBody environments firstRelation sourceLowerRep
      sourceUpperRep targetLowerRep targetUpperRep compiler mapping typed
      targetFirstInterface).typing

private noncomputable def genericIntervalNestedBody
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : IntervalMemberCompiler environments firstRelation
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
      memberDerivation) :
    Path.Body
      (intervalSourceOpenedContext base sourceFirst sourceLower sourceUpper)
      (targetIntervalRepresentationAtSource sourceFirst sourceLower sourceUpper
        targetFirst targetLower targetUpper).existsTy :=
  let relationAt := adjustedIntervalFirstRelationAtSource
    (sourceLower := sourceLower) (sourceUpper := sourceUpper) firstRelation
  let sourceInterface := intervalSourceFirstInterface base sourceFirst
    sourceLower sourceUpper
  let continuation := genericIntervalFirstContinuation environments
    firstRelation sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
    compiler
  {
    expression := relationAt.interfaceMap.run sourceInterface
      (targetIntervalRepresentationAtSource sourceFirst sourceLower sourceUpper
        targetFirst targetLower targetUpper).existsTy continuation
    typing := relationAt.interfaceMap.run_hasType sourceInterface
      (targetIntervalRepresentationAtSource sourceFirst sourceLower sourceUpper
        targetFirst targetLower targetUpper).existsTy continuation
  }

private noncomputable def genericIntervalOpenedBody
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : IntervalMemberCompiler environments firstRelation
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
      memberDerivation) :
    Exp (intervalRepresentationAtBinder sourceFirst sourceLower
      sourceUpper).scope :=
  Pair.fromSuffixExp (sourceFirstAtBinder sourceFirst).binders
    (intervalMemberAtBinder sourceFirst sourceLower sourceUpper)
    (genericIntervalNestedBody environments firstRelation sourceLowerRep
      sourceUpperRep targetLowerRep targetUpperRep compiler).expression

private noncomputable def genericIntervalOpenedBody_hasType
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : IntervalMemberCompiler environments firstRelation
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
      memberDerivation) :
    Exp.HasType
      ((intervalRepresentationAtBinder sourceFirst sourceLower
        sourceUpper).context
          (base.bindVar
            (Pair.Interval.representation sourceFirst sourceLower
              sourceUpper).existsTy))
      (genericIntervalOpenedBody environments firstRelation sourceLowerRep
        sourceUpperRep targetLowerRep targetUpperRep compiler)
      ((intervalRepresentationAtBinder targetFirst targetLower
        targetUpper).existsTy.rename
          (intervalRepresentationAtBinder sourceFirst sourceLower
            sourceUpper).weaken) := by
  let firstTele := (sourceFirstAtBinder sourceFirst).binders
  let memberTele := intervalMemberAtBinder sourceFirst sourceLower sourceUpper
  have nested := (genericIntervalNestedBody environments firstRelation
    sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep compiler).typing
  have transported := fromSuffixExp_hasType firstTele memberTele nested
  have targetEq :
      (targetIntervalRepresentationAtSource sourceFirst sourceLower sourceUpper
        targetFirst targetLower targetUpper).existsTy =
      (((intervalRepresentationAtBinder targetFirst targetLower
        targetUpper).existsTy.rename firstTele.weaken).rename
          memberTele.weaken) := by
    rw [← targetIntervalRepresentationAtSource_eq]
    rw [← Package.existsTy_rename]
    unfold intervalSourceOpening
    rw [Ty.rename_comp]
  have finalTypeEq :
      Pair.fromSuffixTy firstTele memberTele
        (targetIntervalRepresentationAtSource sourceFirst sourceLower
          sourceUpper targetFirst targetLower targetUpper).existsTy =
      (intervalRepresentationAtBinder targetFirst targetLower
        targetUpper).existsTy.rename
          (intervalRepresentationAtBinder sourceFirst sourceLower
            sourceUpper).weaken := by
    calc
      Pair.fromSuffixTy firstTele memberTele
          (targetIntervalRepresentationAtSource sourceFirst sourceLower
            sourceUpper targetFirst targetLower targetUpper).existsTy =
        Pair.fromSuffixTy firstTele memberTele
          (((intervalRepresentationAtBinder targetFirst targetLower
            targetUpper).existsTy.rename firstTele.weaken).rename
              memberTele.weaken) :=
        congrArg (Pair.fromSuffixTy firstTele memberTele) targetEq
      _ = (intervalRepresentationAtBinder targetFirst targetLower
          targetUpper).existsTy.rename
            (firstTele.append memberTele).weaken :=
        fromSuffixTy_weaken firstTele memberTele _
      _ = _ := rfl
  exact finalTypeEq ▸ transported

private noncomputable def genericIntervalRepresentationBody
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : IntervalMemberCompiler environments firstRelation
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
      memberDerivation) : Exp (sig ,, .var) :=
  (intervalRepresentationAtBinder sourceFirst sourceLower sourceUpper).unpack
    (.var .here)
    (intervalRepresentationAtBinder targetFirst targetLower
      targetUpper).existsTy
    (genericIntervalOpenedBody environments firstRelation sourceLowerRep
      sourceUpperRep targetLowerRep targetUpperRep compiler)

private noncomputable def genericIntervalRepresentationBody_hasType
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : IntervalMemberCompiler environments firstRelation
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
      memberDerivation) :
    Exp.HasType
      (base.bindVar
        (Pair.Interval.representation sourceFirst sourceLower
          sourceUpper).existsTy)
      (genericIntervalRepresentationBody environments firstRelation
        sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep compiler)
      ((Pair.Interval.representation targetFirst targetLower
        targetUpper).existsTy.weaken .var) := by
  have result :=
    (intervalRepresentationAtBinder sourceFirst sourceLower sourceUpper).unpack_hasType
      (intervalRepresentationVariable_hasType base sourceFirst sourceLower
        sourceUpper)
      (genericIntervalOpenedBody_hasType environments firstRelation
        sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep compiler)
  rw [Ty.weaken, Package.existsTy_rename,
    intervalRepresentationAtBinder_eq]
  exact result

private noncomputable def genericIntervalRepresentationConversion
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : IntervalMemberCompiler environments firstRelation
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
      memberDerivation) :
    Conversion base
      (Pair.Interval.representation sourceFirst sourceLower sourceUpper).existsTy
      (Pair.Interval.representation targetFirst targetLower
        targetUpper).existsTy :=
  Conversion.ofFunction
    (Adapter.ofBody
      (Pair.Interval.representation sourceFirst sourceLower sourceUpper).existsTy
      (genericIntervalRepresentationBody environments firstRelation
        sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep compiler))
    (Adapter.ofBody_hasType
      (genericIntervalRepresentationBody_hasType environments firstRelation
        sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep compiler))

/-- Compile the literal interval-member dependent-pair covariance rule. -/
noncomputable def interval
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    {firstDerivation : LambdaPFC.Tau.Sub sourceContext
      (.ty sourceFirstType) (.ty targetFirstType)}
    (first : FirstCompilation base firstDerivation sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (member : IntervalMemberCompiler environments first.relation
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
      memberDerivation) :
    Relation base
      (.Pair sourceFirstType label
        (.intv sourceLowerType sourceUpperType))
      (.Pair targetFirstType label
        (.intv targetLowerType targetUpperType))
      (.stable (Pair.Interval.plan sourceFirst sourceLower sourceUpper))
      (.stable (Pair.Interval.plan targetFirst targetLower targetUpper)) :=
  let sourceRepresentation := Pair.Interval.representation sourceFirst
    sourceLower sourceUpper
  let targetRepresentation := Pair.Interval.representation targetFirst
    targetLower targetUpper
  let representation := genericIntervalRepresentationConversion environments
    first.relation sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
    member
  let conversion := Conversion.Pair.retarget base sourceRepresentation
    targetRepresentation representation
  Relation.ofConversion
    (.intervalPair first.relation.sourceRep sourceLowerRep sourceUpperRep)
    (.intervalPair first.relation.targetRep targetLowerRep targetUpperRep)
    conversion



end LambdaPToFCo.Direct.Internal.PairSubtyping
