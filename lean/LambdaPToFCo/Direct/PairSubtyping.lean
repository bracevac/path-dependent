import LambdaPToFCo.Direct.AtomicSubtyping
import LambdaPToFCo.Direct.TermIntroduction

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



end LambdaPToFCo.Direct.Internal.PairSubtyping
