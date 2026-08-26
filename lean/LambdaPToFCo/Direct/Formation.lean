import LambdaPToFCo.Direct.Path

/-!
# Formation-preserving direct well-formedness compilation

This leaf retains exactly the source formation facts needed by later literal
subtyping rules.  It is not an intermediate calculus: every runtime field,
package, function, and typing judgment is ordinary unchanged System FCo.

Focused types are materialized by existentially closing the exact target
focus together with a final value field.  The final field is crucial: the
carrier describes how an eventual value is represented without assuming that
well-formedness itself has already produced such a value.  Nested focus
naturally produces nested closures.
-/

namespace LambdaPToFCo.Direct.Internal.Formation

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation

/-! ## Target substitution of exact interfaces -/

private theorem openVarSubstComm (argument : Exp source)
    (substitution : Subst source target) :
    (Subst.openVar argument).comp substitution =
      (substitution.lift .var).comp
        (Subst.openVar (argument.subst substitution)) := by
  apply Subst.funext
  · intro index
    cases index with
    | here => rfl
    | there index =>
        exact (Exp.weaken_subst_cancel (substitution.var index)
          (Subst.openVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openVar _)).symm
  · intro index
    cases index with
    | there index =>
        exact (Ty.weaken_subst_cancel (substitution.tvar index)
          (Subst.openVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openVar _)).symm
  · intro index
    cases index with
    | there index =>
        exact (Co.weaken_subst_cancel (substitution.cvar index)
          (Subst.openVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openVar _)).symm

private theorem openTVarSubstComm (argument : Ty source)
    (substitution : Subst source target) :
    (Subst.openTVar argument).comp substitution =
      (substitution.lift .tvar).comp
        (Subst.openTVar (argument.subst substitution)) := by
  apply Subst.funext
  · intro index
    cases index with
    | there index =>
        exact (Exp.weaken_subst_cancel (substitution.var index)
          (Subst.openTVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openTVar _)).symm
  · intro index
    cases index with
    | here => rfl
    | there index =>
        exact (Ty.weaken_subst_cancel (substitution.tvar index)
          (Subst.openTVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openTVar _)).symm
  · intro index
    cases index with
    | there index =>
        exact (Co.weaken_subst_cancel (substitution.cvar index)
          (Subst.openTVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openTVar _)).symm

private theorem openCVarSubstComm (argument : Co source)
    (substitution : Subst source target) :
    (Subst.openCVar argument).comp substitution =
      (substitution.lift .cvar).comp
        (Subst.openCVar (argument.subst substitution)) := by
  apply Subst.funext
  · intro index
    cases index with
    | there index =>
        exact (Exp.weaken_subst_cancel (substitution.var index)
          (Subst.openCVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openCVar _)).symm
  · intro index
    cases index with
    | there index =>
        exact (Ty.weaken_subst_cancel (substitution.tvar index)
          (Subst.openCVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openCVar _)).symm
  · intro index
    cases index with
    | here => rfl
    | there index =>
        exact (Co.weaken_subst_cancel (substitution.cvar index)
          (Subst.openCVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openCVar _)).symm

private noncomputable def argumentsTargetSubst
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target} {tele : Telescope source}
    (arguments : Telescope.Args sourceContext tele)
    (substitution : Subst source target)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    Telescope.Args targetContext (tele.subst substitution) := by
  induction arguments generalizing target targetContext with
  | nil => exact .nil
  | @var type tail argument argumentTyping rest ih =>
      refine .var (argument.subst substitution)
        (argumentTyping.subst typed) ?_
      have equal :
          (tail.subst (Subst.openVar argument)).subst substitution =
            (tail.subst (substitution.lift .var)).subst
              (Subst.openVar (argument.subst substitution)) := by
        rw [tail.subst_comp, tail.subst_comp, openVarSubstComm]
      exact equal ▸ ih substitution typed
  | @tvar tail argument rest ih =>
      refine .tvar (argument.subst substitution) ?_
      have equal :
          (tail.subst (Subst.openTVar argument)).subst substitution =
            (tail.subst (substitution.lift .tvar)).subst
              (Subst.openTVar (argument.subst substitution)) := by
        rw [tail.subst_comp, tail.subst_comp, openTVarSubstComm]
      exact equal ▸ ih substitution typed
  | @cvar sourceType targetType tail argument argumentTyping rest ih =>
      refine .cvar (argument.subst substitution)
        (argumentTyping.subst typed) ?_
      have equal :
          (tail.subst (Subst.openCVar argument)).subst substitution =
            (tail.subst (substitution.lift .cvar)).subst
              (Subst.openCVar (argument.subst substitution)) := by
        rw [tail.subst_comp, tail.subst_comp, openCVarSubstComm]
      exact equal ▸ ih substitution typed

private noncomputable def interfaceTargetSubst
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target} {shape : Shape source}
    (interface : Shape.Interface sourceContext shape)
    (substitution : Subst source target)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    Shape.Interface targetContext (shape.subst substitution) where
  arguments := by
    rw [← Shape.binders_subst]
    exact argumentsTargetSubst interface.arguments substitution typed

/-! ## Typed source path substitutions -/

/-- A source path substitution preserves every source-context lookup. -/
structure TypedPathSubstitution
    (sourceContext : LambdaPFC.Ctx n)
    (targetContext : LambdaPFC.Ctx m)
    (substitution : LambdaPFC.PathSubst n m) : Type where
  lookup : (index : Fin n) ->
    LambdaPFC.Path.Ty targetContext (substitution index)
      (.ty ((sourceContext.lookup index).subst substitution))

private theorem pathSubstWeakenCompLift
    (substitution : LambdaPFC.PathSubst n m) :
    LambdaPFC.FinFun.weaken.asSubst.comp substitution.lift =
      substitution.comp LambdaPFC.FinFun.weaken.asSubst := by
  funext index
  change substitution.lift index.succ =
    (substitution index).subst LambdaPFC.FinFun.weaken.asSubst
  rw [LambdaPFC.PathSubst.lift_succ, LambdaPFC.Path.subst_asSubst]
  rfl

private theorem tyWeakenSubstLift
    (sourceType : LambdaPFC.Ty n)
    (substitution : LambdaPFC.PathSubst n m) :
    sourceType.weaken.subst substitution.lift =
      (sourceType.subst substitution).weaken := by
  rw [LambdaPFC.Ty.weaken, ← LambdaPFC.Ty.subst_asSubst]
  rw [LambdaPFC.Ty.subst_comp, pathSubstWeakenCompLift]
  rw [← LambdaPFC.Ty.subst_comp, LambdaPFC.Ty.subst_asSubst]
  rfl

private noncomputable def pathTypingSubst
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : LambdaPFC.Ctx m}
    {substitution : LambdaPFC.PathSubst n m}
    (typed : TypedPathSubstitution sourceContext targetContext substitution) :
    LambdaPFC.Path.Ty sourceContext path sourceType ->
      LambdaPFC.Path.Ty targetContext (path.subst substitution)
        (sourceType.subst substitution)
  | .var => typed.lookup _
  | .fst receiver => (pathTypingSubst typed receiver).fst
  | .sel_r receiver => by
      simpa only [LambdaPFC.Path.subst, LambdaPFC.Tau.open_subst] using
        (pathTypingSubst typed receiver).sel_r
  | .sel_l receiver tail labelsNe =>
      .sel_l (pathTypingSubst typed receiver)
        (pathTypingSubst typed tail) labelsNe

namespace TypedPathSubstitution

noncomputable def weaken
    (context : LambdaPFC.Ctx n) (newest : LambdaPFC.Ty n) :
    TypedPathSubstitution context (context.snoc newest)
      LambdaPFC.FinFun.weaken.asSubst where
  lookup index := by
    simpa only [LambdaPFC.FinFun.asSubst_apply, LambdaPFC.Ctx.lookup,
      LambdaPFC.Ty.subst_asSubst, LambdaPFC.Path.rename] using
      (LambdaPFC.Path.Ty.var :
        LambdaPFC.Path.Ty (context.snoc newest) (.var index.succ)
          (.ty ((context.snoc newest).lookup index.succ)))

noncomputable def lift
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : LambdaPFC.Ctx m}
    {substitution : LambdaPFC.PathSubst n m}
    (typed : TypedPathSubstitution sourceContext targetContext substitution)
    (newest : LambdaPFC.Ty n) :
    TypedPathSubstitution (sourceContext.snoc newest)
      (targetContext.snoc (newest.subst substitution)) substitution.lift where
  lookup index := by
    refine Fin.cases ?_ (fun older => ?_) index
    · change LambdaPFC.Path.Ty
        (targetContext.snoc (newest.subst substitution)) (.var 0)
        (.ty (newest.weaken.subst substitution.lift))
      simpa only [tyWeakenSubstLift] using
        (LambdaPFC.Path.Ty.var : LambdaPFC.Path.Ty
          (targetContext.snoc (newest.subst substitution)) (.var 0)
          (.ty ((targetContext.snoc
            (newest.subst substitution)).lookup 0)))
    · have olderTyping := pathTypingSubst
        (weaken targetContext (newest.subst substitution))
        (typed.lookup older)
      change LambdaPFC.Path.Ty
        (targetContext.snoc (newest.subst substitution))
        (substitution older).weaken
        (.ty ((sourceContext.lookup older).weaken.subst substitution.lift))
      simpa only [tyWeakenSubstLift, LambdaPFC.Path.subst_asSubst,
        LambdaPFC.Tau.subst_asSubst, LambdaPFC.Path.weaken,
        LambdaPFC.Tau.rename] using olderTyping

/-- Open the newest source binding at one precisely typed path. -/
noncomputable def openAt
    {sourceContext : LambdaPFC.Ctx n} {sourceType : LambdaPFC.Ty n}
    {path : LambdaPFC.Path n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty sourceType)) :
    TypedPathSubstitution (sourceContext.snoc sourceType) sourceContext
      (LambdaPFC.PathSubst.openAt path) where
  lookup index := by
    refine Fin.cases ?_ (fun older => ?_) index
    · change LambdaPFC.Path.Ty sourceContext path
        (.ty (sourceType.weaken.open path))
      rw [LambdaPFC.Ty.weaken_open]
      exact typing
    · change LambdaPFC.Path.Ty sourceContext (.var older)
        (.ty ((sourceContext.lookup older).weaken.open path))
      rw [LambdaPFC.Ty.weaken_open]
      exact LambdaPFC.Path.Ty.var

end TypedPathSubstitution

/-! ## Exact formation evidence -/

/-- The compiler-local refinement of `Rep` retained while source derivations
are interpreted.  Singleton formation stores the exact referent interface;
selection formation stores the exact interval endpoints and functions. -/
inductive Formation : {n : Nat} -> {sig : Sig} ->
    (sourceContext : LambdaPFC.Ctx n) ->
    (targetContext : Ctx sig) ->
    (sourceType : LambdaPFC.Ty n) -> Shape sig -> Type where
| bottom {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig} :
    Formation sourceContext targetContext .Bot (.stable (Bot.plan sig))
| top {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig} :
    Formation sourceContext targetContext .Top (.stable (Top.plan sig))
| singleton
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {path : LambdaPFC.Path n} {referentType : LambdaPFC.Ty n}
    {referent : Shape sig}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty referentType))
    (referentInterface : Shape.Interface targetContext referent)
    (referentFormation : Formation sourceContext targetContext
      referentType referent) :
    Formation sourceContext targetContext (.Single path)
      (.stable (Single.plan referent.inputTy))
| selection
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selectedType : Ty sig}
    (typing : LambdaPFC.Path.Ty sourceContext (.sel path label)
      (.intv lowerSource upperSource))
    (lowerFormation : Formation sourceContext targetContext
      lowerSource lower)
    (upperFormation : Formation sourceContext targetContext
      upperSource upper)
    (lowerFunction : Exp sig)
    (lowerTyping : Exp.HasType targetContext lowerFunction
      (.arrow lower.inputTy selectedType))
    (upperFunction : Exp sig)
    (upperTyping : Exp.HasType targetContext upperFunction
      (.arrow selectedType upper.inputTy)) :
    Formation sourceContext targetContext (.TSel path label)
      (.opaque selectedType)
| function
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    {domain : Shape sig} {codomain : Shape domain.scope}
    (domainFormation : Formation sourceContext targetContext
      domainSource domain)
    (codomainFormation : Formation (sourceContext.snoc domainSource)
      (domain.context targetContext) codomainSource codomain) :
    Formation sourceContext targetContext
      (.Fun domainSource codomainSource)
      (.stable (Function.plan domain codomain))
| properPair
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {memberSource : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {first : Shape sig} {member : Shape first.scope}
    (firstFormation : Formation sourceContext targetContext
      firstSource first)
    (memberFormation : Formation (sourceContext.snoc firstSource)
      (first.context targetContext) memberSource member) :
    Formation sourceContext targetContext
      (.Pair firstSource label (.ty memberSource))
      (.stable (Pair.Proper.plan first member))
| intervalPair
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {lowerSource upperSource : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {first : Shape sig} {lower upper : Shape first.scope}
    (firstFormation : Formation sourceContext targetContext
      firstSource first)
    (lowerFormation : Formation (sourceContext.snoc firstSource)
      (first.context targetContext) lowerSource lower)
    (upperFormation : Formation (sourceContext.snoc firstSource)
      (first.context targetContext) upperSource upper) :
    Formation sourceContext targetContext
      (.Pair firstSource label (.intv lowerSource upperSource))
      (.stable (Pair.Interval.plan first lower upper))
| closed
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (fields : Telescope sig)
    (storedShape : Shape fields.scope)
    (storedPackage : Exp fields.scope)
    (storedTyping : Exp.HasType (fields.context targetContext)
      storedPackage storedShape.inputTy)
    (openedFormation : Formation sourceContext
      (storedShape.context (fields.context targetContext)) sourceType
      (storedShape.rename storedShape.binders.weaken)) :
    Formation sourceContext targetContext sourceType
      (.opaque fields.existsTy)

/-- Erase formation evidence to the frozen runtime representation. -/
noncomputable def Formation.rep
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n} {shape : Shape sig}
    (formation : Formation sourceContext targetContext sourceType shape) :
    Rep targetContext sourceType shape := by
  induction formation with
  | bottom => exact .bottom _
  | top => exact .top _
  | singleton => exact .singleton _ _ _
  | selection _ _ _ lowerFunction lowerTyping upperFunction upperTyping
      lowerIH upperIH =>
      exact .selection lowerIH upperIH lowerFunction lowerTyping
        upperFunction upperTyping
  | function _ _ domainIH codomainIH =>
      exact .function domainIH codomainIH
  | properPair _ _ firstIH memberIH =>
      exact .properPair firstIH memberIH
  | intervalPair _ _ _ firstIH lowerIH upperIH =>
      exact .intervalPair firstIH lowerIH upperIH
  | closed fields storedShape storedPackage storedTyping _ openedIH =>
      exact .closed fields storedShape storedPackage storedTyping openedIH

/-- Closure-free formation view reached by exact carrier elimination. -/
inductive Formation.Exposed : {n : Nat} -> {sig : Sig} ->
    (sourceContext : LambdaPFC.Ctx n) ->
    (targetContext : Ctx sig) ->
    (sourceType : LambdaPFC.Ty n) -> Shape sig -> Type where
| bottom {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig} :
    Formation.Exposed sourceContext targetContext .Bot
      (.stable (Bot.plan sig))
| top {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig} :
    Formation.Exposed sourceContext targetContext .Top
      (.stable (Top.plan sig))
| singleton
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {path : LambdaPFC.Path n} {referentType : LambdaPFC.Ty n}
    {referent : Shape sig}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty referentType))
    (referentInterface : Shape.Interface targetContext referent)
    (referentFormation : Formation sourceContext targetContext
      referentType referent) :
    Formation.Exposed sourceContext targetContext (.Single path)
      (.stable (Single.plan referent.inputTy))
| selection
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selectedType : Ty sig}
    (typing : LambdaPFC.Path.Ty sourceContext (.sel path label)
      (.intv lowerSource upperSource))
    (lowerFormation : Formation sourceContext targetContext
      lowerSource lower)
    (upperFormation : Formation sourceContext targetContext
      upperSource upper)
    (lowerFunction : Exp sig)
    (lowerTyping : Exp.HasType targetContext lowerFunction
      (.arrow lower.inputTy selectedType))
    (upperFunction : Exp sig)
    (upperTyping : Exp.HasType targetContext upperFunction
      (.arrow selectedType upper.inputTy)) :
    Formation.Exposed sourceContext targetContext (.TSel path label)
      (.opaque selectedType)
| function
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    {domain : Shape sig} {codomain : Shape domain.scope}
    (domainFormation : Formation sourceContext targetContext
      domainSource domain)
    (codomainFormation : Formation (sourceContext.snoc domainSource)
      (domain.context targetContext) codomainSource codomain) :
    Formation.Exposed sourceContext targetContext
      (.Fun domainSource codomainSource)
      (.stable (Function.plan domain codomain))
| properPair
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {memberSource : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {first : Shape sig} {member : Shape first.scope}
    (firstFormation : Formation sourceContext targetContext
      firstSource first)
    (memberFormation : Formation (sourceContext.snoc firstSource)
      (first.context targetContext) memberSource member) :
    Formation.Exposed sourceContext targetContext
      (.Pair firstSource label (.ty memberSource))
      (.stable (Pair.Proper.plan first member))
| intervalPair
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {lowerSource upperSource : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {first : Shape sig} {lower upper : Shape first.scope}
    (firstFormation : Formation sourceContext targetContext
      firstSource first)
    (lowerFormation : Formation (sourceContext.snoc firstSource)
      (first.context targetContext) lowerSource lower)
    (upperFormation : Formation (sourceContext.snoc firstSource)
      (first.context targetContext) upperSource upper) :
    Formation.Exposed sourceContext targetContext
      (.Pair firstSource label (.intv lowerSource upperSource))
      (.stable (Pair.Interval.plan first lower upper))

namespace Formation.Exposed

noncomputable def toFormation
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n} {shape : Shape sig}
    (exposed : Formation.Exposed sourceContext targetContext
      sourceType shape) :
    Formation sourceContext targetContext sourceType shape :=
  match exposed with
  | .bottom => .bottom
  | .top => .top
  | .singleton typing interface referent =>
      .singleton typing interface referent
  | .selection typing lower upper lowerFunction lowerTyping upperFunction
      upperTyping =>
      .selection typing lower upper lowerFunction lowerTyping upperFunction
        upperTyping
  | .function domain codomain => .function domain codomain
  | .properPair first member => .properPair first member
  | .intervalPair first lower upper => .intervalPair first lower upper

/-- The matching closure-free runtime representation. -/
noncomputable def rep
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n} {shape : Shape sig}
    (exposed : Formation.Exposed sourceContext targetContext
      sourceType shape) :
    Rep.Exposed targetContext sourceType shape :=
  match exposed with
  | .bottom => .bottom _
  | .top => .top _
  | .singleton _ _ _ => .singleton _ _ _
  | .selection _ lower upper lowerFunction lowerTyping upperFunction
      upperTyping =>
      .selection lower.rep upper.rep lowerFunction lowerTyping upperFunction
        upperTyping
  | .function domain codomain => .function domain.rep codomain.rep
  | .properPair first member => .properPair first.rep member.rep
  | .intervalPair first lower upper =>
      .intervalPair first.rep lower.rep upper.rep

end Formation.Exposed

abbrev Formation.ExposeConsumer
    {n : Nat} {root : Sig} (sourceContext : LambdaPFC.Ctx n)
    (rootContext : Ctx root) (sourceType : LambdaPFC.Ty n)
    (answer : Ty root) : Type :=
  forall {current : Sig} {currentContext : Ctx current}
    {shape : Shape current},
    (mapping : Rename root current) ->
    Rename.Typed rootContext currentContext mapping ->
    Shape.Interface currentContext shape ->
    Formation.Exposed sourceContext currentContext sourceType shape ->
    Rep.ExposeBody currentContext (answer.rename mapping)

private noncomputable def Formation.exposeAt
    {sourceContext : LambdaPFC.Ctx n} {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    {sourceType : LambdaPFC.Ty n} {shape : Shape current}
    (formation : Formation sourceContext currentContext sourceType shape)
    (interface : Shape.Interface currentContext shape)
    (answer : Ty root)
    (mapping : Rename root current)
    (typed : Rename.Typed rootContext currentContext mapping)
    (consumer : Formation.ExposeConsumer sourceContext rootContext
      sourceType answer) :
    Rep.ExposeBody currentContext (answer.rename mapping) := by
  induction formation generalizing root with
  | bottom => exact consumer mapping typed interface .bottom
  | top => exact consumer mapping typed interface .top
  | singleton pathTyping referentInterface referentFormation =>
      exact consumer mapping typed interface
        (.singleton pathTyping referentInterface referentFormation)
  | selection pathTyping lowerFormation upperFormation lowerFunction
      lowerTyping upperFunction upperTyping =>
      exact consumer mapping typed interface
        (.selection pathTyping lowerFormation upperFormation lowerFunction
          lowerTyping upperFunction upperTyping)
  | function domainFormation codomainFormation =>
      exact consumer mapping typed interface
        (.function domainFormation codomainFormation)
  | properPair firstFormation memberFormation =>
      exact consumer mapping typed interface
        (.properPair firstFormation memberFormation)
  | intervalPair firstFormation lowerFormation upperFormation =>
      exact consumer mapping typed interface
        (.intervalPair firstFormation lowerFormation upperFormation)
  | @closed _ _ _ closedContext _ fields storedShape storedPackage
      storedTyping openedFormation openedIH =>
      let fieldsMapping := mapping.comp fields.weaken
      let fieldsTyped := TypedRename.comp typed (fields.weaken_typed _)
      let openedMapping := fieldsMapping.comp storedShape.binders.weaken
      let openedTyped := TypedRename.comp fieldsTyped
        (storedShape.binders.weaken_typed _)
      let openedInterface := Shape.Interface.canonical
        (fields.context closedContext) storedShape
      let opened := openedIH openedInterface answer openedMapping openedTyped
        consumer
      let storedBody := storedShape.eliminate storedPackage
        (answer.rename fieldsMapping) opened.expression
      have storedBodyTyping : Exp.HasType (fields.context closedContext)
          storedBody (answer.rename fieldsMapping) := by
        apply storedShape.eliminate_hasType storedTyping
        simpa only [openedMapping, fieldsMapping, Ty.rename_comp] using
          opened.typing
      refine {
        expression := fields.unpack interface.package (answer.rename mapping)
          storedBody
        typing := ?_
      }
      apply fields.unpack_hasType interface.package_hasType
      simpa only [fieldsMapping, Ty.rename_comp] using storedBodyTyping

/-- Expose every closure while retaining the exact formation and runtime
representation in lockstep. -/
noncomputable def Formation.expose
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n} {shape : Shape sig}
    (formation : Formation sourceContext targetContext sourceType shape)
    (interface : Shape.Interface targetContext shape)
    (answer : Ty sig)
    (consumer : Formation.ExposeConsumer sourceContext targetContext
      sourceType answer) :
    Rep.ExposeBody targetContext answer := by
  simpa only [Ty.rename_id] using
    formation.exposeAt interface answer Rename.id
      (TypedRename.id targetContext) consumer

/-! ## Source and target transport -/

noncomputable def Formation.sourceSubst
    {sourceContext : LambdaPFC.Ctx n}
    {targetSourceContext : LambdaPFC.Ctx m}
    {substitution : LambdaPFC.PathSubst n m}
    {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n} {shape : Shape sig}
    (formation : Formation sourceContext targetContext sourceType shape)
    (typed : TypedPathSubstitution sourceContext targetSourceContext
      substitution) :
    Formation targetSourceContext targetContext
      (sourceType.subst substitution) shape := by
  induction formation generalizing m with
  | bottom => exact .bottom
  | top => exact .top
  | singleton pathTyping referentInterface _ referentIH =>
      exact .singleton (pathTypingSubst typed pathTyping) referentInterface
        (referentIH typed)
  | selection pathTyping _ _ lowerFunction lowerTyping upperFunction
      upperTyping lowerIH upperIH =>
      exact .selection (pathTypingSubst typed pathTyping)
        (lowerIH typed) (upperIH typed) lowerFunction lowerTyping
        upperFunction upperTyping
  | @function _ _ _ _ _ _ _ _ _ _ domainIH codomainIH =>
      exact .function (domainIH typed)
        (codomainIH (typed.lift _))
  | @properPair _ _ _ _ _ _ _ _ _ _ _ firstIH memberIH =>
      exact .properPair (firstIH typed)
        (memberIH (typed.lift _))
  | @intervalPair _ _ _ _ _ _ _ _ _ _ _ _ _ _ firstIH lowerIH
      upperIH =>
      exact .intervalPair (firstIH typed)
        (lowerIH (typed.lift _)) (upperIH (typed.lift _))
  | closed fields storedShape storedPackage storedTyping _ openedIH =>
      exact .closed fields storedShape storedPackage storedTyping
        (openedIH typed)

abbrev TypedPathRename
    (sourceContext : LambdaPFC.Ctx n)
    (targetContext : LambdaPFC.Ctx m)
    (mapping : LambdaPFC.FinFun n m) : Type :=
  TypedPathSubstitution sourceContext targetContext mapping.asSubst

noncomputable def Formation.sourceRename
    {sourceContext : LambdaPFC.Ctx n}
    {targetSourceContext : LambdaPFC.Ctx m}
    {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n} {shape : Shape sig}
    (formation : Formation sourceContext targetContext sourceType shape)
    (mapping : LambdaPFC.FinFun n m)
    (typed : TypedPathRename sourceContext targetSourceContext mapping) :
    Formation targetSourceContext targetContext
      (sourceType.rename mapping) shape := by
  simpa only [LambdaPFC.Ty.subst_asSubst] using
    formation.sourceSubst typed

noncomputable def Formation.sourceWeaken
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n} {shape : Shape sig}
    (formation : Formation sourceContext targetContext sourceType shape)
    (newest : LambdaPFC.Ty n) :
    Formation (sourceContext.snoc newest) targetContext
      sourceType.weaken shape := by
  simpa only [LambdaPFC.Ty.weaken] using
    formation.sourceRename LambdaPFC.FinFun.weaken
      (TypedPathSubstitution.weaken sourceContext newest)

noncomputable def Formation.targetRename
    {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : Ctx sourceSig}
    {targetTargetContext : Ctx targetSig}
    {sourceType : LambdaPFC.Ty n} {shape : Shape sourceSig}
    (formation : Formation sourceContext sourceTargetContext
      sourceType shape)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    Formation sourceContext targetTargetContext sourceType
      (shape.rename mapping) := by
  induction formation generalizing targetSig with
  | bottom =>
      simpa only [Shape.rename, Bot.plan_rename] using
        (Formation.bottom (targetContext := targetTargetContext))
  | top =>
      simpa only [Shape.rename, Top.plan_rename] using
        (Formation.top (targetContext := targetTargetContext))
  | singleton pathTyping referentInterface _ referentIH =>
      simpa only [Shape.rename, Single.plan_rename,
        Shape.inputTy_rename] using
        Formation.singleton pathTyping
          (referentInterface.rename mapping typed)
          (referentIH mapping typed)
  | selection pathTyping _ _ lowerFunction lowerTyping upperFunction
      upperTyping lowerIH upperIH =>
      exact .selection pathTyping (lowerIH mapping typed)
        (upperIH mapping typed) (lowerFunction.rename mapping)
        (by simpa only [Ty.rename, Shape.inputTy_rename] using
          lowerTyping.rename typed)
        (upperFunction.rename mapping)
        (by simpa only [Ty.rename, Shape.inputTy_rename] using
          upperTyping.rename typed)
  | @function _ _ _ _ _ _ domain _ _ _ domainIH codomainIH =>
      let domainAt := domainIH mapping typed
      let lifted := domain.liftRename_typed typed
      let codomainAt := codomainIH (domain.liftRename mapping) lifted
      simpa only [Shape.rename, Function.plan_rename,
        Function.renameCodomain] using
        Formation.function domainAt codomainAt
  | @properPair _ _ _ _ _ _ _ first _ _ _ firstIH memberIH =>
      let firstAt := firstIH mapping typed
      let lifted := first.liftRename_typed typed
      let memberAt := memberIH (first.liftRename mapping) lifted
      simpa only [Shape.rename, Pair.Proper.plan_rename,
        Pair.Proper.renameMember] using
        Formation.properPair firstAt memberAt
  | @intervalPair _ _ _ _ _ _ _ _ first _ _ _ _ _ firstIH lowerIH
      upperIH =>
      let firstAt := firstIH mapping typed
      let lifted := first.liftRename_typed typed
      let lowerAt := lowerIH (first.liftRename mapping) lifted
      let upperAt := upperIH (first.liftRename mapping) lifted
      simpa only [Shape.rename, Pair.Interval.plan_rename] using
        Formation.intervalPair firstAt lowerAt upperAt
  | closed fields storedShape storedPackage storedTyping _ openedIH =>
      let fieldsMapping := fields.liftRename mapping
      let fieldsTyped := fields.liftRename_typed typed
      let renamedShape := storedShape.rename fieldsMapping
      let renamedPackage := storedPackage.rename fieldsMapping
      have renamedTyping : Exp.HasType
          ((fields.rename mapping).context targetTargetContext)
          renamedPackage renamedShape.inputTy := by
        simpa only [renamedPackage, renamedShape,
          Shape.inputTy_rename] using storedTyping.rename fieldsTyped
      let openedMapping := storedShape.liftRename fieldsMapping
      let openedTyped := storedShape.liftRename_typed fieldsTyped
      let renamedOpened := openedIH openedMapping openedTyped
      dsimp only [openedMapping, fieldsMapping] at renamedOpened
      let normalizedOpened :=
        Representation.Shape.open_rename storedShape
          (fields.liftRename mapping) ▸
          renamedOpened
      let result := Formation.closed (targetContext := targetTargetContext)
        (fields.rename mapping) renamedShape renamedPackage renamedTyping
        normalizedOpened
      simpa only [Shape.rename, Package.existsTy_rename] using result

noncomputable def Formation.targetSubst
    {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : Ctx sourceSig}
    {targetTargetContext : Ctx targetSig}
    {sourceType : LambdaPFC.Ty n} {shape : Shape sourceSig}
    (formation : Formation sourceContext sourceTargetContext
      sourceType shape)
    (substitution : Subst sourceSig targetSig)
    (typed : Subst.Typed sourceTargetContext targetTargetContext
      substitution) :
    Formation sourceContext targetTargetContext sourceType
      (shape.subst substitution) := by
  induction formation generalizing targetSig with
  | bottom =>
      simpa only [Shape.subst, Bot.plan_subst] using
        (Formation.bottom (targetContext := targetTargetContext))
  | top =>
      simpa only [Shape.subst, Top.plan_subst] using
        (Formation.top (targetContext := targetTargetContext))
  | singleton pathTyping referentInterface _ referentIH =>
      simpa only [Shape.subst, Single.plan_subst,
        Shape.inputTy_subst] using
        Formation.singleton pathTyping
          (interfaceTargetSubst referentInterface substitution typed)
          (referentIH substitution typed)
  | selection pathTyping _ _ lowerFunction lowerTyping upperFunction
      upperTyping lowerIH upperIH =>
      exact .selection pathTyping (lowerIH substitution typed)
        (upperIH substitution typed) (lowerFunction.subst substitution)
        (by simpa only [Ty.subst, Shape.inputTy_subst] using
          lowerTyping.subst typed)
        (upperFunction.subst substitution)
        (by simpa only [Ty.subst, Shape.inputTy_subst] using
          upperTyping.subst typed)
  | @function _ _ _ _ _ _ domain _ _ _ domainIH codomainIH =>
      let domainAt := domainIH substitution typed
      let lifted := domain.liftSubst_typed typed
      let codomainAt := codomainIH (domain.liftSubst substitution) lifted
      simpa only [Shape.subst, Function.plan_subst,
        Function.substCodomain] using
        Formation.function domainAt codomainAt
  | @properPair _ _ _ _ _ _ _ first _ _ _ firstIH memberIH =>
      let firstAt := firstIH substitution typed
      let lifted := first.liftSubst_typed typed
      let memberAt := memberIH (first.liftSubst substitution) lifted
      simpa only [Shape.subst, Pair.Proper.plan_subst,
        Pair.Proper.substMember] using
        Formation.properPair firstAt memberAt
  | @intervalPair _ _ _ _ _ _ _ _ first _ _ _ _ _ firstIH lowerIH
      upperIH =>
      let firstAt := firstIH substitution typed
      let lifted := first.liftSubst_typed typed
      let lowerAt := lowerIH (first.liftSubst substitution) lifted
      let upperAt := upperIH (first.liftSubst substitution) lifted
      simpa only [Shape.subst, Pair.Interval.plan_subst] using
        Formation.intervalPair firstAt lowerAt upperAt
  | closed fields storedShape storedPackage storedTyping _ openedIH =>
      let fieldsSubstitution := fields.liftSubst substitution
      let fieldsTyped := fields.liftSubst_typed typed
      let substitutedShape := storedShape.subst fieldsSubstitution
      let substitutedPackage := storedPackage.subst fieldsSubstitution
      have substitutedTyping : Exp.HasType
          ((fields.subst substitution).context targetTargetContext)
          substitutedPackage substitutedShape.inputTy := by
        simpa only [substitutedPackage, substitutedShape,
          Shape.inputTy_subst] using storedTyping.subst fieldsTyped
      let openedSubstitution := storedShape.liftSubst fieldsSubstitution
      let openedTyped := storedShape.liftSubst_typed fieldsTyped
      let substitutedOpened := openedIH openedSubstitution openedTyped
      dsimp only [openedSubstitution, fieldsSubstitution] at substitutedOpened
      let normalizedOpened :=
        Representation.Shape.open_subst storedShape
          (fields.liftSubst substitution) ▸ substitutedOpened
      let result := Formation.closed (targetContext := targetTargetContext)
        (fields.subst substitution) substitutedShape substitutedPackage
        substitutedTyping normalizedOpened
      simpa only [Shape.subst, Package.existsTy_subst] using result

/-! ## Formed slots and environments -/

structure Slot (sourceContext : LambdaPFC.Ctx n)
    (targetContext : Ctx sig) (sourceType : LambdaPFC.Ty n) : Type where
  shape : Shape sig
  interface : Shape.Interface targetContext shape
  formation : Formation sourceContext targetContext sourceType shape

namespace Slot

noncomputable def erase
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (slot : Slot sourceContext targetContext sourceType) :
    Representation.Slot targetContext sourceType where
  shape := slot.shape
  interface := slot.interface
  rep := slot.formation.rep

noncomputable def targetRename
    {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : Ctx sourceSig}
    {targetTargetContext : Ctx targetSig}
    {sourceType : LambdaPFC.Ty n}
    (slot : Slot sourceContext sourceTargetContext sourceType)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    Slot sourceContext targetTargetContext sourceType where
  shape := slot.shape.rename mapping
  interface := slot.interface.rename mapping typed
  formation := slot.formation.targetRename mapping typed

noncomputable def targetSubst
    {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : Ctx sourceSig}
    {targetTargetContext : Ctx targetSig}
    {sourceType : LambdaPFC.Ty n}
    (slot : Slot sourceContext sourceTargetContext sourceType)
    (substitution : Subst sourceSig targetSig)
    (typed : Subst.Typed sourceTargetContext targetTargetContext
      substitution) :
    Slot sourceContext targetTargetContext sourceType where
  shape := slot.shape.subst substitution
  interface := interfaceTargetSubst slot.interface substitution typed
  formation := slot.formation.targetSubst substitution typed

noncomputable def sourceSubst
    {sourceContext : LambdaPFC.Ctx n}
    {targetSourceContext : LambdaPFC.Ctx m}
    {substitution : LambdaPFC.PathSubst n m}
    {targetContext : Ctx sig} {sourceType : LambdaPFC.Ty n}
    (slot : Slot sourceContext targetContext sourceType)
    (typed : TypedPathSubstitution sourceContext targetSourceContext
      substitution) :
    Slot targetSourceContext targetContext
      (sourceType.subst substitution) where
  shape := slot.shape
  interface := slot.interface
  formation := slot.formation.sourceSubst typed

noncomputable def sourceWeaken
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (slot : Slot sourceContext targetContext sourceType)
    (newest : LambdaPFC.Ty n) :
    Slot (sourceContext.snoc newest) targetContext sourceType.weaken := by
  simpa only [LambdaPFC.Ty.weaken, LambdaPFC.Ty.subst_asSubst] using
    slot.sourceSubst (TypedPathSubstitution.weaken sourceContext newest)

end Slot

structure Env (sourceContext : LambdaPFC.Ctx n)
    (targetContext : Ctx sig) : Type where
  lookup : (index : Fin n) ->
    Slot sourceContext targetContext (sourceContext.lookup index)

namespace Env

def empty (targetContext : Ctx sig) : Env .nil targetContext where
  lookup index := Fin.elim0 index

noncomputable def erase
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext) :
    Representation.Env sourceContext targetContext where
  lookup index := (environment.lookup index).erase

noncomputable def targetRename
    {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : Ctx sourceSig}
    {targetTargetContext : Ctx targetSig}
    (environment : Env sourceContext sourceTargetContext)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    Env sourceContext targetTargetContext where
  lookup index := (environment.lookup index).targetRename mapping typed

noncomputable def targetSubst
    {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : Ctx sourceSig}
    {targetTargetContext : Ctx targetSig}
    (environment : Env sourceContext sourceTargetContext)
    (substitution : Subst sourceSig targetSig)
    (typed : Subst.Typed sourceTargetContext targetTargetContext
      substitution) :
    Env sourceContext targetTargetContext where
  lookup index := (environment.lookup index).targetSubst substitution typed

noncomputable def extend
    {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : Ctx sourceSig}
    {targetTargetContext : Ctx targetSig}
    (environment : Env sourceContext sourceTargetContext)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
    (sourceType : LambdaPFC.Ty n)
    {shape : Shape targetSig}
    (interface : Shape.Interface targetTargetContext shape)
    (boundFormation : Formation (sourceContext.snoc sourceType)
      targetTargetContext sourceType.weaken shape) :
    Env (sourceContext.snoc sourceType) targetTargetContext where
  lookup := Fin.cases
    { shape := shape
      interface := interface
      formation := boundFormation }
    (fun older =>
      ((environment.lookup older).targetRename mapping typed).sourceWeaken
        sourceType)

noncomputable def enter
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext)
    (sourceType : LambdaPFC.Ty n) {shape : Shape sig}
    (boundFormation : Formation sourceContext targetContext
      sourceType shape) :
    Env (sourceContext.snoc sourceType) (shape.context targetContext) :=
  let mapping := shape.binders.weaken
  let typed := shape.binders.weaken_typed targetContext
  let openedFormation := (boundFormation.sourceWeaken sourceType).targetRename
    mapping typed
  environment.extend mapping typed sourceType
    (Shape.Interface.canonical targetContext shape) openedFormation

end Env

/-! ## Material formation results and faithful focus closure -/

/-- One exact material proper formation at a target root. -/
structure Proper (sourceContext : LambdaPFC.Ctx n)
    (targetContext : Ctx sig) (sourceType : LambdaPFC.Ty n) : Type where
  shape : Shape sig
  formation : Formation sourceContext targetContext sourceType shape

/-- Exact material endpoint formations for an interval. -/
structure Interval (sourceContext : LambdaPFC.Ctx n)
    (targetContext : Ctx sig)
    (lowerSource upperSource : LambdaPFC.Ty n) : Type where
  lower : Shape sig
  upper : Shape sig
  lowerFormation : Formation sourceContext targetContext lowerSource lower
  upperFormation : Formation sourceContext targetContext upperSource upper

namespace Proper

def bottom (sourceContext : LambdaPFC.Ctx n) (targetContext : Ctx sig) :
    Proper sourceContext targetContext .Bot where
  shape := .stable (Bot.plan sig)
  formation := .bottom

def top (sourceContext : LambdaPFC.Ctx n) (targetContext : Ctx sig) :
    Proper sourceContext targetContext .Top where
  shape := .stable (Top.plan sig)
  formation := .top

noncomputable def targetRename
    {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : Ctx sourceSig}
    {targetTargetContext : Ctx targetSig}
    {sourceType : LambdaPFC.Ty n}
    (result : Proper sourceContext sourceTargetContext sourceType)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    Proper sourceContext targetTargetContext sourceType where
  shape := result.shape.rename mapping
  formation := result.formation.targetRename mapping typed

noncomputable def targetSubst
    {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : Ctx sourceSig}
    {targetTargetContext : Ctx targetSig}
    {sourceType : LambdaPFC.Ty n}
    (result : Proper sourceContext sourceTargetContext sourceType)
    (substitution : Subst sourceSig targetSig)
    (typed : Subst.Typed sourceTargetContext targetTargetContext
      substitution) :
    Proper sourceContext targetTargetContext sourceType where
  shape := result.shape.subst substitution
  formation := result.formation.targetSubst substitution typed

private structure ClosurePayload
    {sourceContext : LambdaPFC.Ctx n} {sig : Sig}
    (targetContext : Ctx sig) (sourceType : LambdaPFC.Ty n)
    (fields : Telescope sig) where
  storedShape : Shape fields.scope
  storedPackage : Exp fields.scope
  storedTyping : Exp.HasType (fields.context targetContext)
    storedPackage storedShape.inputTy
  openedFormation : Formation sourceContext
    (storedShape.context (fields.context targetContext)) sourceType
    (storedShape.rename storedShape.binders.weaken)

private noncomputable def closurePayload
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (focus : Telescope sig)
    {shape : Shape focus.scope}
    (formation : Formation sourceContext (focus.context targetContext)
      sourceType shape) :
    ClosurePayload (sourceContext := sourceContext) targetContext sourceType
      (focus.append (.var shape.inputTy .nil)) := by
  induction focus with
  | nil =>
      let valueField := Telescope.var shape.inputTy Telescope.nil
      let storedShape := shape.rename valueField.weaken
      let storedPackage : Exp valueField.scope := .var .here
      have storedTyping : Exp.HasType (valueField.context targetContext)
          storedPackage storedShape.inputTy := by
        simpa only [storedPackage, storedShape, Shape.inputTy_rename,
          valueField, Telescope.context, Telescope.weaken, Ty.weaken,
          Ty.rename_id] using
          (Exp.HasType.var (Ctx.Lookup.here :
            Ctx.VarLookup (valueField.context targetContext) .here _))
      let atValue := formation.targetRename valueField.weaken
        (valueField.weaken_typed targetContext)
      let opened := atValue.targetRename storedShape.binders.weaken
        (storedShape.binders.weaken_typed
          (valueField.context targetContext))
      exact {
        storedShape := storedShape
        storedPackage := storedPackage
        storedTyping := storedTyping
        openedFormation := opened
      }
  | var type tail ih =>
      let payload := ih (targetContext := targetContext.bindVar type)
        formation
      exact {
        storedShape := payload.storedShape
        storedPackage := payload.storedPackage
        storedTyping := payload.storedTyping
        openedFormation := payload.openedFormation
      }
  | tvar tail ih =>
      let payload := ih (targetContext := targetContext.bindTVar) formation
      exact {
        storedShape := payload.storedShape
        storedPackage := payload.storedPackage
        storedTyping := payload.storedTyping
        openedFormation := payload.openedFormation
      }
  | cvar source target tail ih =>
      let payload := ih
        (targetContext := targetContext.bindCVar source target) formation
      exact {
        storedShape := payload.storedShape
        storedPackage := payload.storedPackage
        storedTyping := payload.storedTyping
        openedFormation := payload.openedFormation
      }

/-- Close a focused formation without assuming an inhabitant.  The carrier
binds the eventual represented value as its final field.  This is the
type-side closure only; `FormedPath` retains the focus runner which later
repackages an actual compiled value into the matching outer interface. -/
noncomputable def close
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (focus : Telescope sig)
    {shape : Shape focus.scope}
    (formation : Formation sourceContext (focus.context targetContext)
      sourceType shape) :
    Proper sourceContext targetContext sourceType :=
  let fields := focus.append (.var shape.inputTy .nil)
  let payload := closurePayload focus formation
  {
    shape := .opaque fields.existsTy
    formation := .closed fields payload.storedShape payload.storedPackage
      payload.storedTyping payload.openedFormation
  }

end Proper

namespace Interval

def bounds
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (lower : Proper sourceContext targetContext lowerSource)
    (upper : Proper sourceContext targetContext upperSource) :
    Interval sourceContext targetContext lowerSource upperSource where
  lower := lower.shape
  upper := upper.shape
  lowerFormation := lower.formation
  upperFormation := upper.formation

noncomputable def targetRename
    {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : Ctx sourceSig}
    {targetTargetContext : Ctx targetSig}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (result : Interval sourceContext sourceTargetContext
      lowerSource upperSource)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    Interval sourceContext targetTargetContext
      lowerSource upperSource where
  lower := result.lower.rename mapping
  upper := result.upper.rename mapping
  lowerFormation := result.lowerFormation.targetRename mapping typed
  upperFormation := result.upperFormation.targetRename mapping typed

noncomputable def targetSubst
    {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : Ctx sourceSig}
    {targetTargetContext : Ctx targetSig}
    {lowerSource upperSource : LambdaPFC.Ty n}
    (result : Interval sourceContext sourceTargetContext
      lowerSource upperSource)
    (substitution : Subst sourceSig targetSig)
    (typed : Subst.Typed sourceTargetContext targetTargetContext
      substitution) :
    Interval sourceContext targetTargetContext
      lowerSource upperSource where
  lower := result.lower.subst substitution
  upper := result.upper.subst substitution
  lowerFormation := result.lowerFormation.targetSubst substitution typed
  upperFormation := result.upperFormation.targetSubst substitution typed

end Interval

end LambdaPToFCo.Direct.Internal.Formation
