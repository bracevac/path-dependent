import Coercions.Translation.ManySorted.BinderOnly.Layout

/-!
# Metatheory of the binder-only context layout

The executable layout expands one source static binder into a target symbol
and zero, one, or two evidence binders.  This file records the coherence laws
which make that expansion usable in preservation proofs: compatible source
and target renamings commute with syntax translation, source weakening is
compiled by `extendRename`, and term lookup agrees with target lookup.
-/

namespace DOTCaptureToManySortedFC.BinderOnly

private theorem congrArg2 {alpha beta gamma : Sort _}
    (function : alpha → beta → gamma)
    {left₁ right₁ : alpha} {left₂ right₂ : beta}
    (first : left₁ = right₁) (second : left₂ = right₂) :
    function left₁ left₂ = function right₁ right₂ := by
  cases first
  cases second
  rfl

namespace ManySortedRename

/-- Weakening below a block is natural with respect to lifting through the
same block. -/
theorem weakenMany_liftMany_var
    {source target : ManySortedFC.Sig}
    (rho : ManySortedFC.Rename source target)
    (kinds : ManySortedFC.Sig)
    {kind : ManySortedFC.BinderKind}
    (index : ManySortedFC.BVar source kind) :
    (ManySortedFC.Rename.weakenMany target kinds).var (rho.var index) =
      (rho.liftMany kinds).var
        ((ManySortedFC.Rename.weakenMany source kinds).var index) := by
  induction kinds with
  | nil => rfl
  | cons newest rest induction =>
      simp only [ManySortedFC.Rename.weakenMany,
        ManySortedFC.Rename.comp_var, ManySortedFC.Rename.succ_var,
        ManySortedFC.Rename.liftMany_cons,
        ManySortedFC.Rename.lift_there]
      exact congrArg ManySortedFC.BVar.there induction

/-- The corresponding naturality square for a complete static block. -/
theorem weakenStatic_liftStatic_var
    {source target : ManySortedFC.Sig}
    (rho : ManySortedFC.Rename source target)
    (symbols : List ManySortedFC.StaticSort)
    (relations : List ManySortedFC.Relation)
    {kind : ManySortedFC.BinderKind}
    (index : ManySortedFC.BVar source kind) :
    (ManySortedFC.Rename.weakenStatic symbols relations).var
        (rho.var index) =
      (rho.liftStatic symbols relations).var
        ((ManySortedFC.Rename.weakenStatic symbols relations).var index) := by
  change
    (ManySortedFC.Rename.weakenMany
      (ManySortedFC.SymbolScope target symbols)
      (ManySortedFC.evidenceKinds relations)).var
        ((ManySortedFC.Rename.weakenMany target
          (ManySortedFC.symbolKinds symbols)).var (rho.var index)) =
      ((rho.liftMany (ManySortedFC.symbolKinds symbols)).liftMany
        (ManySortedFC.evidenceKinds relations)).var
        ((ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope source symbols)
          (ManySortedFC.evidenceKinds relations)).var
          ((ManySortedFC.Rename.weakenMany source
            (ManySortedFC.symbolKinds symbols)).var index))
  rw [weakenMany_liftMany_var rho (ManySortedFC.symbolKinds symbols) index]
  exact weakenMany_liftMany_var
    (rho.liftMany (ManySortedFC.symbolKinds symbols))
    (ManySortedFC.evidenceKinds relations)
    ((ManySortedFC.Rename.weakenMany source
      (ManySortedFC.symbolKinds symbols)).var index)

theorem comp_weakenStatic
    {source target : ManySortedFC.Sig}
    (rho : ManySortedFC.Rename source target)
    (symbols : List ManySortedFC.StaticSort)
    (relations : List ManySortedFC.Relation) :
    rho.comp (ManySortedFC.Rename.weakenStatic symbols relations) =
      (ManySortedFC.Rename.weakenStatic symbols relations).comp
        (rho.liftStatic symbols relations) := by
  apply ManySortedFC.Rename.ext
  intro kind index
  exact weakenStatic_liftStatic_var rho symbols relations index

end ManySortedRename

@[simp]
theorem termVar_extend_there
    {scope : DOTCapture.BinderOnly.Sig}
    {kind : DOTCapture.BinderOnly.BinderKind}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (binding : DOTCapture.BinderOnly.Binding scope kind)
    (index : DOTCapture.BinderOnly.BVar scope .term) :
    termVar (.extend context binding) (.there index) =
      (extendRename context binding).var (termVar context index) := by
  cases binding <;> rfl

@[simp]
theorem staticSlot_extend_there
    {scope : DOTCapture.BinderOnly.Sig}
    {kind : DOTCapture.BinderOnly.BinderKind}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (binding : DOTCapture.BinderOnly.Binding scope kind)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (index : DOTCapture.BinderOnly.BVar scope (.static sort)) :
    staticSlot (.extend context binding) (.there index) =
      (staticSlot context index).rename (extendRename context binding) := by
  cases binding <;> rfl

/-- A source renaming and a target renaming describe the same movement of a
translated context.  The two fields state the invariant on the only names
that source syntax can currently contain. -/
structure RenameAgreement
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    (sourceContext : DOTCapture.BinderOnly.Ctx sourceScope)
    (targetContext : DOTCapture.BinderOnly.Ctx targetScope)
    (sourceRename : DOTCapture.BinderOnly.Rename sourceScope targetScope)
    (targetRename : ManySortedFC.Rename (sig sourceContext)
      (sig targetContext)) : Prop where
  term : ∀ (index : DOTCapture.BinderOnly.BVar sourceScope .term),
    termVar targetContext (sourceRename.var index) =
      targetRename.var (termVar sourceContext index)
  static : ∀ {sort : DOTCapture.BinderOnly.StaticSort}
      (index : DOTCapture.BinderOnly.BVar sourceScope (.static sort)),
    staticSlot targetContext (sourceRename.var index) =
      (staticSlot sourceContext index).rename targetRename

namespace RenameAgreement

/-- Lift a target renaming across the blocks generated by a source interval.
Pattern matching exposes that renaming an endpoint preserves the interval's
relation shape. -/
def liftTargetStatic
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    {sourceContext : DOTCapture.BinderOnly.Ctx sourceScope}
    {targetContext : DOTCapture.BinderOnly.Ctx targetScope}
    (sourceRename : DOTCapture.BinderOnly.Rename sourceScope targetScope)
    (targetRename : ManySortedFC.Rename (sig sourceContext)
      (sig targetContext))
    {sort : DOTCapture.BinderOnly.StaticSort}
    (interval : DOTCapture.BinderOnly.Interval sort sourceScope) :
    ManySortedFC.Rename
      (sig (sourceContext.extendStatic interval))
      (sig (targetContext.extendStatic (interval.rename sourceRename))) :=
  match interval with
  | .bounds .none .none =>
      targetRename.liftStatic [translateSort sort] []
  | .bounds (.some _) .none =>
      targetRename.liftStatic [translateSort sort]
        [.inclusion (translateSort sort)]
  | .bounds .none (.some _) =>
      targetRename.liftStatic [translateSort sort]
        [.inclusion (translateSort sort)]
  | .bounds (.some _) (.some _) =>
      targetRename.liftStatic [translateSort sort]
        [.inclusion (translateSort sort), .inclusion (translateSort sort)]

/-- Identity renamings agree for every translated context. -/
def identity {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope) :
    RenameAgreement context context DOTCapture.BinderOnly.Rename.id
      ManySortedFC.Rename.id where
  term := by intro index; simp
  static := by intro sort index; simp

/-- Agreement lifts through one translated static interval.  The target lift
crosses the complete names-first symbol/evidence block contributed by that
interval, rather than merely one binder. -/
def liftStatic
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    {sourceContext : DOTCapture.BinderOnly.Ctx sourceScope}
    {targetContext : DOTCapture.BinderOnly.Ctx targetScope}
    {sourceRename : DOTCapture.BinderOnly.Rename sourceScope targetScope}
    {targetRename : ManySortedFC.Rename (sig sourceContext)
      (sig targetContext)}
    (agreement : RenameAgreement sourceContext targetContext
      sourceRename targetRename)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (interval : DOTCapture.BinderOnly.Interval sort sourceScope) :
    RenameAgreement
      (sourceContext.extendStatic interval)
      (targetContext.extendStatic (interval.rename sourceRename))
      (sourceRename.lift (kind := .static sort))
      (liftTargetStatic sourceRename targetRename interval) := by
  cases interval with
  | bounds lower upper =>
      cases lower <;> cases upper
      all_goals
        constructor
        · intro index
          cases index with
          | there older =>
              simp only [DOTCapture.BinderOnly.Rename.lift_there]
              unfold DOTCapture.BinderOnly.Ctx.extendStatic
              rw [termVar_extend_there, termVar_extend_there]
              simp [DOTCapture.BinderOnly.Interval.rename,
                DOTCapture.BinderOnly.Endpoint.rename,
                extendRename, intervalRelations, liftTargetStatic,
                agreement.term older,
                ManySortedRename.weakenStatic_liftStatic_var]
        · intro otherSort index
          cases index with
          | here => rfl
          | there older =>
              simp only [DOTCapture.BinderOnly.Rename.lift_there]
              unfold DOTCapture.BinderOnly.Ctx.extendStatic
              rw [staticSlot_extend_there, staticSlot_extend_there]
              simp [DOTCapture.BinderOnly.Interval.rename,
                DOTCapture.BinderOnly.Endpoint.rename,
                extendRename, intervalRelations, liftTargetStatic,
                agreement.static older,
                ManySortedTranslation.StaticSlot.rename_comp]
              exact congrArg
                (fun rho => (staticSlot sourceContext older).rename rho)
                (ManySortedRename.comp_weakenStatic targetRename _ _)

end RenameAgreement

/-! ## Naturality of syntax translation -/

@[simp]
theorem translatePath_rename
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    {sourceContext : DOTCapture.BinderOnly.Ctx sourceScope}
    {targetContext : DOTCapture.BinderOnly.Ctx targetScope}
    {sourceRename : DOTCapture.BinderOnly.Rename sourceScope targetScope}
    {targetRename : ManySortedFC.Rename (sig sourceContext)
      (sig targetContext)}
    (agreement : RenameAgreement sourceContext targetContext
      sourceRename targetRename)
    (path : DOTCapture.BinderOnly.Path sourceScope) :
    translatePath targetContext (path.rename sourceRename) =
      targetRename.var (translatePath sourceContext path) := by
  cases path with
  | var index => exact agreement.term index

@[simp]
theorem translateRef_rename
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    {sourceContext : DOTCapture.BinderOnly.Ctx sourceScope}
    {targetContext : DOTCapture.BinderOnly.Ctx targetScope}
    {sourceRename : DOTCapture.BinderOnly.Rename sourceScope targetScope}
    {targetRename : ManySortedFC.Rename (sig sourceContext)
      (sig targetContext)}
    (agreement : RenameAgreement sourceContext targetContext
      sourceRename targetRename)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (reference : DOTCapture.BinderOnly.StaticRef sort sourceScope) :
    translateRef targetContext (reference.rename sourceRename) =
      (translateRef sourceContext reference).rename targetRename := by
  cases reference with
  | bound index =>
      have expressionEquality := congrArg
        (fun slot => ManySortedFC.StaticExpr.symbol slot.name)
        (agreement.static index)
      cases sort <;>
        simpa [translateRef, DOTCapture.BinderOnly.StaticRef.rename,
          ManySortedTranslation.StaticSlot.expression,
          ManySortedTranslation.StaticSlot.rename,
          ManySortedFC.StaticExpr.rename, ManySortedFC.Ty.rename,
          ManySortedFC.Capture.rename] using expressionEquality

namespace TargetInterval

@[simp]
theorem endpoint_weaken_rename {source target : ManySortedFC.Sig}
    (rho : ManySortedFC.Rename source target)
    {sort : ManySortedFC.StaticSort}
    (expression : ManySortedFC.StaticExpr sort source) :
    expression.weaken.rename (rho.liftSymbols [sort]) =
      (expression.rename rho).weaken := by
  change
    (expression.rename ManySortedFC.Rename.succ).rename
        (rho.lift (kind := .symbol sort)) =
      (expression.rename rho).rename ManySortedFC.Rename.succ
  rw [ManySortedFC.StaticExpr.rename_comp,
    ManySortedFC.StaticExpr.rename_comp,
    ManySortedFC.Rename.succ_lift_comm]

@[simp]
theorem name_rename {source target : ManySortedFC.Sig}
    (rho : ManySortedFC.Rename source target)
    (sort : ManySortedFC.StaticSort) :
    (ManySortedFC.Interval.name (scope := source) (sort := sort)).rename
        (rho.liftSymbols [sort]) =
      ManySortedFC.Interval.name (scope := target) (sort := sort) := by
  cases sort <;> rfl

@[simp]
theorem unconstrained_rename {source target : ManySortedFC.Sig}
    (rho : ManySortedFC.Rename source target)
    (sort : ManySortedFC.StaticSort) :
    (ManySortedFC.Interval.unconstrained sort).rename rho =
      ManySortedFC.Interval.unconstrained sort := rfl

@[simp]
theorem lowerBounded_rename {source target : ManySortedFC.Sig}
    (rho : ManySortedFC.Rename source target)
    {sort : ManySortedFC.StaticSort}
    (lower : ManySortedFC.StaticExpr sort source) :
    (ManySortedFC.Interval.lowerBounded lower).rename rho =
      ManySortedFC.Interval.lowerBounded (lower.rename rho) := by
  simp [ManySortedFC.Interval.lowerBounded, ManySortedFC.Theory.rename,
    ManySortedFC.Proposition.rename]
  exact endpoint_weaken_rename rho lower

@[simp]
theorem upperBounded_rename {source target : ManySortedFC.Sig}
    (rho : ManySortedFC.Rename source target)
    {sort : ManySortedFC.StaticSort}
    (upper : ManySortedFC.StaticExpr sort source) :
    (ManySortedFC.Interval.upperBounded upper).rename rho =
      ManySortedFC.Interval.upperBounded (upper.rename rho) := by
  simp [ManySortedFC.Interval.upperBounded, ManySortedFC.Theory.rename,
    ManySortedFC.Proposition.rename]
  exact endpoint_weaken_rename rho upper

@[simp]
theorem between_rename {source target : ManySortedFC.Sig}
    (rho : ManySortedFC.Rename source target)
    {sort : ManySortedFC.StaticSort}
    (lower upper : ManySortedFC.StaticExpr sort source) :
    (ManySortedFC.Interval.between lower upper).rename rho =
      ManySortedFC.Interval.between (lower.rename rho)
        (upper.rename rho) := by
  simp [ManySortedFC.Interval.between, ManySortedFC.Theory.rename,
    ManySortedFC.Proposition.rename]
  exact ⟨endpoint_weaken_rename rho lower,
    endpoint_weaken_rename rho upper⟩

end TargetInterval

mutual

@[simp]
def translateCapture_rename
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    {sourceContext : DOTCapture.BinderOnly.Ctx sourceScope}
    {targetContext : DOTCapture.BinderOnly.Ctx targetScope}
    {sourceRename : DOTCapture.BinderOnly.Rename sourceScope targetScope}
    {targetRename : ManySortedFC.Rename (sig sourceContext)
      (sig targetContext)}
    (agreement : RenameAgreement sourceContext targetContext
      sourceRename targetRename)
    (capture : DOTCapture.BinderOnly.Capture sourceScope) :
    translateCapture targetContext (capture.rename sourceRename) =
      (translateCapture sourceContext capture).rename targetRename :=
  match capture with
  | .empty => rfl
  | .union left right => by
      simp only [DOTCapture.BinderOnly.Capture.rename, translateCapture,
        ManySortedFC.Capture.rename, translateCapture_rename agreement left,
        translateCapture_rename agreement right]
  | .singleton path => by
      simp only [DOTCapture.BinderOnly.Capture.rename, translateCapture,
        ManySortedFC.Capture.rename, translatePath_rename agreement path]
  | .ref reference => by
      cases reference with
      | bound index =>
          simpa [DOTCapture.BinderOnly.Capture.rename, translateCapture,
            translateRef, DOTCapture.BinderOnly.StaticRef.rename,
            ManySortedTranslation.StaticSlot.expression,
            ManySortedTranslation.StaticSlot.rename,
            ManySortedFC.StaticExpr.symbol, translateSort,
            ManySortedFC.Capture.rename] using
              congrArg
                (fun slot => ManySortedFC.Capture.cvar slot.name)
                (agreement.static index)

@[simp]
def translateTy_rename
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    {sourceContext : DOTCapture.BinderOnly.Ctx sourceScope}
    {targetContext : DOTCapture.BinderOnly.Ctx targetScope}
    {sourceRename : DOTCapture.BinderOnly.Rename sourceScope targetScope}
    {targetRename : ManySortedFC.Rename (sig sourceContext)
      (sig targetContext)}
    (agreement : RenameAgreement sourceContext targetContext
      sourceRename targetRename)
    (type : DOTCapture.BinderOnly.Ty sourceScope) :
    translateTy targetContext (type.rename sourceRename) =
      (translateTy sourceContext type).rename targetRename :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref reference => by
      cases reference with
      | bound index =>
          simpa [DOTCapture.BinderOnly.Ty.rename, translateTy, translateRef,
            DOTCapture.BinderOnly.StaticRef.rename,
            ManySortedTranslation.StaticSlot.expression,
            ManySortedTranslation.StaticSlot.rename,
            ManySortedFC.StaticExpr.symbol, translateSort,
            ManySortedFC.Ty.rename] using
              congrArg (fun slot => ManySortedFC.Ty.tvar slot.name)
                (agreement.static index)
  | .capturing captures shape => by
      simp only [DOTCapture.BinderOnly.Ty.rename, translateTy,
        ManySortedFC.Ty.rename, translateCapture_rename agreement captures,
        translateTy_rename agreement shape]
  | .arr domain codomain => by
      simp only [DOTCapture.BinderOnly.Ty.rename, translateTy,
        ManySortedFC.Ty.rename, translateTy_rename agreement domain,
        translateTy_rename agreement codomain]
  | @DOTCapture.BinderOnly.Ty.forallI _ sort interval body => by
      cases interval with
      | bounds lower upper =>
          cases lower with
          | none =>
              cases upper with
              | none =>
                  simp only [DOTCapture.BinderOnly.Ty.rename, translateTy,
                    DOTCapture.BinderOnly.Interval.rename,
                    DOTCapture.BinderOnly.Endpoint.rename,
                    translateInterval, ManySortedFC.Ty.rename]
                  apply congrArg2 (fun theory body =>
                    ManySortedFC.Ty.forallT theory body)
                  · exact (TargetInterval.unconstrained_rename
                      targetRename (translateSort sort)).symm
                  · simpa [RenameAgreement.liftTargetStatic,
                      intervalRelations] using
                      translateTy_rename
                        (RenameAgreement.liftStatic agreement
                          (.bounds .none .none)) body
              | some upper =>
                  simp only [DOTCapture.BinderOnly.Ty.rename, translateTy,
                    DOTCapture.BinderOnly.Interval.rename,
                    DOTCapture.BinderOnly.Endpoint.rename,
                    translateInterval, ManySortedFC.Ty.rename,
                    translateExpr_rename agreement upper]
                  apply congrArg2 (fun theory body =>
                    ManySortedFC.Ty.forallT theory body)
                  · exact (TargetInterval.upperBounded_rename targetRename
                      (translateExpr sourceContext upper)).symm
                  · simpa [DOTCapture.BinderOnly.Interval.rename,
                      DOTCapture.BinderOnly.Endpoint.rename,
                      RenameAgreement.liftTargetStatic,
                      intervalRelations] using
                      translateTy_rename
                        (RenameAgreement.liftStatic agreement
                          (.bounds .none (.some upper))) body
          | some lower =>
              cases upper with
              | none =>
                  simp only [DOTCapture.BinderOnly.Ty.rename, translateTy,
                    DOTCapture.BinderOnly.Interval.rename,
                    DOTCapture.BinderOnly.Endpoint.rename,
                    translateInterval, ManySortedFC.Ty.rename,
                    translateExpr_rename agreement lower]
                  apply congrArg2 (fun theory body =>
                    ManySortedFC.Ty.forallT theory body)
                  · exact (TargetInterval.lowerBounded_rename targetRename
                      (translateExpr sourceContext lower)).symm
                  · simpa [DOTCapture.BinderOnly.Interval.rename,
                      DOTCapture.BinderOnly.Endpoint.rename,
                      RenameAgreement.liftTargetStatic,
                      intervalRelations] using
                      translateTy_rename
                        (RenameAgreement.liftStatic agreement
                          (.bounds (.some lower) .none)) body
              | some upper =>
                  simp only [DOTCapture.BinderOnly.Ty.rename, translateTy,
                    DOTCapture.BinderOnly.Interval.rename,
                    DOTCapture.BinderOnly.Endpoint.rename,
                    translateInterval, ManySortedFC.Ty.rename,
                    translateExpr_rename agreement lower,
                    translateExpr_rename agreement upper]
                  apply congrArg2 (fun theory body =>
                    ManySortedFC.Ty.forallT theory body)
                  · exact (TargetInterval.between_rename targetRename
                      (translateExpr sourceContext lower)
                      (translateExpr sourceContext upper)).symm
                  · simpa [DOTCapture.BinderOnly.Interval.rename,
                      DOTCapture.BinderOnly.Endpoint.rename,
                      RenameAgreement.liftTargetStatic,
                      intervalRelations] using
                      translateTy_rename
                        (RenameAgreement.liftStatic agreement
                          (.bounds (.some lower) (.some upper))) body
  | @DOTCapture.BinderOnly.Ty.existsI _ sort interval payload => by
      cases interval with
      | bounds lower upper =>
          cases lower with
          | none =>
              cases upper with
              | none =>
                  simp only [DOTCapture.BinderOnly.Ty.rename, translateTy,
                    DOTCapture.BinderOnly.Interval.rename,
                    DOTCapture.BinderOnly.Endpoint.rename,
                    translateInterval, ManySortedFC.Ty.rename]
                  apply congrArg2 (fun theory body =>
                    ManySortedFC.Ty.existsT theory body)
                  · exact (TargetInterval.unconstrained_rename
                      targetRename (translateSort sort)).symm
                  · simpa [RenameAgreement.liftTargetStatic,
                      intervalRelations] using
                      translateTy_rename
                        (RenameAgreement.liftStatic agreement
                          (.bounds .none .none)) payload
              | some upper =>
                  simp only [DOTCapture.BinderOnly.Ty.rename, translateTy,
                    DOTCapture.BinderOnly.Interval.rename,
                    DOTCapture.BinderOnly.Endpoint.rename,
                    translateInterval, ManySortedFC.Ty.rename,
                    translateExpr_rename agreement upper]
                  apply congrArg2 (fun theory body =>
                    ManySortedFC.Ty.existsT theory body)
                  · exact (TargetInterval.upperBounded_rename targetRename
                      (translateExpr sourceContext upper)).symm
                  · simpa [DOTCapture.BinderOnly.Interval.rename,
                      DOTCapture.BinderOnly.Endpoint.rename,
                      RenameAgreement.liftTargetStatic,
                      intervalRelations] using
                      translateTy_rename
                        (RenameAgreement.liftStatic agreement
                          (.bounds .none (.some upper))) payload
          | some lower =>
              cases upper with
              | none =>
                  simp only [DOTCapture.BinderOnly.Ty.rename, translateTy,
                    DOTCapture.BinderOnly.Interval.rename,
                    DOTCapture.BinderOnly.Endpoint.rename,
                    translateInterval, ManySortedFC.Ty.rename,
                    translateExpr_rename agreement lower]
                  apply congrArg2 (fun theory body =>
                    ManySortedFC.Ty.existsT theory body)
                  · exact (TargetInterval.lowerBounded_rename targetRename
                      (translateExpr sourceContext lower)).symm
                  · simpa [DOTCapture.BinderOnly.Interval.rename,
                      DOTCapture.BinderOnly.Endpoint.rename,
                      RenameAgreement.liftTargetStatic,
                      intervalRelations] using
                      translateTy_rename
                        (RenameAgreement.liftStatic agreement
                          (.bounds (.some lower) .none)) payload
              | some upper =>
                  simp only [DOTCapture.BinderOnly.Ty.rename, translateTy,
                    DOTCapture.BinderOnly.Interval.rename,
                    DOTCapture.BinderOnly.Endpoint.rename,
                    translateInterval, ManySortedFC.Ty.rename,
                    translateExpr_rename agreement lower,
                    translateExpr_rename agreement upper]
                  apply congrArg2 (fun theory body =>
                    ManySortedFC.Ty.existsT theory body)
                  · exact (TargetInterval.between_rename targetRename
                      (translateExpr sourceContext lower)
                      (translateExpr sourceContext upper)).symm
                  · simpa [DOTCapture.BinderOnly.Interval.rename,
                      DOTCapture.BinderOnly.Endpoint.rename,
                      RenameAgreement.liftTargetStatic,
                      intervalRelations] using
                      translateTy_rename
                        (RenameAgreement.liftStatic agreement
                          (.bounds (.some lower) (.some upper))) payload

@[simp]
def translateExpr_rename
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    {sourceContext : DOTCapture.BinderOnly.Ctx sourceScope}
    {targetContext : DOTCapture.BinderOnly.Ctx targetScope}
    {sourceRename : DOTCapture.BinderOnly.Rename sourceScope targetScope}
    {targetRename : ManySortedFC.Rename (sig sourceContext)
      (sig targetContext)}
    (agreement : RenameAgreement sourceContext targetContext
      sourceRename targetRename)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (expression : DOTCapture.BinderOnly.StaticExpr sort sourceScope) :
    translateExpr targetContext (expression.rename sourceRename) =
      (translateExpr sourceContext expression).rename targetRename :=
  match expression with
  | .type type => by
      simp only [DOTCapture.BinderOnly.StaticExpr.rename, translateExpr,
        ManySortedFC.StaticExpr.rename, translateTy_rename agreement type]
  | .capture capture => by
      simp only [DOTCapture.BinderOnly.StaticExpr.rename, translateExpr,
        ManySortedFC.StaticExpr.rename,
        translateCapture_rename agreement capture]

end

/-! ## Canonical one-step weakening -/

namespace RenameAgreement

/-- Extending a source context induces exactly the target weakening chosen by
`extendRename`. -/
def weaken
    {scope : DOTCapture.BinderOnly.Sig}
    {kind : DOTCapture.BinderOnly.BinderKind}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (binding : DOTCapture.BinderOnly.Binding scope kind) :
    RenameAgreement context (.extend context binding)
      (DOTCapture.BinderOnly.Rename.succ)
      (extendRename context binding) where
  term := by
    intro index
    simp only [DOTCapture.BinderOnly.Rename.succ_var]
    exact termVar_extend_there context binding index
  static := by
    intro sort index
    simp only [DOTCapture.BinderOnly.Rename.succ_var]
    exact staticSlot_extend_there context binding index

end RenameAgreement

@[simp]
theorem translateCapture_weaken
    {scope : DOTCapture.BinderOnly.Sig}
    {kind : DOTCapture.BinderOnly.BinderKind}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (binding : DOTCapture.BinderOnly.Binding scope kind)
    (capture : DOTCapture.BinderOnly.Capture scope) :
    translateCapture (.extend context binding) capture.weaken =
      (translateCapture context capture).rename
        (extendRename context binding) :=
  translateCapture_rename (RenameAgreement.weaken context binding) capture

@[simp]
theorem translateTy_weaken
    {scope : DOTCapture.BinderOnly.Sig}
    {kind : DOTCapture.BinderOnly.BinderKind}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (binding : DOTCapture.BinderOnly.Binding scope kind)
    (type : DOTCapture.BinderOnly.Ty scope) :
    translateTy (.extend context binding) type.weaken =
      (translateTy context type).rename (extendRename context binding) :=
  translateTy_rename (RenameAgreement.weaken context binding) type

@[simp]
theorem translateExpr_weaken
    {scope : DOTCapture.BinderOnly.Sig}
    {kind : DOTCapture.BinderOnly.BinderKind}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (binding : DOTCapture.BinderOnly.Binding scope kind)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (expression : DOTCapture.BinderOnly.StaticExpr sort scope) :
    translateExpr (.extend context binding) expression.weaken =
      (translateExpr context expression).rename
        (extendRename context binding) :=
  translateExpr_rename (RenameAgreement.weaken context binding) expression

/-! ## Lookup coherence -/

@[simp]
theorem target_lookup_there
    {scope : ManySortedFC.Sig} {kind newest : ManySortedFC.BinderKind}
    (context : ManySortedFC.Ctx scope)
    (binding : ManySortedFC.Binding scope newest)
    (index : ManySortedFC.BVar scope kind) :
    (context.extend binding).lookup (.there index) =
      (context.lookup index).rename ManySortedFC.Rename.succ := rfl

@[simp]
theorem target_lookup_there2
    {scope : ManySortedFC.Sig}
    {kind firstKind secondKind : ManySortedFC.BinderKind}
    (context : ManySortedFC.Ctx scope)
    (first : ManySortedFC.Binding scope firstKind)
    (second : ManySortedFC.Binding (scope ▹ firstKind) secondKind)
    (index : ManySortedFC.BVar scope kind) :
    ((context.extend first).extend second).lookup
        (.there (.there index)) =
      (context.lookup index).rename
        { var := fun index => .there (.there index) } := by
  rw [target_lookup_there, target_lookup_there,
    ManySortedFC.Binding.rename_comp]
  rfl

@[simp]
theorem target_lookup_there3
    {scope : ManySortedFC.Sig}
    {kind firstKind secondKind thirdKind : ManySortedFC.BinderKind}
    (context : ManySortedFC.Ctx scope)
    (first : ManySortedFC.Binding scope firstKind)
    (second : ManySortedFC.Binding (scope ▹ firstKind) secondKind)
    (third : ManySortedFC.Binding
      ((scope ▹ firstKind) ▹ secondKind) thirdKind)
    (index : ManySortedFC.BVar scope kind) :
    (((context.extend first).extend second).extend third).lookup
        (.there (.there (.there index))) =
      (context.lookup index).rename
        { var := fun index => .there (.there (.there index)) } := by
  rw [target_lookup_there, target_lookup_there2,
    ManySortedFC.Binding.rename_comp]
  rfl

/-- Looking up an older target binding after a translated source extension
returns the old payload weakened through exactly the generated target block. -/
@[simp]
theorem translateContext_lookup_extend
    {scope : DOTCapture.BinderOnly.Sig}
    {kind : DOTCapture.BinderOnly.BinderKind}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (binding : DOTCapture.BinderOnly.Binding scope kind)
    {targetKind : ManySortedFC.BinderKind}
    (index : ManySortedFC.BVar (sig context) targetKind) :
    (translateContext (.extend context binding)).lookup
        ((extendRename context binding).var index) =
      ((translateContext context).lookup index).rename
        (extendRename context binding) := by
  cases binding with
  | term type => rfl
  | static interval =>
      cases interval with
      | bounds lower upper =>
          cases lower <;> cases upper <;>
            simp [translateContext, translateInterval, extendRename,
              intervalRelations,
              ManySortedFC.Interval.unconstrained,
              ManySortedFC.Interval.lowerBounded,
              ManySortedFC.Interval.upperBounded,
              ManySortedFC.Interval.between,
              ManySortedFC.Ctx.extendTheory,
              ManySortedFC.Ctx.extendTheoryEvidence,
              ManySortedFC.Ctx.extendSymbols,
              ManySortedFC.Ctx.extendSymbol,
              ManySortedFC.Ctx.extendEvidence,
              ManySortedFC.Rename.weakenStatic,
              ManySortedFC.Rename.weakenSymbols,
              ManySortedFC.Rename.weakenMany,
              ManySortedFC.symbolKinds, ManySortedFC.evidenceKinds,
              ManySortedFC.Rename.comp, ManySortedFC.Rename.succ,
              ManySortedFC.Binding.rename]
          all_goals first
            | exact target_lookup_there _ _ index
            | exact target_lookup_there2 _ _ _ index
            | exact target_lookup_there3 _ _ _ _ index

@[simp]
theorem source_lookupTerm_extend_there
    {scope : DOTCapture.BinderOnly.Sig}
    {kind : DOTCapture.BinderOnly.BinderKind}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (binding : DOTCapture.BinderOnly.Binding scope kind)
    (index : DOTCapture.BinderOnly.BVar scope .term) :
    (DOTCapture.BinderOnly.Ctx.extend context binding).lookupTerm
        (.there index) =
      (context.lookupTerm index).weaken := by
  unfold DOTCapture.BinderOnly.Ctx.lookupTerm
  rw [DOTCapture.BinderOnly.Ctx.lookup_there]
  generalize found : context.lookup index = result
  cases result with
  | term type => rfl

/-- Source term lookup translates to lookup of the corresponding runtime
coordinate in the expanded target context. -/
@[simp]
theorem translate_lookupTerm :
    {scope : DOTCapture.BinderOnly.Sig} →
    (context : DOTCapture.BinderOnly.Ctx scope) →
    (index : DOTCapture.BinderOnly.BVar scope .term) →
    (translateContext context).lookup (termVar context index) =
      ManySortedFC.Binding.term
        (translateTy context (context.lookupTerm index))
  | _, .extend outer (.term type), .here => by
      change
        ManySortedFC.Binding.term (translateTy outer type).weaken =
          ManySortedFC.Binding.term
            (translateTy (.extend outer (.term type)) type.weaken)
      rw [translateTy_weaken]
      rfl
  | _, .extend outer binding, .there older => by
      rw [termVar_extend_there, translateContext_lookup_extend,
        translate_lookupTerm outer older]
      rw [source_lookupTerm_extend_there]
      simp only [ManySortedFC.Binding.rename]
      change
        ManySortedFC.Binding.term
            ((translateTy outer (outer.lookupTerm older)).rename
              (extendRename outer binding)) =
          ManySortedFC.Binding.term
            (translateTy (.extend outer binding)
              (outer.lookupTerm older).weaken)
      rw [translateTy_weaken]

end DOTCaptureToManySortedFC.BinderOnly
