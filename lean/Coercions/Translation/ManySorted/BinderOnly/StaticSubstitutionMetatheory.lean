import Coercions.DOT.Captures.BinderOnly.Substitution
import Coercions.Translation.ManySorted.BinderOnly.LayoutMetatheory
import Coercions.Translation.ManySorted.BinderOnly.ModelElaboration
import Coercions.Translation.ManySorted.BinderOnly.StaticInstantiation

/-!
# Static substitution commutes with binder-only translation

This module relates a source static substitution to the target substitution
induced by the expanded many-sorted context layout.  The relation is stable
under ordinary binders and complete names-first theory blocks, so the main
commutation theorem traverses nested universal and existential intervals.
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

namespace TargetStaticSubstitution

open ManySortedFC

@[simp]
theorem symbol_rename {source target : Sig} {sort : StaticSort}
    (index : BVar source (.symbol sort)) (rho : Rename source target) :
    (StaticExpr.symbol index).rename rho = StaticExpr.symbol (rho.var index) := by
  cases sort <;> rfl

@[simp]
theorem symbol_substitute {source target : Sig} {sort : StaticSort}
    (index : BVar source (.symbol sort))
    (substitution : StaticSubst source target) :
    (StaticExpr.symbol index).substitute substitution =
      substitution.symbolVar index := by
  cases sort with
  | type =>
      cases result : substitution.symbolVar index with
      | type type =>
          simp [StaticExpr.symbol, StaticExpr.substitute, Ty.substitute,
            result]
  | capture =>
      cases result : substitution.symbolVar index with
      | capture capture =>
          simp [StaticExpr.symbol, StaticExpr.substitute,
            Capture.substitute, result]

def capturePart {scope : Sig} (expression : StaticExpr .capture scope) :
    Capture scope :=
  match expression with
  | .capture capture => capture

def typePart {scope : Sig} (expression : StaticExpr .type scope) : Ty scope :=
  match expression with
  | .type type => type

/-- Static substitution is natural with respect to weakening below an
arbitrary heterogeneous target block, on term variables. -/
theorem liftMany_weakenMany_termVar
    {source target : Sig} (substitution : StaticSubst source target)
    (kinds : Sig) (index : BVar source .term) :
    (substitution.liftMany kinds).termVar
        ((Rename.weakenMany source kinds).var index) =
      (Rename.weakenMany target kinds).var
        (substitution.termVar index) := by
  induction kinds with
  | nil => rfl
  | cons newest rest induction =>
      simp only [StaticSubst.liftMany, Rename.weakenMany,
        Rename.comp_var, Rename.succ_var]
      cases newest <;>
        simp only [StaticSubst.lift, StaticSubst.liftTerm,
          StaticSubst.liftSymbol, StaticSubst.liftEvidence] <;>
        exact congrArg BVar.there induction

/-- Static substitution is natural with respect to weakening below an
arbitrary heterogeneous target block, on static-symbol variables. -/
theorem liftMany_weakenMany_symbolVar
    {source target : Sig} (substitution : StaticSubst source target)
    (kinds : Sig) {sort : StaticSort}
    (index : BVar source (.symbol sort)) :
    (substitution.liftMany kinds).symbolVar
        ((Rename.weakenMany source kinds).var index) =
      (substitution.symbolVar index).rename
        (Rename.weakenMany target kinds) := by
  induction kinds with
  | nil =>
      simp [StaticSubst.liftMany, Rename.weakenMany]
  | cons newest rest induction =>
      simp only [StaticSubst.liftMany, Rename.weakenMany,
        Rename.comp_var, Rename.succ_var]
      cases newest <;>
        simp only [StaticSubst.lift, StaticSubst.liftTerm,
          StaticSubst.liftSymbol, StaticSubst.liftEvidence]
      all_goals
        rw [induction]
        exact StaticExpr.rename_comp _ _ _

/-- The term-variable specialization for one complete names-first theory. -/
theorem liftStatic_weakenStatic_termVar
    {source target : Sig} (substitution : StaticSubst source target)
    (symbols : List StaticSort) (relations : List Relation)
    (index : BVar source .term) :
    (substitution.liftStatic symbols relations).termVar
        ((Rename.weakenStatic symbols relations).var index) =
      (Rename.weakenStatic symbols relations).var
        (substitution.termVar index) := by
  change
    ((substitution.liftMany (symbolKinds symbols)).liftMany
        (evidenceKinds relations)).termVar
        ((Rename.weakenMany (SymbolScope source symbols)
          (evidenceKinds relations)).var
          ((Rename.weakenMany source (symbolKinds symbols)).var index)) =
      (Rename.weakenMany (SymbolScope target symbols)
        (evidenceKinds relations)).var
        ((Rename.weakenMany target (symbolKinds symbols)).var
          (substitution.termVar index))
  rw [liftMany_weakenMany_termVar, liftMany_weakenMany_termVar]

/-- The static-symbol specialization for one complete names-first theory. -/
theorem liftStatic_weakenStatic_symbolVar
    {source target : Sig} (substitution : StaticSubst source target)
    (symbols : List StaticSort) (relations : List Relation)
    {sort : StaticSort} (index : BVar source (.symbol sort)) :
    (substitution.liftStatic symbols relations).symbolVar
        ((Rename.weakenStatic symbols relations).var index) =
      (substitution.symbolVar index).rename
        (Rename.weakenStatic symbols relations) := by
  change
    ((substitution.liftMany (symbolKinds symbols)).liftMany
        (evidenceKinds relations)).symbolVar
        ((Rename.weakenMany (SymbolScope source symbols)
          (evidenceKinds relations)).var
          ((Rename.weakenMany source (symbolKinds symbols)).var index)) =
      (substitution.symbolVar index).rename
        ((Rename.weakenMany target (symbolKinds symbols)).comp
          (Rename.weakenMany (SymbolScope target symbols)
            (evidenceKinds relations)))
  rw [liftMany_weakenMany_symbolVar, liftMany_weakenMany_symbolVar,
    StaticExpr.rename_comp]

/-! The small target-side naturality square needed by interval theories. -/

/-- Two renamings and two static substitutions form a commuting square on
the variables visible to target static syntax. -/
structure Square {upperLeft upperRight lowerLeft lowerRight : Sig}
    (upper : StaticSubst upperLeft upperRight)
    (left : Rename upperLeft lowerLeft)
    (right : Rename upperRight lowerRight)
    (lower : StaticSubst lowerLeft lowerRight) : Prop where
  term (index : BVar upperLeft .term) :
    right.var (upper.termVar index) = lower.termVar (left.var index)
  symbol {sort : StaticSort} (index : BVar upperLeft (.symbol sort)) :
    (upper.symbolVar index).rename right =
      lower.symbolVar (left.var index)

namespace Square

@[simp]
theorem rename_weaken_lift {source target : Sig} {kind : BinderKind}
    {sort : StaticSort} (expression : StaticExpr sort source)
    (rho : Rename source target) :
    expression.weaken.rename (rho.lift (kind := kind)) =
      (expression.rename rho).weaken := by
  change
    (expression.rename (Rename.succ (kind := kind))).rename rho.lift =
      (expression.rename rho).rename Rename.succ
  rw [StaticExpr.rename_comp, StaticExpr.rename_comp,
    Rename.succ_lift_comm]

def liftTerm {upperLeft upperRight lowerLeft lowerRight : Sig}
    {upper : StaticSubst upperLeft upperRight}
    {left : Rename upperLeft lowerLeft}
    {right : Rename upperRight lowerRight}
    {lower : StaticSubst lowerLeft lowerRight}
    (square : Square upper left right lower) :
    Square upper.liftTerm left.lift right.lift lower.liftTerm where
  term := by
    intro index
    cases index with
    | here => rfl
    | there older =>
        exact congrArg BVar.there (square.term older)
  symbol := by
    intro sort index
    cases index with
    | there older =>
        simp only [StaticSubst.liftTerm, Rename.lift_there]
        rw [rename_weaken_lift, square.symbol older]

def liftSymbol {upperLeft upperRight lowerLeft lowerRight : Sig}
    {upper : StaticSubst upperLeft upperRight}
    {left : Rename upperLeft lowerLeft}
    {right : Rename upperRight lowerRight}
    {lower : StaticSubst lowerLeft lowerRight}
    (square : Square upper left right lower) (boundSort : StaticSort) :
    Square (upper.liftSymbol boundSort) left.lift right.lift
      (lower.liftSymbol boundSort) where
  term := by
    intro index
    cases index with
    | there older => exact congrArg BVar.there (square.term older)
  symbol := by
    intro sort index
    cases index with
    | here => cases boundSort <;> rfl
    | there older =>
        simp only [StaticSubst.liftSymbol, Rename.lift_there]
        rw [rename_weaken_lift, square.symbol older]

def liftEvidence {upperLeft upperRight lowerLeft lowerRight : Sig}
    {upper : StaticSubst upperLeft upperRight}
    {left : Rename upperLeft lowerLeft}
    {right : Rename upperRight lowerRight}
    {lower : StaticSubst lowerLeft lowerRight}
    (square : Square upper left right lower) (relation : Relation) :
    Square (upper.liftEvidence relation) left.lift right.lift
      (lower.liftEvidence relation) where
  term := by
    intro index
    cases index with
    | there older => exact congrArg BVar.there (square.term older)
  symbol := by
    intro sort index
    cases index with
    | there older =>
        simp only [StaticSubst.liftEvidence, Rename.lift_there]
        rw [rename_weaken_lift, square.symbol older]

def lift {upperLeft upperRight lowerLeft lowerRight : Sig}
    {upper : StaticSubst upperLeft upperRight}
    {left : Rename upperLeft lowerLeft}
    {right : Rename upperRight lowerRight}
    {lower : StaticSubst lowerLeft lowerRight}
    (square : Square upper left right lower) : (kind : BinderKind) →
    Square (upper.lift kind) left.lift right.lift (lower.lift kind)
  | .term => square.liftTerm
  | .symbol sort => square.liftSymbol sort
  | .evidence relation => square.liftEvidence relation

def liftMany {upperLeft upperRight lowerLeft lowerRight : Sig}
    {upper : StaticSubst upperLeft upperRight}
    {left : Rename upperLeft lowerLeft}
    {right : Rename upperRight lowerRight}
    {lower : StaticSubst lowerLeft lowerRight}
    (square : Square upper left right lower) : (kinds : Sig) →
    Square (upper.liftMany kinds) (left.liftMany kinds)
      (right.liftMany kinds) (lower.liftMany kinds)
  | [] => square
  | kind :: rest => (square.liftMany rest).lift kind

def liftStatic {upperLeft upperRight lowerLeft lowerRight : Sig}
    {upper : StaticSubst upperLeft upperRight}
    {left : Rename upperLeft lowerLeft}
    {right : Rename upperRight lowerRight}
    {lower : StaticSubst lowerLeft lowerRight}
    (square : Square upper left right lower)
    (symbols : List StaticSort) (relations : List Relation) :
    Square (upper.liftStatic symbols relations)
      (left.liftStatic symbols relations)
      (right.liftStatic symbols relations)
      (lower.liftStatic symbols relations) :=
  (square.liftMany (symbolKinds symbols)).liftMany
    (evidenceKinds relations)

end Square

mutual

/-- A commuting variable square extends to every target capture. -/
def capture_square {upperLeft upperRight lowerLeft lowerRight : Sig}
    (capture : Capture upperLeft)
    {upper : StaticSubst upperLeft upperRight}
    {left : Rename upperLeft lowerLeft}
    {right : Rename upperRight lowerRight}
    {lower : StaticSubst lowerLeft lowerRight}
    (square : Square upper left right lower) :
    (capture.substitute upper).rename right =
      (capture.rename left).substitute lower :=
  match capture with
  | .empty => rfl
  | .union first second => by
      simp only [Capture.substitute, Capture.rename,
        capture_square first square, capture_square second square]
  | .readOnly capture => by
      simp only [Capture.substitute, Capture.rename,
        capture_square capture square]
  | .singleton capability => by
      simp only [Capture.substitute, Capture.rename]
      exact congrArg Capture.singleton (square.term capability)
  | .cvar name => by
      have symbolEquality := square.symbol name
      cases upperResult : upper.symbolVar name with
      | capture upperCapture =>
          cases lowerResult : lower.symbolVar (left.var name) with
          | capture lowerCapture =>
              simpa [Capture.substitute, Capture.rename,
                StaticExpr.rename, upperResult, lowerResult] using
                symbolEquality

/-- A commuting variable square extends pointwise to the captures that
generate a modal separation context. -/
def separationContext_square {count : Nat}
    {upperLeft upperRight lowerLeft lowerRight : Sig}
    (context : SeparationContext count upperLeft)
    {upper : StaticSubst upperLeft upperRight}
    {left : Rename upperLeft lowerLeft}
    {right : Rename upperRight lowerRight}
    {lower : StaticSubst lowerLeft lowerRight}
    (square : Square upper left right lower) :
    (context.substitute upper).rename right =
      (context.rename left).substitute lower :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [SeparationContext.substitute, SeparationContext.rename,
        separationContext_square rest square, capture_square capture square]

/-- A commuting variable square extends pointwise to modal mode
requirements. -/
def modeContext_square {modes : List CaptureMode}
    {upperLeft upperRight lowerLeft lowerRight : Sig}
    (context : ModeContext modes upperLeft)
    {upper : StaticSubst upperLeft upperRight}
    {left : Rename upperLeft lowerLeft}
    {right : Rename upperRight lowerRight}
    {lower : StaticSubst lowerLeft lowerRight}
    (square : Square upper left right lower) :
    (context.substitute upper).rename right =
      (context.rename left).substitute lower :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [ModeContext.substitute, ModeContext.rename,
        modeContext_square rest square, capture_square capture square]

/-- A commuting variable square extends to a structured modal context. -/
def modalContext_square {separationCount : Nat}
    {modes : List CaptureMode}
    {upperLeft upperRight lowerLeft lowerRight : Sig}
    (context : ModalContext separationCount modes upperLeft)
    {upper : StaticSubst upperLeft upperRight}
    {left : Rename upperLeft lowerLeft}
    {right : Rename upperRight lowerRight}
    {lower : StaticSubst lowerLeft lowerRight}
    (square : Square upper left right lower) :
    (context.substitute upper).rename right =
      (context.rename left).substitute lower :=
  match context with
  | .mk separation mode => by
      simp only [ModalContext.substitute, ModalContext.rename,
        separationContext_square separation square,
        modeContext_square mode square]

/-- A commuting variable square extends to every target type. -/
def ty_square {upperLeft upperRight lowerLeft lowerRight : Sig}
    (type : Ty upperLeft)
    {upper : StaticSubst upperLeft upperRight}
    {left : Rename upperLeft lowerLeft}
    {right : Rename upperRight lowerRight}
    {lower : StaticSubst lowerLeft lowerRight}
    (square : Square upper left right lower) :
    (type.substitute upper).rename right =
      (type.rename left).substitute lower :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar name => by
      have symbolEquality := square.symbol name
      cases upperResult : upper.symbolVar name with
      | type upperType =>
          cases lowerResult : lower.symbolVar (left.var name) with
          | type lowerType =>
              simpa [Ty.substitute, Ty.rename, StaticExpr.rename,
                upperResult, lowerResult] using symbolEquality
  | .capturing capture shape => by
      simp only [Ty.substitute, Ty.rename,
        capture_square capture square, ty_square shape square]
  | .arr domain codomain => by
      simp only [Ty.substitute, Ty.rename, ty_square domain square,
        ty_square codomain square]
  | .modal requirements body => by
      simp only [Ty.substitute, Ty.rename,
        modalContext_square requirements square, ty_square body square]
  | @Ty.forallT _ symbols relations theory body => by
      simp only [Ty.substitute, Ty.rename,
        theory_square theory square,
        ty_square body (square.liftStatic symbols relations)]
  | @Ty.existsT _ symbols relations theory payload => by
      simp only [Ty.substitute, Ty.rename,
        theory_square theory square,
        ty_square payload (square.liftStatic symbols relations)]

/-- A commuting variable square extends to sorted target expressions. -/
def expression_square {upperLeft upperRight lowerLeft lowerRight : Sig}
    {sort : StaticSort} (expression : StaticExpr sort upperLeft)
    {upper : StaticSubst upperLeft upperRight}
    {left : Rename upperLeft lowerLeft}
    {right : Rename upperRight lowerRight}
    {lower : StaticSubst lowerLeft lowerRight}
    (square : Square upper left right lower) :
    (expression.substitute upper).rename right =
      (expression.rename left).substitute lower :=
  match expression with
  | .type type => by
      simp only [StaticExpr.substitute, StaticExpr.rename,
        ty_square type square]
  | .capture capture => by
      simp only [StaticExpr.substitute, StaticExpr.rename,
        capture_square capture square]

/-- A commuting variable square extends to target propositions. -/
def proposition_square {upperLeft upperRight lowerLeft lowerRight : Sig}
    {relation : Relation} (proposition : Proposition relation upperLeft)
    {upper : StaticSubst upperLeft upperRight}
    {left : Rename upperLeft lowerLeft}
    {right : Rename upperRight lowerRight}
    {lower : StaticSubst lowerLeft lowerRight}
    (square : Square upper left right lower) :
    (proposition.substitute upper).rename right =
      (proposition.rename left).substitute lower :=
  match proposition with
  | .equality first second => by
      simp only [Proposition.substitute, Proposition.rename,
        expression_square first square, expression_square second square]
  | .inclusion first second => by
      simp only [Proposition.substitute, Proposition.rename,
        expression_square first square, expression_square second square]
  | .separate first second => by
      simp only [Proposition.substitute, Proposition.rename,
        capture_square first square, capture_square second square]
  | .disjoint first second => by
      simp only [Proposition.substitute, Proposition.rename,
        capture_square first square, capture_square second square]
  | .mode capture => by
      simp only [Proposition.substitute, Proposition.rename,
        capture_square capture square]

/-- A commuting variable square extends to target theories, including their
names-first proposition scopes. -/
def theory_square {upperLeft upperRight lowerLeft lowerRight : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory upperLeft symbols relations)
    {upper : StaticSubst upperLeft upperRight}
    {left : Rename upperLeft lowerLeft}
    {right : Rename upperRight lowerRight}
    {lower : StaticSubst lowerLeft lowerRight}
    (square : Square upper left right lower) :
    (theory.substitute upper).rename right =
      (theory.rename left).substitute lower :=
  match theory with
  | .nil => rfl
  | .cons proposition rest => by
      simp only [Theory.substitute, Theory.rename]
      apply congrArg2 Theory.cons
      · simpa [StaticSubst.liftSymbols, Rename.liftSymbols] using
          proposition_square proposition
            (square.liftMany (symbolKinds symbols))
      · exact theory_square rest square

end

/-- The weakening square induced by lifting a substitution below one target
binder. -/
def weakenSquare {source target : Sig} (substitution : StaticSubst source target)
    (kind : BinderKind) :
    Square substitution (Rename.succ (kind := kind))
      (Rename.succ (kind := kind)) (substitution.lift kind) where
  term := by intro index; cases kind <;> rfl
  symbol := by intro sort index; cases kind <;> rfl

@[simp]
theorem expression_weaken_substitute {source target : Sig}
    (substitution : StaticSubst source target) (kind : BinderKind)
    {sort : StaticSort} (expression : StaticExpr sort source) :
    expression.weaken.substitute (substitution.lift kind) =
      (expression.substitute substitution).weaken :=
  (expression_square expression (weakenSquare substitution kind)).symm

@[simp]
theorem endpoint_weaken_substitute {source target : Sig}
    (substitution : StaticSubst source target) {sort : StaticSort}
    (expression : StaticExpr sort source) :
    expression.weaken.substitute (substitution.liftSymbols [sort]) =
      (expression.substitute substitution).weaken := by
  simpa [StaticSubst.liftSymbols, symbolKinds, StaticSubst.liftMany,
    StaticSubst.lift] using
    expression_weaken_substitute substitution (.symbol sort) expression

end TargetStaticSubstitution

namespace TargetIntervalSubstitution

open ManySortedFC

@[simp]
theorem name {source target : Sig}
    (substitution : StaticSubst source target) (sort : StaticSort) :
    (Interval.name (scope := source) (sort := sort)).substitute
        (substitution.liftSymbols [sort]) =
      Interval.name (scope := target) (sort := sort) := by
  cases sort <;> rfl

@[simp]
theorem unconstrained {source target : Sig}
    (substitution : StaticSubst source target) (sort : StaticSort) :
    (Interval.unconstrained sort).substitute substitution =
      Interval.unconstrained sort := rfl

@[simp]
theorem lowerBounded {source target : Sig}
    (substitution : StaticSubst source target) {sort : StaticSort}
    (lower : StaticExpr sort source) :
    (Interval.lowerBounded lower).substitute substitution =
      Interval.lowerBounded (lower.substitute substitution) := by
  simp [Interval.lowerBounded, Theory.substitute, Proposition.substitute]
  exact TargetStaticSubstitution.endpoint_weaken_substitute
    substitution lower

@[simp]
theorem upperBounded {source target : Sig}
    (substitution : StaticSubst source target) {sort : StaticSort}
    (upper : StaticExpr sort source) :
    (Interval.upperBounded upper).substitute substitution =
      Interval.upperBounded (upper.substitute substitution) := by
  simp [Interval.upperBounded, Theory.substitute, Proposition.substitute]
  exact TargetStaticSubstitution.endpoint_weaken_substitute
    substitution upper

@[simp]
theorem between {source target : Sig}
    (substitution : StaticSubst source target) {sort : StaticSort}
    (lower upper : StaticExpr sort source) :
    (Interval.between lower upper).substitute substitution =
      Interval.between (lower.substitute substitution)
        (upper.substitute substitution) := by
  simp [Interval.between, Theory.substitute, Proposition.substitute]
  exact ⟨TargetStaticSubstitution.endpoint_weaken_substitute
      substitution lower,
    TargetStaticSubstitution.endpoint_weaken_substitute substitution upper⟩

end TargetIntervalSubstitution

/-- A source static substitution and a target static substitution agree when
they act identically on every source-visible term and static variable after
context expansion. -/
structure StaticSubstitutionAgreement
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    (sourceContext : DOTCapture.BinderOnly.Ctx sourceScope)
    (targetContext : DOTCapture.BinderOnly.Ctx targetScope)
    (sourceSubstitution : DOTCapture.BinderOnly.StaticSubst
      sourceScope targetScope)
    (targetSubstitution : ManySortedFC.StaticSubst
      (sig sourceContext) (sig targetContext)) : Prop where
  term : ∀ (index : DOTCapture.BinderOnly.BVar sourceScope .term),
    termVar targetContext (sourceSubstitution.termVar index) =
      targetSubstitution.termVar (termVar sourceContext index)
  static : ∀ {sort : DOTCapture.BinderOnly.StaticSort}
      (index : DOTCapture.BinderOnly.BVar sourceScope (.static sort)),
    translateExpr targetContext (sourceSubstitution.staticVar index) =
      (translateRef sourceContext (.bound index)).substitute
        targetSubstitution

namespace StaticSubstitutionAgreement

/-- Lift the target substitution through the block generated by a source
interval. Pattern matching hides the definitional equality saying that
static substitution preserves the interval's endpoint/relation shape. -/
def liftTargetStatic
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    {sourceContext : DOTCapture.BinderOnly.Ctx sourceScope}
    {targetContext : DOTCapture.BinderOnly.Ctx targetScope}
    (sourceSubstitution : DOTCapture.BinderOnly.StaticSubst
      sourceScope targetScope)
    (targetSubstitution : ManySortedFC.StaticSubst
      (sig sourceContext) (sig targetContext))
    {sort : DOTCapture.BinderOnly.StaticSort}
    (interval : DOTCapture.BinderOnly.Interval sort sourceScope) :
    ManySortedFC.StaticSubst
      (sig (sourceContext.extendStatic interval))
      (sig (targetContext.extendStatic
        (interval.substitute sourceSubstitution))) :=
  match interval with
  | .bounds .none .none =>
      targetSubstitution.liftStatic [translateSort sort] []
  | .bounds (.some _) .none =>
      targetSubstitution.liftStatic [translateSort sort]
        [.inclusion (translateSort sort)]
  | .bounds .none (.some _) =>
      targetSubstitution.liftStatic [translateSort sort]
        [.inclusion (translateSort sort)]
  | .bounds (.some _) (.some _) =>
      targetSubstitution.liftStatic [translateSort sort]
        [.inclusion (translateSort sort), .inclusion (translateSort sort)]

/-- Agreement is stable below an ordinary source term binder. -/
def liftTerm
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    {sourceContext : DOTCapture.BinderOnly.Ctx sourceScope}
    {targetContext : DOTCapture.BinderOnly.Ctx targetScope}
    {sourceSubstitution : DOTCapture.BinderOnly.StaticSubst
      sourceScope targetScope}
    {targetSubstitution : ManySortedFC.StaticSubst
      (sig sourceContext) (sig targetContext)}
    (agreement : StaticSubstitutionAgreement sourceContext targetContext
      sourceSubstitution targetSubstitution)
    (type : DOTCapture.BinderOnly.Ty sourceScope) :
    StaticSubstitutionAgreement
      (sourceContext.extendTerm type)
      (targetContext.extendTerm (type.substitute sourceSubstitution))
      sourceSubstitution.liftTerm targetSubstitution.liftTerm := by
  constructor
  · intro index
    cases index with
    | here => rfl
    | there older =>
        simp only [DOTCapture.BinderOnly.StaticSubst.liftTerm,
          DOTCapture.BinderOnly.Ctx.extendTerm]
        rw [termVar_extend_there, termVar_extend_there]
        simp only [extendRename, ManySortedFC.StaticSubst.liftTerm]
        exact congrArg ManySortedFC.BVar.there (agreement.term older)
  · intro sort index
    cases index with
    | there older =>
        simp only [DOTCapture.BinderOnly.StaticSubst.liftTerm]
        unfold DOTCapture.BinderOnly.Ctx.extendTerm
        rw [translateExpr_weaken]
        simp only [translateRef]
        rw [staticSlot_extend_there]
        have weakened := congrArg
          (fun expression : ManySortedFC.StaticExpr
              (translateSort sort) (sig targetContext) =>
            expression.rename
              (ManySortedFC.Rename.succ (kind := .term)))
          (agreement.static older)
        simpa [translateRef, ManySortedTranslation.StaticSlot.expression,
          ManySortedTranslation.StaticSlot.rename,
          extendRename, ManySortedFC.StaticSubst.liftTerm] using weakened

/-- Agreement is stable below one source interval and the complete target
symbol/evidence block generated from it. -/
def liftStatic
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    {sourceContext : DOTCapture.BinderOnly.Ctx sourceScope}
    {targetContext : DOTCapture.BinderOnly.Ctx targetScope}
    {sourceSubstitution : DOTCapture.BinderOnly.StaticSubst
      sourceScope targetScope}
    {targetSubstitution : ManySortedFC.StaticSubst
      (sig sourceContext) (sig targetContext)}
    (agreement : StaticSubstitutionAgreement sourceContext targetContext
      sourceSubstitution targetSubstitution)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (interval : DOTCapture.BinderOnly.Interval sort sourceScope) :
    StaticSubstitutionAgreement
      (sourceContext.extendStatic interval)
      (targetContext.extendStatic
        (interval.substitute sourceSubstitution))
      (sourceSubstitution.liftStatic sort)
      (liftTargetStatic sourceSubstitution targetSubstitution interval) := by
  let targetInterval := interval.substitute sourceSubstitution
  let targetWeakening := extendRename targetContext (.static targetInterval)
  cases interval with
  | bounds lower upper =>
      cases lower <;> cases upper
      all_goals
        constructor
        · intro index
          cases index with
          | there older =>
              simp only [DOTCapture.BinderOnly.StaticSubst.liftStatic]
              unfold DOTCapture.BinderOnly.Ctx.extendStatic
              rw [termVar_extend_there, termVar_extend_there]
              simp [DOTCapture.BinderOnly.Interval.substitute,
                DOTCapture.BinderOnly.Endpoint.substitute,
                liftTargetStatic, extendRename, intervalRelations,
                TargetStaticSubstitution.liftStatic_weakenStatic_termVar,
                agreement.term older]
        · intro otherSort index
          cases index with
          | here =>
              cases sort <;> rfl
          | there older =>
              simp only [DOTCapture.BinderOnly.StaticSubst.liftStatic]
              unfold DOTCapture.BinderOnly.Ctx.extendStatic
              rw [translateExpr_weaken]
              simp only [translateRef]
              rw [staticSlot_extend_there]
              cases otherSort
              all_goals
                have weakened := congrArg
                  (fun expression : ManySortedFC.StaticExpr
                      (translateSort _) (sig targetContext) =>
                    expression.rename targetWeakening)
                  (agreement.static older)
                simpa [
                  targetInterval, targetWeakening,
                  DOTCapture.BinderOnly.Interval.substitute,
                  DOTCapture.BinderOnly.Endpoint.substitute,
                  liftTargetStatic, translateRef, extendRename,
                  intervalRelations,
                  ManySortedTranslation.StaticSlot.expression,
                  ManySortedTranslation.StaticSlot.rename,
                  TargetStaticSubstitution.liftStatic_weakenStatic_symbolVar]
                  using weakened

end StaticSubstitutionAgreement

@[simp]
theorem translatePath_substitute
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    {sourceContext : DOTCapture.BinderOnly.Ctx sourceScope}
    {targetContext : DOTCapture.BinderOnly.Ctx targetScope}
    {sourceSubstitution : DOTCapture.BinderOnly.StaticSubst
      sourceScope targetScope}
    {targetSubstitution : ManySortedFC.StaticSubst
      (sig sourceContext) (sig targetContext)}
    (agreement : StaticSubstitutionAgreement sourceContext targetContext
      sourceSubstitution targetSubstitution)
    (path : DOTCapture.BinderOnly.Path sourceScope) :
    translatePath targetContext (path.substitute sourceSubstitution) =
      targetSubstitution.termVar (translatePath sourceContext path) := by
  cases path with
  | var index => exact agreement.term index

mutual

/-- Translation commutes with every agreeing static substitution on source
capture expressions. -/
@[simp]
def translateCapture_substitute
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    {sourceContext : DOTCapture.BinderOnly.Ctx sourceScope}
    {targetContext : DOTCapture.BinderOnly.Ctx targetScope}
    {sourceSubstitution : DOTCapture.BinderOnly.StaticSubst
      sourceScope targetScope}
    {targetSubstitution : ManySortedFC.StaticSubst
      (sig sourceContext) (sig targetContext)}
    (agreement : StaticSubstitutionAgreement sourceContext targetContext
      sourceSubstitution targetSubstitution)
    (capture : DOTCapture.BinderOnly.Capture sourceScope) :
    translateCapture targetContext
        (capture.substitute sourceSubstitution) =
      (translateCapture sourceContext capture).substitute
        targetSubstitution :=
  match capture with
  | .empty => rfl
  | .union first second => by
      simp only [DOTCapture.BinderOnly.Capture.substitute,
        translateCapture, ManySortedFC.Capture.substitute,
        translateCapture_substitute agreement first,
        translateCapture_substitute agreement second]
  | .singleton path => by
      simp only [DOTCapture.BinderOnly.Capture.substitute,
        translateCapture, ManySortedFC.Capture.substitute,
        translatePath_substitute agreement path]
  | .ref (.bound index) => by
      have expressionEquality := agreement.static index
      cases sourceResult : sourceSubstitution.staticVar index with
      | capture sourceCapture =>
          rw [sourceResult] at expressionEquality
          simp only [translateExpr, translateRef,
            ManySortedTranslation.StaticSlot.expression,
            TargetStaticSubstitution.symbol_substitute]
            at expressionEquality
          have projected := congrArg
            TargetStaticSubstitution.capturePart
            expressionEquality
          simp only [DOTCapture.BinderOnly.Capture.substitute,
            DOTCapture.BinderOnly.StaticRef.substitute,
            sourceResult, translateCapture, translateRef, translateSort,
            ManySortedTranslation.StaticSlot.expression,
            ManySortedFC.StaticExpr.symbol,
            ManySortedFC.Capture.substitute]
          change translateCapture targetContext sourceCapture =
            TargetStaticSubstitution.capturePart
              (targetSubstitution.symbolVar
                (staticSlot sourceContext index).name)
          exact projected

/-- Translation commutes with every agreeing static substitution on source
types, including nested interval binders. -/
@[simp]
def translateTy_substitute
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    {sourceContext : DOTCapture.BinderOnly.Ctx sourceScope}
    {targetContext : DOTCapture.BinderOnly.Ctx targetScope}
    {sourceSubstitution : DOTCapture.BinderOnly.StaticSubst
      sourceScope targetScope}
    {targetSubstitution : ManySortedFC.StaticSubst
      (sig sourceContext) (sig targetContext)}
    (agreement : StaticSubstitutionAgreement sourceContext targetContext
      sourceSubstitution targetSubstitution)
    (type : DOTCapture.BinderOnly.Ty sourceScope) :
    translateTy targetContext (type.substitute sourceSubstitution) =
      (translateTy sourceContext type).substitute targetSubstitution :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref (.bound index) => by
      have expressionEquality := agreement.static index
      cases sourceResult : sourceSubstitution.staticVar index with
      | type sourceType =>
          rw [sourceResult] at expressionEquality
          simp only [translateExpr, translateRef,
            ManySortedTranslation.StaticSlot.expression,
            TargetStaticSubstitution.symbol_substitute]
            at expressionEquality
          have projected := congrArg
            TargetStaticSubstitution.typePart
            expressionEquality
          simp only [DOTCapture.BinderOnly.Ty.substitute,
            DOTCapture.BinderOnly.StaticRef.substitute,
            sourceResult, translateTy, translateRef, translateSort,
            ManySortedTranslation.StaticSlot.expression,
            ManySortedFC.StaticExpr.symbol,
            ManySortedFC.Ty.substitute]
          change translateTy targetContext sourceType =
            TargetStaticSubstitution.typePart
              (targetSubstitution.symbolVar
                (staticSlot sourceContext index).name)
          exact projected
  | .capturing capture shape => by
      simp only [DOTCapture.BinderOnly.Ty.substitute, translateTy,
        ManySortedFC.Ty.substitute,
        translateCapture_substitute agreement capture,
        translateTy_substitute agreement shape]
  | .arr domain codomain => by
      simp only [DOTCapture.BinderOnly.Ty.substitute, translateTy,
        ManySortedFC.Ty.substitute,
        translateTy_substitute agreement domain,
        translateTy_substitute agreement codomain]
  | @DOTCapture.BinderOnly.Ty.forallI _ sort interval body => by
      cases interval with
      | bounds lower upper =>
          let original : DOTCapture.BinderOnly.Interval sort sourceScope :=
            .bounds lower upper
          cases lower <;> cases upper <;>
            simp only [DOTCapture.BinderOnly.Ty.substitute,
              DOTCapture.BinderOnly.Interval.substitute,
              DOTCapture.BinderOnly.Endpoint.substitute,
              translateTy, ManySortedFC.Ty.substitute]
          all_goals
            apply congrArg2 (fun theory body =>
              ManySortedFC.Ty.forallT theory body)
            · simp only [translateInterval]
              first
              | exact (TargetIntervalSubstitution.unconstrained
                  targetSubstitution _).symm
              | exact (congrArg ManySortedFC.Interval.lowerBounded
                  (translateExpr_substitute agreement _)).trans
                    (TargetIntervalSubstitution.lowerBounded
                      targetSubstitution _).symm
              | exact (congrArg ManySortedFC.Interval.upperBounded
                  (translateExpr_substitute agreement _)).trans
                    (TargetIntervalSubstitution.upperBounded
                      targetSubstitution _).symm
              | exact (congrArg2 ManySortedFC.Interval.between
                  (translateExpr_substitute agreement _)
                  (translateExpr_substitute agreement _)).trans
                    (TargetIntervalSubstitution.between
                      targetSubstitution _ _).symm
            · simpa [original,
                StaticSubstitutionAgreement.liftTargetStatic,
                intervalRelations] using
                translateTy_substitute
                  (StaticSubstitutionAgreement.liftStatic agreement original)
                  body
  | @DOTCapture.BinderOnly.Ty.existsI _ sort interval payload => by
      cases interval with
      | bounds lower upper =>
          let original : DOTCapture.BinderOnly.Interval sort sourceScope :=
            .bounds lower upper
          cases lower <;> cases upper <;>
            simp only [DOTCapture.BinderOnly.Ty.substitute,
              DOTCapture.BinderOnly.Interval.substitute,
              DOTCapture.BinderOnly.Endpoint.substitute,
              translateTy, ManySortedFC.Ty.substitute]
          all_goals
            apply congrArg2 (fun theory body =>
              ManySortedFC.Ty.existsT theory body)
            · simp only [translateInterval]
              first
              | exact (TargetIntervalSubstitution.unconstrained
                  targetSubstitution _).symm
              | exact (congrArg ManySortedFC.Interval.lowerBounded
                  (translateExpr_substitute agreement _)).trans
                    (TargetIntervalSubstitution.lowerBounded
                      targetSubstitution _).symm
              | exact (congrArg ManySortedFC.Interval.upperBounded
                  (translateExpr_substitute agreement _)).trans
                    (TargetIntervalSubstitution.upperBounded
                      targetSubstitution _).symm
              | exact (congrArg2 ManySortedFC.Interval.between
                  (translateExpr_substitute agreement _)
                  (translateExpr_substitute agreement _)).trans
                    (TargetIntervalSubstitution.between
                      targetSubstitution _ _).symm
            · simpa [original,
                StaticSubstitutionAgreement.liftTargetStatic,
                intervalRelations] using
                translateTy_substitute
                  (StaticSubstitutionAgreement.liftStatic agreement original)
                  payload

/-- Translation commutes with every agreeing substitution on sorted source
static expressions. -/
@[simp]
def translateExpr_substitute
    {sourceScope targetScope : DOTCapture.BinderOnly.Sig}
    {sourceContext : DOTCapture.BinderOnly.Ctx sourceScope}
    {targetContext : DOTCapture.BinderOnly.Ctx targetScope}
    {sourceSubstitution : DOTCapture.BinderOnly.StaticSubst
      sourceScope targetScope}
    {targetSubstitution : ManySortedFC.StaticSubst
      (sig sourceContext) (sig targetContext)}
    (agreement : StaticSubstitutionAgreement sourceContext targetContext
      sourceSubstitution targetSubstitution)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (expression : DOTCapture.BinderOnly.StaticExpr sort sourceScope) :
    translateExpr targetContext
        (expression.substitute sourceSubstitution) =
      (translateExpr sourceContext expression).substitute
        targetSubstitution :=
  match expression with
  | .type type => by
      simp only [DOTCapture.BinderOnly.StaticExpr.substitute,
        translateExpr, ManySortedFC.StaticExpr.substitute,
        translateTy_substitute agreement type]
  | .capture capture => by
      simp only [DOTCapture.BinderOnly.StaticExpr.substitute,
        translateExpr, ManySortedFC.StaticExpr.substitute,
        translateCapture_substitute agreement capture]

end

/-! ## Canonical one-binder instantiation -/

/-- The complete target substitution induced by a source witness.  The
endpoint case split only exposes the relation-list index; every branch uses
the same translated one-symbol argument. -/
def targetInstantiation
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (interval : DOTCapture.BinderOnly.Interval sort scope)
    (witness : DOTCapture.BinderOnly.StaticExpr sort scope) :
    ManySortedFC.StaticSubst (sig (context.extendStatic interval))
      (sig context) :=
  match interval with
  | .bounds .none .none =>
      ManySortedFC.StaticSubst.staticOfSymbolArgs ManySortedFC.Rename.id
        (TargetIntervalModel.symbols (translateExpr context witness)) []
  | .bounds (.some _) .none =>
      ManySortedFC.StaticSubst.staticOfSymbolArgs ManySortedFC.Rename.id
        (TargetIntervalModel.symbols (translateExpr context witness))
        [.inclusion (translateSort sort)]
  | .bounds .none (.some _) =>
      ManySortedFC.StaticSubst.staticOfSymbolArgs ManySortedFC.Rename.id
        (TargetIntervalModel.symbols (translateExpr context witness))
        [.inclusion (translateSort sort)]
  | .bounds (.some _) (.some _) =>
      ManySortedFC.StaticSubst.staticOfSymbolArgs ManySortedFC.Rename.id
        (TargetIntervalModel.symbols (translateExpr context witness))
        [.inclusion (translateSort sort), .inclusion (translateSort sort)]

/-- Instantiation cancels the complete weakening block generated by an
interval, including all of its proof-only evidence binders. -/
def targetInstantiation_cancels
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (interval : DOTCapture.BinderOnly.Interval sort scope)
    (witness : DOTCapture.BinderOnly.StaticExpr sort scope) :
    TargetStaticInstantiation.Cancels
      (extendRename context (.static interval))
      (targetInstantiation context interval witness) := by
  cases interval with
  | bounds lower upper =>
      cases lower <;> cases upper
      all_goals
        constructor
        · intro index
          rfl
        · intro otherSort index
          cases otherSort <;> rfl

/-- The canonical source and target one-binder instantiations agree on every
source-visible variable. -/
def instantiationAgreement
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (interval : DOTCapture.BinderOnly.Interval sort scope)
    (witness : DOTCapture.BinderOnly.StaticExpr sort scope) :
    StaticSubstitutionAgreement (context.extendStatic interval) context
      (DOTCapture.BinderOnly.StaticSubst.instantiateNewest witness)
      (targetInstantiation context interval witness) := by
  cases interval with
  | bounds lower upper =>
      let original : DOTCapture.BinderOnly.Interval sort scope :=
        .bounds lower upper
      cases lower <;> cases upper
      all_goals
        constructor
        · intro index
          cases index with
          | there older =>
              exact (targetInstantiation_cancels context _ witness).termVar
                (termVar context older) |>.symm
        · intro otherSort index
          cases index with
          | here => cases witness <;> rfl
          | there older =>
              simp only [DOTCapture.BinderOnly.StaticSubst.instantiateNewest,
                DOTCapture.BinderOnly.StaticSubst.instantiateStatic,
                DOTCapture.BinderOnly.StaticSubst.id]
              unfold DOTCapture.BinderOnly.Ctx.extendStatic
              simp only [translateRef]
              rw [staticSlot_extend_there]
              cases otherSort
              all_goals
                simpa [original, translateExpr,
                  DOTCapture.BinderOnly.StaticExpr.bound,
                  translateTy, translateCapture, translateRef, translateSort,
                  ManySortedTranslation.StaticSlot.expression,
                  ManySortedTranslation.StaticSlot.rename,
                  TargetStaticSubstitution.symbol_rename] using
                  (TargetStaticInstantiation.expression_rename_substitute
                    (staticSlot context older).expression
                    (targetInstantiation_cancels context original witness)).symm

/-- Type translation commutes with source one-static-binder instantiation.
The public orientation matches static application and package opening. -/
@[simp]
theorem translateTy_instantiateStatic
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (interval : DOTCapture.BinderOnly.Interval sort scope)
    (body : DOTCapture.BinderOnly.Ty (scope ▹ .static sort))
    (witness : DOTCapture.BinderOnly.StaticExpr sort scope) :
    (translateTy (context.extendStatic interval) body).instantiateStatic
        (TargetIntervalModel.symbols (translateExpr context witness)) =
      translateTy context (body.instantiateStatic witness) := by
  cases interval with
  | bounds lower upper =>
      cases lower <;> cases upper
      all_goals
        symm
        simpa [DOTCapture.BinderOnly.Ty.instantiateStatic,
          ManySortedFC.Ty.instantiateStatic, targetInstantiation,
          TargetIntervalModel.symbols] using
          translateTy_substitute
            (instantiationAgreement context _ witness) body

/-- Capture translation commutes with source one-static-binder
instantiation. -/
@[simp]
theorem translateCapture_instantiateStatic
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (interval : DOTCapture.BinderOnly.Interval sort scope)
    (body : DOTCapture.BinderOnly.Capture (scope ▹ .static sort))
    (witness : DOTCapture.BinderOnly.StaticExpr sort scope) :
    (translateCapture (context.extendStatic interval) body).instantiateStatic
        (TargetIntervalModel.symbols (translateExpr context witness)) =
      translateCapture context (body.instantiateStatic witness) := by
  cases interval with
  | bounds lower upper =>
      cases lower <;> cases upper
      all_goals
        symm
        simpa [DOTCapture.BinderOnly.Capture.instantiateStatic,
          ManySortedFC.Capture.instantiateStatic, targetInstantiation,
          TargetIntervalModel.symbols] using
          translateCapture_substitute
            (instantiationAgreement context _ witness) body

/-- Sorted static-expression translation commutes with source
one-static-binder instantiation. -/
@[simp]
theorem translateExpr_instantiateStatic
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {boundSort expressionSort : DOTCapture.BinderOnly.StaticSort}
    (interval : DOTCapture.BinderOnly.Interval boundSort scope)
    (body : DOTCapture.BinderOnly.StaticExpr expressionSort
      (scope ▹ .static boundSort))
    (witness : DOTCapture.BinderOnly.StaticExpr boundSort scope) :
    (translateExpr (context.extendStatic interval) body).instantiateStatic
        (TargetIntervalModel.symbols (translateExpr context witness)) =
      translateExpr context (body.instantiateStatic witness) := by
  cases interval with
  | bounds lower upper =>
      cases lower <;> cases upper
      all_goals
        symm
        simpa [DOTCapture.BinderOnly.StaticExpr.instantiateStatic,
          ManySortedFC.StaticExpr.instantiateStatic, targetInstantiation,
          TargetIntervalModel.symbols] using
          translateExpr_substitute
            (instantiationAgreement context _ witness) body

namespace StaticSubstitutionRegression

open DOTCapture.BinderOnly

private def outerTypeInterval : Interval .type [] :=
  .bounds .none .none

/-- The replaced outer type variable occurs below a nested two-evidence
interval, exercising both nested static lifting and evidence-binder blocks. -/
private def nestedTypeBody : Ty ([.static .type]) :=
  .forallI
    (.bounds (.some (.type .bot)) (.some (.type .top)))
    (.ref (.bound (.there .here)))

example :
    (translateTy ((Ctx.nil).extendStatic outerTypeInterval)
        nestedTypeBody).instantiateStatic
      (TargetIntervalModel.symbols
        (translateExpr Ctx.nil (.type .one))) =
      translateTy Ctx.nil
        (nestedTypeBody.instantiateStatic (.type .one)) := by
  exact translateTy_instantiateStatic Ctx.nil outerTypeInterval
    nestedTypeBody (.type .one)

private def termContext : Ctx ([.term]) :=
  Ctx.nil.extendTerm .one

private def outerCaptureInterval : Interval .capture [.term] :=
  .bounds (.some (.capture .empty)) .none

/-- Capture instantiation is nonvacuous: it replaces the outer abstract
capture by a concrete singleton capability and retains an independent
singleton in the body. -/
private def captureBody : Capture ([.static .capture, .term]) :=
  .union (.ref (.bound .here)) (.singleton (.var (.there .here)))

example :
    (translateCapture (termContext.extendStatic outerCaptureInterval)
        captureBody).instantiateStatic
      (TargetIntervalModel.symbols
        (translateExpr termContext
          (.capture (.singleton (.var .here))))) =
      translateCapture termContext
        (captureBody.instantiateStatic
          (.capture (.singleton (.var .here)))) := by
  exact translateCapture_instantiateStatic termContext outerCaptureInterval
    captureBody (.capture (.singleton (.var .here)))

end StaticSubstitutionRegression

end DOTCaptureToManySortedFC.BinderOnly
