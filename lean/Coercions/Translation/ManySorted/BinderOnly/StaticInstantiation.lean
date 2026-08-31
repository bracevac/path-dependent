import Coercions.ManySortedFC.Substitution

/-!
# Static-instantiation cancellation for translated intervals

An interval endpoint is first weakened below its generated target symbol and
then instantiated with the chosen witness.  The endpoint cannot mention that
fresh symbol, so these two operations cancel.  The proof below states the
slightly more general renaming/substitution law needed to pass through nested
names-first theories.
-/

namespace DOTCaptureToManySortedFC.BinderOnly.TargetStaticInstantiation

open ManySortedFC

/-- A target static substitution is a left inverse of a renaming when it
restores every term and static-symbol variable in the renaming's source. -/
structure Cancels {source target : Sig} (rho : Rename source target)
    (substitution : StaticSubst target source) : Prop where
  termVar (index : BVar source .term) :
    substitution.termVar (rho.var index) = index
  symbolVar {sort : StaticSort} (index : BVar source (.symbol sort)) :
    substitution.symbolVar (rho.var index) = StaticExpr.symbol index

namespace Cancels

/-- Cancellation is stable below a term binder. -/
def liftTerm {source target : Sig} {rho : Rename source target}
    {substitution : StaticSubst target source}
    (cancellation : Cancels rho substitution) :
    Cancels (rho.lift (kind := .term)) substitution.liftTerm where
  termVar := fun index => by
    cases index with
    | here => rfl
    | there index =>
        simp only [Rename.lift, StaticSubst.liftTerm]
        rw [cancellation.termVar index]
  symbolVar := fun {sort} index => by
    cases index with
    | there index =>
        simp only [Rename.lift, StaticSubst.liftTerm]
        rw [cancellation.symbolVar index]
        cases sort <;> rfl

/-- Cancellation is stable below a static-symbol binder. -/
def liftSymbol {source target : Sig} {rho : Rename source target}
    {substitution : StaticSubst target source}
    (cancellation : Cancels rho substitution) (sort : StaticSort) :
    Cancels (rho.lift (kind := .symbol sort))
      (substitution.liftSymbol sort) where
  termVar := fun index => by
    cases index with
    | there index =>
        simp only [Rename.lift, StaticSubst.liftSymbol]
        rw [cancellation.termVar index]
  symbolVar := by
    intro other index
    cases index with
    | here => rfl
    | there index =>
        simp only [Rename.lift, StaticSubst.liftSymbol]
        rw [cancellation.symbolVar index]
        cases other <;> rfl

/-- Cancellation is stable below a proof-only evidence binder. -/
def liftEvidence {source target : Sig} {rho : Rename source target}
    {substitution : StaticSubst target source}
    (cancellation : Cancels rho substitution) (relation : Relation) :
    Cancels (rho.lift (kind := .evidence relation))
      (substitution.liftEvidence relation) where
  termVar := fun index => by
    cases index with
    | there index =>
        simp only [Rename.lift, StaticSubst.liftEvidence]
        rw [cancellation.termVar index]
  symbolVar := fun {sort} index => by
    cases index with
    | there index =>
        simp only [Rename.lift, StaticSubst.liftEvidence]
        rw [cancellation.symbolVar index]
        cases sort <;> rfl

/-- Cancellation is stable below a heterogeneous binder block. -/
def liftMany {source target : Sig} {rho : Rename source target}
    {substitution : StaticSubst target source}
    (cancellation : Cancels rho substitution) : (kinds : Sig) →
    Cancels (rho.liftMany kinds) (substitution.liftMany kinds)
  | [] => cancellation
  | kind :: rest =>
      match kind with
      | .term => (cancellation.liftMany rest).liftTerm
      | .symbol sort => (cancellation.liftMany rest).liftSymbol sort
      | .evidence relation =>
          (cancellation.liftMany rest).liftEvidence relation

/-- Cancellation is stable below a names-first symbol block. -/
def liftSymbols {source target : Sig} {rho : Rename source target}
    {substitution : StaticSubst target source}
    (cancellation : Cancels rho substitution)
    (symbols : List StaticSort) :
    Cancels (rho.liftSymbols symbols)
      (substitution.liftSymbols symbols) :=
  cancellation.liftMany (symbolKinds symbols)

/-- Cancellation is stable below a complete static theory scope. -/
def liftStatic {source target : Sig} {rho : Rename source target}
    {substitution : StaticSubst target source}
    (cancellation : Cancels rho substitution)
    (symbols : List StaticSort) (relations : List Relation) :
    Cancels (rho.liftStatic symbols relations)
      (substitution.liftStatic symbols relations) :=
  (cancellation.liftSymbols symbols).liftMany (evidenceKinds relations)

end Cancels

mutual

/-- Substitution after a cancelled renaming is the identity on captures. -/
def capture_rename_substitute {source target : Sig}
    (capture : Capture source) {rho : Rename source target}
    {substitution : StaticSubst target source}
    (cancellation : Cancels rho substitution) :
    (capture.rename rho).substitute substitution = capture :=
  match capture with
  | .empty => rfl
  | .union left right => by
      simp only [Capture.rename, Capture.substitute,
        capture_rename_substitute left cancellation,
        capture_rename_substitute right cancellation]
  | .readOnly capture => by
      simp only [Capture.rename, Capture.substitute,
        capture_rename_substitute capture cancellation]
  | .singleton capability => by
      simp only [Capture.rename, Capture.substitute]
      rw [cancellation.termVar capability]
  | .cvar name => by
      simp only [Capture.rename, Capture.substitute]
      rw [cancellation.symbolVar name]
      rfl

/-- Cancellation acts pointwise on the captures that generate modal
separation assumptions. -/
def separationContext_rename_substitute {count : Nat} {source target : Sig}
    (context : SeparationContext count source) {rho : Rename source target}
    {substitution : StaticSubst target source}
    (cancellation : Cancels rho substitution) :
    (context.rename rho).substitute substitution = context :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [SeparationContext.rename, SeparationContext.substitute,
        separationContext_rename_substitute rest cancellation,
        capture_rename_substitute capture cancellation]

/-- Cancellation acts pointwise on modal capture-mode requirements. -/
def modeContext_rename_substitute {modes : List CaptureMode}
    {source target : Sig} (context : ModeContext modes source)
    {rho : Rename source target} {substitution : StaticSubst target source}
    (cancellation : Cancels rho substitution) :
    (context.rename rho).substitute substitution = context :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [ModeContext.rename, ModeContext.substitute,
        modeContext_rename_substitute rest cancellation,
        capture_rename_substitute capture cancellation]

/-- Cancellation preserves both components of a structured modal context. -/
def modalContext_rename_substitute {separationCount : Nat}
    {modes : List CaptureMode} {source target : Sig}
    (context : ModalContext separationCount modes source)
    {rho : Rename source target} {substitution : StaticSubst target source}
    (cancellation : Cancels rho substitution) :
    (context.rename rho).substitute substitution = context :=
  match context with
  | .mk separation mode => by
      simp only [ModalContext.rename, ModalContext.substitute,
        separationContext_rename_substitute separation cancellation,
        modeContext_rename_substitute mode cancellation]

/-- Substitution after a cancelled renaming is the identity on types. -/
def ty_rename_substitute {source target : Sig} (type : Ty source)
    {rho : Rename source target}
    {substitution : StaticSubst target source}
    (cancellation : Cancels rho substitution) :
    (type.rename rho).substitute substitution = type :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar name => by
      simp only [Ty.rename, Ty.substitute]
      rw [cancellation.symbolVar name]
      rfl
  | .capturing captures shape => by
      simp only [Ty.rename, Ty.substitute,
        capture_rename_substitute captures cancellation,
        ty_rename_substitute shape cancellation]
  | .arr domain codomain => by
      simp only [Ty.rename, Ty.substitute,
        ty_rename_substitute domain cancellation,
        ty_rename_substitute codomain cancellation]
  | .modal requirements body => by
      simp only [Ty.rename, Ty.substitute,
        modalContext_rename_substitute requirements cancellation,
        ty_rename_substitute body cancellation]
  | @Ty.forallT _ symbols relations theory body => by
      simp only [Ty.rename, Ty.substitute,
        theory_rename_substitute theory cancellation,
        ty_rename_substitute body
          (cancellation.liftStatic symbols relations)]
  | @Ty.existsT _ symbols relations theory payload => by
      simp only [Ty.rename, Ty.substitute,
        theory_rename_substitute theory cancellation,
        ty_rename_substitute payload
          (cancellation.liftStatic symbols relations)]

/-- Substitution after a cancelled renaming is the identity on sorted static
expressions. -/
def expression_rename_substitute {source target : Sig}
    {sort : StaticSort} (expression : StaticExpr sort source)
    {rho : Rename source target}
    {substitution : StaticSubst target source}
    (cancellation : Cancels rho substitution) :
    (expression.rename rho).substitute substitution = expression :=
  match expression with
  | .type type => by
      simp only [StaticExpr.rename, StaticExpr.substitute,
        ty_rename_substitute type cancellation]
  | .capture capture => by
      simp only [StaticExpr.rename, StaticExpr.substitute,
        capture_rename_substitute capture cancellation]

/-- Substitution after a cancelled renaming is the identity on propositions. -/
def proposition_rename_substitute {source target : Sig}
    {relation : Relation} (proposition : Proposition relation source)
    {rho : Rename source target}
    {substitution : StaticSubst target source}
    (cancellation : Cancels rho substitution) :
    (proposition.rename rho).substitute substitution = proposition :=
  match proposition with
  | .equality left right => by
      simp only [Proposition.rename, Proposition.substitute,
        expression_rename_substitute left cancellation,
        expression_rename_substitute right cancellation]
  | .inclusion lower upper => by
      simp only [Proposition.rename, Proposition.substitute,
        expression_rename_substitute lower cancellation,
        expression_rename_substitute upper cancellation]
  | .separate left right => by
      simp only [Proposition.rename, Proposition.substitute,
        capture_rename_substitute left cancellation,
        capture_rename_substitute right cancellation]
  | .disjoint left right => by
      simp only [Proposition.rename, Proposition.substitute,
        capture_rename_substitute left cancellation,
        capture_rename_substitute right cancellation]
  | .mode capture => by
      simp only [Proposition.rename, Proposition.substitute,
        capture_rename_substitute capture cancellation]

/-- Substitution after a cancelled renaming is the identity on theories. -/
def theory_rename_substitute {source target : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory source symbols relations)
    {rho : Rename source target}
    {substitution : StaticSubst target source}
    (cancellation : Cancels rho substitution) :
    (theory.rename rho).substitute substitution = theory :=
  match theory with
  | .nil => rfl
  | .cons proposition rest => by
      simp only [Theory.rename, Theory.substitute,
        proposition_rename_substitute proposition
          (cancellation.liftSymbols symbols),
        theory_rename_substitute rest cancellation]

end

/-- Instantiating a freshly weakened expression with any witness recovers the
original expression. -/
@[simp]
theorem instantiate_weakened {scope : Sig} {boundSort sort : StaticSort}
    (expression : StaticExpr sort scope)
    (witness : StaticExpr boundSort scope) :
    expression.weaken.substitute
      (StaticSubst.ofSymbolArgs Rename.id
        (.cons witness (.nil : SymbolArgs scope []))) = expression := by
  apply expression_rename_substitute expression
  constructor
  · intro index
    rfl
  · intro other index
    rfl

end DOTCaptureToManySortedFC.BinderOnly.TargetStaticInstantiation
