import Coercions.ManySortedFC.StaticInstantiation
import Coercions.ManySortedFC.Erasure

/-!
# Static-application and primitive modal dynamics

ManySortedFC currently gives execution through its independently defined
erased runtime.  This module isolates the annotated rules needed for a
computation-capable static application and primitive modal lock/unlock without
pretending to supply a full annotated dynamics.

`StaticAppStep computationStep` lifts exactly one step of an ambient
computation relation in the scrutinee position, or performs static beta once
the scrutinee is a value-form static abstraction.  Model components have no
evaluation positions.
-/

namespace ManySortedFC

namespace TermStaticSubst

/-- Compose a static substitution's term-variable component with an erasure
renaming. -/
def eraseRenaming {source target : Sig}
    (substitution : TermStaticSubst source target) {runtimeScope : Nat}
    (rho : Erasure.Renaming target runtimeScope) :
    Erasure.Renaming source runtimeScope :=
  fun index => rho (substitution.static.termVar index)

@[simp]
theorem eraseRenaming_liftTerm {source target : Sig}
    (substitution : TermStaticSubst source target) {runtimeScope : Nat}
    (rho : Erasure.Renaming target runtimeScope) :
    eraseRenaming substitution.liftTerm rho.liftTerm =
      (eraseRenaming substitution rho).liftTerm := by
  funext index
  cases index <;> rfl

@[simp]
theorem eraseRenaming_liftSymbol {source target : Sig}
    (substitution : TermStaticSubst source target) {runtimeScope : Nat}
    (rho : Erasure.Renaming target runtimeScope) (sort : StaticSort) :
    eraseRenaming (substitution.liftSymbol sort) (rho.liftSymbol sort) =
      (eraseRenaming substitution rho).liftSymbol sort := by
  funext index
  cases index
  rfl

@[simp]
theorem eraseRenaming_liftEvidence {source target : Sig}
    (substitution : TermStaticSubst source target) {runtimeScope : Nat}
    (rho : Erasure.Renaming target runtimeScope) (relation : Relation) :
    eraseRenaming (substitution.liftEvidence relation)
        (rho.liftEvidence relation) =
      (eraseRenaming substitution rho).liftEvidence relation := by
  funext index
  cases index
  rfl

@[simp]
theorem eraseRenaming_liftSymbols {source target : Sig}
    (substitution : TermStaticSubst source target) {runtimeScope : Nat}
    (rho : Erasure.Renaming target runtimeScope)
    (symbols : List StaticSort) :
    eraseRenaming (substitution.liftMany (symbolKinds symbols))
        (rho.liftSymbols symbols) =
      (eraseRenaming substitution rho).liftSymbols symbols := by
  induction symbols with
  | nil => rfl
  | cons sort rest induction =>
      change eraseRenaming
          ((substitution.liftMany (symbolKinds rest)).liftSymbol sort)
          ((rho.liftSymbols rest).liftSymbol sort) = _
      rw [eraseRenaming_liftSymbol, induction]
      rfl

@[simp]
theorem eraseRenaming_liftEvidenceBlock {source target : Sig}
    (substitution : TermStaticSubst source target) {runtimeScope : Nat}
    (rho : Erasure.Renaming target runtimeScope)
    (relations : List Relation) :
    eraseRenaming (substitution.liftMany (evidenceKinds relations))
        (rho.liftEvidenceBlock relations) =
      (eraseRenaming substitution rho).liftEvidenceBlock relations := by
  induction relations with
  | nil => rfl
  | cons relation rest induction =>
      change eraseRenaming
          ((substitution.liftMany (evidenceKinds rest)).liftEvidence relation)
          ((rho.liftEvidenceBlock rest).liftEvidence relation) = _
      rw [eraseRenaming_liftEvidence, induction]
      rfl

@[simp]
theorem eraseRenaming_liftStatic {source target : Sig}
    (substitution : TermStaticSubst source target) {runtimeScope : Nat}
    (rho : Erasure.Renaming target runtimeScope)
    (symbols : List StaticSort) (relations : List Relation) :
    eraseRenaming (substitution.liftStatic symbols relations)
        (rho.liftStatic symbols relations) =
      (eraseRenaming substitution rho).liftStatic symbols relations := by
  unfold TermStaticSubst.liftStatic Erasure.Renaming.liftStatic
  rw [eraseRenaming_liftEvidenceBlock, eraseRenaming_liftSymbols]

@[simp]
theorem eraseRenaming_liftModal {source target : Sig}
    (substitution : TermStaticSubst source target) {runtimeScope : Nat}
    (rho : Erasure.Renaming target runtimeScope)
    (separationCount : Nat) (modes : List CaptureMode) :
    eraseRenaming (substitution.liftModal separationCount modes)
        (rho.liftModal separationCount modes) =
      (eraseRenaming substitution rho).liftModal
        separationCount modes := by
  unfold TermStaticSubst.liftModal Erasure.Renaming.liftModal
  rw [eraseRenaming_liftEvidenceBlock]

@[simp]
theorem eraseRenaming_instantiateSymbol {source target : Sig}
    (substitution : TermStaticSubst source target) {runtimeScope : Nat}
    (rho : Erasure.Renaming target runtimeScope) {sort : StaticSort}
    (replacement : StaticExpr sort target) :
    eraseRenaming (substitution.instantiateSymbol replacement) rho =
      (eraseRenaming substitution rho).liftSymbol sort := by
  funext index
  cases index
  rfl

@[simp]
theorem eraseRenaming_instantiateEvidence {source target : Sig}
    (substitution : TermStaticSubst source target) {runtimeScope : Nat}
    (rho : Erasure.Renaming target runtimeScope) {relation : Relation}
    (replacement : Evidence relation target) :
    eraseRenaming (substitution.instantiateEvidence replacement) rho =
      (eraseRenaming substitution rho).liftEvidence relation := by
  funext index
  cases index
  rfl

@[simp]
theorem eraseRenaming_fromSymbolArgs {source target : Sig}
    (substitution : TermStaticSubst source target) {runtimeScope : Nat}
    (rho : Erasure.Renaming target runtimeScope)
    {symbols : List StaticSort} (arguments : SymbolArgs target symbols) :
    eraseRenaming (fromSymbolArgs substitution arguments) rho =
      (eraseRenaming substitution rho).liftSymbols symbols := by
  induction arguments with
  | nil => rfl
  | cons newest older induction =>
      change eraseRenaming
          ((fromSymbolArgs substitution older).instantiateSymbol newest) rho = _
      rw [eraseRenaming_instantiateSymbol, induction]
      rfl

@[simp]
theorem eraseRenaming_fromEvidenceArgs {source target : Sig}
    (substitution : TermStaticSubst source target) {runtimeScope : Nat}
    (rho : Erasure.Renaming target runtimeScope)
    {relations : List Relation} (arguments : EvidenceArgs target relations) :
    eraseRenaming (fromEvidenceArgs substitution arguments) rho =
      (eraseRenaming substitution rho).liftEvidenceBlock relations := by
  induction arguments with
  | nil => rfl
  | cons newest older induction =>
      change eraseRenaming
          ((fromEvidenceArgs substitution older).instantiateEvidence newest)
          rho = _
      rw [eraseRenaming_instantiateEvidence, induction]
      rfl

@[simp]
theorem eraseRenaming_fromStaticArgs {source target : Sig}
    (substitution : TermStaticSubst source target) {runtimeScope : Nat}
    (rho : Erasure.Renaming target runtimeScope)
    {symbols : List StaticSort} {relations : List Relation}
    (symbolArguments : SymbolArgs target symbols)
    (evidenceArguments : EvidenceArgs target relations) :
    eraseRenaming
        (fromStaticArgs substitution symbolArguments evidenceArguments) rho =
      (eraseRenaming substitution rho).liftStatic symbols relations := by
  unfold fromStaticArgs Erasure.Renaming.liftStatic
  rw [eraseRenaming_fromEvidenceArgs, eraseRenaming_fromSymbolArgs]

@[simp]
theorem eraseRenaming_id {scope : Sig} {runtimeScope : Nat}
    (rho : Erasure.Renaming scope runtimeScope) :
    eraseRenaming (id (scope := scope)) rho = rho := by
  rfl

end TermStaticSubst

namespace Adapter

/-- Static substitution changes annotations and proof leaves, but not an
adapter's runtime program. -/
@[simp]
theorem erase_substituteStatic {source target : Sig}
    (adapter : Adapter source)
    (substitution : TermStaticSubst source target)
    {runtimeScope : Nat} (term : Runtime.Tm runtimeScope) :
    (adapter.substitute substitution).erase term = adapter.erase term := by
  induction adapter generalizing target runtimeScope with
  | identity => rfl
  | cast => rfl
  | retagCapture => rfl
  | captured captures shape induction =>
      simp [Adapter.substitute, Adapter.erase, induction]
  | compose first second firstInduction secondInduction =>
      simp [Adapter.substitute, Adapter.erase, firstInduction,
        secondInduction]
  | function domain codomain domainInduction codomainInduction =>
      simp [Adapter.substitute, Adapter.erase, domainInduction,
        codomainInduction]
  | modal sourceRequirements targetRequirements requirements result
      induction =>
      simp [Adapter.substitute, Adapter.erase, induction]
  | forallT theory body induction =>
      simp [Adapter.substitute, Adapter.erase, induction]
  | existsT theory payload induction =>
      simp [Adapter.substitute, Adapter.erase, induction]
  | forallMorphism sourceTheory targetTheory constraints body induction =>
      simp [Adapter.substitute, Adapter.erase, induction]
  | existsMorphism sourceTheory targetTheory constraints payload induction =>
      simp [Adapter.substitute, Adapter.erase, induction]

end Adapter

namespace Tm

/-- Erasure commutes with evidence-aware static substitution. -/
theorem eraseWith_substituteStatic {source target : Sig}
    (term : Tm source) (substitution : TermStaticSubst source target)
    {runtimeScope : Nat} (rho : Erasure.Renaming target runtimeScope) :
    (term.substituteStatic substitution).eraseWith rho =
      term.eraseWith (substitution.eraseRenaming rho) := by
  induction term generalizing target runtimeScope with
  | var => rfl
  | unit => rfl
  | lam domain codomain closure body captures induction =>
      simp [substituteStatic, eraseWith, induction]
  | app function argument functionInduction argumentInduction =>
      simp [substituteStatic, eraseWith, functionInduction,
        argumentInduction]
  | let' result bodyOuterUse rhs body discharge rhsInduction bodyInduction =>
      simp [substituteStatic, eraseWith, rhsInduction, bodyInduction]
  | adapt inner adapter induction =>
      simp [substituteStatic, eraseWith, induction]
  | lock requirements result closure body captures induction =>
      simp [substituteStatic, eraseWith, induction]
  | unlock requirements inner evidenceArguments induction =>
      simp [substituteStatic, eraseWith, induction]
  | slam theory closure body captures induction =>
      simp [substituteStatic, eraseWith, induction]
  | sapp theory function symbolArguments evidenceArguments induction =>
      simp [substituteStatic, eraseWith, induction]
  | pack theory payloadType closure symbolArguments evidenceArguments payload
      captures induction =>
      simp [substituteStatic, eraseWith, induction]
  | «open» theory payloadType result bodyOuterUse package body discharge
      packageInduction bodyInduction =>
      simp [substituteStatic, eraseWith, packageInduction, bodyInduction,
        Erasure.Renaming.liftPayload]
  | use inner inclusion induction =>
      simp [substituteStatic, eraseWith, induction]

/-- Static instantiation does not change runtime code. -/
@[simp]
theorem erase_instantiateStatic {scope : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (body : Tm (StaticScope scope symbols relations))
    (symbolArguments : SymbolArgs scope symbols)
    (evidenceArguments : EvidenceArgs scope relations) :
    (body.instantiateStatic symbolArguments evidenceArguments).erase =
      body.eraseWith
        ((Erasure.Renaming.identity scope).liftStatic symbols relations) := by
  unfold instantiateStatic erase
  rw [eraseWith_substituteStatic]
  simp

/-- Replacing a lock's proof variables by external evidence does not change
the suspended runtime program. -/
@[simp]
theorem erase_instantiateModal {scope : Sig}
    {separationCount : Nat} {modes : List CaptureMode}
    (body : Tm (ModalScope scope separationCount modes))
    (evidenceArguments : EvidenceArgs scope
      (modalRelations separationCount modes)) :
    (body.instantiateModal evidenceArguments).erase =
      body.eraseWith
        ((Erasure.Renaming.identity scope).liftModal
          separationCount modes) := by
  unfold instantiateModal erase
  rw [eraseWith_substituteStatic]
  simp [Erasure.Renaming.liftModal]

/-! ## The narrow static-application relation -/

/-- One annotated static-application step, parameterized by the computation
relation used for its scrutinee. -/
inductive StaticAppStep
    (computationStep : {scope : Sig} -> Tm scope -> Tm scope -> Prop) :
    {scope : Sig} -> Tm scope -> Tm scope -> Prop where
  | function {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      {theory : Theory scope symbols relations}
      {function function' : Tm scope}
      {symbolArguments : SymbolArgs scope symbols}
      {evidenceArguments : EvidenceArgs scope relations}
      (functionNotValue : ¬ IsValue function)
      (step : computationStep function function') :
      StaticAppStep computationStep
        (.sapp theory function symbolArguments evidenceArguments)
        (.sapp theory function' symbolArguments evidenceArguments)
  | beta {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      {theory : Theory scope symbols relations}
      {closure : Capture scope}
      {body : Tm (StaticScope scope symbols relations)}
      {captures : Evidence (.inclusion .capture)
        (StaticScope scope symbols relations)}
      {symbolArguments : SymbolArgs scope symbols}
      {evidenceArguments : EvidenceArgs scope relations}
      (bodyValue : IsValue body) :
      StaticAppStep computationStep
        (.sapp theory (.slam theory closure body captures)
          symbolArguments evidenceArguments)
        (body.instantiateStatic symbolArguments evidenceArguments)

/-- Erased behavior of the narrow static-application relation. -/
inductive ErasedStaticAppStep {scope : Nat} :
    Runtime.Tm scope -> Runtime.Tm scope -> Prop where
  | runtime {first second : Runtime.Tm scope}
      (step : Runtime.Step first second) : ErasedStaticAppStep first second
  | stutter {term : Runtime.Tm scope} : ErasedStaticAppStep term term

/-- Lifting a scrutinee step evaluates that scrutinee exactly once and leaves
the supplied model untouched. -/
theorem StaticAppStep.erase_function
    {computationStep : {scope : Sig} -> Tm scope -> Tm scope -> Prop}
    (simulation : ∀ {scope : Sig} {first second : Tm scope},
      computationStep first second -> Runtime.Step first.erase second.erase)
    {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    {theory : Theory scope symbols relations}
    {function function' : Tm scope}
    {symbolArguments : SymbolArgs scope symbols}
    {evidenceArguments : EvidenceArgs scope relations}
    (_functionNotValue : ¬ IsValue function)
    (step : computationStep function function') :
    Runtime.Step
      (Tm.sapp theory function symbolArguments evidenceArguments).erase
      (Tm.sapp theory function' symbolArguments evidenceArguments).erase := by
  simpa using simulation step

/-- Static beta is operationally silent after erasure. -/
theorem StaticAppStep.erase_beta
    {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    {theory : Theory scope symbols relations}
    {closure : Capture scope}
    {body : Tm (StaticScope scope symbols relations)}
    {captures : Evidence (.inclusion .capture)
      (StaticScope scope symbols relations)}
    {symbolArguments : SymbolArgs scope symbols}
    {evidenceArguments : EvidenceArgs scope relations}
    (_bodyValue : IsValue body) :
    (Tm.sapp theory (.slam theory closure body captures)
      symbolArguments evidenceArguments).erase =
      (body.instantiateStatic symbolArguments evidenceArguments).erase := by
  simp

/-- Every narrow static-application step either follows one runtime step of
the scrutinee or stutters for static beta. -/
theorem StaticAppStep.erase_behavior
    {computationStep : {scope : Sig} -> Tm scope -> Tm scope -> Prop}
    (simulation : ∀ {scope : Sig} {first second : Tm scope},
      computationStep first second -> Runtime.Step first.erase second.erase)
    {scope : Sig} {first second : Tm scope}
    (step : StaticAppStep computationStep first second) :
    ErasedStaticAppStep first.erase second.erase := by
  cases step with
  | function functionNotValue inner =>
      exact .runtime
        (StaticAppStep.erase_function simulation functionNotValue inner)
  | beta bodyValue =>
      rw [StaticAppStep.erase_beta bodyValue]
      exact .stutter

/-! ## Primitive modal dynamics -/

/-- The primitive lock/unlock administrative relation.  This deliberately is
not a progress relation for every annotated term form: for example, adapted
modal values execute through erasure and lie outside this narrow relation.
Evidence is substituted only at modal beta, whose runtime image is a genuine
force step rather than an erased stutter. -/
inductive ModalStep
    (computationStep : {scope : Sig} → Tm scope → Tm scope → Prop) :
    {scope : Sig} → Tm scope → Tm scope → Prop where
  | scrutinee {scope : Sig} {separationCount : Nat}
      {modes : List CaptureMode}
      {requirements : ModalContext separationCount modes scope}
      {first second : Tm scope}
      {evidenceArguments : EvidenceArgs scope
        (modalRelations separationCount modes)}
      (firstNotValue : ¬ IsValue first)
      (step : computationStep first second) :
      ModalStep computationStep
        (.unlock requirements first evidenceArguments)
        (.unlock requirements second evidenceArguments)
  | beta {scope : Sig} {separationCount : Nat}
      {modes : List CaptureMode}
      {requirements : ModalContext separationCount modes scope}
      {result : Ty scope} {closure : Capture scope}
      {body : Tm (ModalScope scope separationCount modes)}
      {captures : Evidence (.inclusion .capture)
        (ModalScope scope separationCount modes)}
      {evidenceArguments : EvidenceArgs scope
        (modalRelations separationCount modes)} :
      ModalStep computationStep
        (.unlock requirements
          (.lock requirements result closure body captures)
          evidenceArguments)
        (.use (body.instantiateModal evidenceArguments)
          (captures.substitute
            (TermStaticSubst.fromEvidenceArgs TermStaticSubst.id
              evidenceArguments)))

/-- A modal scrutinee step becomes exactly one runtime force-operand step. -/
theorem ModalStep.erase_scrutinee
    {computationStep : {scope : Sig} → Tm scope → Tm scope → Prop}
    (simulation : ∀ {scope : Sig} {first second : Tm scope},
      computationStep first second → Runtime.Step first.erase second.erase)
    {scope : Sig} {separationCount : Nat}
    {modes : List CaptureMode}
    {requirements : ModalContext separationCount modes scope}
    {first second : Tm scope}
    {evidenceArguments : EvidenceArgs scope
      (modalRelations separationCount modes)}
    (_firstNotValue : ¬ IsValue first)
    (step : computationStep first second) :
    Runtime.Step
      (Tm.unlock requirements first evidenceArguments).erase
      (Tm.unlock requirements second evidenceArguments).erase := by
  exact .forceSuspension (simulation step)

/-- Annotated modal beta erases to primitive runtime force beta. -/
theorem ModalStep.erase_beta
    {scope : Sig} {separationCount : Nat}
    {modes : List CaptureMode}
    {requirements : ModalContext separationCount modes scope}
    {result : Ty scope} {closure : Capture scope}
    {body : Tm (ModalScope scope separationCount modes)}
    {captures : Evidence (.inclusion .capture)
      (ModalScope scope separationCount modes)}
    {evidenceArguments : EvidenceArgs scope
      (modalRelations separationCount modes)} :
    Runtime.Step
      (Tm.unlock requirements
        (.lock requirements result closure body captures)
        evidenceArguments).erase
      (Tm.use (body.instantiateModal evidenceArguments)
        (captures.substitute
          (TermStaticSubst.fromEvidenceArgs TermStaticSubst.id
            evidenceArguments))).erase := by
  simpa using
    (Runtime.Step.forceBeta : Runtime.Step
      (.force (.suspend (body.eraseWith
        ((Erasure.Renaming.identity scope).liftModal
          separationCount modes))))
      (body.eraseWith
        ((Erasure.Renaming.identity scope).liftModal
          separationCount modes)))

/-- Every annotated modal step is one genuine runtime step. -/
theorem ModalStep.erase
    {computationStep : {scope : Sig} → Tm scope → Tm scope → Prop}
    (simulation : ∀ {scope : Sig} {first second : Tm scope},
      computationStep first second → Runtime.Step first.erase second.erase)
    {scope : Sig} {first second : Tm scope}
    (step : ModalStep computationStep first second) :
    Runtime.Step first.erase second.erase := by
  cases step with
  | scrutinee firstNotValue inner =>
      exact ModalStep.erase_scrutinee simulation firstNotValue inner
  | beta => exact ModalStep.erase_beta

end Tm

end ManySortedFC
