import Coercions.ManySortedFC.Term
import Coercions.ManySortedFC.TermProjection

/-!
# Erasure for many-sorted FC

Erasure retains only ordinary variables and the call-by-value term spine.
Types, static symbol witnesses, logical evidence, and constrained static
binders have no runtime representation.  Existential packages erase to their
payload; opening a package remains an ordinary runtime `let` because the
payload binder is computational.

Structural adapters have an explicit runtime interpretation. Logical casts
and identities are transparent, while a function adapter performs genuine
eta-expansion and binds the original call before adapting its result. The
results below state exact syntax equations only; they do not assert an
unproved beta-eta equivalence.
-/

namespace ManySortedFC

/-! ## Renamings used during erasure -/

namespace Erasure

/-- A map from the ordinary variables in a heterogeneous target scope into an
arbitrary runtime scope.  Static binders are handled structurally, avoiding
casts between propositionally equal term counts. -/
abbrev Renaming (source : Sig) (target : Nat) : Type :=
  BVar source .term → Fin target

namespace Renaming

/-- The canonical projection of a target scope to its runtime term scope. -/
def identity (scope : Sig) : Renaming scope scope.termCount :=
  BVar.toTermIndex

/-- Precompose erasure with a heterogeneous target renaming. -/
def precomp {source middle : Sig} {target : Nat}
    (rho : Rename source middle) (sigma : Renaming middle target) :
    Renaming source target :=
  fun index => sigma (rho.var index)

/-- Postcompose erasure with an ordinary runtime renaming. -/
def postcomp {source : Sig} {middle target : Nat}
    (rho : Renaming source middle)
    (sigma : Runtime.Renaming middle target) : Renaming source target :=
  fun index => sigma (rho index)

/-- Preserve a new ordinary binder in both source and runtime scopes. -/
def liftTerm {source : Sig} {target : Nat}
    (rho : Renaming source target) :
    Renaming (source ▹ .term) (Nat.succ target) :=
  fun
  | .here => 0
  | .there index => (rho index).succ

/-- Forget one static symbol binder. -/
def liftSymbol {source : Sig} {target : Nat}
    (rho : Renaming source target) (sort : StaticSort) :
    Renaming (source ▹ .symbol sort) target :=
  fun
  | .there index => rho index

/-- Forget one logical evidence binder. -/
def liftEvidence {source : Sig} {target : Nat}
    (rho : Renaming source target) (relation : Relation) :
    Renaming (source ▹ .evidence relation) target :=
  fun
  | .there index => rho index

/-- Forget a heterogeneous block of static symbols. -/
def liftSymbols {source : Sig} {target : Nat}
    (rho : Renaming source target) : (symbols : List StaticSort) →
    Renaming (SymbolScope source symbols) target
  | [] => rho
  | sort :: rest => (rho.liftSymbols rest).liftSymbol sort

/-- Forget a heterogeneous block of logical assumptions. -/
def liftEvidenceBlock {source : Sig} {target : Nat}
    (rho : Renaming source target) : (relations : List Relation) →
    Renaming (Sig.extendMany source (evidenceKinds relations)) target
  | [] => rho
  | relation :: rest =>
      (rho.liftEvidenceBlock rest).liftEvidence relation

/-- Forget a complete names-first static scope. -/
def liftStatic {source : Sig} {target : Nat}
    (rho : Renaming source target) (symbols : List StaticSort)
    (relations : List Relation) :
    Renaming (StaticScope source symbols relations) target :=
  (rho.liftSymbols symbols).liftEvidenceBlock relations

/-- Forget the proof binders introduced by a primitive modal lock. -/
def liftModal {source : Sig} {target : Nat}
    (rho : Renaming source target) (separationCount : Nat)
    (modes : List CaptureMode) :
    Renaming (ModalScope source separationCount modes) target :=
  rho.liftEvidenceBlock (modalRelations separationCount modes)

/-- Forget a complete static scope while retaining its newest payload term
binder. -/
def liftPayload {source : Sig} {target : Nat}
    (rho : Renaming source target) (symbols : List StaticSort)
    (relations : List Relation) :
    Renaming (PayloadScope source symbols relations) (Nat.succ target) :=
  (rho.liftStatic symbols relations).liftTerm

@[simp]
theorem liftTerm_identity (scope : Sig) :
    (identity scope).liftTerm = identity (scope ▹ .term) := by
  funext index
  cases index <;> rfl

@[simp]
theorem precomp_liftTerm {source middle : Sig} {target : Nat}
    (rho : Rename source middle) (sigma : Renaming middle target) :
    precomp rho.lift sigma.liftTerm = (precomp rho sigma).liftTerm := by
  funext index
  cases index <;> rfl

@[simp]
theorem precomp_liftSymbol {source middle : Sig} {target : Nat}
    (rho : Rename source middle) (sigma : Renaming middle target)
    (sort : StaticSort) :
    precomp (rho.lift (kind := .symbol sort)) (sigma.liftSymbol sort) =
      (precomp rho sigma).liftSymbol sort := by
  funext index
  cases index <;> rfl

@[simp]
theorem precomp_liftEvidence {source middle : Sig} {target : Nat}
    (rho : Rename source middle) (sigma : Renaming middle target)
    (relation : Relation) :
    precomp (rho.lift (kind := .evidence relation))
        (sigma.liftEvidence relation) =
      (precomp rho sigma).liftEvidence relation := by
  funext index
  cases index <;> rfl

@[simp]
theorem precomp_liftSymbols {source middle : Sig} {target : Nat}
    (rho : Rename source middle) (sigma : Renaming middle target)
    (symbols : List StaticSort) :
    precomp (rho.liftSymbols symbols) (sigma.liftSymbols symbols) =
      (precomp rho sigma).liftSymbols symbols := by
  induction symbols with
  | nil => rfl
  | cons sort rest induction =>
      change precomp ((rho.liftSymbols rest).lift
          (kind := .symbol sort))
          ((sigma.liftSymbols rest).liftSymbol sort) =
        ((precomp rho sigma).liftSymbols rest).liftSymbol sort
      rw [precomp_liftSymbol, induction]

@[simp]
theorem precomp_liftEvidenceBlock {source middle : Sig} {target : Nat}
    (rho : Rename source middle) (sigma : Renaming middle target)
    (relations : List Relation) :
    precomp (rho.liftEvidence relations)
        (sigma.liftEvidenceBlock relations) =
      (precomp rho sigma).liftEvidenceBlock relations := by
  induction relations with
  | nil => rfl
  | cons relation rest induction =>
      change precomp ((rho.liftEvidence rest).lift
          (kind := .evidence relation))
          ((sigma.liftEvidenceBlock rest).liftEvidence relation) =
        ((precomp rho sigma).liftEvidenceBlock rest).liftEvidence relation
      rw [precomp_liftEvidence, induction]

@[simp]
theorem precomp_liftStatic {source middle : Sig} {target : Nat}
    (rho : Rename source middle) (sigma : Renaming middle target)
    (symbols : List StaticSort) (relations : List Relation) :
    precomp (rho.liftStatic symbols relations)
        (sigma.liftStatic symbols relations) =
      (precomp rho sigma).liftStatic symbols relations := by
  unfold Rename.liftStatic liftStatic
  rw [precomp_liftEvidenceBlock, precomp_liftSymbols]

@[simp]
theorem precomp_liftModal {source middle : Sig} {target : Nat}
    (rho : Rename source middle) (sigma : Renaming middle target)
    (separationCount : Nat) (modes : List CaptureMode) :
    precomp (rho.liftModal separationCount modes)
        (sigma.liftModal separationCount modes) =
      (precomp rho sigma).liftModal separationCount modes := by
  unfold Rename.liftModal liftModal
  rw [precomp_liftEvidenceBlock]

@[simp]
theorem precomp_liftPayload {source middle : Sig} {target : Nat}
    (rho : Rename source middle) (sigma : Renaming middle target)
    (symbols : List StaticSort) (relations : List Relation) :
    precomp (rho.liftPayload symbols relations)
        (sigma.liftPayload symbols relations) =
      (precomp rho sigma).liftPayload symbols relations := by
  unfold Rename.liftPayload liftPayload
  rw [precomp_liftTerm, precomp_liftStatic]

@[simp]
theorem postcomp_liftTerm {source : Sig} {middle target : Nat}
    (rho : Renaming source middle)
    (sigma : Runtime.Renaming middle target) :
    postcomp rho.liftTerm sigma.lift = (postcomp rho sigma).liftTerm := by
  funext index
  cases index <;> rfl

@[simp]
theorem postcomp_liftSymbol {source : Sig} {middle target : Nat}
    (rho : Renaming source middle)
    (sigma : Runtime.Renaming middle target) (sort : StaticSort) :
    postcomp (rho.liftSymbol sort) sigma =
      (postcomp rho sigma).liftSymbol sort := by
  funext index
  cases index <;> rfl

@[simp]
theorem postcomp_liftEvidence {source : Sig} {middle target : Nat}
    (rho : Renaming source middle)
    (sigma : Runtime.Renaming middle target) (relation : Relation) :
    postcomp (rho.liftEvidence relation) sigma =
      (postcomp rho sigma).liftEvidence relation := by
  funext index
  cases index <;> rfl

@[simp]
theorem postcomp_liftSymbols {source : Sig} {middle target : Nat}
    (rho : Renaming source middle)
    (sigma : Runtime.Renaming middle target) (symbols : List StaticSort) :
    postcomp (rho.liftSymbols symbols) sigma =
      (postcomp rho sigma).liftSymbols symbols := by
  induction symbols with
  | nil => rfl
  | cons sort rest induction =>
      change postcomp ((rho.liftSymbols rest).liftSymbol sort) sigma =
        ((postcomp rho sigma).liftSymbols rest).liftSymbol sort
      rw [postcomp_liftSymbol, induction]

@[simp]
theorem postcomp_liftEvidenceBlock {source : Sig} {middle target : Nat}
    (rho : Renaming source middle)
    (sigma : Runtime.Renaming middle target) (relations : List Relation) :
    postcomp (rho.liftEvidenceBlock relations) sigma =
      (postcomp rho sigma).liftEvidenceBlock relations := by
  induction relations with
  | nil => rfl
  | cons relation rest induction =>
      change postcomp
          ((rho.liftEvidenceBlock rest).liftEvidence relation) sigma =
        ((postcomp rho sigma).liftEvidenceBlock rest).liftEvidence relation
      rw [postcomp_liftEvidence, induction]

@[simp]
theorem postcomp_liftStatic {source : Sig} {middle target : Nat}
    (rho : Renaming source middle)
    (sigma : Runtime.Renaming middle target)
    (symbols : List StaticSort) (relations : List Relation) :
    postcomp (rho.liftStatic symbols relations) sigma =
      (postcomp rho sigma).liftStatic symbols relations := by
  unfold liftStatic
  rw [postcomp_liftEvidenceBlock, postcomp_liftSymbols]

@[simp]
theorem postcomp_liftModal {source : Sig} {middle target : Nat}
    (rho : Renaming source middle)
    (sigma : Runtime.Renaming middle target)
    (separationCount : Nat) (modes : List CaptureMode) :
    postcomp (rho.liftModal separationCount modes) sigma =
      (postcomp rho sigma).liftModal separationCount modes := by
  unfold liftModal
  rw [postcomp_liftEvidenceBlock]

@[simp]
theorem postcomp_liftPayload {source : Sig} {middle target : Nat}
    (rho : Renaming source middle)
    (sigma : Runtime.Renaming middle target)
    (symbols : List StaticSort) (relations : List Relation) :
    postcomp (rho.liftPayload symbols relations) sigma.lift =
      (postcomp rho sigma).liftPayload symbols relations := by
  unfold liftPayload
  rw [postcomp_liftTerm, postcomp_liftStatic]

/-- Projecting a target renaming before canonical erasure is the same as
canonically erasing first and applying its runtime projection. -/
theorem precomp_identity_eq_project {source target : Sig}
    (rho : Rename source target) :
    precomp rho (identity target) =
      postcomp (identity source) rho.projectTerms := by
  funext index
  simp [precomp, postcomp, identity, Rename.projectTerms]

end Renaming

end Erasure

/-! ## Runtime interpretation of structural adapters -/

namespace Runtime.Renaming

/-- Weakening commutes with lifting an ordinary runtime renaming. -/
theorem weaken_lift_comm {source target : Nat}
    (rho : Renaming source target) :
    comp weaken rho.lift = comp rho weaken := by
  funext index
  rfl

end Runtime.Renaming

namespace Adapter

/-- Apply an adapter to an erased term in any runtime scope.

The runtime scope is independent of the adapter's annotated scope because
types, captures, and evidence are all erased.  This generality lets quantified
adapters recurse directly through static binders. A function adapter uses an
administrative let so call-by-value evaluates the original application before
a nested codomain adapter can eta-wrap its result. -/
def erase {scope : Sig} (adapter : Adapter scope) {runtimeScope : Nat}
    (term : Runtime.Tm runtimeScope) : Runtime.Tm runtimeScope :=
  match adapter with
  | .identity _ => term
  | .cast _ => term
  | .retagCapture _ _ _ _ _ => term
  | .captured _ shape => shape.erase term
  | .compose first second => second.erase (first.erase term)
  | .function domain codomain =>
      .lam (.let'
        (.app term.weaken (domain.erase (.var 0)))
        (codomain.erase (.var 0)))
  | .modal _ _ _ result =>
      .suspend (.let' (.force term) (result.erase (.var 0)))
  | .forallT _ body => body.erase term
  | .existsT _ payload => payload.erase term
  | .forallMorphism _ _ _ body => body.erase term
  | .existsMorphism _ _ _ payload => payload.erase term

@[simp]
theorem erase_identity {scope : Sig} (type : Ty scope)
    {runtimeScope : Nat} (term : Runtime.Tm runtimeScope) :
    (Adapter.identity type).erase term = term := rfl

@[simp]
theorem erase_cast {scope : Sig}
    (evidence : Evidence (.inclusion .type) scope)
    {runtimeScope : Nat} (term : Runtime.Tm runtimeScope) :
    (Adapter.cast evidence).erase term = term := rfl

@[simp]
theorem erase_retagCapture {scope : Sig} (source : Ty scope)
    (targetCapture : Capture scope) (targetShape : Ty scope)
    (captures : Evidence (.inclusion .capture) scope)
    (shape : Evidence (.inclusion .type) scope)
    {runtimeScope : Nat} (term : Runtime.Tm runtimeScope) :
    (Adapter.retagCapture source targetCapture targetShape captures shape).erase
      term = term := rfl

@[simp]
theorem erase_captured {scope : Sig}
    (captures : Evidence (.inclusion .capture) scope)
    (shape : Adapter scope) {runtimeScope : Nat}
    (term : Runtime.Tm runtimeScope) :
    (Adapter.captured captures shape).erase term = shape.erase term := rfl

/-- Combining two captured adapters before or after structural composition has
the same runtime interpretation. -/
theorem erase_compose_captured {scope : Sig}
    (firstCapture secondCapture :
      Evidence (.inclusion .capture) scope)
    (firstShape secondShape : Adapter scope)
    {runtimeScope : Nat} (term : Runtime.Tm runtimeScope) :
    (Adapter.compose
      (.captured firstCapture firstShape)
      (.captured secondCapture secondShape)).erase term =
    (Adapter.captured
      (.inclusionTrans firstCapture secondCapture)
      (.compose firstShape secondShape)).erase term := rfl

@[simp]
theorem erase_captured_identity {scope : Sig}
    (captures : Evidence (.inclusion .capture) scope)
    (shape : Ty scope) {runtimeScope : Nat}
    (term : Runtime.Tm runtimeScope) :
    (Adapter.captured captures (.identity shape)).erase term = term := rfl

@[simp]
theorem erase_compose {scope : Sig} (first second : Adapter scope)
    {runtimeScope : Nat} (term : Runtime.Tm runtimeScope) :
    (Adapter.compose first second).erase term =
      second.erase (first.erase term) := rfl

@[simp]
theorem erase_function {scope : Sig} (domain codomain : Adapter scope)
    {runtimeScope : Nat} (term : Runtime.Tm runtimeScope) :
    (Adapter.function domain codomain).erase term =
      .lam (.let'
        (.app term.weaken (domain.erase (.var 0)))
        (codomain.erase (.var 0))) := rfl

@[simp]
theorem erase_modal {scope : Sig}
    {sourceSeparationCount targetSeparationCount : Nat}
    {sourceModes targetModes : List CaptureMode}
    (sourceRequirements : ModalContext sourceSeparationCount sourceModes scope)
    (targetRequirements : ModalContext targetSeparationCount targetModes scope)
    (requirements : ModalTheoryMap scope targetSeparationCount targetModes
      sourceSeparationCount sourceModes)
    (result : Adapter
      (ModalScope scope targetSeparationCount targetModes))
    {runtimeScope : Nat} (term : Runtime.Tm runtimeScope) :
    (Adapter.modal sourceRequirements targetRequirements requirements
      result).erase term =
      .suspend (.let' (.force term) (result.erase (.var 0))) := rfl

@[simp]
theorem erase_forall {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (body : Adapter (StaticScope scope symbols relations))
    {runtimeScope : Nat} (term : Runtime.Tm runtimeScope) :
    (Adapter.forallT theory body).erase term = body.erase term := rfl

@[simp]
theorem erase_exists {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (payload : Adapter (StaticScope scope symbols relations))
    {runtimeScope : Nat} (term : Runtime.Tm runtimeScope) :
    (Adapter.existsT theory payload).erase term = payload.erase term := rfl

@[simp]
theorem erase_forallMorphism {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    (sourceTheory targetTheory : Theory scope symbols relations)
    (constraints : TheoryMorphism targetTheory sourceTheory)
    (body : Adapter (StaticScope scope symbols relations))
    {runtimeScope : Nat} (term : Runtime.Tm runtimeScope) :
    (Adapter.forallMorphism sourceTheory targetTheory constraints body).erase
      term = body.erase term := rfl

@[simp]
theorem erase_existsMorphism {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    (sourceTheory targetTheory : Theory scope symbols relations)
    (constraints : TheoryMorphism sourceTheory targetTheory)
    (payload : Adapter (StaticScope scope symbols relations))
    {runtimeScope : Nat} (term : Runtime.Tm runtimeScope) :
    (Adapter.existsMorphism sourceTheory targetTheory constraints payload).erase
      term = payload.erase term := rfl

/-- Renaming annotations or logical evidence cannot affect an adapter's
runtime interpretation. -/
@[simp]
theorem erase_rename {source target : Sig} (adapter : Adapter source)
    (rho : Rename source target) {runtimeScope : Nat}
    (term : Runtime.Tm runtimeScope) :
    (adapter.rename rho).erase term = adapter.erase term := by
  induction adapter generalizing target runtimeScope with
  | identity => rfl
  | cast => rfl
  | retagCapture => rfl
  | captured captures shape induction =>
      simp [Adapter.rename, erase, induction]
  | compose first second firstInduction secondInduction =>
      simp [Adapter.rename, erase, firstInduction, secondInduction]
  | function domain codomain domainInduction codomainInduction =>
      simp [Adapter.rename, erase, domainInduction, codomainInduction]
  | modal sourceRequirements targetRequirements requirements result
      induction =>
      simp [Adapter.rename, erase, induction]
  | forallT theory body induction =>
      simp [Adapter.rename, erase, induction]
  | existsT theory payload induction =>
      simp [Adapter.rename, erase, induction]
  | forallMorphism sourceTheory targetTheory constraints body induction =>
      simp [Adapter.rename, erase, induction]
  | existsMorphism sourceTheory targetTheory constraints payload induction =>
      simp [Adapter.rename, erase, induction]

/-- Adapter interpretation is natural in the surrounding runtime scope. -/
theorem erase_runtimeRename {scope : Sig} (adapter : Adapter scope)
    {source target : Nat} (term : Runtime.Tm source)
    (rho : Runtime.Renaming source target) :
    (adapter.erase term).rename rho = adapter.erase (term.rename rho) := by
  induction adapter generalizing source target with
  | identity => rfl
  | cast => rfl
  | retagCapture => rfl
  | captured captures shape induction =>
      simpa only [erase] using induction term rho
  | compose first second firstInduction secondInduction =>
      simp only [erase, secondInduction, firstInduction]
  | function domain codomain domainInduction codomainInduction =>
      simp only [erase, Runtime.Tm.rename, codomainInduction,
        domainInduction]
      congr 3
      unfold Runtime.Tm.weaken
      rw [Runtime.Tm.rename_comp, Runtime.Tm.rename_comp,
        Runtime.Renaming.weaken_lift_comm]
  | modal sourceRequirements targetRequirements requirements result
      induction =>
      simp only [erase, Runtime.Tm.rename]
      rw [induction (.var 0) rho.lift]
      rfl
  | forallT theory body induction =>
      simpa only [erase] using induction term rho
  | existsT theory payload induction =>
      simpa only [erase] using induction term rho
  | forallMorphism sourceTheory targetTheory constraints body induction =>
      simpa only [erase] using induction term rho
  | existsMorphism sourceTheory targetTheory constraints payload induction =>
      simpa only [erase] using induction term rho

/-- Every adapter sends an erased runtime value to a runtime value. -/
theorem erase_value {scope : Sig} (adapter : Adapter scope)
    {runtimeScope : Nat} {term : Runtime.Tm runtimeScope}
    (termValue : Runtime.IsValue term) :
    Runtime.IsValue (adapter.erase term) := by
  induction adapter generalizing runtimeScope with
  | identity => exact termValue
  | cast => exact termValue
  | retagCapture => exact termValue
  | captured captures shape induction => exact induction termValue
  | compose first second firstInduction secondInduction =>
      exact secondInduction (firstInduction termValue)
  | function => exact .lam
  | modal => exact .suspend
  | forallT theory body induction => exact induction termValue
  | existsT theory payload induction => exact induction termValue
  | forallMorphism sourceTheory targetTheory constraints body induction =>
      exact induction termValue
  | existsMorphism sourceTheory targetTheory constraints payload induction =>
      exact induction termValue

end Adapter

/-! ## Term erasure -/

namespace Tm

/-- Erase a term relative to an arbitrary map for its free ordinary
variables.  The helper extends that map structurally at term binders and
forgets every static binder. -/
def eraseWith {scope : Sig} (term : Tm scope) {runtimeScope : Nat}
    (rho : Erasure.Renaming scope runtimeScope) :
    Runtime.Tm runtimeScope :=
  match term with
  | .var index => .var (rho index)
  | .unit => .unit
  | .lam _ _ _ body _ => .lam (body.eraseWith rho.liftTerm)
  | .app function argument =>
      .app (function.eraseWith rho) (argument.eraseWith rho)
  | .let' _ _ rhs body _ =>
      .let' (rhs.eraseWith rho) (body.eraseWith rho.liftTerm)
  | .adapt inner adapter => adapter.erase (inner.eraseWith rho)
  | @Tm.lock _ separationCount modes _ _ _ body _ =>
      .suspend (body.eraseWith
        (rho.liftModal separationCount modes))
  | .unlock _ inner _ => .force (inner.eraseWith rho)
  | @Tm.slam _ symbols relations _ _ body _ =>
      body.eraseWith (rho.liftStatic symbols relations)
  | .sapp _ function _ _ => function.eraseWith rho
  | .pack _ _ _ _ _ payload _ => payload.eraseWith rho
  | @Tm.«open» _ symbols relations _ _ _ _ package body _ =>
      .let' (package.eraseWith rho)
        (body.eraseWith (rho.liftPayload symbols relations))
  | .use inner _ => inner.eraseWith rho

/-- Canonical erasure into the runtime scope containing exactly the ordinary
binders of the annotated term. -/
def erase {scope : Sig} (term : Tm scope) : Runtime.Tm scope.termCount :=
  term.eraseWith (Erasure.Renaming.identity scope)

/-! ### Constructor equations -/

@[simp]
theorem erase_var {scope : Sig} (index : BVar scope .term) :
    (Tm.var index).erase = .var index.toTermIndex := rfl

@[simp]
theorem erase_unit {scope : Sig} :
    (Tm.unit : Tm scope).erase = Runtime.Tm.unit := rfl

@[simp]
theorem erase_lam {scope : Sig} (domain codomain : Ty scope)
    (closure : Capture scope) (body : Tm (scope ▹ .term))
    (captures : Evidence (.inclusion .capture) (scope ▹ .term)) :
    (Tm.lam domain codomain closure body captures).erase = .lam body.erase := by
  simp [erase, eraseWith]

@[simp]
theorem erase_app {scope : Sig} (function argument : Tm scope) :
    (Tm.app function argument).erase =
      .app function.erase argument.erase := rfl

@[simp]
theorem erase_let {scope : Sig} (result : Ty scope)
    (bodyOuterUse : Capture scope) (rhs : Tm scope)
    (body : Tm (scope ▹ .term))
    (discharge : Evidence (.inclusion .capture) (scope ▹ .term)) :
    (Tm.let' result bodyOuterUse rhs body discharge).erase =
      .let' rhs.erase body.erase := by
  simp [erase, eraseWith]

@[simp]
theorem erase_adapt {scope : Sig} (term : Tm scope)
    (adapter : Adapter scope) :
    (Tm.adapt term adapter).erase = adapter.erase term.erase := rfl

@[simp]
theorem erase_lock {scope : Sig} {separationCount : Nat}
    {modes : List CaptureMode}
    (requirements : ModalContext separationCount modes scope)
    (result : Ty scope) (closure : Capture scope)
    (body : Tm (ModalScope scope separationCount modes))
    (captures : Evidence (.inclusion .capture)
      (ModalScope scope separationCount modes)) :
    (Tm.lock requirements result closure body captures).erase =
      .suspend (body.eraseWith
        ((Erasure.Renaming.identity scope).liftModal
          separationCount modes)) := rfl

@[simp]
theorem erase_unlock {scope : Sig} {separationCount : Nat}
    {modes : List CaptureMode}
    (requirements : ModalContext separationCount modes scope)
    (inner : Tm scope)
    (evidenceArguments : EvidenceArgs scope
      (modalRelations separationCount modes)) :
    (Tm.unlock requirements inner evidenceArguments).erase =
      .force inner.erase := rfl

@[simp]
theorem erase_slam {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (closure : Capture scope)
    (body : Tm (StaticScope scope symbols relations))
    (captures : Evidence (.inclusion .capture)
      (StaticScope scope symbols relations)) :
    (Tm.slam theory closure body captures).erase =
      body.eraseWith
        ((Erasure.Renaming.identity scope).liftStatic symbols relations) :=
  rfl

@[simp]
theorem erase_sapp {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (function : Tm scope) (symbolArguments : SymbolArgs scope symbols)
    (evidenceArguments : EvidenceArgs scope relations) :
    (Tm.sapp theory function symbolArguments evidenceArguments).erase =
      function.erase := rfl

@[simp]
theorem erase_pack {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (payloadType : Ty (StaticScope scope symbols relations))
    (closure : Capture scope)
    (symbolArguments : SymbolArgs scope symbols)
    (evidenceArguments : EvidenceArgs scope relations)
    (payload : Tm scope)
    (captures : Evidence (.inclusion .capture) scope) :
    (Tm.pack theory payloadType closure symbolArguments evidenceArguments
      payload captures).erase = payload.erase := rfl

@[simp]
theorem erase_open {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (payloadType : Ty (StaticScope scope symbols relations))
    (result : Ty scope) (bodyOuterUse : Capture scope)
    (package : Tm scope)
    (body : Tm (PayloadScope scope symbols relations))
    (discharge : Evidence (.inclusion .capture)
      (PayloadScope scope symbols relations)) :
    (Tm.open theory payloadType result bodyOuterUse package body discharge).erase =
      .let' package.erase
        (body.eraseWith
          ((Erasure.Renaming.identity scope).liftPayload
            symbols relations)) := rfl

@[simp]
theorem erase_use {scope : Sig} (term : Tm scope)
    (inclusion : Evidence (.inclusion .capture) scope) :
    (Tm.use term inclusion).erase = term.erase := rfl

/-! ### Compatibility -/

/-- Erasing after a target renaming is equivalent to precomposing the free
variable map with that renaming. -/
theorem eraseWith_rename {source target : Sig} (term : Tm source)
    (sigma : Rename source target) {runtimeScope : Nat}
    (rho : Erasure.Renaming target runtimeScope) :
    (term.rename sigma).eraseWith rho =
      term.eraseWith (Erasure.Renaming.precomp sigma rho) := by
  induction term generalizing target runtimeScope with
  | var => rfl
  | unit => rfl
  | lam domain codomain closure body captures induction =>
      simp [rename, eraseWith, induction]
  | app function argument functionInduction argumentInduction =>
      simp [rename, eraseWith, functionInduction, argumentInduction]
  | let' result bodyOuterUse rhs body discharge rhsInduction bodyInduction =>
      simp [rename, eraseWith, rhsInduction, bodyInduction]
  | adapt inner adapter induction =>
      simp [rename, eraseWith, induction]
  | lock requirements result closure body captures induction =>
      simp [rename, eraseWith, induction]
  | unlock requirements inner evidenceArguments induction =>
      simp [rename, eraseWith, induction]
  | slam theory closure body captures induction =>
      simp [rename, eraseWith, induction]
  | sapp theory function symbolArguments evidenceArguments induction =>
      simp [rename, eraseWith, induction]
  | pack theory payloadType closure symbolArguments evidenceArguments payload
      captures induction =>
      simp [rename, eraseWith, induction]
  | «open» theory payloadType result bodyOuterUse package body discharge
      packageInduction bodyInduction =>
      simp [rename, eraseWith, packageInduction, bodyInduction]
  | use inner inclusion induction =>
      simp [rename, eraseWith, induction]

/-- Erasure is natural in an additional runtime renaming. -/
theorem eraseWith_runtimeRename {scope : Sig} (term : Tm scope)
    {source target : Nat} (rho : Erasure.Renaming scope source)
    (sigma : Runtime.Renaming source target) :
    (term.eraseWith rho).rename sigma =
      term.eraseWith (Erasure.Renaming.postcomp rho sigma) := by
  induction term generalizing source target with
  | var => rfl
  | unit => rfl
  | lam domain codomain closure body captures induction =>
      simp [eraseWith, Runtime.Tm.rename, induction]
  | app function argument functionInduction argumentInduction =>
      simp [eraseWith, Runtime.Tm.rename, functionInduction,
        argumentInduction]
  | let' result bodyOuterUse rhs body discharge rhsInduction bodyInduction =>
      simp [eraseWith, Runtime.Tm.rename, rhsInduction, bodyInduction]
  | adapt inner adapter induction =>
      simp [eraseWith, Adapter.erase_runtimeRename, induction]
  | lock requirements result closure body captures induction =>
      simp [eraseWith, Runtime.Tm.rename, induction]
  | unlock requirements inner evidenceArguments induction =>
      simp [eraseWith, Runtime.Tm.rename, induction]
  | slam theory closure body captures induction =>
      simp [eraseWith, induction]
  | sapp theory function symbolArguments evidenceArguments induction =>
      simp [eraseWith, induction]
  | pack theory payloadType closure symbolArguments evidenceArguments payload
      captures induction =>
      simp [eraseWith, induction]
  | «open» theory payloadType result bodyOuterUse package body discharge
      packageInduction bodyInduction =>
      simp [eraseWith, Runtime.Tm.rename, packageInduction, bodyInduction]
  | use inner inclusion induction =>
      simp [eraseWith, induction]

/-- Canonical erasure commutes with heterogeneous renaming after projecting
that renaming to the runtime term scope. -/
@[simp]
theorem erase_rename {source target : Sig} (term : Tm source)
    (rho : Rename source target) :
    (term.rename rho).erase = term.erase.rename rho.projectTerms := by
  rw [erase, eraseWith_rename]
  rw [Erasure.Renaming.precomp_identity_eq_project]
  symm
  exact eraseWith_runtimeRename term
    (Erasure.Renaming.identity source) rho.projectTerms

/-- The syntactic value restriction is sufficient under every free-variable
map for erasure to yield a runtime call-by-value value. -/
theorem IsValue.eraseWith {scope : Sig} {term : Tm scope}
    (termValue : IsValue term) {runtimeScope : Nat}
    (rho : Erasure.Renaming scope runtimeScope) :
    Runtime.IsValue (term.eraseWith rho) := by
  induction termValue with
  | var => exact .var
  | unit => exact .unit
  | lam => exact .lam
  | adapt innerValue induction =>
      exact Adapter.erase_value _ (induction rho)
  | lock => exact .suspend
  | slam bodyValue induction =>
      exact induction (rho.liftStatic _ _)
  | pack payloadValue induction =>
      exact induction rho

/-- Canonical erasure of an annotated value is a runtime value. -/
theorem IsValue.erase {scope : Sig} {term : Tm scope}
    (termValue : IsValue term) : Runtime.IsValue term.erase :=
  termValue.eraseWith (Erasure.Renaming.identity scope)

end Tm

end ManySortedFC
