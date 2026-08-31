import Coercions.ManySortedFC.Adapter
import Coercions.ManySortedFC.TheoryModel

/-!
# Annotated terms for many-sorted FC

The term language makes every static boundary explicit.  Static abstractions
bind a complete local theory, while static applications and existential
packages supply simultaneous symbol witnesses and logical evidence in the
ambient scope.  Ordinary application accepts computation operands, and
existential opening accepts a package computation before exposing the
theory's complete static scope and one ordinary payload binder.

Function codomains and elimination results are recorded in the ambient scope.
This reflects the nondependent `Ty.arr` constructor and gives later typing and
checking judgments a structural nonescape boundary.
-/

namespace ManySortedFC

/-- Scope of an existential-open body: all hidden static binders followed by
one newest ordinary binder for the package payload. -/
@[reducible]
def PayloadScope (scope : Sig) (symbols : List StaticSort)
    (relations : List Relation) : Sig :=
  StaticScope scope symbols relations ▹ .term

namespace Rename

/-- Lift an ambient renaming through a complete local theory and its payload
binder. -/
def liftPayload {source target : Sig} (rho : Rename source target)
    (symbols : List StaticSort) (relations : List Relation) :
    Rename (PayloadScope source symbols relations)
      (PayloadScope target symbols relations) :=
  (rho.liftStatic symbols relations).lift (kind := .term)

@[simp]
theorem liftPayload_id {scope : Sig} (symbols : List StaticSort)
    (relations : List Relation) :
    (id (scope := scope)).liftPayload symbols relations = id := by
  unfold liftPayload
  simp

theorem liftPayload_comp {first second third : Sig}
    (rho₁ : Rename first second) (rho₂ : Rename second third)
    (symbols : List StaticSort) (relations : List Relation) :
    (rho₁.comp rho₂).liftPayload symbols relations =
      (rho₁.liftPayload symbols relations).comp
        (rho₂.liftPayload symbols relations) := by
  unfold liftPayload
  rw [liftStatic_comp, lift_comp]

end Rename

/-! ## Explicit term syntax -/

/-- Explicitly annotated target terms.

`lam` records an ambient, nondependent codomain and a closure capture.  Its
logical certificate covers the body's predicted use by that closure.  `let'`
and `open` likewise record their ambient result type and the capture exported
by their body, together with a certificate discharging the locally scoped
prediction.  `slam` and `pack` retain an explicit closure because those
markers erase and therefore cannot hide capabilities retained by their value
body or payload.

`use` is the sole capture-subsumption node.  Keeping it distinct from `adapt`
prevents immediate-use widening from being confused with type transport.
All witnesses used to eliminate a static abstraction or construct a package
remain in the ambient scope; assumptions exported by the theory are therefore
unavailable while those witnesses and certificates are formed. -/
inductive Tm : Sig → Type where
  | var {scope : Sig} (index : BVar scope .term) : Tm scope
  | unit {scope : Sig} : Tm scope
  | lam {scope : Sig} (domain codomain : Ty scope)
      (closure : Capture scope) (body : Tm (scope ▹ .term))
      (captures : Evidence (.inclusion .capture) (scope ▹ .term)) :
      Tm scope
  | app {scope : Sig} (function argument : Tm scope) : Tm scope
  | let' {scope : Sig} (result : Ty scope) (bodyOuterUse : Capture scope)
      (rhs : Tm scope) (body : Tm (scope ▹ .term))
      (discharge : Evidence (.inclusion .capture) (scope ▹ .term)) :
      Tm scope
  | adapt {scope : Sig} (term : Tm scope)
      (adapter : Adapter scope) : Tm scope
  | slam {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      (theory : Theory scope symbols relations) (closure : Capture scope)
      (body : Tm (StaticScope scope symbols relations))
      (captures : Evidence (.inclusion .capture)
        (StaticScope scope symbols relations)) : Tm scope
  | sapp {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      (theory : Theory scope symbols relations)
      (function : Tm scope)
      (symbolArguments : SymbolArgs scope symbols)
      (evidenceArguments : EvidenceArgs scope relations) : Tm scope
  | pack {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      (theory : Theory scope symbols relations)
      (payloadType : Ty (StaticScope scope symbols relations))
      (closure : Capture scope)
      (symbolArguments : SymbolArgs scope symbols)
      (evidenceArguments : EvidenceArgs scope relations)
      (payload : Tm scope)
      (captures : Evidence (.inclusion .capture) scope) : Tm scope
  | «open» {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      (theory : Theory scope symbols relations)
      (payloadType : Ty (StaticScope scope symbols relations))
      (result : Ty scope) (bodyOuterUse : Capture scope)
      (package : Tm scope)
      (body : Tm (PayloadScope scope symbols relations))
      (discharge : Evidence (.inclusion .capture)
        (PayloadScope scope symbols relations)) : Tm scope
  | use {scope : Sig} (term : Tm scope)
      (inclusion : Evidence (.inclusion .capture) scope) : Tm scope
deriving DecidableEq

namespace Tm

/-- Discoverable name for constrained static abstraction. -/
def staticLam {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (closure : Capture scope)
    (body : Tm (StaticScope scope symbols relations))
    (captures : Evidence (.inclusion .capture)
      (StaticScope scope symbols relations)) : Tm scope :=
  .slam theory closure body captures

/-- Discoverable name for constrained static application. -/
def staticApp {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (function : Tm scope) (symbolArguments : SymbolArgs scope symbols)
    (evidenceArguments : EvidenceArgs scope relations) : Tm scope :=
  .sapp theory function symbolArguments evidenceArguments

/-! ## Structural renaming -/

/-- Rename every free variable and annotation, preserving every binder
introduced by the term. -/
def rename {source target : Sig} (term : Tm source)
    (rho : Rename source target) : Tm target :=
  match term with
  | .var index => .var (rho.var index)
  | .unit => .unit
  | .lam domain codomain closure body captures =>
      .lam (domain.rename rho) (codomain.rename rho)
        (closure.rename rho)
        (body.rename (rho.lift (kind := .term)))
        (captures.rename (rho.lift (kind := .term)))
  | .app function argument =>
      .app (function.rename rho) (argument.rename rho)
  | .let' result bodyOuterUse rhs body discharge =>
      .let' (result.rename rho) (bodyOuterUse.rename rho) (rhs.rename rho)
        (body.rename (rho.lift (kind := .term)))
        (discharge.rename (rho.lift (kind := .term)))
  | .adapt inner adapter =>
      .adapt (inner.rename rho) (adapter.rename rho)
  | @Tm.slam _ symbols relations theory closure body captures =>
      .slam (theory.rename rho) (closure.rename rho)
        (body.rename (rho.liftStatic symbols relations))
        (captures.rename (rho.liftStatic symbols relations))
  | @Tm.sapp _ _ _ theory function symbolArguments evidenceArguments =>
      .sapp (theory.rename rho) (function.rename rho)
        (symbolArguments.rename rho) (evidenceArguments.rename rho)
  | @Tm.pack _ symbols relations theory payloadType closure symbolArguments
      evidenceArguments payload captures =>
      .pack (theory.rename rho)
        (payloadType.rename (rho.liftStatic symbols relations))
        (closure.rename rho)
        (symbolArguments.rename rho) (evidenceArguments.rename rho)
        (payload.rename rho) (captures.rename rho)
  | @Tm.«open» _ symbols relations theory payloadType result bodyOuterUse
      package body discharge =>
      .«open» (theory.rename rho)
        (payloadType.rename (rho.liftStatic symbols relations))
        (result.rename rho) (bodyOuterUse.rename rho) (package.rename rho)
        (body.rename (rho.liftPayload symbols relations))
        (discharge.rename (rho.liftPayload symbols relations))
  | .use inner inclusion =>
      .use (inner.rename rho) (inclusion.rename rho)

/-- Weaken a term below one heterogeneous binder. -/
def weaken {scope : Sig} {kind : BinderKind} (term : Tm scope) :
    Tm (scope ▹ kind) :=
  term.rename Rename.succ

@[simp]
theorem rename_id {scope : Sig} (term : Tm scope) :
    term.rename Rename.id = term := by
  induction term with
  | var => rfl
  | unit => rfl
  | lam domain codomain closure body captures induction =>
      simp [rename, induction]
  | app function argument functionInduction argumentInduction =>
      simp [rename, functionInduction, argumentInduction]
  | let' result bodyOuterUse rhs body discharge rhsInduction bodyInduction =>
      simp [rename, rhsInduction, bodyInduction]
  | adapt inner adapter induction =>
      simp [rename, induction]
  | slam theory closure body captures induction =>
      simp [rename, induction]
  | sapp theory function symbolArguments evidenceArguments induction =>
      simp [rename, induction]
  | pack theory payloadType closure symbolArguments evidenceArguments payload
      captures induction =>
      simp [rename, induction]
  | «open» theory payloadType result bodyOuterUse package body discharge
      packageInduction bodyInduction =>
      simp [rename, packageInduction, bodyInduction]
  | use inner inclusion induction =>
      simp [rename, induction]

@[simp]
theorem rename_comp {first second third : Sig} (term : Tm first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (term.rename rho₁).rename rho₂ = term.rename (rho₁.comp rho₂) := by
  induction term generalizing second third with
  | var => rfl
  | unit => rfl
  | lam domain codomain closure body captures induction =>
      simp [rename, induction, Ty.rename_comp, Rename.lift_comp]
  | app function argument functionInduction argumentInduction =>
      simp [rename, functionInduction, argumentInduction]
  | let' result bodyOuterUse rhs body discharge rhsInduction bodyInduction =>
      simp [rename, rhsInduction, bodyInduction, Rename.lift_comp]
  | adapt inner adapter induction =>
      simp [rename, induction, Adapter.rename_comp]
  | slam theory closure body captures induction =>
      simp [rename, induction, Theory.rename_comp,
        Rename.liftStatic_comp]
  | sapp theory function symbolArguments evidenceArguments induction =>
      simp [rename, induction, Theory.rename_comp,
        SymbolArgs.rename_comp, EvidenceArgs.rename_comp]
  | pack theory payloadType closure symbolArguments evidenceArguments payload
      captures induction =>
      simp [rename, induction, Theory.rename_comp, Ty.rename_comp,
        SymbolArgs.rename_comp, EvidenceArgs.rename_comp,
        Rename.liftStatic_comp]
  | «open» theory payloadType result bodyOuterUse package body discharge
      packageInduction bodyInduction =>
      simp [rename, packageInduction, bodyInduction, Theory.rename_comp,
        Ty.rename_comp, Rename.liftStatic_comp, Rename.liftPayload_comp]
  | use inner inclusion induction =>
      simp [rename, induction, Evidence.rename_comp]

/-! ## Call-by-value values before erasure -/

/-- Annotated terms whose erasure is already a runtime value.

Adapters and packages erase to, or administratively expose, their contained
value.  A static abstraction is a value only when its erased body already is
one: because the abstraction itself disappears, it cannot delay evaluation of
a non-value body. -/
inductive IsValue : {scope : Sig} → Tm scope → Prop where
  | var {scope : Sig} {index : BVar scope .term} :
      IsValue (.var index)
  | unit {scope : Sig} : IsValue (.unit : Tm scope)
  | lam {scope : Sig} {domain codomain : Ty scope}
      {closure : Capture scope} {body : Tm (scope ▹ .term)}
      {captures : Evidence (.inclusion .capture) (scope ▹ .term)} :
      IsValue (.lam domain codomain closure body captures)
  | adapt {scope : Sig} {term : Tm scope} {adapter : Adapter scope}
      (termValue : IsValue term) : IsValue (.adapt term adapter)
  | slam {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      {theory : Theory scope symbols relations} {closure : Capture scope}
      {body : Tm (StaticScope scope symbols relations)}
      {captures : Evidence (.inclusion .capture)
        (StaticScope scope symbols relations)}
      (bodyValue : IsValue body) :
      IsValue (.slam theory closure body captures)
  | pack {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      {theory : Theory scope symbols relations}
      {payloadType : Ty (StaticScope scope symbols relations)}
      {closure : Capture scope}
      {symbolArguments : SymbolArgs scope symbols}
      {evidenceArguments : EvidenceArgs scope relations}
      {payload : Tm scope}
      {captures : Evidence (.inclusion .capture) scope}
      (payloadValue : IsValue payload) :
      IsValue (.pack theory payloadType closure symbolArguments
        evidenceArguments payload captures)

end Tm

end ManySortedFC
