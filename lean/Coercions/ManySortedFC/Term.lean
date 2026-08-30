import Coercions.ManySortedFC.Adapter
import Coercions.ManySortedFC.TheoryModel

/-!
# Annotated terms for many-sorted FC

The term language makes every static boundary explicit.  Static abstractions
bind a complete local theory, while applications and existential packages
supply simultaneous symbol witnesses and logical evidence in the ambient
scope.  Existential opening exposes the theory's complete static scope and
then one ordinary payload binder.

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

`lam` records an ambient, nondependent codomain.  `let'` and `open` likewise
record their ambient result type, so their bodies can later be checked against
the corresponding weakened annotation without synthesizing an escaping type.
All witnesses used to eliminate a static abstraction or construct a package
remain in the ambient scope; assumptions exported by the theory are therefore
unavailable while those witnesses and certificates are formed. -/
inductive Tm : Sig → Type where
  | var {scope : Sig} (index : BVar scope .term) : Tm scope
  | unit {scope : Sig} : Tm scope
  | lam {scope : Sig} (domain codomain : Ty scope)
      (body : Tm (scope ▹ .term)) : Tm scope
  | app {scope : Sig} (function argument : Tm scope) : Tm scope
  | let' {scope : Sig} (result : Ty scope) (rhs : Tm scope)
      (body : Tm (scope ▹ .term)) : Tm scope
  | adapt {scope : Sig} (term : Tm scope)
      (adapter : Adapter scope) : Tm scope
  | slam {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      (theory : Theory scope symbols relations)
      (body : Tm (StaticScope scope symbols relations)) : Tm scope
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
      (symbolArguments : SymbolArgs scope symbols)
      (evidenceArguments : EvidenceArgs scope relations)
      (payload : Tm scope) : Tm scope
  | «open» {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      (theory : Theory scope symbols relations)
      (payloadType : Ty (StaticScope scope symbols relations))
      (result : Ty scope) (package : Tm scope)
      (body : Tm (PayloadScope scope symbols relations)) : Tm scope
deriving DecidableEq

namespace Tm

/-- Discoverable name for constrained static abstraction. -/
def staticLam {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (body : Tm (StaticScope scope symbols relations)) : Tm scope :=
  .slam theory body

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
  | .lam domain codomain body =>
      .lam (domain.rename rho) (codomain.rename rho)
        (body.rename (rho.lift (kind := .term)))
  | .app function argument =>
      .app (function.rename rho) (argument.rename rho)
  | .let' result rhs body =>
      .let' (result.rename rho) (rhs.rename rho)
        (body.rename (rho.lift (kind := .term)))
  | .adapt inner adapter =>
      .adapt (inner.rename rho) (adapter.rename rho)
  | @Tm.slam _ symbols relations theory body =>
      .slam (theory.rename rho)
        (body.rename (rho.liftStatic symbols relations))
  | @Tm.sapp _ _ _ theory function symbolArguments evidenceArguments =>
      .sapp (theory.rename rho) (function.rename rho)
        (symbolArguments.rename rho) (evidenceArguments.rename rho)
  | @Tm.pack _ symbols relations theory payloadType symbolArguments
      evidenceArguments payload =>
      .pack (theory.rename rho)
        (payloadType.rename (rho.liftStatic symbols relations))
        (symbolArguments.rename rho) (evidenceArguments.rename rho)
        (payload.rename rho)
  | @Tm.«open» _ symbols relations theory payloadType result package body =>
      .«open» (theory.rename rho)
        (payloadType.rename (rho.liftStatic symbols relations))
        (result.rename rho) (package.rename rho)
        (body.rename (rho.liftPayload symbols relations))

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
  | lam domain codomain body induction =>
      simp [rename, induction]
  | app function argument functionInduction argumentInduction =>
      simp [rename, functionInduction, argumentInduction]
  | let' result rhs body rhsInduction bodyInduction =>
      simp [rename, rhsInduction, bodyInduction]
  | adapt inner adapter induction =>
      simp [rename, induction]
  | slam theory body induction =>
      simp [rename, induction]
  | sapp theory function symbolArguments evidenceArguments induction =>
      simp [rename, induction]
  | pack theory payloadType symbolArguments evidenceArguments payload induction =>
      simp [rename, induction]
  | «open» theory payloadType result package body packageInduction
      bodyInduction =>
      simp [rename, packageInduction, bodyInduction]

@[simp]
theorem rename_comp {first second third : Sig} (term : Tm first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (term.rename rho₁).rename rho₂ = term.rename (rho₁.comp rho₂) := by
  induction term generalizing second third with
  | var => rfl
  | unit => rfl
  | lam domain codomain body induction =>
      simp [rename, induction, Ty.rename_comp, Rename.lift_comp]
  | app function argument functionInduction argumentInduction =>
      simp [rename, functionInduction, argumentInduction]
  | let' result rhs body rhsInduction bodyInduction =>
      simp [rename, rhsInduction, bodyInduction, Rename.lift_comp]
  | adapt inner adapter induction =>
      simp [rename, induction, Adapter.rename_comp]
  | slam theory body induction =>
      simp [rename, induction, Theory.rename_comp,
        Rename.liftStatic_comp]
  | sapp theory function symbolArguments evidenceArguments induction =>
      simp [rename, induction, Theory.rename_comp,
        SymbolArgs.rename_comp, EvidenceArgs.rename_comp]
  | pack theory payloadType symbolArguments evidenceArguments payload induction =>
      simp [rename, induction, Theory.rename_comp, Ty.rename_comp,
        SymbolArgs.rename_comp, EvidenceArgs.rename_comp,
        Rename.liftStatic_comp]
  | «open» theory payloadType result package body packageInduction
      bodyInduction =>
      simp [rename, packageInduction, bodyInduction, Theory.rename_comp,
        Ty.rename_comp, Rename.liftStatic_comp, Rename.liftPayload_comp]

/-! ## Call-by-value values before erasure -/

/-- Annotated terms whose erasure is already a runtime value.

Adapters and packages erase to, or administratively expose, their contained
value.  A static abstraction is a value only when its erased body already is
one: because the abstraction itself disappears, it cannot delay evaluation of
a non-value body. -/
inductive IsValue : {scope : Sig} → Tm scope → Prop where
  | unit {scope : Sig} : IsValue (.unit : Tm scope)
  | lam {scope : Sig} {domain codomain : Ty scope}
      {body : Tm (scope ▹ .term)} :
      IsValue (.lam domain codomain body)
  | adapt {scope : Sig} {term : Tm scope} {adapter : Adapter scope}
      (termValue : IsValue term) : IsValue (.adapt term adapter)
  | slam {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      {theory : Theory scope symbols relations}
      {body : Tm (StaticScope scope symbols relations)}
      (bodyValue : IsValue body) : IsValue (.slam theory body)
  | pack {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      {theory : Theory scope symbols relations}
      {payloadType : Ty (StaticScope scope symbols relations)}
      {symbolArguments : SymbolArgs scope symbols}
      {evidenceArguments : EvidenceArgs scope relations}
      {payload : Tm scope} (payloadValue : IsValue payload) :
      IsValue (.pack theory payloadType symbolArguments evidenceArguments
        payload)

end Tm

end ManySortedFC
