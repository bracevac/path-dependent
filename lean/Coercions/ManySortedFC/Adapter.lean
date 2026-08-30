import Coercions.ManySortedFC.Context
import Coercions.ManySortedFC.Evidence
import Coercions.ManySortedFC.EvidenceChecker

/-!
# Structural adapters for many-sorted FC

Logical `Evidence` proves a static proposition.  An `Adapter`, by contrast,
describes the administrative term structure required to transport a value
between two types.  The only bridge is `Adapter.cast`, which embeds explicit
type-inclusion evidence as a logical cast.

Function adapters stand for eta-expansion with a contravariant domain adapter
and a covariant codomain adapter.  Universal adapters stand for static
abstraction/application, while existential adapters stand for opening and
repacking.  The quantified forms currently preserve one exact theory on both
sides.  Adapters between different theories require explicit theory
morphisms and are intentionally left for future work.
-/

namespace ManySortedFC

/-- Explicit structural transports between target types. -/
inductive Adapter : Sig → Type where
  /-- Administrative identity at an explicitly recorded type. -/
  | identity {scope : Sig} (type : Ty scope) : Adapter scope

  /-- The adapter induced by one logical type-inclusion certificate. -/
  | cast {scope : Sig}
      (evidence : Evidence (.inclusion .type) scope) : Adapter scope

  /-- Sequential administrative transport. -/
  | compose {scope : Sig} (first second : Adapter scope) : Adapter scope

  /-- Function eta-adaptation.  Typing checks the domain contravariantly and
  the codomain covariantly. -/
  | function {scope : Sig} (domain codomain : Adapter scope) : Adapter scope

  /-- Same-theory universal congruence.  Operationally this represents static
  abstraction/application around the adapted body. -/
  | forallT {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      (theory : Theory scope symbols relations)
      (body : Adapter (StaticScope scope symbols relations)) : Adapter scope

  /-- Same-theory existential congruence.  Operationally this represents
  opening the source package and repacking its adapted payload. -/
  | existsT {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      (theory : Theory scope symbols relations)
      (payload : Adapter (StaticScope scope symbols relations)) : Adapter scope

deriving DecidableEq

namespace Adapter

/-! ## Structural renaming -/

/-- Rename every annotation and logical leaf of an adapter. -/
def rename {source target : Sig} (adapter : Adapter source)
    (rho : Rename source target) : Adapter target :=
  match adapter with
  | .identity type => .identity (type.rename rho)
  | .cast evidence => .cast (evidence.rename rho)
  | .compose first second =>
      .compose (first.rename rho) (second.rename rho)
  | .function domain codomain =>
      .function (domain.rename rho) (codomain.rename rho)
  | @Adapter.forallT _ symbols relations theory body =>
      .forallT (theory.rename rho)
        (body.rename (rho.liftStatic symbols relations))
  | @Adapter.existsT _ symbols relations theory payload =>
      .existsT (theory.rename rho)
        (payload.rename (rho.liftStatic symbols relations))

/-- Weaken an adapter below one heterogeneous binder. -/
def weaken {scope : Sig} {kind : BinderKind} (adapter : Adapter scope) :
    Adapter (scope ▹ kind) :=
  adapter.rename Rename.succ

@[simp]
theorem rename_id {scope : Sig} (adapter : Adapter scope) :
    adapter.rename Rename.id = adapter := by
  induction adapter with
  | identity type => simp [rename]
  | cast evidence => simp [rename]
  | compose first second firstInduction secondInduction =>
      simp [rename, firstInduction, secondInduction]
  | function domain codomain domainInduction codomainInduction =>
      simp [rename, domainInduction, codomainInduction]
  | @forallT scope symbols relations theory body induction =>
      simp [rename, induction]
  | @existsT scope symbols relations theory payload induction =>
      simp [rename, induction]

@[simp]
theorem rename_comp {first second third : Sig} (adapter : Adapter first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (adapter.rename rho₁).rename rho₂ =
      adapter.rename (rho₁.comp rho₂) := by
  induction adapter generalizing second third with
  | identity type => simp [rename, Ty.rename_comp]
  | cast evidence => simp [rename, Evidence.rename_comp]
  | compose first second firstInduction secondInduction =>
      simp [rename, firstInduction, secondInduction]
  | function domain codomain domainInduction codomainInduction =>
      simp [rename, domainInduction, codomainInduction]
  | @forallT scope symbols relations theory body induction =>
      simp [rename, induction, Theory.rename_comp, Rename.liftStatic_comp]
  | @existsT scope symbols relations theory payload induction =>
      simp [rename, induction, Theory.rename_comp, Rename.liftStatic_comp]

/-! ## Declarative adapter typing -/

/-- An adapter transports values from its source type to its target type. -/
inductive HasType : {scope : Sig} → Ctx scope → Adapter scope →
    Ty scope → Ty scope → Type where
  | identity {scope : Sig} {context : Ctx scope} (type : Ty scope) :
      HasType context (.identity type) type type

  | cast {scope : Sig} {context : Ctx scope}
      {evidence : Evidence (.inclusion .type) scope}
      {source target : Ty scope}
      (typing : Evidence.Proves context evidence
        (.inclusion (.type source) (.type target))) :
      HasType context (.cast evidence) source target

  | compose {scope : Sig} {context : Ctx scope}
      {first second : Adapter scope} {source middle target : Ty scope}
      (firstTyping : HasType context first source middle)
      (secondTyping : HasType context second middle target) :
      HasType context (.compose first second) source target

  | function {scope : Sig} {context : Ctx scope}
      {domain codomain : Adapter scope}
      {sourceDomain targetDomain sourceCodomain targetCodomain : Ty scope}
      (domainTyping : HasType context domain targetDomain sourceDomain)
      (codomainTyping : HasType context codomain sourceCodomain targetCodomain) :
      HasType context (.function domain codomain)
        (.arr sourceDomain sourceCodomain)
        (.arr targetDomain targetCodomain)

  | forallT {scope : Sig} {context : Ctx scope}
      {symbols : List StaticSort} {relations : List Relation}
      {theory : Theory scope symbols relations}
      {body : Adapter (StaticScope scope symbols relations)}
      {sourceBody targetBody : Ty (StaticScope scope symbols relations)}
      (bodyTyping : HasType (context.extendTheory theory) body
        sourceBody targetBody) :
      HasType context (.forallT theory body)
        (.forallT theory sourceBody) (.forallT theory targetBody)

  | existsT {scope : Sig} {context : Ctx scope}
      {symbols : List StaticSort} {relations : List Relation}
      {theory : Theory scope symbols relations}
      {payload : Adapter (StaticScope scope symbols relations)}
      {sourcePayload targetPayload : Ty
        (StaticScope scope symbols relations)}
      (payloadTyping : HasType (context.extendTheory theory) payload
        sourcePayload targetPayload) :
      HasType context (.existsT theory payload)
        (.existsT theory sourcePayload) (.existsT theory targetPayload)

/-- The source and target synthesized for an adapter, together with the
declarative derivation justifying those endpoints. -/
structure Checked {scope : Sig} (context : Ctx scope)
    (adapter : Adapter scope) where
  source : Ty scope
  target : Ty scope
  typing : HasType context adapter source target

/-! ## Proof-producing structural checker -/

/-- Structurally synthesize an adapter's endpoints.

The checker follows the supplied adapter recursively.  Its only adapter-level
endpoint test is the exact equality at `compose`; it performs no subtyping,
subcapturing, constraint solving, or search for a different adapter. -/
def check {scope : Sig} (context : Ctx scope) (adapter : Adapter scope) :
    Option (Checked context adapter) :=
  match adapter with
  | .identity type =>
      some ⟨type, type, .identity type⟩
  | .cast evidence => do
      let checked ← Evidence.check context evidence
      let ⟨proposition, typing⟩ := checked
      match proposition with
      | .inclusion (.type source) (.type target) =>
          pure ⟨source, target, .cast typing⟩
  | .compose first second => do
      let firstChecked ← check context first
      let secondChecked ← check context second
      if middleMatches : firstChecked.target = secondChecked.source then
        let alignedSecondTyping : HasType context second
            firstChecked.target secondChecked.target := by
          simpa [middleMatches] using secondChecked.typing
        pure ⟨firstChecked.source, secondChecked.target,
          .compose firstChecked.typing alignedSecondTyping⟩
      else
        none
  | .function domain codomain => do
      let domainChecked ← check context domain
      let codomainChecked ← check context codomain
      pure ⟨.arr domainChecked.target codomainChecked.source,
        .arr domainChecked.source codomainChecked.target,
        .function domainChecked.typing codomainChecked.typing⟩
  | .forallT theory body => do
      let bodyChecked ← check (context.extendTheory theory) body
      pure ⟨.forallT theory bodyChecked.source,
        .forallT theory bodyChecked.target,
        .forallT bodyChecked.typing⟩
  | .existsT theory payload => do
      let payloadChecked ← check (context.extendTheory theory) payload
      pure ⟨.existsT theory payloadChecked.source,
        .existsT theory payloadChecked.target,
        .existsT payloadChecked.typing⟩

/-- The endpoint-only public view of the proof-producing checker. -/
def synth {scope : Sig} (context : Ctx scope) (adapter : Adapter scope) :
    Option (Ty scope × Ty scope) :=
  (check context adapter).map fun checked => (checked.source, checked.target)

/-- Every successful checker result contains its declarative typing proof. -/
theorem check_sound {scope : Sig} {context : Ctx scope}
    {adapter : Adapter scope} {checked : Checked context adapter}
    (_accepted : check context adapter = some checked) :
    Nonempty (HasType context adapter checked.source checked.target) :=
  ⟨checked.typing⟩

end Adapter

end ManySortedFC
