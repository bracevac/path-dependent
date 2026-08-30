import Coercions.DOT.Acyclic.Explicit.Context

/-!
# Structural target typing

Every judgment in this file is `Type`-valued.  Equality and inclusion
certificates synthesize both endpoints, exposures synthesize one reusable
`MemberSpec`, and context morphisms relate an actual target context to its
view.  Target term typing is syntax directed and deliberately has no
subsumption constructor.

Stage A deliberately retains `Source.Ty`.  Its target formation contract is
therefore intrinsic scope formation, formalized below, rather than
declarative DOT well-formedness.  In particular a scoped selection annotation
is an opaque atom: it does not authorize either selection-bound rule.  Those
rules remain available only through an explicitly bound `MemberSpec` handle.
Source elaboration records the stronger source-`Wf` provenance separately.
-/

namespace DotFC.Explicit

open DotFC

/-! ## Exact explicit-type formation contract -/

namespace Formation

/-- Intrinsic scope formation for retained explicit types.

The `selection` constructor checks only what the index `Source.Ty s` already
guarantees: its path is a term variable in `s`.  It intentionally carries no
member-exposure evidence and cannot justify `LeCo.lower` or `LeCo.upper`. -/
inductive TyScoped : {s : Sig} → Source.Ty s → Type where
  | top {s : Sig} : TyScoped (.top : Source.Ty s)
  | bot {s : Sig} : TyScoped (.bot : Source.Ty s)
  | all {s : Sig} {domain : Source.Ty s}
      {codomain : Source.Ty (s ▹ .term)}
      (domainScoped : TyScoped domain)
      (codomainScoped : TyScoped codomain) :
      TyScoped (.all domain codomain)
  | member {s : Sig} {label : Name} {lower upper : Source.Ty s}
      (lowerScoped : TyScoped lower) (upperScoped : TyScoped upper) :
      TyScoped (.member label lower upper)
  | selection {s : Sig} (path : BVar s .term) (label : Name) :
      TyScoped (.sel path label)

namespace TyScoped

/-- Every intrinsically indexed explicit type satisfies the scope-only
formation contract.  This is not a proof of `Source.Wf`. -/
def total {s : Sig} (type : Source.Ty s) : TyScoped type :=
  match type with
  | .top => .top
  | .bot => .bot
  | .all domain codomain => .all (total domain) (total codomain)
  | .member _ lower upper => .member (total lower) (total upper)
  | .sel path label => .selection path label

end TyScoped

/-- Scope formation for a reusable member fact.  The stable path is already
scoped by `MemberSpec s`; this judgment recursively records its bounds. -/
structure MemberScoped {s : Sig} (member : MemberSpec s) : Type where
  lower : TyScoped member.lower
  upper : TyScoped member.upper

namespace MemberScoped

def total {s : Sig} (member : MemberSpec s) : MemberScoped member where
  lower := TyScoped.total member.lower
  upper := TyScoped.total member.upper

end MemberScoped

/-- Scope formation for heterogeneous context payloads. -/
inductive BindingScoped : {s : Sig} → {kind : BinderKind} →
    Binding s kind → Type where
  | term {s : Sig} {type : Source.Ty s} (typeScoped : TyScoped type) :
      BindingScoped (.term type)
  | typeVar {s : Sig} : BindingScoped (.typeVar : Binding s .type)
  | equality {s : Sig} {left right : Source.Ty s}
      (leftScoped : TyScoped left) (rightScoped : TyScoped right) :
      BindingScoped (.equality left right)
  | inclusion {s : Sig} {source target : Source.Ty s}
      (sourceScoped : TyScoped source) (targetScoped : TyScoped target) :
      BindingScoped (.inclusion source target)
  | member {s : Sig} {specification : MemberSpec s}
      (memberScoped : MemberScoped specification) :
      BindingScoped (.member specification)

namespace BindingScoped

def total {s : Sig} {kind : BinderKind} (binding : Binding s kind) :
    BindingScoped binding :=
  match binding with
  | .term type => .term (TyScoped.total type)
  | .typeVar => .typeVar
  | .equality left right =>
      .equality (TyScoped.total left) (TyScoped.total right)
  | .inclusion source target =>
      .inclusion (TyScoped.total source) (TyScoped.total target)
  | .member specification => .member (MemberScoped.total specification)

end BindingScoped

/-- Scope formation for a complete heterogeneous target telescope. -/
inductive ContextScoped : {s : Sig} → Ctx s → Type where
  | nil : ContextScoped .nil
  | extend {s : Sig} {kind : BinderKind} {context : Ctx s}
      {binding : Binding s kind}
      (contextScoped : ContextScoped context)
      (bindingScoped : BindingScoped binding) :
      ContextScoped (.extend context binding)

namespace ContextScoped

def total {s : Sig} (context : Ctx s) : ContextScoped context :=
  match context with
  | .nil => .nil
  | .extend outer binding => .extend (total outer) (BindingScoped.total binding)

end ContextScoped

end Formation

/-! ## Removing proof-only binders and checking nonescape -/

namespace ScopedTy

/-- A map of stable term paths.  Source types contain no variables of the
other binder kinds, so this is the exact action needed when an erased
non-term binder is removed. -/
structure TermRename (s₁ s₂ : Sig) where
  var : BVar s₁ .term → BVar s₂ .term

namespace TermRename

/-- Forget the non-term components of a heterogeneous renaming. -/
def ofRename (rho : Rename s₁ s₂) : TermRename s₁ s₂ where
  var := rho.var

/-- Composition, in the same diagrammatic order as `Rename.comp`. -/
def comp (rho₁ : TermRename s₁ s₂) (rho₂ : TermRename s₂ s₃) :
    TermRename s₁ s₃ where
  var := fun path => rho₂.var (rho₁.var path)

@[ext]
theorem ext {rho₁ rho₂ : TermRename s₁ s₂}
    (pointwise : ∀ path, rho₁.var path = rho₂.var path) : rho₁ = rho₂ := by
  cases rho₁
  cases rho₂
  congr
  funext path
  exact pointwise path

/-- Lift a stable-path renaming below a dependent term binder. -/
def lift (rho : TermRename s₁ s₂) :
    TermRename (s₁ ▹ .term) (s₂ ▹ .term) where
  var := fun
    | .here => .here
    | .there path => .there (rho.var path)

/-- Remove a newest reusable-member binder. -/
def dropMember : TermRename (s ▹ .member) s where
  var := fun
    | .there path => path

/-- Remove a newest evidence binder. -/
def dropEvidence {relation : Relation} :
    TermRename (s ▹ .evidence relation) s where
  var := fun
    | .there path => path

@[simp]
theorem lift_comp (rho₁ : TermRename s₁ s₂) (rho₂ : TermRename s₂ s₃) :
    (rho₁.comp rho₂).lift = rho₁.lift.comp rho₂.lift := by
  ext path
  cases path <;> rfl

@[simp]
theorem ofRename_lift (rho : Rename s₁ s₂) :
    ofRename rho.lift = (ofRename rho).lift := by
  ext path
  cases path <;> rfl

end TermRename

/-- Apply a stable-path-only renaming to a source type. -/
def rename (type : Source.Ty s₁) (rho : TermRename s₁ s₂) : Source.Ty s₂ :=
  match type with
  | .top => .top
  | .bot => .bot
  | .all domain codomain => .all (rename domain rho) (rename codomain rho.lift)
  | .member label lower upper =>
      .member label (rename lower rho) (rename upper rho)
  | .sel path label => .sel (rho.var path) label

@[simp]
theorem rename_comp (type : Source.Ty s₁) (rho₁ : TermRename s₁ s₂)
    (rho₂ : TermRename s₂ s₃) :
    rename (rename type rho₁) rho₂ = rename type (rho₁.comp rho₂) := by
  induction type generalizing s₂ s₃ with
  | top => rfl
  | bot => rfl
  | all domain codomain domainInduction codomainInduction =>
      simp [rename, domainInduction, codomainInduction]
  | member label lower upper lowerInduction upperInduction =>
      simp [rename, lowerInduction, upperInduction]
  | sel path label => rfl

@[simp]
theorem rename_ofRename (type : Source.Ty s₁) (rho : Rename s₁ s₂) :
    rename type (TermRename.ofRename rho) = type.rename rho := by
  induction type generalizing s₂ with
  | top => rfl
  | bot => rfl
  | all domain codomain domainInduction codomainInduction =>
      simp only [rename, Source.Ty.rename, domainInduction]
      congr 1
      simpa only [TermRename.ofRename_lift] using codomainInduction rho.lift
  | member label lower upper lowerInduction upperInduction =>
      simp [rename, Source.Ty.rename, lowerInduction, upperInduction]
  | sel path label => rfl

/-- A partial stable-path map, used to enforce that the result of a `let`
does not mention its local term variable. -/
structure PartialTermRename (s₁ s₂ : Sig) where
  var : BVar s₁ .term → Option (BVar s₂ .term)

namespace PartialTermRename

/-- Lift a partial path map below a dependent term binder. -/
def lift (rho : PartialTermRename s₁ s₂) :
    PartialTermRename (s₁ ▹ .term) (s₂ ▹ .term) where
  var := fun
    | .here => some .here
    | .there path => Option.map BVar.there (rho.var path)

/-- Reject the newest term variable and remove one `.there` from every older
stable path. -/
def strengthenTerm : PartialTermRename (s ▹ .term) s where
  var := fun
    | .here => none
    | .there path => some path

end PartialTermRename

/-- Apply a partial stable-path map to a type. -/
def rename? (type : Source.Ty s₁) (rho : PartialTermRename s₁ s₂) :
    Option (Source.Ty s₂) :=
  match type with
  | .top => some .top
  | .bot => some .bot
  | .all domain codomain => do
      let domain' ← rename? domain rho
      let codomain' ← rename? codomain rho.lift
      pure (.all domain' codomain')
  | .member label lower upper => do
      let lower' ← rename? lower rho
      let upper' ← rename? upper rho
      pure (.member label lower' upper')
  | .sel path label => do
      let path' ← rho.var path
      pure (.sel path' label)

/-- Remove a proof-only member binder from a type. -/
def dropMember (type : Source.Ty (s ▹ .member)) : Source.Ty s :=
  rename type TermRename.dropMember

/-- Remove a proof-only evidence binder from a type. -/
def dropEvidence {relation : Relation}
    (type : Source.Ty (s ▹ .evidence relation)) : Source.Ty s :=
  rename type TermRename.dropEvidence

/-- Remove a term binder exactly when it does not occur in the type. -/
def strengthenTerm (type : Source.Ty (s ▹ .term)) : Option (Source.Ty s) :=
  rename? type PartialTermRename.strengthenTerm

/-- Remove the private equality binder introduced by `letExact`, then reject
escape of the exact object's term path. -/
def strengthenExact
    (type : Source.Ty ((s ▹ .term) ▹ .evidence .equality)) :
    Option (Source.Ty s) :=
  strengthenTerm (dropEvidence type)

/-- Removing a proof-only member binder commutes with renaming its outer
context.  This is the key endpoint equation for renaming `letHandle`
certificates. -/
theorem dropMember_rename {s₁ s₂ : Sig} (type : Source.Ty (s₁ ▹ .member))
    (rho : Rename s₁ s₂) :
    dropMember (type.rename rho.lift) = (dropMember type).rename rho := by
  calc
    dropMember (type.rename rho.lift) =
        rename type ((TermRename.ofRename rho.lift).comp TermRename.dropMember) := by
          unfold dropMember
          rw [← rename_ofRename type rho.lift]
          exact rename_comp type _ _
    _ = rename type (TermRename.dropMember.comp (TermRename.ofRename rho)) := by
          congr 1
          ext path
          cases path with
          | there path => rfl
    _ = (dropMember type).rename rho := by
          unfold dropMember
          rw [← rename_ofRename (rename type TermRename.dropMember) rho]
          exact (rename_comp type _ _).symm

end ScopedTy

/-! ## Lookup-preserving context renamings -/

namespace Binding

@[simp]
theorem termType_rename (binding : Binding s₁ .term) (rho : Rename s₁ s₂) :
    (binding.rename rho).termType = binding.termType.rename rho := by
  cases binding
  rfl

@[simp]
theorem equalityEndpoints_rename
    (binding : Binding s₁ (.evidence .equality)) (rho : Rename s₁ s₂) :
    (binding.rename rho).equalityEndpoints =
      (binding.equalityEndpoints.1.rename rho,
        binding.equalityEndpoints.2.rename rho) := by
  cases binding
  rfl

@[simp]
theorem inclusionEndpoints_rename
    (binding : Binding s₁ (.evidence .inclusion)) (rho : Rename s₁ s₂) :
    (binding.rename rho).inclusionEndpoints =
      (binding.inclusionEndpoints.1.rename rho,
        binding.inclusionEndpoints.2.rename rho) := by
  cases binding
  rfl

@[simp]
theorem memberSpec_rename (binding : Binding s₁ .member) (rho : Rename s₁ s₂) :
    (binding.rename rho).memberSpec = binding.memberSpec.rename rho := by
  cases binding
  rfl

end Binding

namespace Ctx

/-- `Renames source target rho` records precisely the lookup equation needed
to transport structural certificates.  It permits insertion embeddings as
well as shape-preserving renamings. -/
structure Renames {s₁ s₂ : Sig} (source : Ctx s₁) (target : Ctx s₂)
    (rho : Rename s₁ s₂) : Type where
  lookup : ∀ {kind : BinderKind} (index : BVar s₁ kind),
    target.lookup (rho.var index) = (source.lookup index).rename rho

namespace Renames

/-- Lift a lookup-preserving context renaming below a corresponding binding. -/
def extend {s₁ s₂ : Sig} {source : Ctx s₁} {target : Ctx s₂}
    {rho : Rename s₁ s₂} (renames : Renames source target rho)
    {kind : BinderKind} (binding : Binding s₁ kind) :
    Renames (.extend source binding) (.extend target (binding.rename rho)) rho.lift where
  lookup := fun index => by
    cases index with
    | here =>
        simp only [Rename.lift_here, Ctx.lookup_here]
        simp [Binding.weaken, Binding.rename_comp, Rename.succ_lift_comm]
    | there older =>
        simp only [Rename.lift_there, Ctx.lookup_there]
        rw [renames.lookup older]
        simp [Binding.weaken, Binding.rename_comp, Rename.succ_lift_comm]

/-- Inserting a fresh term binding weakens every older lookup. -/
def weakenTerm (context : Ctx s) (bound : Source.Ty s) :
    Renames context (context.extendTerm bound) Rename.succ where
  lookup := fun _index => rfl

end Renames

end Ctx

/-! ## Certificate endpoint judgments -/

namespace EqCo

/-- Structural endpoints of symmetric equality evidence. -/
inductive HasType : {s : Sig} → Ctx s → EqCo s →
    Source.Ty s → Source.Ty s → Type where
  | var {s : Sig} {context : Ctx s}
      (index : BVar s (.evidence .equality)) :
      HasType context (.var index)
        (context.lookup index).equalityEndpoints.1
        (context.lookup index).equalityEndpoints.2
  | refl {s : Sig} {context : Ctx s} (type : Source.Ty s) :
      HasType context (.refl type) type type
  | symm {s : Sig} {context : Ctx s} {evidence : EqCo s}
      {left right : Source.Ty s}
      (typing : HasType context evidence left right) :
      HasType context (.symm evidence) right left
  | trans {s : Sig} {context : Ctx s} {first second : EqCo s}
      {left middle right : Source.Ty s}
      (firstTyping : HasType context first left middle)
      (secondTyping : HasType context second middle right) :
      HasType context (.trans first second) left right

end EqCo

mutual

/-- Structural endpoints of directed inclusion evidence. -/
inductive LeCo.HasType : {s : Sig} → Ctx s → LeCo s →
    Source.Ty s → Source.Ty s → Type where
  | var {s : Sig} {context : Ctx s}
      (index : BVar s (.evidence .inclusion)) :
      LeCo.HasType context (.var index)
        (context.lookup index).inclusionEndpoints.1
        (context.lookup index).inclusionEndpoints.2
  | refl {s : Sig} {context : Ctx s} (type : Source.Ty s) :
      LeCo.HasType context (.refl type) type type
  | trans {s : Sig} {context : Ctx s} {first second : LeCo s}
      {source middle target : Source.Ty s}
      (firstTyping : LeCo.HasType context first source middle)
      (secondTyping : LeCo.HasType context second middle target) :
      LeCo.HasType context (.trans first second) source target
  | top {s : Sig} {context : Ctx s} (source : Source.Ty s) :
      LeCo.HasType context (.top source) source .top
  | bot {s : Sig} {context : Ctx s} (target : Source.Ty s) :
      LeCo.HasType context (.bot target) .bot target
  | eqToLe {s : Sig} {context : Ctx s} {evidence : EqCo s}
      {source target : Source.Ty s}
      (typing : EqCo.HasType context evidence source target) :
      LeCo.HasType context (.eqToLe evidence) source target
  | member {s : Sig} {context : Ctx s} {label : Name}
      {lower upper : LeCo s} {lower₁ upper₁ lower₂ upper₂ : Source.Ty s}
      (lowerTyping : LeCo.HasType context lower lower₂ lower₁)
      (upperTyping : LeCo.HasType context upper upper₁ upper₂) :
      LeCo.HasType context (.member label lower upper)
        (.member label lower₁ upper₁) (.member label lower₂ upper₂)
  | all {s : Sig} {context : Ctx s} {domain : LeCo s}
      {view : CtxMor (s ▹ .term)} {codomain : LeCo (s ▹ .term)}
      {domain₁ domain₂ : Source.Ty s}
      {codomain₁ codomain₂ : Source.Ty (s ▹ .term)}
      (domainTyping : LeCo.HasType context domain domain₂ domain₁)
      (viewTyping : CtxMor.HasType (context.extendTerm domain₂)
        (context.extendTerm domain₁) view)
      (codomainTyping : LeCo.HasType (context.extendTerm domain₂)
        codomain codomain₁ codomain₂) :
      LeCo.HasType context (.all domain view codomain)
        (.all domain₁ codomain₁) (.all domain₂ codomain₂)
  | lower {s : Sig} {context : Ctx s} {handle : BVar s .member}
      : LeCo.HasType context (.lower handle)
        (context.lookup handle).memberSpec.lower
        (.sel (context.lookup handle).memberSpec.path
          (context.lookup handle).memberSpec.label)
  | upper {s : Sig} {context : Ctx s} {handle : BVar s .member}
      : LeCo.HasType context (.upper handle)
        (.sel (context.lookup handle).memberSpec.path
          (context.lookup handle).memberSpec.label)
        (context.lookup handle).memberSpec.upper
  | letHandle {s : Sig} {context : Ctx s} {exposure : Exposure s}
      {body : LeCo (s ▹ .member)} {member : MemberSpec s}
      {source target : Source.Ty (s ▹ .member)}
      (exposureTyping : Exposure.HasType context exposure member)
      (bodyTyping : LeCo.HasType (context.extendMember member) body source target) :
      LeCo.HasType context (.letHandle exposure body)
        (ScopedTy.dropMember source) (ScopedTy.dropMember target)

/-- Structural synthesis of a reusable member fact. -/
inductive Exposure.HasType : {s : Sig} → Ctx s → Exposure s →
    MemberSpec s → Type where
  | view {s : Sig} {context : Ctx s} {path : BVar s .term} {label : Name}
      {lower upper : Source.Ty s} {inclusion : LeCo s}
      (inclusionTyping : LeCo.HasType context inclusion
        (context.lookup path).termType
        (.member label lower upper)) :
      Exposure.HasType context (.view path label lower upper inclusion)
        ⟨path, label, lower, upper⟩

/-- A context morphism relates complete actual and view telescopes. -/
inductive CtxMor.HasType : {s : Sig} → Ctx s → Ctx s →
    CtxMor s → Type where
  | refl {s : Sig} {context : Ctx s} :
      CtxMor.HasType context context .refl
  | function {s : Sig} {context : Ctx s} {domain : LeCo s}
      {actual view : Source.Ty s}
      (domainTyping : LeCo.HasType context domain actual view) :
      CtxMor.HasType (context.extendTerm actual) (context.extendTerm view)
        (.function domain)

end

/-! ## Renaming structural certificates -/

namespace EqCo.HasType

/-- Equality certificates are stable under any lookup-preserving context
renaming. -/
def rename {s₁ s₂ : Sig} {sourceContext : Ctx s₁}
    {targetContext : Ctx s₂} {rho : Rename s₁ s₂}
    {evidence : EqCo s₁} {source target : Source.Ty s₁}
    (typing : EqCo.HasType sourceContext evidence source target)
    (contexts : Ctx.Renames sourceContext targetContext rho) :
    EqCo.HasType targetContext (evidence.rename rho)
      (source.rename rho) (target.rename rho) :=
  match typing with
  | .var index => by
      simpa [contexts.lookup index] using
        (EqCo.HasType.var (context := targetContext) (rho.var index))
  | .refl type => .refl (type.rename rho)
  | .symm inner => .symm (rename inner contexts)
  | .trans first second => .trans (rename first contexts) (rename second contexts)

end EqCo.HasType

mutual

/-- Inclusion certificates are stable under any lookup-preserving context
renaming.  The recursive `all` case lifts the context relation under the
function binder; the recursive `letHandle` case lifts it under the reusable
member binder. -/
def renameLeTyping {s₁ s₂ : Sig} {sourceContext : Ctx s₁}
    {targetContext : Ctx s₂} {rho : Rename s₁ s₂}
    {evidence : LeCo s₁} {source target : Source.Ty s₁}
    (typing : LeCo.HasType sourceContext evidence source target)
    (contexts : Ctx.Renames sourceContext targetContext rho) :
    LeCo.HasType targetContext (evidence.rename rho)
      (source.rename rho) (target.rename rho) :=
  match typing with
  | .var index => by
      simpa [LeCo.rename, contexts.lookup index] using
        (LeCo.HasType.var (context := targetContext) (rho.var index))
  | .refl type => by
      simpa [LeCo.rename] using
        (LeCo.HasType.refl (context := targetContext) (type.rename rho))
  | .trans first second => by
      simpa [LeCo.rename] using
        LeCo.HasType.trans (renameLeTyping first contexts)
          (renameLeTyping second contexts)
  | .top source => by
      simpa [LeCo.rename] using
        (LeCo.HasType.top (context := targetContext) (source.rename rho))
  | .bot target => by
      simpa [LeCo.rename] using
        (LeCo.HasType.bot (context := targetContext) (target.rename rho))
  | .eqToLe equality => by
      simpa [LeCo.rename] using
        LeCo.HasType.eqToLe (EqCo.HasType.rename equality contexts)
  | .member (label := label) lower upper => by
      simpa [LeCo.rename] using
        (LeCo.HasType.member (label := label)
          (renameLeTyping lower contexts)
          (renameLeTyping upper contexts))
  | .all domain view codomain => by
      simpa [LeCo.rename] using
        LeCo.HasType.all (renameLeTyping domain contexts)
          (renameFunctionMorTyping view contexts)
          (renameLeTyping codomain
            (contexts.extend (.term _)))
  | .lower (handle := handle) => by
      simpa [LeCo.rename, contexts.lookup handle] using
        (LeCo.HasType.lower (context := targetContext)
          (handle := rho.var handle))
  | .upper (handle := handle) => by
      simpa [LeCo.rename, contexts.lookup handle] using
        (LeCo.HasType.upper (context := targetContext)
          (handle := rho.var handle))
  | .letHandle exposure body => by
      have renamed := LeCo.HasType.letHandle
        (renameExposureTyping exposure contexts)
        (renameLeTyping body (contexts.extend (.member _)))
      simpa [LeCo.rename, ScopedTy.dropMember_rename] using renamed

termination_by sizeOf evidence

/-- Exposure recipes are stable under lookup-preserving context renaming. -/
def renameExposureTyping {s₁ s₂ : Sig} {sourceContext : Ctx s₁}
    {targetContext : Ctx s₂} {rho : Rename s₁ s₂}
    {exposure : Exposure s₁} {member : MemberSpec s₁}
    (typing : Exposure.HasType sourceContext exposure member)
    (contexts : Ctx.Renames sourceContext targetContext rho) :
    Exposure.HasType targetContext (exposure.rename rho) (member.rename rho) :=
  match typing with
  | .view (path := path) (label := label) (lower := lower) (upper := upper)
      (inclusion := inclusionEvidence) inclusionTyping => by
      have renamed := renameLeTyping inclusionTyping contexts
      have endpointTyping : LeCo.HasType targetContext
          (inclusionEvidence.rename rho)
          (targetContext.lookup (rho.var path)).termType
          (.member label (lower.rename rho) (upper.rename rho)) := by
        simpa [contexts.lookup path] using renamed
      simpa [Exposure.rename, MemberSpec.rename] using
        Exposure.HasType.view endpointTyping

termination_by sizeOf exposure

/-- Rename the function-specific context morphism stored by `LeCo.all`.
Both endpoint telescopes share the renamed outer context. -/
def renameFunctionMorTyping {s₁ s₂ : Sig}
    {sourceContext : Ctx s₁} {targetContext : Ctx s₂}
    {rho : Rename s₁ s₂} {actual view : Source.Ty s₁}
    {morphism : CtxMor (s₁ ▹ .term)}
    (typing : CtxMor.HasType (sourceContext.extendTerm actual)
      (sourceContext.extendTerm view) morphism)
    (contexts : Ctx.Renames sourceContext targetContext rho) :
    CtxMor.HasType (targetContext.extendTerm (actual.rename rho))
      (targetContext.extendTerm (view.rename rho))
      (morphism.renameLift rho) :=
  match typing with
  | .refl => by
      simpa only [CtxMor.renameLift_refl] using
        (CtxMor.HasType.refl (context :=
          targetContext.extendTerm (actual.rename rho)))
  | .function (domain := domainEvidence) domainTyping => by
      simpa only [CtxMor.renameLift_function] using
        CtxMor.HasType.function (renameLeTyping domainTyping contexts)

termination_by sizeOf morphism

end

/-- Namespaced public form of general inclusion-certificate renaming. -/
def LeCo.HasType.rename := @renameLeTyping

/-- Namespaced public form of general exposure-certificate renaming. -/
def Exposure.HasType.rename := @renameExposureTyping

/-- Namespaced public form of function-context-morphism renaming. -/
def CtxMor.HasType.renameFunction := @renameFunctionMorTyping

/-! The common elaborator operation is weakening below a freshly bound term.
These are corollaries of general certificate renaming, rather than separate
constructor-by-constructor proofs. -/

def EqCo.HasType.weakenTerm {s : Sig} {context : Ctx s}
    {evidence : EqCo s} {source target : Source.Ty s}
    (typing : EqCo.HasType context evidence source target)
    (bound : Source.Ty s) :
    EqCo.HasType (context.extendTerm bound) evidence.weaken
      source.weaken target.weaken :=
  EqCo.HasType.rename typing (Ctx.Renames.weakenTerm context bound)

def LeCo.HasType.weakenTerm {s : Sig} {context : Ctx s}
    {evidence : LeCo s} {source target : Source.Ty s}
    (typing : LeCo.HasType context evidence source target)
    (bound : Source.Ty s) :
    LeCo.HasType (context.extendTerm bound) evidence.weaken
      source.weaken target.weaken :=
  renameLeTyping typing (Ctx.Renames.weakenTerm context bound)

def Exposure.HasType.weakenTerm {s : Sig} {context : Ctx s}
    {exposure : Exposure s} {member : MemberSpec s}
    (typing : Exposure.HasType context exposure member)
    (bound : Source.Ty s) :
    Exposure.HasType (context.extendTerm bound) exposure.weaken member.weaken :=
  renameExposureTyping typing (Ctx.Renames.weakenTerm context bound)

/-- Insert a fresh term in the outer context of a function-view morphism. -/
def CtxMor.HasType.weakenBaseTerm {s : Sig} {context : Ctx s}
    {actual view : Source.Ty s} {morphism : CtxMor (s ▹ .term)}
    (typing : CtxMor.HasType (context.extendTerm actual)
      (context.extendTerm view) morphism)
    (bound : Source.Ty s) :
    CtxMor.HasType
      ((context.extendTerm bound).extendTerm actual.weaken)
      ((context.extendTerm bound).extendTerm view.weaken)
      (morphism.weakenBase (kind := .term)) :=
  renameFunctionMorTyping typing (Ctx.Renames.weakenTerm context bound)

namespace Tm

/-- Syntax-directed target term typing.  The only rule that changes a term's
type is the explicit `cast` constructor. -/
inductive HasType : {s : Sig} → Ctx s → Tm s → Source.Ty s → Type where
  | var {s : Sig} {context : Ctx s} (path : BVar s .term) :
      HasType context (.var path) (context.lookup path).termType
  | lam {s : Sig} {context : Ctx s} {domain : Source.Ty s}
      {body : Tm (s ▹ .term)} {codomain : Source.Ty (s ▹ .term)}
      (bodyTyping : HasType (context.extendTerm domain) body codomain) :
      HasType context (.lam domain body) (.all domain codomain)
  | obj {s : Sig} {context : Ctx s} (label : Name) (witness : Source.Ty s) :
      HasType context (.obj label witness) (.member label witness witness)
  | app {s : Sig} {context : Ctx s} {function argument : BVar s .term}
      {functionView argumentView : LeCo s}
      {domain : Source.Ty s} {codomain : Source.Ty (s ▹ .term)}
      (functionTyping : LeCo.HasType context functionView
        (context.lookup function).termType (.all domain codomain))
      (argumentTyping : LeCo.HasType context argumentView
        (context.lookup argument).termType domain) :
      HasType context (.app function argument functionView argumentView)
        (codomain.open argument)
  | let' {s : Sig} {context : Ctx s} {rhs : Tm s}
      {body : Tm (s ▹ .term)} {bound : Source.Ty s}
      {bodyType : Source.Ty (s ▹ .term)} {result : Source.Ty s}
      (rhsTyping : HasType context rhs bound)
      (bodyTyping : HasType (context.extendTerm bound) body bodyType)
      (nonescape : ScopedTy.strengthenTerm bodyType = some result) :
      HasType context (.let' rhs body) result
  | cast {s : Sig} {context : Ctx s} {term : Tm s} {inclusion : LeCo s}
      {source target : Source.Ty s}
      (termTyping : HasType context term source)
      (inclusionTyping : LeCo.HasType context inclusion source target) :
      HasType context (.cast term inclusion) target
  | letHandle {s : Sig} {context : Ctx s} {exposure : Exposure s}
      {body : Tm (s ▹ .member)} {member : MemberSpec s}
      {bodyType : Source.Ty (s ▹ .member)}
      (exposureTyping : Exposure.HasType context exposure member)
      (bodyTyping : HasType (context.extendMember member) body bodyType) :
      HasType context (.letHandle exposure body) (ScopedTy.dropMember bodyType)
  | letExact {s : Sig} {context : Ctx s} {label : Name}
      {witness : Source.Ty s}
      {body : Tm ((s ▹ .term) ▹ .evidence .equality)}
      {bodyType : Source.Ty ((s ▹ .term) ▹ .evidence .equality)}
      {result : Source.Ty s}
      (bodyTyping : HasType (context.extendExact label witness) body bodyType)
      (nonescape : ScopedTy.strengthenExact bodyType = some result) :
      HasType context (.letExact label witness body) result

end Tm

end DotFC.Explicit
