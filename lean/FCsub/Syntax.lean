import FCsub.Scope

/-!
# Standalone FCsub syntax

Constraint telescopes are intrinsically names-first.  A value of
`Telescope s n m` allocates `n` abstract type names simultaneously; each of
its `m` propositions is scoped in `TypeScope s n`, before any constraint
evidence is added.  The full static body lives in `StaticScope s n m`.

Existential payloads are deliberately not telescope entries.  `pack` carries
an ambient runtime payload, and `open` adds a separate final term binder after
all names and evidence.  This representation makes self-discharge of package
constraints impossible at the syntax boundary: packaged `LeArgs` live in the
ambient scope, not in the telescope's evidence-extended scope.
-/

namespace FCsub

mutual

/-- Selection-free FCsub types. -/
inductive Ty : Sig → Type where
  | top {scope : Sig} : Ty scope
  | bot {scope : Sig} : Ty scope
  | one {scope : Sig} : Ty scope
  | tvar {scope : Sig} (name : BVar scope .type) : Ty scope
  | arr {scope : Sig} (domain : Ty scope)
      (codomain : Ty (scope ▹ .term)) : Ty scope
  | existsT {scope : Sig} {names constraints : Nat}
      (telescope : Telescope scope names constraints)
      (payload : Ty (StaticScope scope names constraints)) : Ty scope
  | forallT {scope : Sig} {names constraints : Nat}
      (telescope : Telescope scope names constraints)
      (body : Ty (StaticScope scope names constraints)) : Ty scope

/-- The uniform proposition category of FCsub constraint telescopes.
Milestone 3.5 intentionally has only directed type inclusion. -/
inductive Proposition : Sig → Type where
  | inclusion {scope : Sig} (source target : Ty scope) : Proposition scope

/-- A names-first constraint telescope.

`names` is independent of telescope length.  Every `snoc` proposition sees
all names and no evidence binders, while `constraints` counts the directed
evidence binders that the complete telescope introduces. -/
inductive Telescope : (scope : Sig) → (names constraints : Nat) → Type where
  | nil {scope : Sig} {names : Nat} : Telescope scope names 0
  | snoc {scope : Sig} {names constraints : Nat}
      (initial : Telescope scope names constraints)
      (proposition : Proposition (TypeScope scope names)) :
      Telescope scope names (constraints + 1)

end

deriving instance DecidableEq for Ty, Proposition, Telescope

mutual

/-- Rename a type through every term and static telescope binder. -/
def Ty.rename {source target : Sig} (type : Ty source)
    (rho : Rename source target) : Ty target :=
  match type with
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .tvar name => .tvar (rho.var name)
  | .arr domain codomain =>
      .arr (domain.rename rho)
        (codomain.rename (rho.lift (kind := .term)))
  | .existsT telescope payload =>
      .existsT (telescope.rename rho)
        (payload.rename (rho.liftStatic _ _))
  | .forallT telescope body =>
      .forallT (telescope.rename rho)
        (body.rename (rho.liftStatic _ _))

/-- Rename a telescope proposition. -/
def Proposition.rename {source target : Sig}
    (proposition : Proposition source) (rho : Rename source target) :
    Proposition target :=
  match proposition with
  | .inclusion lower upper =>
      .inclusion (lower.rename rho) (upper.rename rho)

/-- Rename the ambient scope of a telescope without changing its arity. -/
def Telescope.rename {source target : Sig} {names constraints : Nat}
    (telescope : Telescope source names constraints)
    (rho : Rename source target) : Telescope target names constraints :=
  match telescope with
  | .nil => .nil
  | .snoc initial proposition =>
      .snoc (initial.rename rho)
        (proposition.rename (rho.liftTypes names))

end

namespace Ty

/-- Weaken a type below one heterogeneous binder. -/
def weaken {scope : Sig} {kind : BinderKind} (type : Ty scope) :
    Ty (scope ▹ kind) :=
  type.rename Rename.succ

end Ty

namespace Proposition

/-- Weaken a proposition below one heterogeneous binder. -/
def weaken {scope : Sig} {kind : BinderKind}
    (proposition : Proposition scope) : Proposition (scope ▹ kind) :=
  proposition.rename Rename.succ

end Proposition

namespace Telescope

/-- Weaken the ambient scope of a telescope. -/
def weaken {scope : Sig} {kind : BinderKind} {names constraints : Nat}
    (telescope : Telescope scope names constraints) :
    Telescope (scope ▹ kind) names constraints :=
  telescope.rename Rename.succ

end Telescope

mutual

@[simp]
def Ty.rename_id {scope : Sig} (type : Ty scope) :
    type.rename Rename.id = type :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar _ => rfl
  | .arr domain codomain => by
      simp only [Ty.rename, Rename.lift_id, Ty.rename_id domain,
        Ty.rename_id codomain]
  | .existsT telescope payload => by
      simp only [Ty.rename, Rename.liftStatic_id,
        Telescope.rename_id telescope, Ty.rename_id payload]
  | .forallT telescope body => by
      simp only [Ty.rename, Rename.liftStatic_id,
        Telescope.rename_id telescope, Ty.rename_id body]

@[simp]
def Proposition.rename_id {scope : Sig}
    (proposition : Proposition scope) :
    proposition.rename Rename.id = proposition :=
  match proposition with
  | .inclusion source target => by
      simp only [Proposition.rename, Ty.rename_id]

@[simp]
def Telescope.rename_id {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints) :
    telescope.rename Rename.id = telescope :=
  match telescope with
  | .nil => rfl
  | .snoc initial proposition => by
      simp only [Telescope.rename, Telescope.rename_id initial,
        Rename.liftTypes_id, Proposition.rename_id]

end

mutual

@[simp]
def Ty.rename_comp {first second third : Sig} (type : Ty first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (type.rename rho₁).rename rho₂ = type.rename (rho₁.comp rho₂) :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar _ => rfl
  | .arr domain codomain => by
      simp only [Ty.rename, Ty.rename_comp domain, Ty.rename_comp codomain,
        Rename.lift_comp]
  | .existsT telescope payload => by
      simp only [Ty.rename, Telescope.rename_comp telescope,
        Ty.rename_comp payload, Rename.liftStatic_comp]
  | .forallT telescope body => by
      simp only [Ty.rename, Telescope.rename_comp telescope,
        Ty.rename_comp body, Rename.liftStatic_comp]

@[simp]
def Proposition.rename_comp {first second third : Sig}
    (proposition : Proposition first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (proposition.rename rho₁).rename rho₂ =
      proposition.rename (rho₁.comp rho₂) :=
  match proposition with
  | .inclusion source target => by
      simp only [Proposition.rename, Ty.rename_comp]

@[simp]
def Telescope.rename_comp {first second third : Sig}
    {names constraints : Nat}
    (telescope : Telescope first names constraints)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (telescope.rename rho₁).rename rho₂ =
      telescope.rename (rho₁.comp rho₂) :=
  match telescope with
  | .nil => rfl
  | .snoc initial proposition => by
      simp only [Telescope.rename, Telescope.rename_comp initial,
        Proposition.rename_comp proposition, Rename.liftTypes_comp]

end

/-! ## Length-indexed type arguments -/

/-- Simultaneous witnesses for all abstract names of a telescope.  Every
witness is scoped in the ambient context, so witnesses are simultaneous. -/
inductive TypeArgs (scope : Sig) : Nat → Type where
  | nil : TypeArgs scope 0
  | snoc {count : Nat} (initial : TypeArgs scope count) (type : Ty scope) :
      TypeArgs scope (count + 1)
deriving DecidableEq

namespace TypeArgs

def rename {source target : Sig} {count : Nat}
    (arguments : TypeArgs source count) (rho : Rename source target) :
    TypeArgs target count :=
  match arguments with
  | .nil => .nil
  | .snoc initial type => .snoc (initial.rename rho) (type.rename rho)

def weaken {scope : Sig} {kind : BinderKind} {count : Nat}
    (arguments : TypeArgs scope count) : TypeArgs (scope ▹ kind) count :=
  arguments.rename Rename.succ

@[simp]
theorem rename_id {scope : Sig} {count : Nat}
    (arguments : TypeArgs scope count) :
    arguments.rename Rename.id = arguments := by
  induction arguments with
  | nil => rfl
  | snoc initial type induction => simp [rename, induction]

@[simp]
theorem rename_comp {first second third : Sig} {count : Nat}
    (arguments : TypeArgs first count) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (arguments.rename rho₁).rename rho₂ =
      arguments.rename (rho₁.comp rho₂) := by
  induction arguments with
  | nil => rfl
  | snoc initial type induction => simp [rename, induction, Ty.rename_comp]

end TypeArgs

/-! ## Equality and directed-inclusion certificates -/

/-- Symmetric type-equality evidence. -/
inductive EqCo : Sig → Type where
  | var {scope : Sig} (evidence : BVar scope (.evidence .equality)) :
      EqCo scope
  | refl {scope : Sig} (type : Ty scope) : EqCo scope
  | symm {scope : Sig} (evidence : EqCo scope) : EqCo scope
  | trans {scope : Sig} (first second : EqCo scope) : EqCo scope
deriving DecidableEq

mutual

/-- Directed inclusion evidence.  There is deliberately no symmetry
constructor and no conversion from two inclusions to equality.

Existential adaptation runs from the source telescope to the target
telescope, and its payload coercion is checked in the source static scope.
Universal adaptation is contravariant: it runs from the target telescope to
the source telescope, and its body coercion is checked in the target scope. -/
inductive LeCo : Sig → Type where
  | var {scope : Sig} (evidence : BVar scope (.evidence .inclusion)) :
      LeCo scope
  | refl {scope : Sig} (type : Ty scope) : LeCo scope
  | trans {scope : Sig} (first second : LeCo scope) : LeCo scope
  | top {scope : Sig} (source : Ty scope) : LeCo scope
  | bot {scope : Sig} (target : Ty scope) : LeCo scope
  | eqToLe {scope : Sig} (evidence : EqCo scope) : LeCo scope
  | arr {scope : Sig} (domain : LeCo scope)
      (codomain : LeCo (scope ▹ .term)) : LeCo scope
  | existsT {scope : Sig}
      {sourceNames sourceConstraints targetNames targetConstraints : Nat}
      (adaptation : TelMor scope sourceNames sourceConstraints
        targetNames targetConstraints)
      (sourcePayload : Ty
        (StaticScope scope sourceNames sourceConstraints))
      (targetPayload : Ty
        (StaticScope scope targetNames targetConstraints))
      (payload : LeCo (StaticScope scope sourceNames sourceConstraints)) :
      LeCo scope
  | forallT {scope : Sig}
      {sourceNames sourceConstraints targetNames targetConstraints : Nat}
      (adaptation : TelMor scope targetNames targetConstraints
        sourceNames sourceConstraints)
      (sourceBody : Ty (StaticScope scope sourceNames sourceConstraints))
      (targetBody : Ty (StaticScope scope targetNames targetConstraints))
      (body : LeCo (StaticScope scope targetNames targetConstraints)) :
      LeCo scope

/-- A vector of independently constructed directed-inclusion certificates. -/
inductive LeArgs : Sig → Nat → Type where
  | nil {scope : Sig} : LeArgs scope 0
  | snoc {scope : Sig} {count : Nat} (initial : LeArgs scope count)
      (evidence : LeCo scope) : LeArgs scope (count + 1)

/-- A syntactic map `source ⇒ target` between constraint telescopes.

Assuming `source`, it supplies an interpretation of every target name and an
independently checkable certificate for every target proposition.  Typing of
these fields against the instantiated target telescope is defined by the
kernel's declarative layer; the syntax itself records exact arities/scopes. -/
inductive TelMor : Sig → Nat → Nat → Nat → Nat → Type where
  | refl {scope : Sig} {names constraints : Nat}
      (telescope : Telescope scope names constraints) :
      TelMor scope names constraints names constraints
  | map {scope : Sig}
      {sourceNames sourceConstraints targetNames targetConstraints : Nat}
      (source : Telescope scope sourceNames sourceConstraints)
      (target : Telescope scope targetNames targetConstraints)
      (names : TypeArgs (StaticScope scope sourceNames sourceConstraints)
        targetNames)
      (evidence : LeArgs (StaticScope scope sourceNames sourceConstraints)
        targetConstraints) :
      TelMor scope sourceNames sourceConstraints targetNames targetConstraints
  | trans {scope : Sig}
      {firstNames firstConstraints middleNames middleConstraints
        lastNames lastConstraints : Nat}
      (first : TelMor scope firstNames firstConstraints
        middleNames middleConstraints)
      (second : TelMor scope middleNames middleConstraints
        lastNames lastConstraints) :
      TelMor scope firstNames firstConstraints lastNames lastConstraints

end


deriving instance DecidableEq for LeCo, LeArgs, TelMor

namespace EqCo

def rename {source target : Sig} (evidence : EqCo source)
    (rho : Rename source target) : EqCo target :=
  match evidence with
  | .var index => .var (rho.var index)
  | .refl type => .refl (type.rename rho)
  | .symm inner => .symm (inner.rename rho)
  | .trans first second => .trans (first.rename rho) (second.rename rho)

def weaken {scope : Sig} {kind : BinderKind} (evidence : EqCo scope) :
    EqCo (scope ▹ kind) :=
  evidence.rename Rename.succ

@[simp]
theorem rename_id {scope : Sig} (evidence : EqCo scope) :
    evidence.rename Rename.id = evidence := by
  induction evidence with
  | var => rfl
  | refl type => simp [rename]
  | symm inner induction => simp [rename, induction]
  | trans first second firstInduction secondInduction =>
      simp [rename, firstInduction, secondInduction]

@[simp]
theorem rename_comp {first second third : Sig} (evidence : EqCo first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (evidence.rename rho₁).rename rho₂ =
      evidence.rename (rho₁.comp rho₂) := by
  induction evidence generalizing second third with
  | var => rfl
  | refl type => simp [rename, Ty.rename_comp]
  | symm inner induction => simp [rename, induction]
  | trans firstEvidence secondEvidence firstInduction secondInduction =>
      simp [rename, firstInduction, secondInduction]

end EqCo

mutual

/-- Rename directed evidence and every nested telescope adaptation. -/
def LeCo.rename {source target : Sig} (certificate : LeCo source)
    (rho : Rename source target) : LeCo target :=
  match certificate with
  | .var index => .var (rho.var index)
  | .refl type => .refl (type.rename rho)
  | .trans first second => .trans (first.rename rho) (second.rename rho)
  | .top sourceType => .top (sourceType.rename rho)
  | .bot targetType => .bot (targetType.rename rho)
  | .eqToLe equality => .eqToLe (equality.rename rho)
  | .arr domain codomain =>
      .arr (domain.rename rho)
        (codomain.rename (rho.lift (kind := .term)))
  | .existsT adaptation sourcePayload targetPayload payload =>
      .existsT (adaptation.rename rho)
        (sourcePayload.rename (rho.liftStatic _ _))
        (targetPayload.rename (rho.liftStatic _ _))
        (payload.rename (rho.liftStatic _ _))
  | .forallT adaptation sourceBody targetBody body =>
      .forallT (adaptation.rename rho)
        (sourceBody.rename (rho.liftStatic _ _))
        (targetBody.rename (rho.liftStatic _ _))
        (body.rename (rho.liftStatic _ _))

/-- Rename a vector of directed certificates. -/
def LeArgs.rename {source target : Sig} {count : Nat}
    (arguments : LeArgs source count) (rho : Rename source target) :
    LeArgs target count :=
  match arguments with
  | .nil => .nil
  | .snoc initial evidence =>
      .snoc (initial.rename rho) (evidence.rename rho)

/-- Rename the common ambient scope of both telescope endpoints. -/
def TelMor.rename {sourceScope targetScope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor sourceScope sourceNames sourceConstraints
      targetNames targetConstraints)
    (rho : Rename sourceScope targetScope) :
    TelMor targetScope sourceNames sourceConstraints
      targetNames targetConstraints :=
  match morphism with
  | .refl telescope => .refl (telescope.rename rho)
  | .map source target names evidence =>
      .map (source.rename rho) (target.rename rho)
        (names.rename (rho.liftStatic sourceNames sourceConstraints))
        (evidence.rename (rho.liftStatic sourceNames sourceConstraints))
  | .trans first second => .trans (first.rename rho) (second.rename rho)

end

namespace LeCo

def weaken {scope : Sig} {kind : BinderKind} (evidence : LeCo scope) :
    LeCo (scope ▹ kind) :=
  evidence.rename Rename.succ

end LeCo

namespace LeArgs

def weaken {scope : Sig} {kind : BinderKind} {count : Nat}
    (arguments : LeArgs scope count) : LeArgs (scope ▹ kind) count :=
  arguments.rename Rename.succ

end LeArgs

namespace TelMor

def weaken {scope : Sig} {kind : BinderKind}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints) :
    TelMor (scope ▹ kind) sourceNames sourceConstraints
      targetNames targetConstraints :=
  morphism.rename Rename.succ

end TelMor

mutual

@[simp]
def LeCo.rename_id {scope : Sig} (evidence : LeCo scope) :
    evidence.rename Rename.id = evidence :=
  match evidence with
  | .var _ => rfl
  | .refl type => by simp only [LeCo.rename, Ty.rename_id]
  | .trans first second => by
      simp only [LeCo.rename, LeCo.rename_id first, LeCo.rename_id second]
  | .top source => by simp only [LeCo.rename, Ty.rename_id]
  | .bot target => by simp only [LeCo.rename, Ty.rename_id]
  | .eqToLe equality => by simp only [LeCo.rename, EqCo.rename_id]
  | .arr domain codomain => by
      simp only [LeCo.rename, Rename.lift_id,
        LeCo.rename_id domain, LeCo.rename_id codomain]
  | .existsT adaptation sourcePayload targetPayload payload => by
      simp only [LeCo.rename, TelMor.rename_id adaptation,
        Rename.liftStatic_id, Ty.rename_id, LeCo.rename_id payload]
  | .forallT adaptation sourceBody targetBody body => by
      simp only [LeCo.rename, TelMor.rename_id adaptation,
        Rename.liftStatic_id, Ty.rename_id, LeCo.rename_id body]

@[simp]
def LeArgs.rename_id {scope : Sig} {count : Nat}
    (arguments : LeArgs scope count) :
    arguments.rename Rename.id = arguments :=
  match arguments with
  | .nil => rfl
  | .snoc initial evidence => by
      simp only [LeArgs.rename, LeArgs.rename_id initial,
        LeCo.rename_id evidence]

@[simp]
def TelMor.rename_id {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints) :
    morphism.rename Rename.id = morphism :=
  match morphism with
  | .refl telescope => by
      simp only [TelMor.rename, Telescope.rename_id]
  | .map source target names evidence => by
      simp only [TelMor.rename, Rename.liftStatic_id,
        Telescope.rename_id, TypeArgs.rename_id, LeArgs.rename_id]
  | .trans first second => by
      simp only [TelMor.rename, TelMor.rename_id first, TelMor.rename_id second]

end

mutual

@[simp]
def LeCo.rename_comp {first second third : Sig} (evidence : LeCo first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (evidence.rename rho₁).rename rho₂ =
      evidence.rename (rho₁.comp rho₂) :=
  match evidence with
  | .var _ => rfl
  | .refl type => by simp only [LeCo.rename, Ty.rename_comp]
  | .trans firstEvidence secondEvidence => by
      simp only [LeCo.rename, LeCo.rename_comp firstEvidence,
        LeCo.rename_comp secondEvidence]
  | .top source => by simp only [LeCo.rename, Ty.rename_comp]
  | .bot target => by simp only [LeCo.rename, Ty.rename_comp]
  | .eqToLe equality => by simp only [LeCo.rename, EqCo.rename_comp]
  | .arr domain codomain => by
      simp only [LeCo.rename, LeCo.rename_comp domain,
        LeCo.rename_comp codomain, Rename.lift_comp]
  | .existsT adaptation sourcePayload targetPayload payload => by
      simp only [LeCo.rename, TelMor.rename_comp adaptation,
        Ty.rename_comp, LeCo.rename_comp payload, Rename.liftStatic_comp]
  | .forallT adaptation sourceBody targetBody body => by
      simp only [LeCo.rename, TelMor.rename_comp adaptation,
        Ty.rename_comp, LeCo.rename_comp body, Rename.liftStatic_comp]

@[simp]
def LeArgs.rename_comp {first second third : Sig} {count : Nat}
    (arguments : LeArgs first count) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (arguments.rename rho₁).rename rho₂ =
      arguments.rename (rho₁.comp rho₂) :=
  match arguments with
  | .nil => rfl
  | .snoc initial evidence => by
      simp only [LeArgs.rename, LeArgs.rename_comp initial,
        LeCo.rename_comp evidence]

@[simp]
def TelMor.rename_comp {first second third : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor first sourceNames sourceConstraints
      targetNames targetConstraints)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (morphism.rename rho₁).rename rho₂ =
      morphism.rename (rho₁.comp rho₂) :=
  match morphism with
  | .refl telescope => by
      simp only [TelMor.rename, Telescope.rename_comp]
  | .map source target names evidence => by
      simp only [TelMor.rename, Telescope.rename_comp,
        TypeArgs.rename_comp, LeArgs.rename_comp, Rename.liftStatic_comp]
  | .trans firstMorphism secondMorphism => by
      simp only [TelMor.rename, TelMor.rename_comp firstMorphism,
        TelMor.rename_comp secondMorphism]

end

/-! ## Explicitly annotated terms -/

/-- FCsub terms with explicit static abstraction/application and
existential package construction/opening. -/
inductive Tm : Sig → Type where
  | unit {scope : Sig} : Tm scope
  | var {scope : Sig} (index : BVar scope .term) : Tm scope
  | lam {scope : Sig} (domain : Ty scope)
      (body : Tm (scope ▹ .term)) : Tm scope
  | app {scope : Sig} (function argument : Tm scope) : Tm scope
  | let' {scope : Sig} (rhs : Tm scope)
      (body : Tm (scope ▹ .term)) : Tm scope
  | cast {scope : Sig} (term : Tm scope) (evidence : LeCo scope) : Tm scope
  | pack {scope : Sig} {names constraints : Nat}
      (telescope : Telescope scope names constraints)
      (payloadType : Ty (StaticScope scope names constraints))
      (witnesses : TypeArgs scope names)
      (evidence : LeArgs scope constraints)
      (payload : Tm scope) : Tm scope
  | «open» {scope : Sig} {names constraints : Nat}
      (telescope : Telescope scope names constraints)
      (payloadType : Ty (StaticScope scope names constraints))
      (scrutinee : Tm scope)
      (body : Tm (PayloadScope scope names constraints)) : Tm scope
  | slam {scope : Sig} {names constraints : Nat}
      (telescope : Telescope scope names constraints)
      (body : Tm (StaticScope scope names constraints)) : Tm scope
  | sapp {scope : Sig} {names constraints : Nat}
      (telescope : Telescope scope names constraints)
      (function : Tm scope)
      (witnesses : TypeArgs scope names)
      (evidence : LeArgs scope constraints) : Tm scope
  | newtype {scope : Sig} (witness : Ty scope)
      (body : Tm (NewtypeScope scope)) : Tm scope
deriving DecidableEq

namespace Tm

def rename {source target : Sig} (term : Tm source)
    (rho : Rename source target) : Tm target :=
  match term with
  | .unit => .unit
  | .var index => .var (rho.var index)
  | .lam domain body =>
      .lam (domain.rename rho) (body.rename (rho.lift (kind := .term)))
  | .app function argument =>
      .app (function.rename rho) (argument.rename rho)
  | .let' rhs body =>
      .let' (rhs.rename rho) (body.rename (rho.lift (kind := .term)))
  | .cast term evidence => .cast (term.rename rho) (evidence.rename rho)
  | .pack telescope payloadType witnesses evidence payload =>
      .pack (telescope.rename rho)
        (payloadType.rename (rho.liftStatic _ _))
        (witnesses.rename rho) (evidence.rename rho) (payload.rename rho)
  | .«open» telescope payloadType scrutinee body =>
      .«open» (telescope.rename rho)
        (payloadType.rename (rho.liftStatic _ _))
        (scrutinee.rename rho) (body.rename (rho.liftPayload _ _))
  | .slam telescope body =>
      .slam (telescope.rename rho) (body.rename (rho.liftStatic _ _))
  | .sapp telescope function witnesses evidence =>
      .sapp (telescope.rename rho) (function.rename rho)
        (witnesses.rename rho) (evidence.rename rho)
  | .newtype witness body =>
      .newtype (witness.rename rho) (body.rename rho.liftNewtype)

def weaken {scope : Sig} {kind : BinderKind} (term : Tm scope) :
    Tm (scope ▹ kind) :=
  term.rename Rename.succ

@[simp]
theorem rename_id {scope : Sig} (term : Tm scope) :
    term.rename Rename.id = term := by
  induction term with
  | unit => rfl
  | var => rfl
  | lam domain body induction => simp [rename, induction]
  | app function argument functionInduction argumentInduction =>
      simp [rename, functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp [rename, rhsInduction, bodyInduction]
  | cast term evidence induction => simp [rename, induction]
  | pack telescope payloadType witnesses evidence payload induction =>
      simp [rename, induction]
  | «open» telescope payloadType scrutinee body scrutineeInduction
      bodyInduction => simp [rename, scrutineeInduction, bodyInduction]
  | slam telescope body induction => simp [rename, induction]
  | sapp telescope function witnesses evidence induction =>
      simp [rename, induction]
  | newtype witness body induction => simp [rename, induction]

@[simp]
theorem rename_comp {first second third : Sig} (term : Tm first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (term.rename rho₁).rename rho₂ = term.rename (rho₁.comp rho₂) := by
  induction term generalizing second third with
  | unit => rfl
  | var => rfl
  | lam domain body induction =>
      simp [rename, induction, Ty.rename_comp, Rename.lift_comp]
  | app function argument functionInduction argumentInduction =>
      simp [rename, functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp [rename, rhsInduction, bodyInduction, Rename.lift_comp]
  | cast term evidence induction =>
      simp [rename, induction, LeCo.rename_comp]
  | pack telescope payloadType witnesses evidence payload induction =>
      simp [rename, induction, Telescope.rename_comp, Ty.rename_comp,
        TypeArgs.rename_comp, LeArgs.rename_comp, Rename.liftStatic_comp]
  | «open» telescope payloadType scrutinee body scrutineeInduction
      bodyInduction =>
      simp [rename, scrutineeInduction, bodyInduction,
        Telescope.rename_comp, Ty.rename_comp, Rename.liftStatic_comp,
        Rename.liftPayload_comp]
  | slam telescope body induction =>
      simp [rename, induction, Telescope.rename_comp,
        Rename.liftStatic_comp]
  | sapp telescope function witnesses evidence induction =>
      simp [rename, induction, Telescope.rename_comp,
        TypeArgs.rename_comp, LeArgs.rename_comp]
  | newtype witness body induction =>
      simp [rename, induction, Ty.rename_comp, Rename.liftNewtype_comp]

end Tm

end FCsub
