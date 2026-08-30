import Coercions.ManySortedFC.Scope

/-!
# Static syntax for many-sorted FC

The initial target has two static sorts.  Type expressions and capture
expressions are intrinsically separated, while `StaticExpr` exposes the small
uniform interface needed by heterogeneous theories.  A theory allocates all
of its symbols before any evidence binder: its propositions therefore see the
complete symbol block but cannot refer to evidence exported by that same
theory.

Capture expressions deliberately have no top element.  An omitted capture
upper bound is represented by omitting a proposition from a theory, not by a
distinguished capture expression.
-/

namespace ManySortedFC

/-- Binder kinds contributed by a heterogeneous block of static symbols. -/
def symbolKinds : List StaticSort → Sig
  | [] => []
  | sort :: rest => .symbol sort :: symbolKinds rest

/-- Binder kinds contributed by a heterogeneous block of propositions. -/
def evidenceKinds : List Relation → Sig
  | [] => []
  | relation :: rest => .evidence relation :: evidenceKinds rest

/-- Scope after all symbols of a names-first theory have been allocated. -/
@[reducible]
def SymbolScope (scope : Sig) (symbols : List StaticSort) : Sig :=
  Sig.extendMany scope (symbolKinds symbols)

/-- Scope after both the symbol and evidence blocks of a theory. -/
@[reducible]
def StaticScope (scope : Sig) (symbols : List StaticSort)
    (relations : List Relation) : Sig :=
  Sig.extendMany (SymbolScope scope symbols) (evidenceKinds relations)

namespace Rename

/-- Lift below a heterogeneous block of static symbols. -/
def liftSymbols {source target : Sig} (rho : Rename source target)
    (symbols : List StaticSort) :
    Rename (SymbolScope source symbols) (SymbolScope target symbols) :=
  rho.liftMany (symbolKinds symbols)

/-- Lift below the evidence block of a theory. -/
def liftEvidence {source target : Sig} (rho : Rename source target)
    (relations : List Relation) :
    Rename (Sig.extendMany source (evidenceKinds relations))
      (Sig.extendMany target (evidenceKinds relations)) :=
  rho.liftMany (evidenceKinds relations)

/-- Lift below a complete names-first theory. -/
def liftStatic {source target : Sig} (rho : Rename source target)
    (symbols : List StaticSort) (relations : List Relation) :
    Rename (StaticScope source symbols relations)
      (StaticScope target symbols relations) :=
  (rho.liftSymbols symbols).liftEvidence relations

/-- Weaken an ambient scope below a heterogeneous binder block. -/
def weakenMany (scope : Sig) : (kinds : Sig) →
    Rename scope (Sig.extendMany scope kinds)
  | [] => id
  | kind :: rest => (weakenMany scope rest).comp (succ (kind := kind))

/-- Weaken an ambient scope below a heterogeneous symbol block. -/
def weakenSymbols {scope : Sig} (symbols : List StaticSort) :
    Rename scope (SymbolScope scope symbols) :=
  weakenMany scope (symbolKinds symbols)

/-- Weaken an ambient scope below a complete theory. -/
def weakenStatic {scope : Sig} (symbols : List StaticSort)
    (relations : List Relation) :
    Rename scope (StaticScope scope symbols relations) :=
  (weakenSymbols symbols).comp
    (weakenMany (SymbolScope scope symbols) (evidenceKinds relations))

@[simp]
theorem liftSymbols_id {scope : Sig} (symbols : List StaticSort) :
    (id (scope := scope)).liftSymbols symbols = id := by
  unfold liftSymbols
  exact liftMany_id _

@[simp]
theorem liftEvidence_id {scope : Sig} (relations : List Relation) :
    (id (scope := scope)).liftEvidence relations = id := by
  unfold liftEvidence
  exact liftMany_id _

@[simp]
theorem liftStatic_id {scope : Sig} (symbols : List StaticSort)
    (relations : List Relation) :
    (id (scope := scope)).liftStatic symbols relations = id := by
  unfold liftStatic
  simp

theorem liftSymbols_comp {first second third : Sig}
    (rho₁ : Rename first second) (rho₂ : Rename second third)
    (symbols : List StaticSort) :
    (rho₁.comp rho₂).liftSymbols symbols =
      (rho₁.liftSymbols symbols).comp (rho₂.liftSymbols symbols) := by
  unfold liftSymbols
  exact liftMany_comp _ _ _

theorem liftEvidence_comp {first second third : Sig}
    (rho₁ : Rename first second) (rho₂ : Rename second third)
    (relations : List Relation) :
    (rho₁.comp rho₂).liftEvidence relations =
      (rho₁.liftEvidence relations).comp (rho₂.liftEvidence relations) := by
  unfold liftEvidence
  exact liftMany_comp _ _ _

theorem liftStatic_comp {first second third : Sig}
    (rho₁ : Rename first second) (rho₂ : Rename second third)
    (symbols : List StaticSort) (relations : List Relation) :
    (rho₁.comp rho₂).liftStatic symbols relations =
      (rho₁.liftStatic symbols relations).comp
        (rho₂.liftStatic symbols relations) := by
  unfold liftStatic
  rw [liftSymbols_comp, liftEvidence_comp]

end Rename

mutual

/-- Capture expressions.  `singleton` denotes an ordinary term capability;
`cvar` denotes an abstract capture symbol. -/
inductive Capture : Sig → Type where
  | empty {scope : Sig} : Capture scope
  | union {scope : Sig} (left right : Capture scope) : Capture scope
  | singleton {scope : Sig} (capability : BVar scope .term) : Capture scope
  | cvar {scope : Sig}
      (name : BVar scope (.symbol .capture)) : Capture scope

/-- Types of the many-sorted target.  Static quantifiers bind an entire local
theory, including a heterogeneous names-first symbol block. -/
inductive Ty : Sig → Type where
  | top {scope : Sig} : Ty scope
  | bot {scope : Sig} : Ty scope
  | one {scope : Sig} : Ty scope
  | tvar {scope : Sig} (name : BVar scope (.symbol .type)) : Ty scope
  | capturing {scope : Sig} (captures : Capture scope)
      (shape : Ty scope) : Ty scope
  | arr {scope : Sig} (domain codomain : Ty scope) : Ty scope
  | forallT {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      (theory : Theory scope symbols relations)
      (body : Ty (StaticScope scope symbols relations)) : Ty scope
  | existsT {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      (theory : Theory scope symbols relations)
      (payload : Ty (StaticScope scope symbols relations)) : Ty scope

/-- A static expression indexed by its sort. -/
inductive StaticExpr : StaticSort → Sig → Type where
  | type {scope : Sig} (type : Ty scope) : StaticExpr .type scope
  | capture {scope : Sig} (capture : Capture scope) :
      StaticExpr .capture scope

/-- A relation proposition whose endpoints are intrinsically of the relation's
sort.  Cross-sort equalities and inclusions are therefore unrepresentable. -/
inductive Proposition : Relation → Sig → Type where
  | equality {scope : Sig} {sort : StaticSort}
      (left right : StaticExpr sort scope) :
      Proposition (.equality sort) scope
  | inclusion {scope : Sig} {sort : StaticSort}
      (lower upper : StaticExpr sort scope) :
      Proposition (.inclusion sort) scope

/-- A names-first local theory.  Every proposition is scoped after all symbols
but before every evidence binder, preventing a theory from citing its own
exported evidence. -/
inductive Theory : (scope : Sig) → (symbols : List StaticSort) →
    List Relation → Type where
  | nil {scope : Sig} {symbols : List StaticSort} : Theory scope symbols []
  | cons {scope : Sig} {symbols : List StaticSort}
      {relation : Relation} {relations : List Relation}
      (proposition : Proposition relation (SymbolScope scope symbols))
      (rest : Theory scope symbols relations) :
      Theory scope symbols (relation :: relations)

end

deriving instance DecidableEq for Capture, Ty, StaticExpr, Proposition, Theory

namespace Ty

/-- Capabilities retained by the outermost capturing annotation.

For a bare type this projection returns the empty capture as the neutral
accounting default. That projection alone does not justify contracting a
variable singleton to empty: `Evidence.captureVariable` requires an explicit
`capturing` binding. -/
def outerCapture {scope : Sig} : Ty scope → Capture scope
  | .capturing captures _ => captures
  | _ => .empty

/-- Remove one outer capturing annotation, if present. -/
def stripCapture {scope : Sig} : Ty scope → Ty scope
  | .capturing _ shape => shape
  | type => type

/-- Install one canonical outer capture, replacing any previous outer
annotation instead of constructing nested capturing types. -/
def withCapture {scope : Sig} (captures : Capture scope)
    (type : Ty scope) : Ty scope :=
  .capturing captures type.stripCapture

/-- Give a variable of capturing type its precise singleton capture. Bare
types remain bare and export no variable-root contraction evidence. -/
def precise {scope : Sig} (capability : BVar scope .term) :
    Ty scope → Ty scope
  | .capturing _ shape => .capturing (.singleton capability) shape
  | type => type

end Ty

mutual

/-- Rename a capture expression through a heterogeneous scope map. -/
def Capture.rename {source target : Sig} (capture : Capture source)
    (rho : Rename source target) : Capture target :=
  match capture with
  | .empty => .empty
  | .union left right => .union (left.rename rho) (right.rename rho)
  | .singleton capability => .singleton (rho.var capability)
  | .cvar name => .cvar (rho.var name)

/-- Rename a type, lifting through every local theory. -/
def Ty.rename {source target : Sig} (type : Ty source)
    (rho : Rename source target) : Ty target :=
  match type with
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .tvar name => .tvar (rho.var name)
  | .capturing captures shape =>
      .capturing (captures.rename rho) (shape.rename rho)
  | .arr domain codomain => .arr (domain.rename rho) (codomain.rename rho)
  | @Ty.forallT _ symbols relations theory body =>
      .forallT (theory.rename rho)
        (body.rename (rho.liftStatic symbols relations))
  | @Ty.existsT _ symbols relations theory payload =>
      .existsT (theory.rename rho)
        (payload.rename (rho.liftStatic symbols relations))

/-- Rename a static expression without changing its sort. -/
def StaticExpr.rename {sort : StaticSort} {source target : Sig}
    (expression : StaticExpr sort source) (rho : Rename source target) :
    StaticExpr sort target :=
  match expression with
  | .type type => .type (type.rename rho)
  | .capture capture => .capture (capture.rename rho)

/-- Rename both endpoints of a proposition. -/
def Proposition.rename {relation : Relation} {source target : Sig}
    (proposition : Proposition relation source) (rho : Rename source target) :
    Proposition relation target :=
  match proposition with
  | .equality left right => .equality (left.rename rho) (right.rename rho)
  | .inclusion lower upper => .inclusion (lower.rename rho) (upper.rename rho)

/-- Rename the ambient scope of a theory without changing its interface. -/
def Theory.rename {source target : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory source symbols relations)
    (rho : Rename source target) : Theory target symbols relations :=
  match theory with
  | .nil => .nil
  | .cons proposition rest =>
      .cons (proposition.rename (rho.liftSymbols symbols)) (rest.rename rho)

end

namespace Capture

/-- Weaken a capture expression below one binder. -/
def weaken {scope : Sig} {kind : BinderKind} (capture : Capture scope) :
    Capture (scope ▹ kind) :=
  capture.rename Rename.succ

end Capture

namespace Ty

/-- Weaken a type below one binder. -/
def weaken {scope : Sig} {kind : BinderKind} (type : Ty scope) :
    Ty (scope ▹ kind) :=
  type.rename Rename.succ

end Ty

namespace StaticExpr

/-- Weaken a static expression below one binder. -/
def weaken {scope : Sig} {kind : BinderKind} {sort : StaticSort}
    (expression : StaticExpr sort scope) : StaticExpr sort (scope ▹ kind) :=
  expression.rename Rename.succ

end StaticExpr

mutual

@[simp]
def Capture.rename_id {scope : Sig} (capture : Capture scope) :
    capture.rename Rename.id = capture :=
  match capture with
  | .empty => rfl
  | .union left right => by
      simp only [Capture.rename, Capture.rename_id left,
        Capture.rename_id right]
  | .singleton _ => rfl
  | .cvar _ => rfl

@[simp]
def Ty.rename_id {scope : Sig} (type : Ty scope) :
    type.rename Rename.id = type :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar _ => rfl
  | .capturing captures shape => by
      simp only [Ty.rename, Capture.rename_id captures, Ty.rename_id shape]
  | .arr domain codomain => by
      simp only [Ty.rename, Ty.rename_id domain, Ty.rename_id codomain]
  | @Ty.forallT _ symbols relations theory body => by
      simp only [Ty.rename, Theory.rename_id theory, Rename.liftStatic_id,
        Ty.rename_id body]
  | @Ty.existsT _ symbols relations theory payload => by
      simp only [Ty.rename, Theory.rename_id theory, Rename.liftStatic_id,
        Ty.rename_id payload]

@[simp]
def StaticExpr.rename_id {scope : Sig} {sort : StaticSort}
    (expression : StaticExpr sort scope) :
    expression.rename Rename.id = expression :=
  match expression with
  | .type type => by
      simp only [StaticExpr.rename, Ty.rename_id type]
  | .capture capture => by
      simp only [StaticExpr.rename, Capture.rename_id capture]

@[simp]
def Proposition.rename_id {scope : Sig} {relation : Relation}
    (proposition : Proposition relation scope) :
    proposition.rename Rename.id = proposition :=
  match proposition with
  | .equality left right => by
      simp only [Proposition.rename, StaticExpr.rename_id left,
        StaticExpr.rename_id right]
  | .inclusion lower upper => by
      simp only [Proposition.rename, StaticExpr.rename_id lower,
        StaticExpr.rename_id upper]

@[simp]
def Theory.rename_id {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations) :
    theory.rename Rename.id = theory :=
  match theory with
  | .nil => rfl
  | .cons proposition rest => by
      simp only [Theory.rename, Rename.liftSymbols_id,
        Proposition.rename_id proposition, Theory.rename_id rest]

end

@[simp]
theorem Ty.outerCapture_rename {source target : Sig} (type : Ty source)
    (rho : Rename source target) :
    (type.rename rho).outerCapture = type.outerCapture.rename rho := by
  cases type <;> rfl

@[simp]
theorem Ty.stripCapture_rename {source target : Sig} (type : Ty source)
    (rho : Rename source target) :
    (type.rename rho).stripCapture = type.stripCapture.rename rho := by
  cases type <;> rfl

@[simp]
theorem Ty.withCapture_rename {source target : Sig}
    (captures : Capture source) (type : Ty source)
    (rho : Rename source target) :
    (type.withCapture captures).rename rho =
      (type.rename rho).withCapture (captures.rename rho) := by
  simp [Ty.withCapture, Ty.rename]

@[simp]
theorem Ty.precise_rename {source target : Sig}
    (capability : BVar source .term) (type : Ty source)
    (rho : Rename source target) :
    (type.precise capability).rename rho =
      (type.rename rho).precise (rho.var capability) := by
  cases type <;> rfl

mutual

@[simp]
def Capture.rename_comp {first second third : Sig}
    (capture : Capture first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (capture.rename rho₁).rename rho₂ = capture.rename (rho₁.comp rho₂) :=
  match capture with
  | .empty => rfl
  | .union left right => by
      simp only [Capture.rename, Capture.rename_comp left,
        Capture.rename_comp right]
  | .singleton _ => rfl
  | .cvar _ => rfl

@[simp]
def Ty.rename_comp {first second third : Sig} (type : Ty first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (type.rename rho₁).rename rho₂ = type.rename (rho₁.comp rho₂) :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar _ => rfl
  | .capturing captures shape => by
      simp only [Ty.rename, Capture.rename_comp captures,
        Ty.rename_comp shape]
  | .arr domain codomain => by
      simp only [Ty.rename, Ty.rename_comp domain, Ty.rename_comp codomain]
  | @Ty.forallT _ symbols relations theory body => by
      simp only [Ty.rename, Theory.rename_comp theory,
        Ty.rename_comp body, Rename.liftStatic_comp]
  | @Ty.existsT _ symbols relations theory payload => by
      simp only [Ty.rename, Theory.rename_comp theory,
        Ty.rename_comp payload, Rename.liftStatic_comp]

@[simp]
def StaticExpr.rename_comp {sort : StaticSort} {first second third : Sig}
    (expression : StaticExpr sort first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (expression.rename rho₁).rename rho₂ =
      expression.rename (rho₁.comp rho₂) :=
  match expression with
  | .type type => by
      simp only [StaticExpr.rename, Ty.rename_comp type]
  | .capture capture => by
      simp only [StaticExpr.rename, Capture.rename_comp capture]

@[simp]
def Proposition.rename_comp {relation : Relation}
    {first second third : Sig} (proposition : Proposition relation first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (proposition.rename rho₁).rename rho₂ =
      proposition.rename (rho₁.comp rho₂) :=
  match proposition with
  | .equality left right => by
      simp only [Proposition.rename, StaticExpr.rename_comp left,
        StaticExpr.rename_comp right]
  | .inclusion lower upper => by
      simp only [Proposition.rename, StaticExpr.rename_comp lower,
        StaticExpr.rename_comp upper]

@[simp]
def Theory.rename_comp {first second third : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory first symbols relations) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (theory.rename rho₁).rename rho₂ = theory.rename (rho₁.comp rho₂) :=
  match theory with
  | .nil => rfl
  | .cons proposition rest => by
      simp only [Theory.rename, Proposition.rename_comp proposition,
        Theory.rename_comp rest, Rename.liftSymbols_comp]

end

end ManySortedFC
