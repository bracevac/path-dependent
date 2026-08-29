import DotFC.Source.Syntax

/-!
# Explicit Stage A syntax

Stage A deliberately reuses `DotFC.Source.Ty`: selections remain in the type
language, while every non-syntactic equality, inclusion, exposure, and context
adjustment is represented by explicit syntax.  All categories share the one
heterogeneous `Sig` from `DotFC.Scope`.

Member exposure is reusable rather than copied into every selection coercion.
`LeCo.lower` and `LeCo.upper` consequently accept only a bound `.member`
variable; `LeCo.letHandle` and `Tm.letHandle` are the forms that bind such a
handle.
-/

namespace DotFC.Explicit

open DotFC

abbrev Name := Source.Name

/-- The fact stored at a reusable member-handle binder. -/
structure MemberSpec (s : Sig) where
  path : BVar s .term
  label : Name
  lower : Source.Ty s
  upper : Source.Ty s
deriving DecidableEq

namespace MemberSpec

/-- Rename every component of a reusable member specification. -/
def rename {s₁ s₂ : Sig} (member : MemberSpec s₁) (rho : Rename s₁ s₂) :
    MemberSpec s₂ where
  path := rho.var member.path
  label := member.label
  lower := member.lower.rename rho
  upper := member.upper.rename rho

/-- Weaken a member specification below a binder of any kind. -/
def weaken {s : Sig} {kind : BinderKind} (member : MemberSpec s) :
    MemberSpec (s ▹ kind) :=
  member.rename Rename.succ

@[simp]
theorem rename_id {s : Sig} (member : MemberSpec s) :
    member.rename Rename.id = member := by
  cases member
  simp [rename]

@[simp]
theorem rename_comp {s₁ s₂ s₃ : Sig} (member : MemberSpec s₁)
    (rho₁ : Rename s₁ s₂) (rho₂ : Rename s₂ s₃) :
    (member.rename rho₁).rename rho₂ = member.rename (rho₁.comp rho₂) := by
  cases member
  simp [rename, Source.Ty.rename_comp]

end MemberSpec

mutual

/-- Symmetric type-equality evidence.  Unlike inclusion evidence, this syntax
has an explicit symmetry constructor. -/
inductive EqCo : Sig → Type where
  | var {s : Sig} (evidence : BVar s (.evidence .equality)) : EqCo s
  | refl {s : Sig} (type : Source.Ty s) : EqCo s
  | symm {s : Sig} (evidence : EqCo s) : EqCo s
  | trans {s : Sig} (left right : EqCo s) : EqCo s

/-- Directed inclusion evidence.  In particular, there is no symmetry
constructor and no conversion from mutual inclusion to equality. -/
inductive LeCo : Sig → Type where
  | var {s : Sig} (evidence : BVar s (.evidence .inclusion)) : LeCo s
  | refl {s : Sig} (type : Source.Ty s) : LeCo s
  | trans {s : Sig} (left right : LeCo s) : LeCo s
  | top {s : Sig} (source : Source.Ty s) : LeCo s
  | bot {s : Sig} (target : Source.Ty s) : LeCo s
  | eqToLe {s : Sig} (evidence : EqCo s) : LeCo s
  | member {s : Sig} (label : Name) (lower upper : LeCo s) : LeCo s
  | all {s : Sig} (domain : LeCo s)
      (view : CtxMor (s ▹ .term))
      (codomain : LeCo (s ▹ .term)) : LeCo s
  | lower {s : Sig} (handle : BVar s .member) : LeCo s
  | upper {s : Sig} (handle : BVar s .member) : LeCo s
  | letHandle {s : Sig} (exposure : Exposure s)
      (body : LeCo (s ▹ .member)) : LeCo s

/-- A structural recipe for exposing a member.  The inclusion is checked as a
view from the path's actual type to `{ A : lower .. upper }`; exposure never
runs declarative source subtyping. -/
inductive Exposure : Sig → Type where
  | view {s : Sig} (path : BVar s .term) (label : Name)
      (lower upper : Source.Ty s) (inclusion : LeCo s) : Exposure s

/-- A function-specific adjustment from an actual context to a view context.
`function domain` says that the two outer contexts are identical and that the
newest term binder is viewed through `domain`.  The newest path remains
`.here`; no second actual/view variable is introduced. -/
inductive CtxMor : Sig → Type where
  | refl {s : Sig} : CtxMor s
  | function {s : Sig} (domain : LeCo s) : CtxMor (s ▹ .term)

/-- Explicitly coerced ANF terms.  There is no implicit subsumption form.

`letExact A T e` binds, in order, an exact object `x : {A : T .. T}` and a
private equality `phi : x.A ≃ T`; the equality is the newest binder in `e`.
It cannot occur in the result type and is erased with the type definition. -/
inductive Tm : Sig → Type where
  | var {s : Sig} (path : BVar s .term) : Tm s
  | lam {s : Sig} (domain : Source.Ty s) (body : Tm (s ▹ .term)) : Tm s
  | obj {s : Sig} (label : Name) (witness : Source.Ty s) : Tm s
  | app {s : Sig} (function argument : BVar s .term)
      (functionView argumentView : LeCo s) : Tm s
  | let' {s : Sig} (rhs : Tm s) (body : Tm (s ▹ .term)) : Tm s
  | cast {s : Sig} (term : Tm s) (inclusion : LeCo s) : Tm s
  | letHandle {s : Sig} (exposure : Exposure s)
      (body : Tm (s ▹ .member)) : Tm s
  | letExact {s : Sig} (label : Name) (witness : Source.Ty s)
      (body : Tm ((s ▹ .term) ▹ .evidence .equality)) : Tm s

end

deriving instance DecidableEq for EqCo, LeCo, Exposure, CtxMor, Tm

mutual

/-- Rename equality evidence. -/
def EqCo.rename {s₁ s₂ : Sig} (evidence : EqCo s₁) (rho : Rename s₁ s₂) :
    EqCo s₂ :=
  match evidence with
  | .var evidenceVar => .var (rho.var evidenceVar)
  | .refl type => .refl (type.rename rho)
  | .symm inner => .symm (inner.rename rho)
  | .trans left right => .trans (left.rename rho) (right.rename rho)

/-- Rename directed inclusion evidence and lift under its handle and function
binders. -/
def LeCo.rename {s₁ s₂ : Sig} (evidence : LeCo s₁) (rho : Rename s₁ s₂) :
    LeCo s₂ :=
  match evidence with
  | .var evidenceVar => .var (rho.var evidenceVar)
  | .refl type => .refl (type.rename rho)
  | .trans left right => .trans (left.rename rho) (right.rename rho)
  | .top source => .top (source.rename rho)
  | .bot target => .bot (target.rename rho)
  | .eqToLe equality => .eqToLe (equality.rename rho)
  | .member label lower upper =>
      .member label (lower.rename rho) (upper.rename rho)
  | .all domain view codomain =>
      .all (domain.rename rho) (view.renameLift rho) (codomain.rename rho.lift)
  | .lower handle => .lower (rho.var handle)
  | .upper handle => .upper (rho.var handle)
  | .letHandle exposure body =>
      .letHandle (exposure.rename rho) (body.rename rho.lift)

/-- Rename an exposure recipe. -/
def Exposure.rename {s₁ s₂ : Sig} (exposure : Exposure s₁)
    (rho : Rename s₁ s₂) : Exposure s₂ :=
  match exposure with
  | .view path label lower upper inclusion =>
      .view (rho.var path) label (lower.rename rho) (upper.rename rho)
        (inclusion.rename rho)

/-- Rename a function context morphism along the corresponding renaming of
its outer context.  This is total for exactly the shape stored by `LeCo.all`;
an arbitrary renaming of a telescope morphism would not preserve its newest
binder. -/
def CtxMor.renameLift {s₁ s₂ : Sig} (morphism : CtxMor (s₁ ▹ .term))
    (rho : Rename s₁ s₂) : CtxMor (s₂ ▹ .term) :=
  match morphism with
  | .refl => .refl
  | .function domain => .function (domain.rename rho)

/-- Rename an explicitly coerced term. -/
def Tm.rename {s₁ s₂ : Sig} (term : Tm s₁) (rho : Rename s₁ s₂) :
    Tm s₂ :=
  match term with
  | .var path => .var (rho.var path)
  | .lam domain body => .lam (domain.rename rho) (body.rename rho.lift)
  | .obj label witness => .obj label (witness.rename rho)
  | .app function argument functionView argumentView =>
      .app (rho.var function) (rho.var argument)
        (functionView.rename rho) (argumentView.rename rho)
  | .let' rhs body => .let' (rhs.rename rho) (body.rename rho.lift)
  | .cast term inclusion => .cast (term.rename rho) (inclusion.rename rho)
  | .letHandle exposure body =>
      .letHandle (exposure.rename rho) (body.rename rho.lift)
  | .letExact label witness body =>
      .letExact label (witness.rename rho) (body.rename rho.lift.lift)

end

namespace EqCo

def weaken {s : Sig} {kind : BinderKind} (evidence : EqCo s) : EqCo (s ▹ kind) :=
  evidence.rename Rename.succ

end EqCo

namespace LeCo

def weaken {s : Sig} {kind : BinderKind} (evidence : LeCo s) : LeCo (s ▹ kind) :=
  evidence.rename Rename.succ

end LeCo

namespace Exposure

def weaken {s : Sig} {kind : BinderKind} (exposure : Exposure s) :
    Exposure (s ▹ kind) :=
  exposure.rename Rename.succ

end Exposure

namespace CtxMor

/-- Weaken the outer context below a new binder while retaining the newest
function binder. -/
def weakenBase {s : Sig} {kind : BinderKind}
    (morphism : CtxMor (s ▹ .term)) : CtxMor ((s ▹ kind) ▹ .term) :=
  morphism.renameLift (Rename.succ (k := kind))

/-- The context adjustment used by dependent-function inclusion.  The new
argument keeps the identity `.here`, while the domain inclusion is weakened
under that argument binder. -/
def functionView {s : Sig} (domain : LeCo s) : CtxMor (s ▹ .term) :=
  .function domain

end CtxMor

namespace Tm

def weaken {s : Sig} {kind : BinderKind} (term : Tm s) : Tm (s ▹ kind) :=
  term.rename Rename.succ

end Tm

/-! The following constructor equations are the core reduction laws used by
the checker and elaborator. -/

@[simp] theorem EqCo.rename_var {s₁ s₂ : Sig}
    (evidenceVar : BVar s₁ (.evidence .equality)) (rho : Rename s₁ s₂) :
    (EqCo.var evidenceVar).rename rho = .var (rho.var evidenceVar) := rfl

@[simp] theorem EqCo.rename_refl {s₁ s₂ : Sig} (type : Source.Ty s₁)
    (rho : Rename s₁ s₂) :
    (EqCo.refl type).rename rho = .refl (type.rename rho) := rfl

@[simp] theorem EqCo.rename_symm {s₁ s₂ : Sig} (evidence : EqCo s₁)
    (rho : Rename s₁ s₂) :
    (EqCo.symm evidence).rename rho = .symm (evidence.rename rho) := rfl

@[simp] theorem EqCo.rename_trans {s₁ s₂ : Sig} (left right : EqCo s₁)
    (rho : Rename s₁ s₂) :
    (EqCo.trans left right).rename rho =
      .trans (left.rename rho) (right.rename rho) := rfl

@[simp] theorem LeCo.rename_lower {s₁ s₂ : Sig}
    (handle : BVar s₁ .member) (rho : Rename s₁ s₂) :
    (LeCo.lower handle).rename rho = .lower (rho.var handle) := by
  simp [LeCo.rename]

@[simp] theorem LeCo.rename_upper {s₁ s₂ : Sig}
    (handle : BVar s₁ .member) (rho : Rename s₁ s₂) :
    (LeCo.upper handle).rename rho = .upper (rho.var handle) := by
  simp [LeCo.rename]

@[simp] theorem LeCo.rename_letHandle {s₁ s₂ : Sig}
    (exposure : Exposure s₁) (body : LeCo (s₁ ▹ .member))
    (rho : Rename s₁ s₂) :
    (LeCo.letHandle exposure body).rename rho =
      .letHandle (exposure.rename rho) (body.rename rho.lift) := by
  simp [LeCo.rename]

@[simp] theorem LeCo.rename_all {s₁ s₂ : Sig} (domain : LeCo s₁)
    (view : CtxMor (s₁ ▹ .term)) (codomain : LeCo (s₁ ▹ .term))
    (rho : Rename s₁ s₂) :
    (LeCo.all domain view codomain).rename rho =
      .all (domain.rename rho) (view.renameLift rho) (codomain.rename rho.lift) := by
  simp [LeCo.rename]

@[simp] theorem Exposure.rename_view {s₁ s₂ : Sig}
    (path : BVar s₁ .term) (label : Name) (lower upper : Source.Ty s₁)
    (inclusion : LeCo s₁) (rho : Rename s₁ s₂) :
    (Exposure.view path label lower upper inclusion).rename rho =
      .view (rho.var path) label (lower.rename rho) (upper.rename rho)
        (inclusion.rename rho) := by
  simp [Exposure.rename]

@[simp] theorem CtxMor.renameLift_function {s₁ s₂ : Sig}
    (domain : LeCo s₁) (rho : Rename s₁ s₂) :
    (CtxMor.function domain).renameLift rho =
      .function (domain.rename rho) := by
  simp [CtxMor.renameLift]

@[simp] theorem CtxMor.renameLift_refl {s₁ s₂ : Sig}
    (rho : Rename s₁ s₂) :
    (CtxMor.refl : CtxMor (s₁ ▹ .term)).renameLift rho = .refl := by
  exact CtxMor.renameLift.eq_1 rho

@[simp] theorem Tm.rename_letHandle {s₁ s₂ : Sig}
    (exposure : Exposure s₁) (body : Tm (s₁ ▹ .member))
    (rho : Rename s₁ s₂) :
    (Tm.letHandle exposure body).rename rho =
      .letHandle (exposure.rename rho) (body.rename rho.lift) := rfl

@[simp] theorem Tm.rename_letExact {s₁ s₂ : Sig} (label : Name)
    (witness : Source.Ty s₁)
    (body : Tm ((s₁ ▹ .term) ▹ .evidence .equality))
    (rho : Rename s₁ s₂) :
    (Tm.letExact label witness body).rename rho =
      .letExact label (witness.rename rho) (body.rename rho.lift.lift) := rfl

end DotFC.Explicit
