import Coercions.DOT.Acyclic.Scope

/-!
# The acyclic ANF DOT source language

This is the acyclic `D_<:`-like source subcalculus.  It
uses the ANF, call-by-value, variable-selection discipline of *The Essence of
Dependent Object Types* and *A Simple Soundness Proof for Dependent Object
Types*, while deliberately removing fields, intersections, recursive self
types, and general paths.  It is a tailored subfragment, not a claim to be a
verbatim mechanization of either published calculus.

The fragment has dependent functions and one type member per object.  Labels
are nevertheless explicit: the stable identity eliminated by the Stage B
translation is the pair `(path, label)`, not merely the path.

Every syntactic category uses `DotFC.Sig`.  Source types contain only stable
term-variable paths, so opening a dependent codomain substitutes an existing
term variable rather than an arbitrary term.
-/

namespace DotFC.Source

/-- Source member labels. -/
abbrev Name : Type := Nat

/-- Types of the acyclic, selection-bearing source calculus. -/
inductive Ty : Sig → Type where
  | top {s : Sig} : Ty s
  | bot {s : Sig} : Ty s
  | all {s : Sig} (domain : Ty s) (codomain : Ty (s ▹ .term)) : Ty s
  | member {s : Sig} (label : Name) (lower upper : Ty s) : Ty s
  | sel {s : Sig} (path : BVar s .term) (label : Name) : Ty s
deriving DecidableEq

/-- Administrative-normal-form source terms.  Applications have variable
operands.  An object contains an exact type definition and no term field. -/
inductive Tm : Sig → Type where
  | var {s : Sig} (x : BVar s .term) : Tm s
  | lam {s : Sig} (domain : Ty s) (body : Tm (s ▹ .term)) : Tm s
  | obj {s : Sig} (label : Name) (witness : Ty s) : Tm s
  | app {s : Sig} (function argument : BVar s .term) : Tm s
  | let' {s : Sig} (rhs : Tm s) (body : Tm (s ▹ .term)) : Tm s

namespace Ty

/-- An exact member declaration is an interval with identical bounds. -/
def exact {s : Sig} (label : Name) (witness : Ty s) : Ty s :=
  .member label witness witness

/-- Rename every stable path in a type. -/
def rename {s₁ s₂ : Sig} (type : Ty s₁) (ρ : Rename s₁ s₂) :
    Ty s₂ :=
  match type with
  | .top => .top
  | .bot => .bot
  | .all domain codomain =>
      .all (rename domain ρ) (rename codomain ρ.lift)
  | .member label lower upper =>
      .member label (rename lower ρ) (rename upper ρ)
  | .sel path label => .sel (ρ.var path) label

/-- Weaken a type below a new binder of any kind. -/
def weaken {s : Sig} {kind : BinderKind} (type : Ty s) : Ty (s ▹ kind) :=
  type.rename Rename.succ

end Ty

namespace Tm

/-- Rename every variable in a source term and its annotations. -/
def rename {s₁ s₂ : Sig} (term : Tm s₁) (ρ : Rename s₁ s₂) :
    Tm s₂ :=
  match term with
  | .var x => .var (ρ.var x)
  | .lam domain body =>
      .lam (domain.rename ρ) (rename body ρ.lift)
  | .obj label witness => .obj label (witness.rename ρ)
  | .app function argument =>
      .app (ρ.var function) (ρ.var argument)
  | .let' rhs body => .let' (rename rhs ρ) (rename body ρ.lift)

/-- Weaken a term below a new binder of any kind. -/
def weaken {s : Sig} {kind : BinderKind} (term : Tm s) : Tm (s ▹ kind) :=
  term.rename Rename.succ

end Tm

namespace Rename

/-- Replace the newest term binder by an existing stable path.  Variables of
all other kinds can only come from the older signature and pass through. -/
def openAt {s : Sig} (path : BVar s .term) : Rename (s ▹ .term) s where
  var := fun
    | .here => path
    | .there x => x

@[simp]
theorem openAt_here {s : Sig} (path : BVar s .term) :
    (openAt path).var (.here : BVar (s ▹ .term) .term) = path := rfl

@[simp]
theorem openAt_there {s : Sig} (path : BVar s .term)
    {kind : BinderKind} (x : BVar s kind) :
    (openAt path).var (.there x : BVar (s ▹ .term) kind) = x := rfl

end Rename

namespace Ty

/-- Open a dependent type by replacing its newest binder with a stable path. -/
def «open» {s : Sig} (type : Ty (s ▹ .term)) (path : BVar s .term) : Ty s :=
  type.rename (Rename.openAt path)

@[simp]
theorem rename_top {s₁ s₂ : Sig} (ρ : Rename s₁ s₂) :
    (top : Ty s₁).rename ρ = top := rfl

@[simp]
theorem rename_bot {s₁ s₂ : Sig} (ρ : Rename s₁ s₂) :
    (bot : Ty s₁).rename ρ = bot := rfl

@[simp]
theorem rename_all {s₁ s₂ : Sig} (domain : Ty s₁)
    (codomain : Ty (s₁ ▹ .term)) (ρ : Rename s₁ s₂) :
    (all domain codomain).rename ρ =
      all (domain.rename ρ) (codomain.rename ρ.lift) := rfl

@[simp]
theorem rename_member {s₁ s₂ : Sig} (label : Name) (lower upper : Ty s₁)
    (ρ : Rename s₁ s₂) :
    (member label lower upper).rename ρ =
      member label (lower.rename ρ) (upper.rename ρ) := rfl

@[simp]
theorem rename_sel {s₁ s₂ : Sig} (path : BVar s₁ .term)
    (label : Name) (ρ : Rename s₁ s₂) :
    (sel path label).rename ρ = sel (ρ.var path) label := rfl

@[simp]
theorem rename_id {s : Sig} (type : Ty s) :
    type.rename Rename.id = type := by
  induction type with
  | top => rfl
  | bot => rfl
  | all domain codomain ihDomain ihCodomain =>
      simp only [rename_all, Rename.lift_id, ihDomain, ihCodomain]
  | member label lower upper ihLower ihUpper =>
      simp only [rename_member, ihLower, ihUpper]
  | sel path label => rfl

@[simp]
theorem rename_comp {s₁ s₂ s₃ : Sig} (type : Ty s₁)
    (ρ₁ : Rename s₁ s₂) (ρ₂ : Rename s₂ s₃) :
    (type.rename ρ₁).rename ρ₂ =
      type.rename (ρ₁.comp ρ₂) := by
  induction type generalizing s₂ s₃ with
  | top => rfl
  | bot => rfl
  | all domain codomain ihDomain ihCodomain =>
      simp only [rename_all, ihDomain, ihCodomain, Rename.lift_comp]
  | member label lower upper ihLower ihUpper =>
      simp only [rename_member, ihLower, ihUpper]
  | sel path label => rfl

@[simp]
theorem open_sel_here {s : Sig} (label : Name) (path : BVar s .term) :
    (sel (.here : BVar (s ▹ .term) .term) label).open path = sel path label := rfl

@[simp]
theorem open_sel_there {s : Sig} (label : Name) (x path : BVar s .term) :
    (sel (.there x : BVar (s ▹ .term) .term) label).open path = sel x label := rfl

end Ty

namespace Tm

@[simp]
theorem rename_id {s : Sig} (term : Tm s) :
    term.rename Rename.id = term := by
  induction term with
  | var x => rfl
  | lam domain body ih =>
      simp only [rename, Ty.rename_id, Rename.lift_id, ih]
  | obj label witness => simp only [rename, Ty.rename_id]
  | app function argument => rfl
  | let' rhs body ihRhs ihBody =>
      simp only [rename, Rename.lift_id, ihRhs, ihBody]

@[simp]
theorem rename_comp {s₁ s₂ s₃ : Sig} (term : Tm s₁)
    (ρ₁ : Rename s₁ s₂) (ρ₂ : Rename s₂ s₃) :
    (term.rename ρ₁).rename ρ₂ =
      term.rename (ρ₁.comp ρ₂) := by
  induction term generalizing s₂ s₃ with
  | var x => rfl
  | lam domain body ih =>
      simp only [rename, Ty.rename_comp, ih, Rename.lift_comp]
  | obj label witness => simp only [rename, Ty.rename_comp]
  | app function argument => rfl
  | let' rhs body ihRhs ihBody =>
      simp only [rename, ihRhs, ihBody, Rename.lift_comp]

end Tm

end DotFC.Source
