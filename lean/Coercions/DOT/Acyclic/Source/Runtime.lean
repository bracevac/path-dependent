import Coercions.DOT.Acyclic.Source.Typing

/-!
# Erased call-by-value runtime

Typed source syntax is intentionally not closed under substitution of values:
substituting a lambda or object for `x` in `x.A` would violate the
variable-only path restriction.  Runtime behavior is therefore defined on this
intrinsically scoped erasure, where all types and selections have disappeared
and ordinary value substitution is well formed.
-/

namespace DotFC.Source.Runtime

/-- Untyped runtime terms.  Unlike source ANF applications, runtime
applications accept arbitrary terms because beta and let reduction substitute
values into them. -/
inductive Tm : Sig → Type where
  | var {s : Sig} (x : BVar s .term) : Tm s
  | lam {s : Sig} (body : Tm (s ▹ .term)) : Tm s
  | obj {s : Sig} : Tm s
  | app {s : Sig} (function argument : Tm s) : Tm s
  | let' {s : Sig} (rhs : Tm s) (body : Tm (s ▹ .term)) : Tm s
deriving DecidableEq

namespace Tm

/-- Rename the free term variables of a runtime term. -/
def rename {s₁ s₂ : Sig} (term : Tm s₁) (ρ : Rename s₁ s₂) : Tm s₂ :=
  match term with
  | .var x => .var (ρ.var x)
  | .lam body => .lam (rename body ρ.lift)
  | .obj => .obj
  | .app function argument => .app (rename function ρ) (rename argument ρ)
  | .let' rhs body => .let' (rename rhs ρ) (rename body ρ.lift)

/-- Weaken a runtime term below a new binder of any kind. -/
def weaken {s : Sig} {kind : BinderKind} (term : Tm s) : Tm (s ▹ kind) :=
  term.rename Rename.succ

@[simp]
theorem rename_id {s : Sig} (term : Tm s) : term.rename Rename.id = term := by
  induction term with
  | var x => rfl
  | lam body ih => simp only [rename, Rename.lift_id, ih]
  | obj => rfl
  | app function argument ihFunction ihArgument =>
      simp only [rename, ihFunction, ihArgument]
  | let' rhs body ihRhs ihBody =>
      simp only [rename, Rename.lift_id, ihRhs, ihBody]

@[simp]
theorem rename_comp {s₁ s₂ s₃ : Sig} (term : Tm s₁)
    (ρ₁ : Rename s₁ s₂) (ρ₂ : Rename s₂ s₃) :
    (term.rename ρ₁).rename ρ₂ = term.rename (ρ₁.comp ρ₂) := by
  induction term generalizing s₂ s₃ with
  | var x => rfl
  | lam body ih => simp only [rename, ih, Rename.lift_comp]
  | obj => rfl
  | app function argument ihFunction ihArgument =>
      simp only [rename, ihFunction, ihArgument]
  | let' rhs body ihRhs ihBody =>
      simp only [rename, ihRhs, ihBody, Rename.lift_comp]

end Tm

/-- A simultaneous substitution of arbitrary runtime terms for term
variables.  Other binder kinds share the signature but do not occur in erased
terms. -/
structure Subst (s₁ s₂ : Sig) where
  var : BVar s₁ .term → Tm s₂

namespace Subst

/-- Substitutions are equal when they agree on every term variable. -/
@[ext]
theorem ext {s₁ s₂ : Sig} {first second : Subst s₁ s₂}
    (equal : ∀ x, first.var x = second.var x) : first = second := by
  cases first
  cases second
  congr
  funext x
  exact equal x

/-- The identity runtime substitution. -/
def id {s : Sig} : Subst s s where
  var := Tm.var

/-- Regard a heterogeneous renaming as a runtime substitution. -/
def ofRename {s₁ s₂ : Sig} (ρ : Rename s₁ s₂) : Subst s₁ s₂ where
  var := fun x => .var (ρ.var x)

/-- Lift a substitution below a term binder. -/
def lift {s₁ s₂ : Sig} (substitution : Subst s₁ s₂) :
    Subst (s₁ ▹ .term) (s₂ ▹ .term) where
  var := fun
    | .here => .var .here
    | .there x => (substitution.var x).weaken

@[simp]
theorem lift_id {s : Sig} :
    (id (s := s)).lift = (id : Subst (s ▹ .term) (s ▹ .term)) := by
  apply ext
  intro x
  cases x <;> rfl

/-- Replace the newest term binder with an arbitrary runtime term. -/
def openAt {s : Sig} (replacement : Tm s) : Subst (s ▹ .term) s where
  var := fun
    | .here => replacement
    | .there x => .var x

@[simp]
theorem lift_here {s₁ s₂ : Sig} (substitution : Subst s₁ s₂) :
    substitution.lift.var (.here : BVar (s₁ ▹ .term) .term) =
      (.var .here : Tm (s₂ ▹ .term)) := rfl

@[simp]
theorem lift_there {s₁ s₂ : Sig} (substitution : Subst s₁ s₂)
    (x : BVar s₁ .term) :
    substitution.lift.var (.there x) = (substitution.var x).weaken := rfl

@[simp]
theorem openAt_here {s : Sig} (replacement : Tm s) :
    (openAt replacement).var (.here : BVar (s ▹ .term) .term) = replacement := rfl

@[simp]
theorem openAt_there {s : Sig} (replacement : Tm s) (x : BVar s .term) :
    (openAt replacement).var (.there x) = (.var x : Tm s) := rfl

end Subst

namespace Tm

/-- Capture-avoiding simultaneous runtime substitution. -/
def subst {s₁ s₂ : Sig} (term : Tm s₁) (substitution : Subst s₁ s₂) :
    Tm s₂ :=
  match term with
  | .var x => substitution.var x
  | .lam body => .lam (subst body substitution.lift)
  | .obj => .obj
  | .app function argument =>
      .app (subst function substitution) (subst argument substitution)
  | .let' rhs body => .let' (subst rhs substitution) (subst body substitution.lift)

/-- Open the newest runtime binder with an arbitrary value or term. -/
def «open» {s : Sig} (body : Tm (s ▹ .term)) (replacement : Tm s) : Tm s :=
  body.subst (Subst.openAt replacement)

@[simp]
theorem subst_id {s : Sig} (term : Tm s) : term.subst Subst.id = term := by
  induction term with
  | var x => rfl
  | lam body ih => simp only [subst, Subst.lift_id, ih]
  | obj => rfl
  | app function argument ihFunction ihArgument =>
      simp only [subst, ihFunction, ihArgument]
  | let' rhs body ihRhs ihBody =>
      simp only [subst, Subst.lift_id, ihRhs, ihBody]

end Tm

/-- Runtime values.  The object is a unit-like tag: its exact type witness was
static and has been erased. -/
inductive IsValue : {s : Sig} → Tm s → Prop where
  | lam {s : Sig} {body : Tm (s ▹ .term)} : IsValue (.lam body)
  | obj {s : Sig} : IsValue (.obj : Tm s)

/-- Standard left-to-right call-by-value reduction. -/
inductive Step : {s : Sig} → Tm s → Tm s → Prop where
  | appFunction {s : Sig} {function function' argument : Tm s}
      (step : Step function function') :
      Step (.app function argument) (.app function' argument)
  | appArgument {s : Sig} {function argument argument' : Tm s}
      (functionValue : IsValue function) (step : Step argument argument') :
      Step (.app function argument) (.app function argument')
  | beta {s : Sig} {body : Tm (s ▹ .term)} {argument : Tm s}
      (argumentValue : IsValue argument) :
      Step (.app (.lam body) argument) (body.open argument)
  | letRhs {s : Sig} {rhs rhs' : Tm s} {body : Tm (s ▹ .term)}
      (step : Step rhs rhs') : Step (.let' rhs body) (.let' rhs' body)
  | zeta {s : Sig} {rhs : Tm s} {body : Tm (s ▹ .term)}
      (rhsValue : IsValue rhs) : Step (.let' rhs body) (body.open rhs)

/-- Reflexive-transitive closure of runtime reduction. -/
inductive Steps : {s : Sig} → Tm s → Tm s → Prop where
  | refl {s : Sig} {term : Tm s} : Steps term term
  | tail {s : Sig} {first second third : Tm s}
      (steps : Steps first second) (step : Step second third) : Steps first third

end DotFC.Source.Runtime

namespace DotFC.Source.Tm

/-- Erase all source types and convert ANF variable applications to ordinary
runtime applications. -/
def erase {s : Sig} (term : Tm s) : Runtime.Tm s :=
  match term with
  | .var x => .var x
  | .lam _ body => .lam (erase body)
  | .obj _ _ => .obj
  | .app function argument => .app (.var function) (.var argument)
  | .let' rhs body => .let' (erase rhs) (erase body)

@[simp]
theorem erase_var {s : Sig} (x : BVar s .term) :
    (Tm.var x).erase = Runtime.Tm.var x := rfl

@[simp]
theorem erase_lam {s : Sig} (domain : Ty s) (body : Tm (s ▹ .term)) :
    (Tm.lam domain body).erase = Runtime.Tm.lam body.erase := rfl

@[simp]
theorem erase_obj {s : Sig} (label : Name) (witness : Ty s) :
    (Tm.obj label witness).erase = (Runtime.Tm.obj : Runtime.Tm s) := rfl

@[simp]
theorem erase_app {s : Sig} (function argument : BVar s .term) :
    (Tm.app function argument).erase =
      Runtime.Tm.app (.var function) (.var argument) := rfl

@[simp]
theorem erase_let {s : Sig} (rhs : Tm s) (body : Tm (s ▹ .term)) :
    (Tm.let' rhs body).erase = Runtime.Tm.let' rhs.erase body.erase := rfl

end DotFC.Source.Tm
