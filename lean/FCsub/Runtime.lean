import FCsub.Scope

/-!
# Erased FCsub runtime

The runtime is deliberately owned by `FCsub`.  Its terms retain only ordinary
term variables, functions, unit, application, and let.  Type names, constraint
evidence, telescope abstraction/application, packages, and casts are erased
before execution.
-/

namespace FCsub.Runtime

open FCsub

/-- Untyped call-by-value runtime terms, indexed by the FCsub scope solely to
retain intrinsic scoping of term variables. -/
inductive Tm : Sig → Type where
  | var {s : Sig} (index : BVar s .term) : Tm s
  | lam {s : Sig} (body : Tm (s ▹ .term)) : Tm s
  | unit {s : Sig} : Tm s
  | app {s : Sig} (function argument : Tm s) : Tm s
  | let' {s : Sig} (rhs : Tm s) (body : Tm (s ▹ .term)) : Tm s
deriving DecidableEq

namespace Tm

/-- Rename all free runtime variables. -/
def rename {s₁ s₂ : Sig} (term : Tm s₁) (rho : Rename s₁ s₂) :
    Tm s₂ :=
  match term with
  | .var index => .var (rho.var index)
  | .lam body => .lam (rename body rho.lift)
  | .unit => .unit
  | .app function argument =>
      .app (rename function rho) (rename argument rho)
  | .let' rhs body => .let' (rename rhs rho) (rename body rho.lift)

def weaken {s : Sig} {kind : BinderKind} (term : Tm s) : Tm (s ▹ kind) :=
  term.rename Rename.succ

@[simp]
theorem rename_id {s : Sig} (term : Tm s) : term.rename Rename.id = term := by
  induction term with
  | var index => rfl
  | lam body ih => simp only [rename, Rename.lift_id, ih]
  | unit => rfl
  | app function argument ihFunction ihArgument =>
      simp only [rename, ihFunction, ihArgument]
  | let' rhs body ihRhs ihBody =>
      simp only [rename, Rename.lift_id, ihRhs, ihBody]

@[simp]
theorem rename_comp {s₁ s₂ s₃ : Sig} (term : Tm s₁)
    (first : Rename s₁ s₂) (second : Rename s₂ s₃) :
    (term.rename first).rename second = term.rename (first.comp second) := by
  induction term generalizing s₂ s₃ with
  | var index => rfl
  | lam body ih => simp only [rename, ih, Rename.lift_comp]
  | unit => rfl
  | app function argument ihFunction ihArgument =>
      simp only [rename, ihFunction, ihArgument]
  | let' rhs body ihRhs ihBody =>
      simp only [rename, ihRhs, ihBody, Rename.lift_comp]

end Tm

/-- Simultaneous substitution of runtime terms for term variables. -/
structure Subst (source target : Sig) where
  var : BVar source .term → Tm target

namespace Subst

@[ext]
theorem ext {s₁ s₂ : Sig} {first second : Subst s₁ s₂}
    (equal : ∀ index, first.var index = second.var index) : first = second := by
  cases first
  cases second
  congr
  funext index
  exact equal index

def id {s : Sig} : Subst s s where
  var := Tm.var

def ofRename {s₁ s₂ : Sig} (rho : Rename s₁ s₂) :
    Subst s₁ s₂ where
  var := fun index => .var (rho.var index)

def lift {s₁ s₂ : Sig} (substitution : Subst s₁ s₂) :
    Subst (s₁ ▹ .term) (s₂ ▹ .term) where
  var := fun
    | .here => .var .here
    | .there older => (substitution.var older).weaken

def openAt {s : Sig} (replacement : Tm s) : Subst (s ▹ .term) s where
  var := fun
    | .here => replacement
    | .there older => .var older

/-- Erase a sequence of abstract type-name binders. -/
def dropTypes {scope : Sig} : (names : Nat) → Subst (TypeScope scope names) scope
  | 0 => id
  | names + 1 =>
      { var := fun
          | .there older => (dropTypes names).var older }

/-- Erase all names and directed-evidence binders of a static telescope. -/
def dropStatic {scope : Sig} (names : Nat) :
    (constraints : Nat) → Subst (StaticScope scope names constraints) scope
  | 0 => dropTypes names
  | constraints + 1 =>
      { var := fun
          | .there older => (dropStatic names constraints).var older }

/-- Erase a complete package-opening scope while preserving its separate
payload as the newest runtime term variable. -/
def dropPayload {scope : Sig} (names constraints : Nat) :
    Subst (PayloadScope scope names constraints) (scope ▹ .term) where
  var := fun
    | .here => .var .here
    | .there older => (dropStatic names constraints).var older |>.weaken

/-- Erase a private type name and its equality witness. -/
def dropNewtype {scope : Sig} : Subst (NewtypeScope scope) scope where
  var := fun
    | .there (.there older) => .var older

@[simp]
theorem lift_id {s : Sig} :
    (id (s := s)).lift = (id : Subst (s ▹ .term) (s ▹ .term)) := by
  apply ext
  intro index
  cases index <;> simp [lift, id, Tm.weaken, Tm.rename]

@[simp]
theorem dropPayload_here {scope : Sig} (names constraints : Nat) :
    (dropPayload (scope := scope) names constraints).var
      (.here : BVar (PayloadScope scope names constraints) .term) =
      (.var .here : Tm (scope ▹ .term)) := rfl

end Subst

namespace Tm

def subst {s₁ s₂ : Sig} (term : Tm s₁) (substitution : Subst s₁ s₂) :
    Tm s₂ :=
  match term with
  | .var index => substitution.var index
  | .lam body => .lam (subst body substitution.lift)
  | .unit => .unit
  | .app function argument =>
      .app (subst function substitution) (subst argument substitution)
  | .let' rhs body =>
      .let' (subst rhs substitution) (subst body substitution.lift)

def «open» (body : Tm (s ▹ .term)) (replacement : Tm s) : Tm s :=
  body.subst (Subst.openAt replacement)

@[simp]
theorem subst_id {s : Sig} (term : Tm s) : term.subst Subst.id = term := by
  induction term with
  | var index => rfl
  | lam body ih => simp only [subst, Subst.lift_id, ih]
  | unit => rfl
  | app function argument ihFunction ihArgument =>
      simp only [subst, ihFunction, ihArgument]
  | let' rhs body ihRhs ihBody =>
      simp only [subst, Subst.lift_id, ihRhs, ihBody]

end Tm

inductive IsValue : {s : Sig} → Tm s → Prop where
  | lam {s : Sig} {body : Tm (s ▹ .term)} : IsValue (.lam body)
  | unit {s : Sig} : IsValue (.unit : Tm s)

/-- Deterministic, left-to-right call-by-value reduction. -/
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

inductive Steps : {s : Sig} → Tm s → Tm s → Prop where
  | refl {s : Sig} {term : Tm s} : Steps term term
  | tail {s : Sig} {first second third : Tm s}
      (steps : Steps first second) (step : Step second third) : Steps first third

end FCsub.Runtime
