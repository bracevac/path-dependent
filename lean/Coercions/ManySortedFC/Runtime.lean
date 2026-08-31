/-!
# Erased runtime for the many-sorted coercion calculus

The runtime retains ordinary term variables, unit, functions, application,
let, and primitive suspension. Static names, constraints, evidence, and
adapters are absent by construction. A suspension is a value regardless of
its body; forcing it is the only operation that starts evaluating that body.

Runtime scopes count term binders directly. This keeps the runtime independent
of the source calculus and of the target's heterogeneous static scope while
still giving erasure an intrinsically scoped destination.
-/

namespace ManySortedFC.Runtime

/-! ## Renamings -/

/-- A renaming of intrinsically scoped runtime variables. -/
abbrev Renaming (source target : Nat) : Type := Fin source -> Fin target

namespace Renaming

/-- Identity renaming. -/
def id {scope : Nat} : Renaming scope scope := fun index => index

/-- Diagrammatic composition: apply `first`, then `second`. -/
def comp {first middle last : Nat} (firstRenaming : Renaming first middle)
    (secondRenaming : Renaming middle last) : Renaming first last :=
  fun index => secondRenaming (firstRenaming index)

/-- Preserve the newest variable while renaming every older variable. -/
def lift {source target : Nat} (rho : Renaming source target) :
    Renaming (Nat.succ source) (Nat.succ target) :=
  Fin.cases 0 (fun index => (rho index).succ)

/-- Weaken a scope below one fresh term binder. -/
def weaken {scope : Nat} : Renaming scope (Nat.succ scope) := Fin.succ

@[simp]
theorem id_apply {scope : Nat} (index : Fin scope) :
    (id (scope := scope)) index = index := rfl

@[simp]
theorem comp_apply {first middle last : Nat}
    (firstRenaming : Renaming first middle)
    (secondRenaming : Renaming middle last) (index : Fin first) :
    comp firstRenaming secondRenaming index =
      secondRenaming (firstRenaming index) := rfl

@[simp]
theorem lift_id {scope : Nat} :
    lift (id (scope := scope)) = id := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro older
    rfl

@[simp]
theorem lift_comp {first middle last : Nat}
    (firstRenaming : Renaming first middle)
    (secondRenaming : Renaming middle last) :
    lift (comp firstRenaming secondRenaming) =
      comp (lift firstRenaming) (lift secondRenaming) := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro older
    rfl

end Renaming

/-! ## Terms and structural operations -/

/-- Untyped call-by-value runtime terms, intrinsically scoped by the number of
ordinary term binders in scope. -/
inductive Tm : Nat -> Type where
  | var {scope : Nat} (index : Fin scope) : Tm scope
  | unit {scope : Nat} : Tm scope
  | lam {scope : Nat} (body : Tm (Nat.succ scope)) : Tm scope
  | app {scope : Nat} (function argument : Tm scope) : Tm scope
  | let' {scope : Nat} (rhs : Tm scope)
      (body : Tm (Nat.succ scope)) : Tm scope
  /-- Delay a computation without evaluating its body. -/
  | suspend {scope : Nat} (body : Tm scope) : Tm scope
  /-- Evaluate a suspension-producing computation and then run its body. -/
  | force {scope : Nat} (suspension : Tm scope) : Tm scope
deriving DecidableEq

namespace Tm

/-- Rename every free term variable. -/
def rename {source target : Nat} (term : Tm source)
    (rho : Renaming source target) : Tm target :=
  match term with
  | .var index => .var (rho index)
  | .unit => .unit
  | .lam body => .lam (body.rename rho.lift)
  | .app function argument =>
      .app (function.rename rho) (argument.rename rho)
  | .let' rhs body =>
      .let' (rhs.rename rho) (body.rename rho.lift)
  | .suspend body => .suspend (body.rename rho)
  | .force suspension => .force (suspension.rename rho)

/-- Weaken a runtime term below one fresh term binder. -/
def weaken {scope : Nat} (term : Tm scope) : Tm (Nat.succ scope) :=
  term.rename Renaming.weaken

@[simp]
theorem rename_id {scope : Nat} (term : Tm scope) :
    term.rename Renaming.id = term := by
  induction term with
  | var index => rfl
  | unit => rfl
  | lam body induction =>
      simp only [rename, Renaming.lift_id, induction]
  | app function argument functionInduction argumentInduction =>
      simp only [rename, functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp only [rename, Renaming.lift_id, rhsInduction, bodyInduction]
  | suspend body induction =>
      simp only [rename, induction]
  | force suspension induction =>
      simp only [rename, induction]

@[simp]
theorem rename_comp {first middle last : Nat} (term : Tm first)
    (firstRenaming : Renaming first middle)
    (secondRenaming : Renaming middle last) :
    (term.rename firstRenaming).rename secondRenaming =
      term.rename (firstRenaming.comp secondRenaming) := by
  induction term generalizing middle last with
  | var index => rfl
  | unit => rfl
  | lam body induction =>
      simp only [rename, induction, Renaming.lift_comp]
  | app function argument functionInduction argumentInduction =>
      simp only [rename, functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp only [rename, rhsInduction, bodyInduction, Renaming.lift_comp]
  | suspend body induction =>
      simp only [rename, induction]
  | force suspension induction =>
      simp only [rename, induction]

end Tm

/-! ## Substitutions -/

/-- A simultaneous substitution of runtime terms for term variables. -/
abbrev Substitution (source target : Nat) : Type :=
  Fin source -> Tm target

namespace Substitution

/-- Identity substitution. -/
def id {scope : Nat} : Substitution scope scope := Tm.var

/-- Regard a renaming as a substitution by variables. -/
def ofRenaming {source target : Nat} (rho : Renaming source target) :
    Substitution source target :=
  fun index => .var (rho index)

/-- Preserve the newest variable and weaken every substituted older term. -/
def lift {source target : Nat} (substitution : Substitution source target) :
    Substitution (Nat.succ source) (Nat.succ target) :=
  Fin.cases (.var 0) (fun index => (substitution index).weaken)

/-- Replace the newest variable and retain every older variable. -/
def openAt {scope : Nat} (replacement : Tm scope) :
    Substitution (Nat.succ scope) scope :=
  Fin.cases replacement Tm.var

@[simp]
theorem lift_id {scope : Nat} :
    lift (id (scope := scope)) = id := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro older
    simp [lift, id, Tm.weaken, Tm.rename, Renaming.weaken]

end Substitution

namespace Tm

/-- Apply a simultaneous, capture-avoiding term substitution. -/
def subst {source target : Nat} (term : Tm source)
    (substitution : Substitution source target) : Tm target :=
  match term with
  | .var index => substitution index
  | .unit => .unit
  | .lam body => .lam (body.subst substitution.lift)
  | .app function argument =>
      .app (function.subst substitution) (argument.subst substitution)
  | .let' rhs body =>
      .let' (rhs.subst substitution) (body.subst substitution.lift)
  | .suspend body => .suspend (body.subst substitution)
  | .force suspension => .force (suspension.subst substitution)

/-- Instantiate the newest binder in a runtime term. -/
def instantiate {scope : Nat} (body : Tm (Nat.succ scope))
    (replacement : Tm scope) : Tm scope :=
  body.subst (Substitution.openAt replacement)

/-- Binder-opening notation used by the operational semantics. -/
def «open» {scope : Nat} (body : Tm (Nat.succ scope))
    (replacement : Tm scope) : Tm scope :=
  body.instantiate replacement

@[simp]
theorem subst_id {scope : Nat} (term : Tm scope) :
    term.subst Substitution.id = term := by
  induction term with
  | var index => rfl
  | unit => rfl
  | lam body induction =>
      simp only [subst, Substitution.lift_id, induction]
  | app function argument functionInduction argumentInduction =>
      simp only [subst, functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp only [subst, Substitution.lift_id, rhsInduction, bodyInduction]
  | suspend body induction =>
      simp only [subst, induction]
  | force suspension induction =>
      simp only [subst, induction]

@[simp]
theorem open_eq_instantiate {scope : Nat}
    (body : Tm (Nat.succ scope)) (replacement : Tm scope) :
    body.open replacement = body.instantiate replacement := rfl

end Tm

/-! ## Call-by-value reduction -/

/-- Runtime values. -/
inductive IsValue : {scope : Nat} -> Tm scope -> Prop where
  | var {scope : Nat} {index : Fin scope} : IsValue (.var index)
  | unit {scope : Nat} : IsValue (.unit : Tm scope)
  | lam {scope : Nat} {body : Tm (Nat.succ scope)} :
      IsValue (.lam body)
  | suspend {scope : Nat} {body : Tm scope} : IsValue (.suspend body)

/-- Deterministic, left-to-right call-by-value reduction. -/
inductive Step : {scope : Nat} -> Tm scope -> Tm scope -> Prop where
  | appFunction {scope : Nat} {function function' argument : Tm scope}
      (step : Step function function') :
      Step (.app function argument) (.app function' argument)
  | appArgument {scope : Nat} {function argument argument' : Tm scope}
      (functionValue : IsValue function) (step : Step argument argument') :
      Step (.app function argument) (.app function argument')
  | beta {scope : Nat} {body : Tm (Nat.succ scope)} {argument : Tm scope}
      (argumentValue : IsValue argument) :
      Step (.app (.lam body) argument) (body.open argument)
  | letRhs {scope : Nat} {rhs rhs' : Tm scope}
      {body : Tm (Nat.succ scope)} (step : Step rhs rhs') :
      Step (.let' rhs body) (.let' rhs' body)
  | zeta {scope : Nat} {rhs : Tm scope} {body : Tm (Nat.succ scope)}
      (rhsValue : IsValue rhs) :
      Step (.let' rhs body) (body.open rhs)
  /-- The suspension-producing operand is evaluated exactly once. -/
  | forceSuspension {scope : Nat}
      {suspension suspension' : Tm scope}
      (step : Step suspension suspension') :
      Step (.force suspension) (.force suspension')
  /-- Forcing a suspension starts its delayed computation. -/
  | forceBeta {scope : Nat} {body : Tm scope} :
      Step (.force (.suspend body)) body

/-- Reflexive-transitive closure of runtime reduction. -/
inductive Steps : {scope : Nat} -> Tm scope -> Tm scope -> Prop where
  | refl {scope : Nat} {term : Tm scope} : Steps term term
  | tail {scope : Nat} {first second third : Tm scope}
      (steps : Steps first second) (step : Step second third) :
      Steps first third

namespace Steps

/-- Embed one runtime step into the reflexive-transitive closure. -/
theorem single {scope : Nat} {first second : Tm scope}
    (step : Step first second) : Steps first second :=
  .tail .refl step

/-- Transitivity of multi-step reduction. -/
theorem trans {scope : Nat} {first second third : Tm scope}
    (initial : Steps first second) (final : Steps second third) :
    Steps first third := by
  induction final with
  | refl => exact initial
  | tail _ step induction => exact .tail induction step

/-- Multi-step closure under the function position of application. -/
theorem appFunction {scope : Nat}
    {function function' argument : Tm scope}
    (steps : Steps function function') :
    Steps (.app function argument) (.app function' argument) := by
  induction steps with
  | refl => exact .refl
  | tail _ step induction => exact .tail induction (.appFunction step)

/-- Multi-step closure under the argument position of application. -/
theorem appArgument {scope : Nat}
    {function argument argument' : Tm scope}
    (functionValue : IsValue function) (steps : Steps argument argument') :
    Steps (.app function argument) (.app function argument') := by
  induction steps with
  | refl => exact .refl
  | tail _ step induction =>
      exact .tail induction (.appArgument functionValue step)

/-- Multi-step closure under a let right-hand side. -/
theorem letRhs {scope : Nat} {rhs rhs' : Tm scope}
    {body : Tm (Nat.succ scope)} (steps : Steps rhs rhs') :
    Steps (.let' rhs body) (.let' rhs' body) := by
  induction steps with
  | refl => exact .refl
  | tail _ step induction => exact .tail induction (.letRhs step)

/-- Multi-step closure under the operand of `force`. -/
theorem forceSuspension {scope : Nat}
    {suspension suspension' : Tm scope}
    (steps : Steps suspension suspension') :
    Steps (.force suspension) (.force suspension') := by
  induction steps with
  | refl => exact .refl
  | tail _ step induction =>
      exact .tail induction (.forceSuspension step)

end Steps

end ManySortedFC.Runtime
