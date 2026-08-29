import DotFCI.Source.Typing

/-!
# Erased call-by-value runtime for DotFCI

Static member definitions and intersection structure have no runtime payload.
Every multi-definition object therefore erases to the single `unit` value.
Reduction lives on an ordinary untyped runtime syntax, where substitution of
lambda and unit values is unrestricted despite the source's variable-only
path discipline.
-/

namespace DotFCI.Source.Runtime

open DotFC

/-- Untyped runtime terms. -/
inductive Tm : Sig → Type where
  | var {scope : Sig} (path : BVar scope .term) : Tm scope
  | lam {scope : Sig} (body : Tm (scope ▹ .term)) : Tm scope
  | unit {scope : Sig} : Tm scope
  | app {scope : Sig} (function argument : Tm scope) : Tm scope
  | let' {scope : Sig} (rhs : Tm scope)
      (body : Tm (scope ▹ .term)) : Tm scope
deriving DecidableEq

namespace Tm

/-- Rename free runtime variables through a heterogeneous source signature. -/
def rename {source target : Sig} (term : Tm source)
    (rho : Rename source target) : Tm target :=
  match term with
  | .var path => .var (rho.var path)
  | .lam body => .lam (rename body rho.lift)
  | .unit => .unit
  | .app function argument =>
      .app (rename function rho) (rename argument rho)
  | .let' rhs body => .let' (rename rhs rho) (rename body rho.lift)

def weaken {scope : Sig} {kind : BinderKind} (term : Tm scope) :
    Tm (scope ▹ kind) :=
  term.rename Rename.succ

@[simp]
theorem rename_id {scope : Sig} (term : Tm scope) :
    term.rename Rename.id = term := by
  induction term with
  | var => rfl
  | lam body induction => simp [rename, induction]
  | unit => rfl
  | app function argument functionInduction argumentInduction =>
      simp [rename, functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp [rename, rhsInduction, bodyInduction]

@[simp]
theorem rename_comp {first second third : Sig} (term : Tm first)
    (firstRename : Rename first second) (secondRename : Rename second third) :
    (term.rename firstRename).rename secondRename =
      term.rename (firstRename.comp secondRename) := by
  induction term generalizing second third with
  | var => rfl
  | lam body induction => simp [rename, induction, Rename.lift_comp]
  | unit => rfl
  | app function argument functionInduction argumentInduction =>
      simp [rename, functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp [rename, rhsInduction, bodyInduction, Rename.lift_comp]

end Tm

/-- Simultaneous substitution of arbitrary runtime terms for term variables. -/
structure Subst (source target : Sig) where
  var : BVar source .term → Tm target

namespace Subst

@[ext]
theorem ext {source target : Sig} {first second : Subst source target}
    (equal : ∀ path, first.var path = second.var path) : first = second := by
  cases first
  cases second
  congr
  funext path
  exact equal path

def id {scope : Sig} : Subst scope scope where
  var := Tm.var

def ofRename {source target : Sig} (rho : Rename source target) :
    Subst source target where
  var := fun path => .var (rho.var path)

/-- Preserve the newest term variable while weakening substituted terms. -/
def lift {source target : Sig} (substitution : Subst source target) :
    Subst (source ▹ .term) (target ▹ .term) where
  var := fun
    | .here => .var .here
    | .there path => (substitution.var path).weaken

/-- Eliminate the newest term binder with one runtime replacement. -/
def openAt {scope : Sig} (replacement : Tm scope) :
    Subst (scope ▹ .term) scope where
  var := fun
    | .here => replacement
    | .there path => .var path

@[simp]
theorem lift_id {scope : Sig} :
    (id (scope := scope)).lift =
      (id : Subst (scope ▹ .term) (scope ▹ .term)) := by
  ext path
  cases path <;> rfl

@[simp]
theorem lift_here {source target : Sig} (substitution : Subst source target) :
    substitution.lift.var (.here : BVar (source ▹ .term) .term) =
      (.var .here : Tm (target ▹ .term)) := rfl

@[simp]
theorem lift_there {source target : Sig}
    (substitution : Subst source target) (path : BVar source .term) :
    substitution.lift.var (.there path) =
      (substitution.var path).weaken := rfl

@[simp]
theorem openAt_here {scope : Sig} (replacement : Tm scope) :
    (openAt replacement).var (.here : BVar (scope ▹ .term) .term) =
      replacement := rfl

@[simp]
theorem openAt_there {scope : Sig} (replacement : Tm scope)
    (path : BVar scope .term) :
    (openAt replacement).var (.there path) = (.var path : Tm scope) := rfl

end Subst

namespace Tm

/-- Capture-avoiding runtime substitution. -/
def subst {source target : Sig} (term : Tm source)
    (substitution : Subst source target) : Tm target :=
  match term with
  | .var path => substitution.var path
  | .lam body => .lam (subst body substitution.lift)
  | .unit => .unit
  | .app function argument =>
      .app (subst function substitution) (subst argument substitution)
  | .let' rhs body =>
      .let' (subst rhs substitution) (subst body substitution.lift)

def «open» {scope : Sig} (body : Tm (scope ▹ .term))
    (replacement : Tm scope) : Tm scope :=
  body.subst (Subst.openAt replacement)

@[simp]
theorem subst_id {scope : Sig} (term : Tm scope) :
    term.subst Subst.id = term := by
  induction term with
  | var => rfl
  | lam body induction => simp [subst, induction]
  | unit => rfl
  | app function argument functionInduction argumentInduction =>
      simp [subst, functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp [subst, rhsInduction, bodyInduction]

end Tm

/-- Runtime values. -/
inductive IsValue : {scope : Sig} → Tm scope → Prop where
  | lam {scope : Sig} {body : Tm (scope ▹ .term)} : IsValue (.lam body)
  | unit {scope : Sig} : IsValue (.unit : Tm scope)

/-- Standard left-to-right call-by-value reduction. -/
inductive Step : {scope : Sig} → Tm scope → Tm scope → Prop where
  | appFunction {scope : Sig} {function function' argument : Tm scope}
      (step : Step function function') :
      Step (.app function argument) (.app function' argument)
  | appArgument {scope : Sig} {function argument argument' : Tm scope}
      (functionValue : IsValue function) (step : Step argument argument') :
      Step (.app function argument) (.app function argument')
  | beta {scope : Sig} {body : Tm (scope ▹ .term)} {argument : Tm scope}
      (argumentValue : IsValue argument) :
      Step (.app (.lam body) argument) (body.open argument)
  | letRhs {scope : Sig} {rhs rhs' : Tm scope}
      {body : Tm (scope ▹ .term)} (step : Step rhs rhs') :
      Step (.let' rhs body) (.let' rhs' body)
  | zeta {scope : Sig} {rhs : Tm scope} {body : Tm (scope ▹ .term)}
      (rhsValue : IsValue rhs) : Step (.let' rhs body) (body.open rhs)

/-- Reflexive-transitive closure of runtime reduction. -/
inductive Steps : {scope : Sig} → Tm scope → Tm scope → Prop where
  | refl {scope : Sig} {term : Tm scope} : Steps term term
  | tail {scope : Sig} {first second third : Tm scope}
      (steps : Steps first second) (step : Step second third) :
      Steps first third

end DotFCI.Source.Runtime

namespace DotFCI.Source.Tm

open DotFC

/-- Erase annotations, intersections, and every static object definition. -/
def erase {scope : Sig} (term : Tm scope) : Runtime.Tm scope :=
  match term with
  | .var path => .var path
  | .lam _ body => .lam body.erase
  | .obj _ => .unit
  | .app function argument => .app (.var function) (.var argument)
  | .let' rhs body => .let' rhs.erase body.erase

@[simp]
theorem erase_var {scope : Sig} (path : BVar scope .term) :
    (Tm.var path).erase = Runtime.Tm.var path := rfl

@[simp]
theorem erase_lam {scope : Sig} (domain : Ty scope)
    (body : Tm (scope ▹ .term)) :
    (Tm.lam domain body).erase = Runtime.Tm.lam body.erase := rfl

@[simp]
theorem erase_obj {scope : Sig} (definitions : List (TypeDef scope)) :
    (Tm.obj definitions).erase = (Runtime.Tm.unit : Runtime.Tm scope) := rfl

/-- Runtime erasure cannot observe the number, labels, or witnesses of an
object's static definitions. -/
theorem erase_obj_irrelevant {scope : Sig}
    (first second : List (TypeDef scope)) :
    (Tm.obj first).erase = (Tm.obj second).erase := rfl

@[simp]
theorem erase_app {scope : Sig} (function argument : BVar scope .term) :
    (Tm.app function argument).erase =
      Runtime.Tm.app (.var function) (.var argument) := rfl

@[simp]
theorem erase_let {scope : Sig} (rhs : Tm scope)
    (body : Tm (scope ▹ .term)) :
    (Tm.let' rhs body).erase = Runtime.Tm.let' rhs.erase body.erase := rfl

end DotFCI.Source.Tm
