import Coercions.DOT.TraceablePaths.Source.Typing

/-!
# Immutable transparent-alias runtime

Runtime terms include general receivers, but an alias-field step is available
only when the receiver is the embedding of a certified stable path.  The
`AliasStore` parameter never changes.  This makes the supported boundary
precise: transparent finite aliases reduce; opaque or dynamically computed
receivers have no `TraceableReceiver` certificate.

Alias reduction is a compatible rewrite relation, not a deterministic
evaluation strategy: a nested certified selection may reduce its receiver
first or collapse directly to its final transparent target.  The
traceable-path bridge uses anchor coherence and target stuttering, not
source-step determinism.
-/

namespace DotFCRP.Source.Runtime

open DotFC
open DotFCRP.Source

/-- Untyped runtime terms with explicit term-field selection. -/
inductive Tm : Sig → Type where
  | var {scope : Sig} (root : BVar scope .term) : Tm scope
  | select {scope : Sig} (receiver : Tm scope) (label : Name) : Tm scope
  | lam {scope : Sig} (body : Tm (scope ▹ .term)) : Tm scope
  | unit {scope : Sig} : Tm scope
  | app {scope : Sig} (function argument : Tm scope) : Tm scope
  | let' {scope : Sig} (rhs : Tm scope)
      (body : Tm (scope ▹ .term)) : Tm scope
deriving DecidableEq

namespace Tm

/-- Embed stable paths into runtime receiver syntax. -/
def ofPath {scope : Sig} : Path scope → Tm scope
  | .var root => .var root
  | .select receiver label => .select (ofPath receiver) label

def rename {source target : Sig} (term : Tm source)
    (rho : Rename source target) : Tm target :=
  match term with
  | .var root => .var (rho.var root)
  | .select receiver label => .select (receiver.rename rho) label
  | .lam body => .lam (body.rename rho.lift)
  | .unit => .unit
  | .app function argument => .app (function.rename rho) (argument.rename rho)
  | .let' rhs body => .let' (rhs.rename rho) (body.rename rho.lift)

def weaken {scope : Sig} {kind : BinderKind} (term : Tm scope) :
    Tm (scope ▹ kind) :=
  term.rename Rename.succ

@[simp]
theorem ofPath_rename {source target : Sig} (path : Path source)
    (rho : Rename source target) :
    ofPath (path.rename rho) = (ofPath path).rename rho := by
  induction path with
  | var => rfl
  | select receiver label induction =>
      simp only [Path.rename, ofPath, rename]
      rw [induction]

@[simp]
theorem rename_id {scope : Sig} (term : Tm scope) :
    term.rename Rename.id = term := by
  induction term with
  | var => rfl
  | select receiver label induction => simp [rename, induction]
  | lam body induction => simp [rename, induction]
  | unit => rfl
  | app function argument functionInduction argumentInduction =>
      simp [rename, functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp [rename, rhsInduction, bodyInduction]

end Tm

/-- General runtime substitution. -/
structure Subst (source target : Sig) where
  var : BVar source .term → Tm target

namespace Subst

@[ext]
theorem ext {source target : Sig} {first second : Subst source target}
    (equal : ∀ root, first.var root = second.var root) : first = second := by
  cases first
  cases second
  congr
  funext root
  exact equal root

def id {scope : Sig} : Subst scope scope where
  var := Tm.var

def lift {source target : Sig} (substitution : Subst source target) :
    Subst (source ▹ .term) (target ▹ .term) where
  var := fun
    | .here => .var .here
    | .there root => (substitution.var root).weaken

def openAt {scope : Sig} (replacement : Tm scope) :
    Subst (scope ▹ .term) scope where
  var := fun
    | .here => replacement
    | .there root => .var root

@[simp]
theorem lift_id {scope : Sig} :
    (id (scope := scope)).lift =
      (id : Subst (scope ▹ .term) (scope ▹ .term)) := by
  ext root
  cases root <;> rfl

end Subst

namespace Tm

def subst {source target : Sig} (term : Tm source)
    (substitution : Subst source target) : Tm target :=
  match term with
  | .var root => substitution.var root
  | .select receiver label => .select (receiver.subst substitution) label
  | .lam body => .lam (body.subst substitution.lift)
  | .unit => .unit
  | .app function argument =>
      .app (function.subst substitution) (argument.subst substitution)
  | .let' rhs body =>
      .let' (rhs.subst substitution) (body.subst substitution.lift)

def «open» {scope : Sig} (body : Tm (scope ▹ .term))
    (replacement : Tm scope) : Tm scope :=
  body.subst (Subst.openAt replacement)

@[simp]
theorem subst_id {scope : Sig} (term : Tm scope) :
    term.subst Subst.id = term := by
  induction term with
  | var => rfl
  | select receiver label induction => simp [subst, induction]
  | lam body induction => simp [subst, induction]
  | unit => rfl
  | app function argument functionInduction argumentInduction =>
      simp [subst, functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp [subst, rhsInduction, bodyInduction]

end Tm

/-- Runtime values.  Open variables are neutral values. -/
inductive IsValue : {scope : Sig} → Tm scope → Prop where
  | var {scope : Sig} {root : BVar scope .term} : IsValue (.var root)
  | lam {scope : Sig} {body : Tm (scope ▹ .term)} : IsValue (.lam body)
  | unit {scope : Sig} : IsValue (.unit : Tm scope)

/-- Compatible reduction under one fixed immutable alias store. -/
inductive Step {scope : Sig} (store : AliasStore scope) :
    Tm scope → Tm scope → Prop where
  | selectReceiver {receiver receiver' : Tm scope} {label : Name}
      (step : Step store receiver receiver') :
      Step store (.select receiver label) (.select receiver' label)
  | alias {receiver target : Path scope}
      {owner anchor : BVar scope .term} {label : Name}
      (receiverTrace : Traceable store receiver owner)
      (field : FieldAt store owner label target)
      (targetTrace : Traceable store target anchor) :
      Step store (.select (Tm.ofPath receiver) label) (Tm.ofPath target)
  | appFunction {function function' argument : Tm scope}
      (step : Step store function function') :
      Step store (.app function argument) (.app function' argument)
  | appArgument {function argument argument' : Tm scope}
      (functionValue : IsValue function)
      (step : Step store argument argument') :
      Step store (.app function argument) (.app function argument')
  | beta {body : Tm (scope ▹ .term)} {argument : Tm scope}
      (argumentValue : IsValue argument) :
      Step store (.app (.lam body) argument) (body.open argument)
  | letRhs {rhs rhs' : Tm scope} {body : Tm (scope ▹ .term)}
      (step : Step store rhs rhs') :
      Step store (.let' rhs body) (.let' rhs' body)
  | zeta {rhs : Tm scope} {body : Tm (scope ▹ .term)}
      (rhsValue : IsValue rhs) :
      Step store (.let' rhs body) (body.open rhs)

namespace Step

/-- Source-level path reduction is one runtime alias step. -/
def ofPathStep {store : AliasStore scope} {source target : Path scope}
    (step : PathStep store source target) :
    Step store (Tm.ofPath source) (Tm.ofPath target) :=
  match step with
  | .field receiverTrace field targetTrace =>
      .alias receiverTrace field targetTrace

end Step

/-- A configuration records explicitly that reduction never mutates aliases. -/
structure Config (scope : Sig) where
  store : AliasStore scope
  term : Tm scope

inductive ConfigStep {scope : Sig} : Config scope → Config scope → Prop where
  | step {store : AliasStore scope} {term term' : Tm scope}
      (reduction : Step store term term') :
      ConfigStep ⟨store, term⟩ ⟨store, term'⟩

theorem ConfigStep.store_preserved {scope : Sig} {first second : Config scope}
    (step : ConfigStep first second) : first.store = second.store := by
  cases step
  rfl

/-! ## Explicit supported/unsupported receiver boundary -/

/-- A receiver offered to the alias-resolution subsystem. -/
inductive Receiver (scope : Sig) where
  | stable (path : Path scope)
  | dynamic (term : Tm scope)

/-- Only stable receivers with a trace certificate are supported. -/
inductive TraceableReceiver {scope : Sig} (store : AliasStore scope) :
    Receiver scope → Type where
  | stable {path : Path scope} {anchor : BVar scope .term}
      (trace : Traceable store path anchor) :
      TraceableReceiver store (.stable path)

/-- Opaque or dynamically computed receivers have no trace certificate. -/
theorem dynamic_not_traceable {scope : Sig} (store : AliasStore scope)
    (term : Tm scope) :
    TraceableReceiver store (.dynamic term) → False := by
  intro trace
  cases trace

end DotFCRP.Source.Runtime

namespace DotFCRP.Source.Tm

open DotFC

/-- Erase source annotations while retaining stable path selections. -/
def erase {scope : Sig} (term : Tm scope) : Runtime.Tm scope :=
  match term with
  | .ref path => .ofPath path
  | .lam _ body => .lam body.erase
  | .obj _ => .unit
  | .recObj _ => .unit
  | .app function argument => .app (.ofPath function) (.ofPath argument)
  | .let' rhs body => .let' rhs.erase body.erase

@[simp]
theorem erase_ref {scope : Sig} (path : Path scope) :
    (Tm.ref path).erase = Runtime.Tm.ofPath path := rfl

@[simp]
theorem erase_obj {scope : Sig} (definitions : List (TypeDef scope)) :
    (Tm.obj definitions).erase = (Runtime.Tm.unit : Runtime.Tm scope) := rfl

@[simp]
theorem erase_recObj {scope : Sig}
    (definitions : List (TypeDef (scope ▹ .term))) :
    (Tm.recObj definitions).erase =
      (Runtime.Tm.unit : Runtime.Tm scope) := rfl

end DotFCRP.Source.Tm

namespace DotFCRP.Source.Legacy

open DotFC

/-- Embed the erased recursive-object runtime into the path runtime. -/
def runtime {scope : Sig} : DotFCR.Source.Runtime.Tm scope →
    Runtime.Tm scope
  | .var root => .var root
  | .lam body => .lam (runtime body)
  | .unit => .unit
  | .app function argument => .app (runtime function) (runtime argument)
  | .let' rhs body => .let' (runtime rhs) (runtime body)

/-- Erasure commutes with the complete recursive-object syntax embedding. -/
@[simp]
theorem erase_tm {scope : Sig} (term : DotFCR.Source.Tm scope) :
    (tm term).erase = runtime term.erase := by
  induction term with
  | var => rfl
  | lam domain body induction => simp [tm, Tm.erase, runtime, induction,
      DotFCR.Source.Tm.erase]
  | obj => rfl
  | recObj => rfl
  | app => rfl
  | let' rhs body rhsInduction bodyInduction =>
      simp [tm, Tm.erase, runtime, DotFCR.Source.Tm.erase,
        rhsInduction, bodyInduction]

/-- The embedded mutual recursive object still erases to unit. -/
theorem erase_mutualObject :
    (tm DotFCR.Source.MutualExample.object).erase =
      (Runtime.Tm.unit : Runtime.Tm []) := rfl

end DotFCRP.Source.Legacy
