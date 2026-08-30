import Coercions.DOT.Captures.BinderOnly.Term

/-!
# Static substitution for the binder-only capture source

A source static substitution preserves term variables, and hence the roots of
paths, while replacing every static variable by an expression of the same
sort.  This module belongs entirely to the source language: no target scope,
symbol, evidence, or coercion type occurs in its interface.
-/

namespace DOTCapture.BinderOnly

/-- A simultaneous, sort-preserving substitution for source static syntax.

Term variables remain variables, so applying a static substitution cannot
turn a path into a term.  Static variables may be replaced by arbitrary
same-sort expressions. -/
structure StaticSubst (source target : Sig) where
  termVar : BVar source .term -> BVar target .term
  staticVar : {sort : StaticSort} ->
    BVar source (.static sort) -> StaticExpr sort target

namespace StaticSubst

@[ext]
theorem ext {source target : Sig} {first second : StaticSubst source target}
    (terms : forall index, first.termVar index = second.termVar index)
    (statics : forall {sort : StaticSort}
      (index : BVar source (.static sort)),
      first.staticVar index = second.staticVar index) :
    first = second := by
  cases first
  cases second
  congr
  · funext index
    exact terms index
  · funext sort index
    exact statics index

/-- Identity static substitution. -/
def id {scope : Sig} : StaticSubst scope scope where
  termVar := fun index => index
  staticVar := StaticExpr.bound

/-- Regard a kind-preserving renaming as a static substitution. -/
def ofRename {source target : Sig} (rho : Rename source target) :
    StaticSubst source target where
  termVar := fun index => rho.var index
  staticVar := fun index => StaticExpr.bound (rho.var index)

/-- Preserve a fresh term variable on both sides of a substitution. -/
def liftTerm {source target : Sig}
    (substitution : StaticSubst source target) :
    StaticSubst (source ▹ .term) (target ▹ .term) where
  termVar := fun
    | .here => .here
    | .there index => .there (substitution.termVar index)
  staticVar := fun
    | .there index => (substitution.staticVar index).weaken

/-- Preserve a fresh static variable of the selected sort. -/
def liftStatic {source target : Sig}
    (substitution : StaticSubst source target) (sort : StaticSort) :
    StaticSubst (source ▹ .static sort) (target ▹ .static sort) where
  termVar := fun
    | .there index => .there (substitution.termVar index)
  staticVar := fun
    | .here => StaticExpr.bound .here
    | .there index => (substitution.staticVar index).weaken

/-- Preserve one heterogeneous source binder. -/
def lift {source target : Sig} (substitution : StaticSubst source target) :
    (kind : BinderKind) -> StaticSubst (source ▹ kind) (target ▹ kind)
  | .term => substitution.liftTerm
  | .static sort => substitution.liftStatic sort

/-- Replace the newest static variable and eliminate its binder. -/
def instantiateStatic {source target : Sig}
    (substitution : StaticSubst source target) {sort : StaticSort}
    (replacement : StaticExpr sort target) :
    StaticSubst (source ▹ .static sort) target where
  termVar := fun
    | .there index => substitution.termVar index
  staticVar := fun
    | .here => replacement
    | .there index => substitution.staticVar index

/-- The one-binder substitution replacing the newest static variable. -/
def instantiateNewest {scope : Sig} {sort : StaticSort}
    (replacement : StaticExpr sort scope) :
    StaticSubst (scope ▹ .static sort) scope :=
  (id (scope := scope)).instantiateStatic replacement

@[simp]
theorem ofRename_id {scope : Sig} :
    ofRename (Rename.id (scope := scope)) = id := by
  rfl

@[simp]
theorem liftTerm_id {scope : Sig} :
    (id (scope := scope)).liftTerm = id := by
  apply ext
  · intro index
    cases index <;> rfl
  · intro sort index
    cases index with
    | there index =>
        cases sort <;> rfl

@[simp]
theorem liftStatic_id {scope : Sig} (sort : StaticSort) :
    (id (scope := scope)).liftStatic sort = id := by
  apply ext
  · intro index
    cases index with
    | there index => rfl
  · intro other index
    cases index with
    | here => rfl
    | there index =>
        cases other <;> rfl

@[simp]
theorem instantiateNewest_termVar {scope : Sig} {sort : StaticSort}
    (replacement : StaticExpr sort scope) (index : BVar scope .term) :
    (instantiateNewest replacement).termVar (.there index) = index := rfl

@[simp]
theorem instantiateNewest_here {scope : Sig} {sort : StaticSort}
    (replacement : StaticExpr sort scope) :
    (instantiateNewest replacement).staticVar
      (.here : BVar (scope ▹ .static sort) (.static sort)) =
      replacement := rfl

@[simp]
theorem instantiateNewest_there {scope : Sig} {boundSort sort : StaticSort}
    (replacement : StaticExpr boundSort scope)
    (index : BVar scope (.static sort)) :
    (instantiateNewest replacement).staticVar (.there index) =
      StaticExpr.bound index := rfl

end StaticSubst

/-! ## Capture-avoiding action on source syntax -/

namespace Path

/-- Apply the term-variable component while retaining the path form. -/
def substitute {source target : Sig} (path : Path source)
    (substitution : StaticSubst source target) : Path target :=
  match path with
  | .var name => .var (substitution.termVar name)

end Path

namespace StaticRef

/-- Replace a static reference by the expression assigned to its binder. -/
def substitute {source target : Sig} {sort : StaticSort}
    (reference : StaticRef sort source)
    (substitution : StaticSubst source target) : StaticExpr sort target :=
  match reference with
  | .bound name => substitution.staticVar name

end StaticRef

mutual

/-- Apply a simultaneous static substitution to a capture expression. -/
def Capture.substitute {source target : Sig} (capture : Capture source)
    (substitution : StaticSubst source target) : Capture target :=
  match capture with
  | .empty => .empty
  | .union left right =>
      .union (left.substitute substitution) (right.substitute substitution)
  | .singleton path => .singleton (path.substitute substitution)
  | .ref reference =>
      match reference.substitute substitution with
      | .capture replacement => replacement

/-- Apply a simultaneous static substitution to a type. -/
def Ty.substitute {source target : Sig} (type : Ty source)
    (substitution : StaticSubst source target) : Ty target :=
  match type with
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .ref reference =>
      match reference.substitute substitution with
      | .type replacement => replacement
  | .capturing captures shape =>
      .capturing (captures.substitute substitution)
        (shape.substitute substitution)
  | .arr domain codomain =>
      .arr (domain.substitute substitution) (codomain.substitute substitution)
  | @Ty.forallI _ sort interval body =>
      .forallI (interval.substitute substitution)
        (body.substitute (substitution.liftStatic sort))
  | @Ty.existsI _ sort interval body =>
      .existsI (interval.substitute substitution)
        (body.substitute (substitution.liftStatic sort))

/-- Apply a simultaneous substitution to a sorted static expression. -/
def StaticExpr.substitute {sort : StaticSort} {source target : Sig}
    (expression : StaticExpr sort source)
    (substitution : StaticSubst source target) : StaticExpr sort target :=
  match expression with
  | .type type => .type (type.substitute substitution)
  | .capture capture => .capture (capture.substitute substitution)

/-- Substitute an optional interval endpoint. -/
def Endpoint.substitute {sort : StaticSort} {source target : Sig}
    (endpoint : Endpoint sort source)
    (substitution : StaticSubst source target) : Endpoint sort target :=
  match endpoint with
  | .none => .none
  | .some expression => .some (expression.substitute substitution)

/-- Substitute both independently optional interval endpoints. -/
def Interval.substitute {sort : StaticSort} {source target : Sig}
    (interval : Interval sort source)
    (substitution : StaticSubst source target) : Interval sort target :=
  match interval with
  | .bounds lower upper =>
      .bounds (lower.substitute substitution)
        (upper.substitute substitution)

end

/-! ## Capture-avoiding action on source terms -/

mutual

/-- Apply a static substitution to a value.  Term variables are transported
by the substitution's term component, while static binders lift it. -/
def Value.substitute {source target : Sig} (value : Value source)
    (substitution : StaticSubst source target) : Value target :=
  match value with
  | .var name => .var (substitution.termVar name)
  | .unit => .unit
  | .lam domain codomain body =>
      .lam (domain.substitute substitution) (codomain.substitute substitution)
        (body.substitute substitution.liftTerm)
  | @Value.staticLam _ sort interval body =>
      .staticLam (interval.substitute substitution)
        (body.substitute (substitution.liftStatic sort))
  | @Value.pack _ sort interval payloadType witness payload =>
      .pack (interval.substitute substitution)
        (payloadType.substitute (substitution.liftStatic sort))
        (witness.substitute substitution) (payload.substitute substitution)

/-- Apply a static substitution to an ANF computation, lifting through every
term or static scope opened by the computation. -/
def Term.substitute {source target : Sig} (term : Term source)
    (substitution : StaticSubst source target) : Term target :=
  match term with
  | .ret value => .ret (value.substitute substitution)
  | .app function argument =>
      .app (function.substitute substitution)
        (argument.substitute substitution)
  | .let' result rhs body =>
      .let' (result.substitute substitution) (rhs.substitute substitution)
        (body.substitute substitution.liftTerm)
  | @Term.staticApp _ _ interval function argument =>
      .staticApp (interval.substitute substitution)
        (function.substitute substitution) (argument.substitute substitution)
  | @Term.«open» _ sort interval payloadType result package body =>
      .«open» (interval.substitute substitution)
        (payloadType.substitute (substitution.liftStatic sort))
        (result.substitute substitution) (package.substitute substitution)
        (body.substitute (substitution.liftStatic sort).liftTerm)

end

/-! ## One-static-binder instantiation -/

namespace Path

def instantiateStatic {scope : Sig} {sort : StaticSort}
    (path : Path (scope ▹ .static sort))
    (replacement : StaticExpr sort scope) : Path scope :=
  path.substitute (StaticSubst.instantiateNewest replacement)

end Path

namespace StaticRef

def instantiateStatic {scope : Sig} {boundSort sort : StaticSort}
    (reference : StaticRef sort (scope ▹ .static boundSort))
    (replacement : StaticExpr boundSort scope) : StaticExpr sort scope :=
  reference.substitute (StaticSubst.instantiateNewest replacement)

end StaticRef

namespace Capture

def instantiateStatic {scope : Sig} {sort : StaticSort}
    (capture : Capture (scope ▹ .static sort))
    (replacement : StaticExpr sort scope) : Capture scope :=
  capture.substitute (StaticSubst.instantiateNewest replacement)

end Capture

namespace Ty

def instantiateStatic {scope : Sig} {sort : StaticSort}
    (type : Ty (scope ▹ .static sort))
    (replacement : StaticExpr sort scope) : Ty scope :=
  type.substitute (StaticSubst.instantiateNewest replacement)

end Ty

namespace StaticExpr

def instantiateStatic {scope : Sig} {boundSort sort : StaticSort}
    (expression : StaticExpr sort (scope ▹ .static boundSort))
    (replacement : StaticExpr boundSort scope) : StaticExpr sort scope :=
  expression.substitute (StaticSubst.instantiateNewest replacement)

end StaticExpr

namespace Endpoint

def instantiateStatic {scope : Sig} {boundSort sort : StaticSort}
    (endpoint : Endpoint sort (scope ▹ .static boundSort))
    (replacement : StaticExpr boundSort scope) : Endpoint sort scope :=
  endpoint.substitute (StaticSubst.instantiateNewest replacement)

end Endpoint

namespace Interval

def instantiateStatic {scope : Sig} {boundSort sort : StaticSort}
    (interval : Interval sort (scope ▹ .static boundSort))
    (replacement : StaticExpr boundSort scope) : Interval sort scope :=
  interval.substitute (StaticSubst.instantiateNewest replacement)

end Interval

namespace Value

/-- Replace the newest static variable throughout a value. -/
def instantiateStatic {scope : Sig} {sort : StaticSort}
    (value : Value (scope ▹ .static sort))
    (replacement : StaticExpr sort scope) : Value scope :=
  value.substitute (StaticSubst.instantiateNewest replacement)

end Value

namespace Term

/-- Replace the newest static variable throughout a computation. -/
def instantiateStatic {scope : Sig} {sort : StaticSort}
    (term : Term (scope ▹ .static sort))
    (replacement : StaticExpr sort scope) : Term scope :=
  term.substitute (StaticSubst.instantiateNewest replacement)

end Term

/-! ## Identity laws -/

@[simp]
theorem Path.substitute_id {scope : Sig} (path : Path scope) :
    path.substitute StaticSubst.id = path := by
  cases path
  rfl

@[simp]
theorem StaticRef.substitute_id {scope : Sig} {sort : StaticSort}
    (reference : StaticRef sort scope) :
    reference.substitute StaticSubst.id = reference.asExpression := by
  cases reference
  rfl

mutual

@[simp]
def Capture.substitute_id {scope : Sig} (capture : Capture scope) :
    capture.substitute StaticSubst.id = capture :=
  match capture with
  | .empty => rfl
  | .union left right => by
      simp only [Capture.substitute, Capture.substitute_id left,
        Capture.substitute_id right]
  | .singleton path => by
      simp only [Capture.substitute, Path.substitute_id path]
  | .ref reference => by
      cases reference
      rfl

@[simp]
def Ty.substitute_id {scope : Sig} (type : Ty scope) :
    type.substitute StaticSubst.id = type :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref reference => by
      cases reference
      rfl
  | .capturing captures shape => by
      simp only [Ty.substitute, Capture.substitute_id captures,
        Ty.substitute_id shape]
  | .arr domain codomain => by
      simp only [Ty.substitute, Ty.substitute_id domain,
        Ty.substitute_id codomain]
  | .forallI interval body => by
      simp only [Ty.substitute, Interval.substitute_id interval,
        StaticSubst.liftStatic_id, Ty.substitute_id body]
  | .existsI interval body => by
      simp only [Ty.substitute, Interval.substitute_id interval,
        StaticSubst.liftStatic_id, Ty.substitute_id body]

@[simp]
def StaticExpr.substitute_id {scope : Sig} {sort : StaticSort}
    (expression : StaticExpr sort scope) :
    expression.substitute StaticSubst.id = expression :=
  match expression with
  | .type type => by
      simp only [StaticExpr.substitute, Ty.substitute_id type]
  | .capture capture => by
      simp only [StaticExpr.substitute, Capture.substitute_id capture]

@[simp]
def Endpoint.substitute_id {scope : Sig} {sort : StaticSort}
    (endpoint : Endpoint sort scope) :
    endpoint.substitute StaticSubst.id = endpoint :=
  match endpoint with
  | .none => rfl
  | .some expression => by
      simp only [Endpoint.substitute, StaticExpr.substitute_id expression]

@[simp]
def Interval.substitute_id {scope : Sig} {sort : StaticSort}
    (interval : Interval sort scope) :
    interval.substitute StaticSubst.id = interval :=
  match interval with
  | .bounds lower upper => by
      simp only [Interval.substitute, Endpoint.substitute_id lower,
        Endpoint.substitute_id upper]

end

mutual

@[simp]
def Value.substitute_id {scope : Sig} (value : Value scope) :
    value.substitute StaticSubst.id = value :=
  match value with
  | .var _ => rfl
  | .unit => rfl
  | .lam domain codomain body => by
      simp only [Value.substitute, Ty.substitute_id domain,
        Ty.substitute_id codomain, StaticSubst.liftTerm_id,
        Term.substitute_id body]
  | .staticLam interval body => by
      simp only [Value.substitute, Interval.substitute_id interval,
        StaticSubst.liftStatic_id, Value.substitute_id body]
  | .pack interval payloadType witness payload => by
      simp only [Value.substitute, Interval.substitute_id interval,
        StaticSubst.liftStatic_id, Ty.substitute_id payloadType,
        StaticExpr.substitute_id witness, Value.substitute_id payload]

@[simp]
def Term.substitute_id {scope : Sig} (term : Term scope) :
    term.substitute StaticSubst.id = term :=
  match term with
  | .ret value => by
      simp only [Term.substitute, Value.substitute_id value]
  | .app function argument => by
      simp only [Term.substitute, Value.substitute_id function,
        Value.substitute_id argument]
  | .let' result rhs body => by
      simp only [Term.substitute, Ty.substitute_id result,
        Term.substitute_id rhs, StaticSubst.liftTerm_id,
        Term.substitute_id body]
  | .staticApp interval function argument => by
      simp only [Term.substitute, Interval.substitute_id interval,
        Value.substitute_id function, StaticExpr.substitute_id argument]
  | @Term.«open» scope sort interval payloadType result package body => by
      simp only [Term.substitute, Interval.substitute_id interval,
        StaticSubst.liftStatic_id, Ty.substitute_id payloadType,
        Ty.substitute_id result, Value.substitute_id package,
        StaticSubst.liftTerm_id, Term.substitute_id body]

end

end DOTCapture.BinderOnly
