import Coercions.DOT.Captures.ModalIntersections.Term

/-!
# Static substitution for modal captured intersections

A static substitution preserves the distinction between term variables and
static variables.  Term variables, and therefore stable path roots, remain
variables.  Lexical static variables may be replaced by arbitrary expressions
of the same sort.  Selected member references retain their stable receiver,
while local member references remain local to their enclosing object
interface.
-/

namespace DOTCapture.ModalIntersections

/-- A simultaneous sort-preserving substitution for cumulative source syntax. -/
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

/-- Regard a heterogeneous renaming as a static substitution. -/
def ofRename {source target : Sig} (rho : Rename source target) :
    StaticSubst source target where
  termVar := fun index => rho.var index
  staticVar := fun index => StaticExpr.bound (rho.var index)

/-- Preserve a fresh term variable. -/
def liftTerm {source target : Sig} (substitution : StaticSubst source target) :
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

/-- Lift through an existential's hidden static name and payload variable. -/
def liftPayload {source target : Sig}
    (substitution : StaticSubst source target) (sort : StaticSort) :
    StaticSubst (PayloadScope source sort) (PayloadScope target sort) :=
  (substitution.liftStatic sort).liftTerm

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
    ofRename (DOTCapture.BinderOnly.Rename.id (scope := scope)) = id := by
  rfl

@[simp]
theorem liftTerm_id {scope : Sig} :
    (id (scope := scope)).liftTerm = id := by
  apply ext
  · intro index
    cases index <;> rfl
  · intro sort index
    cases index with
    | there index => cases sort <;> rfl

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
    | there index => cases other <;> rfl

@[simp]
theorem liftPayload_id {scope : Sig} (sort : StaticSort) :
    (id (scope := scope)).liftPayload sort = id := by
  unfold liftPayload
  simp

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

/-- Apply the term-variable component while retaining stable path form. -/
def substitute {source target : Sig} (path : Path source)
    (substitution : StaticSubst source target) : Path target :=
  match path with
  | .var name => .var (substitution.termVar name)

end Path

namespace StaticRef

/-- Substitute a static reference.  Selected references keep their stable
root, and local references remain in the current interface namespace. -/
def substitute {source target : Sig} {sort : StaticSort}
    (reference : StaticRef sort source)
    (substitution : StaticSubst source target) : StaticExpr sort target :=
  match reference with
  | .bound name => substitution.staticVar name
  | .typeMember receiver label =>
      .type (.ref (.typeMember (receiver.substitute substitution) label))
  | .captureMember receiver label =>
      .capture (.ref (.captureMember (receiver.substitute substitution) label))
  | .localTypeMember label => .type (.ref (.localTypeMember label))
  | .localCaptureMember label => .capture (.ref (.localCaptureMember label))

end StaticRef

def Capture.substitute {source target : Sig} (capture : Capture source)
    (substitution : StaticSubst source target) : Capture target :=
  match capture with
  | .empty => .empty
  | .union left right =>
      .union (left.substitute substitution) (right.substitute substitution)
  | .readOnly inner => .readOnly (inner.substitute substitution)
  | .singleton path => .singleton (path.substitute substitution)
  | .ref reference =>
      match reference.substitute substitution with
      | .capture replacement => replacement

def SeparationContext.substitute {count : Nat} {source target : Sig}
    (context : SeparationContext count source)
    (substitution : StaticSubst source target) :
    SeparationContext count target :=
  match context with
  | .nil => .nil
  | .cons rest capture =>
      .cons (rest.substitute substitution) (capture.substitute substitution)

def ModeContext.substitute {modes : List CaptureMode} {source target : Sig}
    (context : ModeContext modes source)
    (substitution : StaticSubst source target) : ModeContext modes target :=
  match context with
  | .nil => .nil
  | .cons rest capture =>
      .cons (rest.substitute substitution) (capture.substitute substitution)

def ModalRequirements.substitute {separationCount : Nat}
    {modes : List CaptureMode} {source target : Sig}
    (requirements : ModalRequirements separationCount modes source)
    (substitution : StaticSubst source target) :
    ModalRequirements separationCount modes target :=
  match requirements with
  | .mk separation mode =>
      .mk (separation.substitute substitution) (mode.substitute substitution)

mutual

/-- Apply a simultaneous static substitution to a type.  Nested object
interfaces are traversed for lexical references, but their local references
remain local because `StaticRef.substitute` never realizes them. -/
def Ty.substitute {source target : Sig} (type : Ty source)
    (substitution : StaticSubst source target) : Ty target :=
  match type with
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .ref reference =>
      match reference.substitute substitution with
      | .type replacement => replacement
  | .arr domain codomain =>
      .arr (domain.substitute substitution) (codomain.substitute substitution)
  | .objectArrow parameter resultTemplate =>
      .objectArrow (parameter.substitute substitution)
        (resultTemplate.substitute substitution)
  | .capturing captures shape =>
      .capturing (captures.substitute substitution)
        (shape.substitute substitution)
  | @Ty.forallI _ sort interval body =>
      .forallI (interval.substitute substitution)
        (body.substitute (substitution.liftStatic sort))
  | @Ty.existsI _ sort interval body =>
      .existsI (interval.substitute substitution)
        (body.substitute (substitution.liftStatic sort))
  | .modal requirements body =>
      .modal (requirements.substitute substitution)
        (body.substitute substitution)
  | .object object => .object (object.substitute substitution)

def StaticExpr.substitute {sort : StaticSort} {source target : Sig}
    (expression : StaticExpr sort source)
    (substitution : StaticSubst source target) : StaticExpr sort target :=
  match expression with
  | .type type => .type (type.substitute substitution)
  | .capture capture => .capture (capture.substitute substitution)

def Endpoint.substitute {sort : StaticSort} {source target : Sig}
    (endpoint : Endpoint sort source)
    (substitution : StaticSubst source target) : Endpoint sort target :=
  match endpoint with
  | .none => .none
  | .some expression => .some (expression.substitute substitution)

def Interval.substitute {sort : StaticSort} {source target : Sig}
    (interval : Interval sort source)
    (substitution : StaticSubst source target) : Interval sort target :=
  match interval with
  | .bounds lower upper =>
      .bounds (lower.substitute substitution) (upper.substitute substitution)

def Interface.substitute {source target : Sig} (interface : Interface source)
    (substitution : StaticSubst source target) : Interface target :=
  match interface with
  | .empty => .empty
  | .typeMember label lower upper =>
      .typeMember label (lower.substitute substitution)
        (upper.substitute substitution)
  | .captureMember label lower upper =>
      .captureMember label (lower.substitute substitution)
        (upper.substitute substitution)
  | .inter left right =>
      .inter (left.substitute substitution) (right.substitute substitution)

def ObjectType.substitute {source target : Sig} (object : ObjectType source)
    (substitution : StaticSubst source target) : ObjectType target :=
  match object with
  | .mk interface representation outerCapture =>
      .mk (interface.substitute substitution)
        (representation.substitute substitution)
        (outerCapture.substitute substitution)

end

/-! ## Capture-avoiding action on terms -/

mutual

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
  | .lock requirements result closure body =>
      .lock (requirements.substitute substitution)
        (result.substitute substitution) (closure.substitute substitution)
        (body.substitute substitution)
  | .object objectType payload =>
      .object (objectType.substitute substitution)
        (payload.substitute substitution)
  | .objectConsumer parameter result body =>
      .objectConsumer (parameter.substitute substitution)
        (result.substitute substitution)
        (body.substitute substitution.liftTerm)

def Term.substitute {source target : Sig} (term : Term source)
    (substitution : StaticSubst source target) : Term target :=
  match term with
  | .ret value => .ret (value.substitute substitution)
  | .select receiver label =>
      .select (receiver.substitute substitution) label
  | .app function argument =>
      .app (function.substitute substitution) (argument.substitute substitution)
  | .let' result rhs body =>
      .let' (result.substitute substitution) (rhs.substitute substitution)
        (body.substitute substitution.liftTerm)
  | .staticApp interval function argument =>
      .staticApp (interval.substitute substitution)
        (function.substitute substitution) (argument.substitute substitution)
  | @Term.«open» _ sort interval payloadType result package body =>
      .«open» (interval.substitute substitution)
        (payloadType.substitute (substitution.liftStatic sort))
        (result.substitute substitution) (package.substitute substitution)
        (body.substitute (substitution.liftPayload sort))
  | .unlock requirements scrutinee =>
      .unlock (requirements.substitute substitution)
        (scrutinee.substitute substitution)
  | .objectApp parameter function argument =>
      .objectApp (parameter.substitute substitution)
        (function.substitute substitution) (argument.substitute substitution)
  | .objectLet objectType result rhs body =>
      .objectLet (objectType.substitute substitution)
        (result.substitute substitution) (rhs.substitute substitution)
        (body.substitute substitution.liftTerm)

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

namespace SeparationContext

def instantiateStatic {scope : Sig} {sort : StaticSort} {count : Nat}
    (context : SeparationContext count (scope ▹ .static sort))
    (replacement : StaticExpr sort scope) : SeparationContext count scope :=
  context.substitute (StaticSubst.instantiateNewest replacement)

end SeparationContext

namespace ModeContext

def instantiateStatic {scope : Sig} {sort : StaticSort}
    {modes : List CaptureMode}
    (context : ModeContext modes (scope ▹ .static sort))
    (replacement : StaticExpr sort scope) : ModeContext modes scope :=
  context.substitute (StaticSubst.instantiateNewest replacement)

end ModeContext

namespace ModalRequirements

def instantiateStatic {scope : Sig} {sort : StaticSort}
    {separationCount : Nat} {modes : List CaptureMode}
    (requirements : ModalRequirements separationCount modes
      (scope ▹ .static sort))
    (replacement : StaticExpr sort scope) :
    ModalRequirements separationCount modes scope :=
  requirements.substitute (StaticSubst.instantiateNewest replacement)

end ModalRequirements

namespace Ty

/-- Replace the newest lexical static variable throughout a type. -/
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

namespace Interface

def instantiateStatic {scope : Sig} {sort : StaticSort}
    (interface : Interface (scope ▹ .static sort))
    (replacement : StaticExpr sort scope) : Interface scope :=
  interface.substitute (StaticSubst.instantiateNewest replacement)

end Interface

namespace ObjectType

def instantiateStatic {scope : Sig} {sort : StaticSort}
    (object : ObjectType (scope ▹ .static sort))
    (replacement : StaticExpr sort scope) : ObjectType scope :=
  object.substitute (StaticSubst.instantiateNewest replacement)

end ObjectType

namespace Value

def instantiateStatic {scope : Sig} {sort : StaticSort}
    (value : Value (scope ▹ .static sort))
    (replacement : StaticExpr sort scope) : Value scope :=
  value.substitute (StaticSubst.instantiateNewest replacement)

end Value

namespace Term

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
  cases reference with
  | bound name => cases sort <;> rfl
  | typeMember receiver label =>
      simp only [StaticRef.substitute, Path.substitute_id,
        StaticRef.asExpression]
  | captureMember receiver label =>
      simp only [StaticRef.substitute, Path.substitute_id,
        StaticRef.asExpression]
  | localTypeMember label => rfl
  | localCaptureMember label => rfl

@[simp]
theorem StaticExpr.bound_substitute {source target : Sig}
    {sort : StaticSort} (name : BVar source (.static sort))
    (substitution : StaticSubst source target) :
    (StaticExpr.bound name).substitute substitution =
      substitution.staticVar name := by
  cases sort <;> cases h : substitution.staticVar name <;>
    simp [StaticExpr.bound, StaticExpr.substitute, Ty.substitute,
      Capture.substitute, StaticRef.substitute, h]

@[simp]
def Capture.substitute_id {scope : Sig} (capture : Capture scope) :
    capture.substitute StaticSubst.id = capture :=
  match capture with
  | .empty => rfl
  | .union left right => by
      simp only [Capture.substitute, Capture.substitute_id left,
        Capture.substitute_id right]
  | .readOnly inner => by
      simp only [Capture.substitute, Capture.substitute_id inner]
  | .singleton path => by
      simp only [Capture.substitute, Path.substitute_id path]
  | .ref reference => by
      simp only [Capture.substitute, StaticRef.substitute_id reference]
      cases reference <;> rfl

@[simp]
def SeparationContext.substitute_id {scope : Sig} {count : Nat}
    (context : SeparationContext count scope) :
    context.substitute StaticSubst.id = context :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [SeparationContext.substitute,
        SeparationContext.substitute_id rest, Capture.substitute_id capture]

@[simp]
def ModeContext.substitute_id {scope : Sig} {modes : List CaptureMode}
    (context : ModeContext modes scope) :
    context.substitute StaticSubst.id = context :=
  match context with
  | .nil => rfl
  | .cons rest capture => by
      simp only [ModeContext.substitute, ModeContext.substitute_id rest,
        Capture.substitute_id capture]

@[simp]
def ModalRequirements.substitute_id {scope : Sig}
    {separationCount : Nat} {modes : List CaptureMode}
    (requirements : ModalRequirements separationCount modes scope) :
    requirements.substitute StaticSubst.id = requirements :=
  match requirements with
  | .mk separation mode => by
      simp only [ModalRequirements.substitute,
        SeparationContext.substitute_id separation,
        ModeContext.substitute_id mode]

mutual

@[simp]
def Ty.substitute_id {scope : Sig} (type : Ty scope) :
    type.substitute StaticSubst.id = type :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref reference => by
      simp only [Ty.substitute, StaticRef.substitute_id reference]
      cases reference <;> rfl
  | .arr domain codomain => by
      simp only [Ty.substitute, Ty.substitute_id domain,
        Ty.substitute_id codomain]
  | .objectArrow parameter resultTemplate => by
      simp only [Ty.substitute, ObjectType.substitute_id parameter,
        Ty.substitute_id resultTemplate]
  | .capturing captures shape => by
      simp only [Ty.substitute, Capture.substitute_id captures,
        Ty.substitute_id shape]
  | .forallI interval body => by
      simp only [Ty.substitute, Interval.substitute_id interval,
        StaticSubst.liftStatic_id, Ty.substitute_id body]
  | .existsI interval body => by
      simp only [Ty.substitute, Interval.substitute_id interval,
        StaticSubst.liftStatic_id, Ty.substitute_id body]
  | .modal requirements body => by
      simp only [Ty.substitute, ModalRequirements.substitute_id requirements,
        Ty.substitute_id body]
  | .object object => by
      simp only [Ty.substitute, ObjectType.substitute_id object]

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

@[simp]
def Interface.substitute_id {scope : Sig} (interface : Interface scope) :
    interface.substitute StaticSubst.id = interface :=
  match interface with
  | .empty => rfl
  | .typeMember _ lower upper => by
      simp only [Interface.substitute, Ty.substitute_id lower,
        Ty.substitute_id upper]
  | .captureMember _ lower upper => by
      simp only [Interface.substitute, Capture.substitute_id lower,
        Capture.substitute_id upper]
  | .inter left right => by
      simp only [Interface.substitute, Interface.substitute_id left,
        Interface.substitute_id right]

@[simp]
def ObjectType.substitute_id {scope : Sig} (object : ObjectType scope) :
    object.substitute StaticSubst.id = object :=
  match object with
  | .mk interface representation outerCapture => by
      simp only [ObjectType.substitute, Interface.substitute_id interface,
        Ty.substitute_id representation, Capture.substitute_id outerCapture]

end

@[simp]
theorem ObjectType.formedType_substitute {source target : Sig}
    (object : ObjectType source) (substitution : StaticSubst source target) :
    object.formedType.substitute substitution =
      (object.substitute substitution).formedType := by
  cases object
  rfl


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
  | .lock requirements result closure body => by
      simp only [Value.substitute,
        ModalRequirements.substitute_id requirements, Ty.substitute_id result,
        Capture.substitute_id closure, Term.substitute_id body]
  | .object objectType payload => by
      simp only [Value.substitute, ObjectType.substitute_id objectType,
        Value.substitute_id payload]
  | .objectConsumer parameter result body => by
      simp only [Value.substitute, ObjectType.substitute_id parameter,
        Ty.substitute_id result, StaticSubst.liftTerm_id,
        Term.substitute_id body]

@[simp]
def Term.substitute_id {scope : Sig} (term : Term scope) :
    term.substitute StaticSubst.id = term :=
  match term with
  | .ret value => by
      simp only [Term.substitute, Value.substitute_id value]
  | .select receiver _ => by
      simp only [Term.substitute, Path.substitute_id receiver]
  | .app function argument => by
      simp only [Term.substitute, Term.substitute_id function,
        Term.substitute_id argument]
  | .let' result rhs body => by
      simp only [Term.substitute, Ty.substitute_id result,
        Term.substitute_id rhs, StaticSubst.liftTerm_id,
        Term.substitute_id body]
  | .staticApp interval function argument => by
      simp only [Term.substitute, Interval.substitute_id interval,
        Term.substitute_id function, StaticExpr.substitute_id argument]
  | .«open» interval payloadType result package body => by
      simp only [Term.substitute, Interval.substitute_id interval,
        StaticSubst.liftStatic_id, Ty.substitute_id payloadType,
        Ty.substitute_id result, Term.substitute_id package,
        StaticSubst.liftPayload_id, Term.substitute_id body]
  | .unlock requirements scrutinee => by
      simp only [Term.substitute,
        ModalRequirements.substitute_id requirements,
        Term.substitute_id scrutinee]
  | .objectApp parameter function argument => by
      simp only [Term.substitute, ObjectType.substitute_id parameter,
        Term.substitute_id function, Term.substitute_id argument]
  | .objectLet objectType result rhs body => by
      simp only [Term.substitute, ObjectType.substitute_id objectType,
        Ty.substitute_id result, Term.substitute_id rhs,
        StaticSubst.liftTerm_id, Term.substitute_id body]

end


end DOTCapture.ModalIntersections
