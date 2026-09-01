import Coercions.DOT.Captures.Intersections.GeneralExpression.Erasure
import Coercions.DOT.Captures.ModalIntersections.Embedding

/-!
# Independent runtime erasure for modal captured intersections

This erasure is defined directly on the cumulative source syntax. Static and
object annotations disappear.  Modal locking and unlocking become runtime
suspension and forcing, while the remaining captured-intersection runtime
structure is retained literally. It does not mention a target compiler or
target evidence.
-/

namespace DOTCapture.ModalIntersections.Erasure

namespace Runtime

export ManySortedFC.Runtime (Tm)

end Runtime

open DOTCapture.ModalIntersections

/-- Map the term variables of a heterogeneous source scope into a runtime
scope.  Static variables have no runtime coordinate. -/
abbrev Renaming (source : Sig) (target : Nat) : Type :=
  BVar source .term → Fin target

namespace Renaming

/-- Preserve a newly bound runtime variable. -/
def liftTerm {source : Sig} {target : Nat} (rho : Renaming source target) :
    Renaming (source ▹ .term) (target + 1) :=
  fun
  | .here => 0
  | .there index => (rho index).succ

/-- Forget a newly bound static variable.  It has no runtime coordinate. -/
def liftStatic {source : Sig} {target : Nat} (rho : Renaming source target)
    (sort : StaticSort) : Renaming (source ▹ .static sort) target :=
  fun
  | .there index => rho index

/-- Forget an existential's hidden static variable while preserving its
newest payload variable in the runtime scope. -/
def liftPayload {source : Sig} {target : Nat} (rho : Renaming source target)
    (sort : StaticSort) : Renaming (PayloadScope source sort) (target + 1) :=
  (rho.liftStatic sort).liftTerm

/-- Canonical runtime coordinates for an all-term heterogeneous scope. -/
def allTermIdentity : {scope : Nat} → Renaming (termScope scope) scope
  | 0 => fun index => nomatch index
  | _ + 1 => fun
      | .here => 0
      | .there index => (allTermIdentity index).succ

end Renaming

def erasePathWith {scope : Sig} {runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) : Path scope → Fin runtimeScope
  | .var name => rho name

mutual

def eraseValueWith {scope : Sig} {runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) : Value scope → Runtime.Tm runtimeScope
  | .var name => .var (rho name)
  | .unit => .unit
  | .lam _ _ body => .lam (eraseTermWith rho.liftTerm body)
  | @Value.staticLam _ sort _ body =>
      eraseValueWith (rho.liftStatic sort) body
  | .pack _ _ _ payload => eraseValueWith rho payload
  | .lock _ _ _ body => .suspend (eraseTermWith rho body)
  | .object _ payload => eraseValueWith rho payload
  | .recursiveObject _ payload => eraseValueWith rho payload
  | .objectConsumer _ _ body => .lam (eraseTermWith rho.liftTerm body)

def eraseTermWith {scope : Sig} {runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) : Term scope → Runtime.Tm runtimeScope
  | .ret value => eraseValueWith rho value
  | .select receiver .payload => .var (erasePathWith rho receiver)
  | .app function argument =>
      .app (eraseTermWith rho function) (eraseTermWith rho argument)
  | .let' _ rhs body =>
      .let' (eraseTermWith rho rhs) (eraseTermWith rho.liftTerm body)
  | .staticApp _ function _ => eraseTermWith rho function
  | @Term.«open» _ sort _ _ _ package body =>
      .let' (eraseTermWith rho package)
        (eraseTermWith (rho.liftPayload sort) body)
  | .unlock _ scrutinee => .force (eraseTermWith rho scrutinee)
  | .objectApp _ function argument =>
      .app (eraseTermWith rho function) (eraseTermWith rho argument)
  | .objectLet _ _ rhs body =>
      .let' (eraseTermWith rho rhs) (eraseTermWith rho.liftTerm body)

end

/-! ## Exact generalized erasure equations -/

/-- Static abstraction is runtime-transparent; its body is erased under a
projection that forgets the new static variable. -/
@[simp]
theorem eraseValueWith_staticLam {scope : Sig} {runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) {sort : StaticSort}
    (interval : Interval sort scope)
    (body : Value (scope ▹ .static sort)) :
    eraseValueWith rho (.staticLam interval body) =
      eraseValueWith (rho.liftStatic sort) body := rfl

/-- Existential packaging erases to its runtime payload exactly. -/
@[simp]
theorem eraseValueWith_pack {scope : Sig} {runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) {sort : StaticSort}
    (interval : Interval sort scope)
    (payloadType : Ty (scope ▹ .static sort))
    (witness : StaticExpr sort scope) (payload : Value scope) :
    eraseValueWith rho (.pack interval payloadType witness payload) =
      eraseValueWith rho payload := rfl

/-- A source modal lock is an independently defined runtime suspension.
Its requirements and type annotations have no runtime representation. -/
@[simp]
theorem eraseValueWith_lock {scope : Sig} {runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) {separationCount : Nat}
    {modes : List CaptureMode}
    (requirements : ModalRequirements separationCount modes scope)
    (result : Ty scope) (closure : Capture scope) (body : Term scope) :
    eraseValueWith rho (.lock requirements result closure body) =
      .suspend (eraseTermWith rho body) := rfl

/-- A recursive object tag records the positive/open-only source discipline;
it has no runtime representation. -/
@[simp]
theorem eraseValueWith_recursiveObject {scope : Sig} {runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) (objectType : ObjectType scope)
    (payload : Value scope) :
    eraseValueWith rho (.recursiveObject objectType payload) =
      eraseValueWith rho payload := rfl

/-- Static application erases its interval and static argument without
changing or reordering the function computation. -/
@[simp]
theorem eraseTermWith_staticApp {scope : Sig} {runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) {sort : StaticSort}
    (interval : Interval sort scope) (function : Term scope)
    (argument : StaticExpr sort scope) :
    eraseTermWith rho (.staticApp interval function argument) =
      eraseTermWith rho function := rfl

/-- Existential opening executes the package once and becomes the
corresponding runtime binding.  The hidden static name has no runtime slot;
the payload variable does. -/
@[simp]
theorem eraseTermWith_open {scope : Sig} {runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) {sort : StaticSort}
    (interval : Interval sort scope)
    (payloadType : Ty (scope ▹ .static sort)) (result : Ty scope)
    (package : Term scope) (body : Term (PayloadScope scope sort)) :
    eraseTermWith rho
        (.open interval payloadType result package body) =
      .let' (eraseTermWith rho package)
        (eraseTermWith (rho.liftPayload sort) body) := rfl

/-- Modal unlocking forces its computed scrutinee exactly once; requirement
evidence remains absent from source runtime syntax. -/
@[simp]
theorem eraseTermWith_unlock {scope : Sig} {runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) {separationCount : Nat}
    {modes : List CaptureMode}
    (requirements : ModalRequirements separationCount modes scope)
    (scrutinee : Term scope) :
    eraseTermWith rho (.unlock requirements scrutinee) =
      .force (eraseTermWith rho scrutinee) := rfl

/-- Canonical erasure on the all-term fragment. -/
def eraseValue {scope : Nat} (value : Value (termScope scope)) :
    Runtime.Tm scope :=
  eraseValueWith Renaming.allTermIdentity value

/-- Canonical erasure on the all-term fragment. -/
def eraseTerm {scope : Nat} (term : Term (termScope scope)) :
    Runtime.Tm scope :=
  eraseTermWith Renaming.allTermIdentity term

/-! ## Exact canonical erasure equations -/

@[simp]
theorem eraseValue_staticLam {scope : Nat} {sort : StaticSort}
    (interval : Interval sort (termScope scope))
    (body : Value (termScope scope ▹ .static sort)) :
    eraseValue (.staticLam interval body) =
      eraseValueWith (Renaming.allTermIdentity.liftStatic sort) body := rfl

@[simp]
theorem eraseValue_pack {scope : Nat} {sort : StaticSort}
    (interval : Interval sort (termScope scope))
    (payloadType : Ty (termScope scope ▹ .static sort))
    (witness : StaticExpr sort (termScope scope))
    (payload : Value (termScope scope)) :
    eraseValue (.pack interval payloadType witness payload) =
      eraseValue payload := rfl

@[simp]
theorem eraseValue_lock {scope : Nat} {separationCount : Nat}
    {modes : List CaptureMode}
    (requirements : ModalRequirements separationCount modes (termScope scope))
    (result : Ty (termScope scope)) (closure : Capture (termScope scope))
    (body : Term (termScope scope)) :
    eraseValue (.lock requirements result closure body) =
      .suspend (eraseTerm body) := rfl

@[simp]
theorem eraseValue_recursiveObject {scope : Nat}
    (objectType : ObjectType (termScope scope))
    (payload : Value (termScope scope)) :
    eraseValue (.recursiveObject objectType payload) = eraseValue payload := rfl

@[simp]
theorem eraseTerm_staticApp {scope : Nat} {sort : StaticSort}
    (interval : Interval sort (termScope scope))
    (function : Term (termScope scope))
    (argument : StaticExpr sort (termScope scope)) :
    eraseTerm (.staticApp interval function argument) =
      eraseTerm function := rfl

@[simp]
theorem eraseTerm_open {scope : Nat} {sort : StaticSort}
    (interval : Interval sort (termScope scope))
    (payloadType : Ty (termScope scope ▹ .static sort))
    (result : Ty (termScope scope)) (package : Term (termScope scope))
    (body : Term (PayloadScope (termScope scope) sort)) :
    eraseTerm (.open interval payloadType result package body) =
      .let' (eraseTerm package)
        (eraseTermWith (Renaming.allTermIdentity.liftPayload sort) body) := rfl

@[simp]
theorem eraseTerm_unlock {scope : Nat} {separationCount : Nat}
    {modes : List CaptureMode}
    (requirements : ModalRequirements separationCount modes (termScope scope))
    (scrutinee : Term (termScope scope)) :
    eraseTerm (.unlock requirements scrutinee) =
      .force (eraseTerm scrutinee) := rfl

namespace CapturedIntersections

abbrev Renaming :=
  DOTCapture.Intersections.GeneralExpression.Erasure.Renaming
abbrev erasePathWith {source runtimeScope : Nat}
    (rho : Renaming source runtimeScope)
    (sourcePath : Embedding.CapturedIntersections.Path source) : Fin runtimeScope :=
  DOTCapture.Intersections.GeneralExpression.Erasure.erasePathWith
    rho sourcePath
abbrev eraseValueWith {source runtimeScope : Nat}
    (rho : Renaming source runtimeScope)
    (sourceValue : Embedding.CapturedIntersections.Value source) :
      Runtime.Tm runtimeScope :=
  DOTCapture.Intersections.GeneralExpression.Erasure.eraseValueWith
    rho sourceValue
abbrev eraseTermWith {source runtimeScope : Nat}
    (rho : Renaming source runtimeScope)
    (sourceTerm : Embedding.CapturedIntersections.Term source) :
      Runtime.Tm runtimeScope :=
  DOTCapture.Intersections.GeneralExpression.Erasure.eraseTermWith
    rho sourceTerm
abbrev eraseValue {scope : Nat}
    (sourceValue : Embedding.CapturedIntersections.Value scope) :
    Runtime.Tm scope :=
  DOTCapture.Intersections.GeneralExpression.Erasure.eraseValue sourceValue
abbrev eraseTerm {scope : Nat}
    (sourceTerm : Embedding.CapturedIntersections.Term scope) :
    Runtime.Tm scope :=
  DOTCapture.Intersections.GeneralExpression.Erasure.eraseTerm sourceTerm

end CapturedIntersections

/-- Reinterpret a captured-intersection runtime renaming on its embedded
all-term scope. -/
def embeddedRenaming {source runtimeScope : Nat}
    (rho : CapturedIntersections.Renaming source runtimeScope) :
    Renaming (termScope source) runtimeScope :=
  fun index => rho (projectVar index)

theorem embeddedRenaming_lift {source runtimeScope : Nat}
    (rho : CapturedIntersections.Renaming source runtimeScope) :
    embeddedRenaming
        (DOTCapture.Intersections.GeneralExpression.Erasure.Renaming.lift rho) =
      (embeddedRenaming rho).liftTerm := by
  funext index
  cases index <;> rfl

@[simp]
theorem liftTerm_embeddedRenaming {source runtimeScope : Nat}
    (rho : CapturedIntersections.Renaming source runtimeScope) :
    (embeddedRenaming rho).liftTerm =
      embeddedRenaming
        (DOTCapture.Intersections.GeneralExpression.Erasure.Renaming.lift rho) :=
  (embeddedRenaming_lift rho).symm

@[simp]
theorem oldIdentity_projectVar {scope : Nat}
    (index : BVar (termScope scope) .term) :
    DOTCapture.Intersections.GeneralExpression.Erasure.Renaming.identity
        (projectVar index) =
      Renaming.allTermIdentity index := by
  induction scope with
  | zero => nomatch index
  | succ scope induction =>
      cases index with
      | here => rfl
      | there older =>
          simp only [projectVar,
            DOTCapture.Intersections.GeneralExpression.Erasure.Renaming.identity_there,
            induction]
          rfl

@[simp]
theorem embeddedRenaming_identity {scope : Nat} :
    embeddedRenaming
        (DOTCapture.Intersections.GeneralExpression.Erasure.Renaming.identity :
          CapturedIntersections.Renaming scope scope) =
      Renaming.allTermIdentity := by
  funext index
  exact oldIdentity_projectVar index

@[simp]
theorem erasePathWith_embedding {source runtimeScope : Nat}
    (rho : CapturedIntersections.Renaming source runtimeScope)
    (sourcePath : Embedding.CapturedIntersections.Path source) :
    erasePathWith (embeddedRenaming rho) (Embedding.path sourcePath) =
      CapturedIntersections.erasePathWith rho sourcePath := by
  cases sourcePath
  simp only [erasePathWith, Embedding.path, embeddedRenaming,
    CapturedIntersections.erasePathWith,
    DOTCapture.Intersections.GeneralExpression.Erasure.erasePathWith,
    projectVar_embedVar]

mutual

@[simp]
def eraseValueWith_embedding {source runtimeScope : Nat}
    (rho : CapturedIntersections.Renaming source runtimeScope)
    (sourceValue : Embedding.CapturedIntersections.Value source) :
    eraseValueWith (embeddedRenaming rho) (Embedding.value sourceValue) =
      CapturedIntersections.eraseValueWith rho sourceValue :=
  match sourceValue with
  | .var name => by
      simp only [Embedding.value, eraseValueWith, embeddedRenaming,
        CapturedIntersections.eraseValueWith,
        DOTCapture.Intersections.GeneralExpression.Erasure.eraseValueWith,
        projectVar_embedVar]
  | .unit => rfl
  | .lam _ _ body => by
      simp only [Embedding.value, eraseValueWith,
        DOTCapture.Intersections.GeneralExpression.Erasure.eraseValueWith,
        liftTerm_embeddedRenaming]
      exact congrArg (fun erasedBody =>
          (.lam erasedBody : Runtime.Tm runtimeScope))
        (eraseTermWith_embedding rho.lift body)
  | .object _ payload => by
      simp only [Embedding.value, eraseValueWith,
        DOTCapture.Intersections.GeneralExpression.Erasure.eraseValueWith,
        eraseValueWith_embedding rho payload]
  | .objectConsumer _ _ body => by
      simp only [Embedding.value, eraseValueWith,
        DOTCapture.Intersections.GeneralExpression.Erasure.eraseValueWith,
        liftTerm_embeddedRenaming]
      exact congrArg (fun erasedBody =>
          (.lam erasedBody : Runtime.Tm runtimeScope))
        (eraseTermWith_embedding rho.lift body)

@[simp]
def eraseTermWith_embedding {source runtimeScope : Nat}
    (rho : CapturedIntersections.Renaming source runtimeScope)
    (sourceTerm : Embedding.CapturedIntersections.Term source) :
    eraseTermWith (embeddedRenaming rho) (Embedding.term sourceTerm) =
      CapturedIntersections.eraseTermWith rho sourceTerm :=
  match sourceTerm with
  | .ret sourceValue => by
      simp only [Embedding.term, eraseTermWith,
        DOTCapture.Intersections.GeneralExpression.Erasure.eraseTermWith,
        eraseValueWith_embedding rho sourceValue]
  | .select receiver label => by
      cases label
      simp only [Embedding.term, Embedding.valueLabel, eraseTermWith,
        DOTCapture.Intersections.GeneralExpression.Erasure.eraseTermWith,
        erasePathWith_embedding]
  | .app function argument => by
      simp only [Embedding.term, eraseTermWith,
        DOTCapture.Intersections.GeneralExpression.Erasure.eraseTermWith,
        eraseTermWith_embedding rho function,
        eraseTermWith_embedding rho argument]
  | .let' _ rhs body => by
      simp only [Embedding.term, eraseTermWith,
        DOTCapture.Intersections.GeneralExpression.Erasure.eraseTermWith,
        eraseTermWith_embedding rho rhs, liftTerm_embeddedRenaming]
      exact congrArg (fun erasedBody =>
          (.let' (CapturedIntersections.eraseTermWith rho rhs) erasedBody :
            Runtime.Tm runtimeScope))
        (eraseTermWith_embedding rho.lift body)
  | .objectApp _ function argument => by
      simp only [Embedding.term, eraseTermWith,
        DOTCapture.Intersections.GeneralExpression.Erasure.eraseTermWith,
        eraseTermWith_embedding rho function,
        eraseTermWith_embedding rho argument]
  | .objectLet _ _ rhs body => by
      simp only [Embedding.term, eraseTermWith,
        DOTCapture.Intersections.GeneralExpression.Erasure.eraseTermWith,
        eraseTermWith_embedding rho rhs, liftTerm_embeddedRenaming]
      exact congrArg (fun erasedBody =>
          (.let' (CapturedIntersections.eraseTermWith rho rhs) erasedBody :
            Runtime.Tm runtimeScope))
        (eraseTermWith_embedding rho.lift body)

end


/-- The cumulative embedding preserves captured-intersection runtime code
exactly. -/
@[simp]
theorem eraseValue_embedding {scope : Nat}
    (sourceValue : Embedding.CapturedIntersections.Value scope) :
    eraseValue (Embedding.value sourceValue) =
      CapturedIntersections.eraseValue sourceValue := by
  simpa only [eraseValue, CapturedIntersections.eraseValue,
    embeddedRenaming_identity] using
    eraseValueWith_embedding
      (DOTCapture.Intersections.GeneralExpression.Erasure.Renaming.identity :
        CapturedIntersections.Renaming scope scope) sourceValue

/-- The cumulative embedding preserves captured-intersection runtime code
exactly. -/
@[simp]
theorem eraseTerm_embedding {scope : Nat}
    (sourceTerm : Embedding.CapturedIntersections.Term scope) :
    eraseTerm (Embedding.term sourceTerm) =
      CapturedIntersections.eraseTerm sourceTerm := by
  simpa only [eraseTerm, CapturedIntersections.eraseTerm,
    embeddedRenaming_identity] using
    eraseTermWith_embedding
      (DOTCapture.Intersections.GeneralExpression.Erasure.Renaming.identity :
        CapturedIntersections.Renaming scope scope) sourceTerm

end DOTCapture.ModalIntersections.Erasure
