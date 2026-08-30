import Coercions.DOT.Captures.BinderOnly.Term
import Coercions.ManySortedFC.Runtime
import Coercions.ManySortedFC.TermProjection
import Coercions.Translation.ManySorted.BinderOnly.Layout

/-!
# Direct runtime erasure of the binder-only source

This module forgets source types, static witnesses, intervals, and package
annotations directly into the runtime shared by many-sorted FC.  It states a
syntax-directed erasure only.  Agreement with future elaboration is a
separate theorem and is not claimed here.
-/

namespace DOTCaptureToManySortedFC.BinderOnly.SourceErasure

/-- Map the ordinary variables of a heterogeneous source scope into an
arbitrary runtime scope. -/
abbrev Renaming (source : DOTCapture.BinderOnly.Sig) (target : Nat) : Type :=
  DOTCapture.BinderOnly.BVar source .term → Fin target

namespace Renaming

/-- Precompose with a source heterogeneous renaming. -/
def precomp {source middle : DOTCapture.BinderOnly.Sig} {target : Nat}
    (rho : DOTCapture.BinderOnly.Rename source middle)
    (sigma : Renaming middle target) : Renaming source target :=
  fun index => sigma (rho.var index)

/-- Postcompose with an ordinary runtime renaming. -/
def postcomp {source : DOTCapture.BinderOnly.Sig} {middle target : Nat}
    (rho : Renaming source middle)
    (sigma : ManySortedFC.Runtime.Renaming middle target) :
    Renaming source target :=
  fun index => sigma (rho index)

/-- Preserve one new term variable in both source and runtime scopes. -/
def liftTerm {source : DOTCapture.BinderOnly.Sig} {target : Nat}
    (rho : Renaming source target) :
    Renaming (source ▹ .term) (Nat.succ target) :=
  fun
  | .here => 0
  | .there index => (rho index).succ

/-- Forget one source static binder. -/
def liftStatic {source : DOTCapture.BinderOnly.Sig} {target : Nat}
    (rho : Renaming source target) (sort : DOTCapture.BinderOnly.StaticSort) :
    Renaming (source ▹ .static sort) target :=
  fun
  | .there index => rho index

/-- Forget an existential's hidden static binder while retaining its newest
payload term binder. -/
def liftPayload {source : DOTCapture.BinderOnly.Sig} {target : Nat}
    (rho : Renaming source target) (sort : DOTCapture.BinderOnly.StaticSort) :
    Renaming (DOTCapture.BinderOnly.PayloadScope source sort)
      (Nat.succ target) :=
  (rho.liftStatic sort).liftTerm

@[simp]
theorem precomp_liftTerm
    {source middle : DOTCapture.BinderOnly.Sig} {target : Nat}
    (rho : DOTCapture.BinderOnly.Rename source middle)
    (sigma : Renaming middle target) :
    precomp (rho.lift (kind := .term)) sigma.liftTerm =
      (precomp rho sigma).liftTerm := by
  funext index
  cases index <;> rfl

@[simp]
theorem precomp_liftStatic
    {source middle : DOTCapture.BinderOnly.Sig} {target : Nat}
    (rho : DOTCapture.BinderOnly.Rename source middle)
    (sigma : Renaming middle target)
    (sort : DOTCapture.BinderOnly.StaticSort) :
    precomp (rho.lift (kind := .static sort)) (sigma.liftStatic sort) =
      (precomp rho sigma).liftStatic sort := by
  funext index
  cases index
  rfl

@[simp]
theorem precomp_liftPayload
    {source middle : DOTCapture.BinderOnly.Sig} {target : Nat}
    (rho : DOTCapture.BinderOnly.Rename source middle)
    (sigma : Renaming middle target)
    (sort : DOTCapture.BinderOnly.StaticSort) :
    precomp (rho.liftPayload sort) (sigma.liftPayload sort) =
      (precomp rho sigma).liftPayload sort := by
  unfold DOTCapture.BinderOnly.Rename.liftPayload liftPayload
  rw [precomp_liftTerm, precomp_liftStatic]

@[simp]
theorem postcomp_liftTerm
    {source : DOTCapture.BinderOnly.Sig} {middle target : Nat}
    (rho : Renaming source middle)
    (sigma : ManySortedFC.Runtime.Renaming middle target) :
    postcomp rho.liftTerm sigma.lift = (postcomp rho sigma).liftTerm := by
  funext index
  cases index <;> rfl

@[simp]
theorem postcomp_liftStatic
    {source : DOTCapture.BinderOnly.Sig} {middle target : Nat}
    (rho : Renaming source middle)
    (sigma : ManySortedFC.Runtime.Renaming middle target)
    (sort : DOTCapture.BinderOnly.StaticSort) :
    postcomp (rho.liftStatic sort) sigma =
      (postcomp rho sigma).liftStatic sort := by
  funext index
  cases index
  rfl

@[simp]
theorem postcomp_liftPayload
    {source : DOTCapture.BinderOnly.Sig} {middle target : Nat}
    (rho : Renaming source middle)
    (sigma : ManySortedFC.Runtime.Renaming middle target)
    (sort : DOTCapture.BinderOnly.StaticSort) :
    postcomp (rho.liftPayload sort) sigma.lift =
      (postcomp rho sigma).liftPayload sort := by
  unfold liftPayload
  rw [postcomp_liftTerm, postcomp_liftStatic]

end Renaming

mutual

/-- Erase a source value using an arbitrary projection of its term
variables. -/
def eraseValueWith {scope : DOTCapture.BinderOnly.Sig} {runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) :
    DOTCapture.BinderOnly.Value scope →
      ManySortedFC.Runtime.Tm runtimeScope
  | .var name => .var (rho name)
  | .unit => .unit
  | .lam _domain _codomain body =>
      .lam (eraseTermWith rho.liftTerm body)
  | @DOTCapture.BinderOnly.Value.staticLam _ sort _interval body =>
      eraseValueWith (rho.liftStatic sort) body
  | .pack _interval _payloadType _witness payload =>
      eraseValueWith rho payload

/-- Erase a source computation using an arbitrary projection of its term
variables. -/
def eraseTermWith {scope : DOTCapture.BinderOnly.Sig} {runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) :
    DOTCapture.BinderOnly.Term scope →
      ManySortedFC.Runtime.Tm runtimeScope
  | .ret value => eraseValueWith rho value
  | .app function argument =>
      .app (eraseValueWith rho function) (eraseValueWith rho argument)
  | .let' _result rhs body =>
      .let' (eraseTermWith rho rhs) (eraseTermWith rho.liftTerm body)
  | .staticApp _interval function _argument => eraseValueWith rho function
  | @DOTCapture.BinderOnly.Term.«open» _ sort _interval _payloadType _result
      package body =>
      .let' (eraseValueWith rho package)
        (eraseTermWith (rho.liftPayload sort) body)

end

/-- Canonical source-to-runtime variable projection: first compile the source
variable to its many-sorted target coordinate, then forget target static and
evidence binders. -/
def compiledRenaming {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope) :
    Renaming scope (sig context).termCount :=
  fun index => ManySortedFC.BVar.toTermIndex (termVar context index)

/-- Direct erasure of a source value under its source context. -/
def eraseValue {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (value : DOTCapture.BinderOnly.Value scope) :
    ManySortedFC.Runtime.Tm (sig context).termCount :=
  eraseValueWith (compiledRenaming context) value

/-- Direct erasure of a source computation under its source context. -/
def eraseTerm {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (term : DOTCapture.BinderOnly.Term scope) :
    ManySortedFC.Runtime.Tm (sig context).termCount :=
  eraseTermWith (compiledRenaming context) term

/-! ## Exact erasure equations -/

@[simp]
theorem eraseValue_var {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (name : DOTCapture.BinderOnly.BVar scope .term) :
    eraseValue context (.var name) =
      .var (ManySortedFC.BVar.toTermIndex (termVar context name)) := rfl

@[simp]
theorem eraseValue_unit {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope) :
    eraseValue context (.unit : DOTCapture.BinderOnly.Value scope) =
      .unit := rfl

@[simp]
theorem eraseValue_lam {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (domain codomain : DOTCapture.BinderOnly.Ty scope)
    (body : DOTCapture.BinderOnly.Term (scope ▹ .term)) :
    eraseValue context (.lam domain codomain body) =
      .lam (eraseTermWith (compiledRenaming context).liftTerm body) := rfl

@[simp]
theorem eraseValue_staticLam {scope : DOTCapture.BinderOnly.Sig}
    {sort : DOTCapture.BinderOnly.StaticSort}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (interval : DOTCapture.BinderOnly.Interval sort scope)
    (body : DOTCapture.BinderOnly.Value (scope ▹ .static sort)) :
    eraseValue context (.staticLam interval body) =
      eraseValueWith ((compiledRenaming context).liftStatic sort) body := rfl

@[simp]
theorem eraseValue_pack {scope : DOTCapture.BinderOnly.Sig}
    {sort : DOTCapture.BinderOnly.StaticSort}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (interval : DOTCapture.BinderOnly.Interval sort scope)
    (payloadType : DOTCapture.BinderOnly.Ty (scope ▹ .static sort))
    (witness : DOTCapture.BinderOnly.StaticExpr sort scope)
    (payload : DOTCapture.BinderOnly.Value scope) :
    eraseValue context (.pack interval payloadType witness payload) =
      eraseValue context payload := rfl

@[simp]
theorem eraseTerm_ret {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (value : DOTCapture.BinderOnly.Value scope) :
    eraseTerm context (.ret value) = eraseValue context value := rfl

@[simp]
theorem eraseTerm_app {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (function argument : DOTCapture.BinderOnly.Value scope) :
    eraseTerm context (.app function argument) =
      .app (eraseValue context function) (eraseValue context argument) := rfl

@[simp]
theorem eraseTerm_let {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (result : DOTCapture.BinderOnly.Ty scope)
    (rhs : DOTCapture.BinderOnly.Term scope)
    (body : DOTCapture.BinderOnly.Term (scope ▹ .term)) :
    eraseTerm context (.let' result rhs body) =
      .let' (eraseTerm context rhs)
        (eraseTermWith (compiledRenaming context).liftTerm body) := rfl

@[simp]
theorem eraseTerm_staticApp {scope : DOTCapture.BinderOnly.Sig}
    {sort : DOTCapture.BinderOnly.StaticSort}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (interval : DOTCapture.BinderOnly.Interval sort scope)
    (function : DOTCapture.BinderOnly.Value scope)
    (argument : DOTCapture.BinderOnly.StaticExpr sort scope) :
    eraseTerm context (.staticApp interval function argument) =
      eraseValue context function := rfl

@[simp]
theorem eraseTerm_open {scope : DOTCapture.BinderOnly.Sig}
    {sort : DOTCapture.BinderOnly.StaticSort}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (interval : DOTCapture.BinderOnly.Interval sort scope)
    (payloadType : DOTCapture.BinderOnly.Ty (scope ▹ .static sort))
    (result : DOTCapture.BinderOnly.Ty scope)
    (package : DOTCapture.BinderOnly.Value scope)
    (body : DOTCapture.BinderOnly.Term
      (DOTCapture.BinderOnly.PayloadScope scope sort)) :
    eraseTerm context
        (.«open» interval payloadType result package body) =
      .let' (eraseValue context package)
        (eraseTermWith ((compiledRenaming context).liftPayload sort) body) := rfl

/-! ## Naturality of the generalized erasure -/

mutual

/-- Source renaming changes only the variable projection seen by erasure. -/
@[simp]
def eraseValueWith_sourceRename
    {source middle : DOTCapture.BinderOnly.Sig} {runtimeScope : Nat}
    (sigma : Renaming middle runtimeScope)
    (rho : DOTCapture.BinderOnly.Rename source middle)
    (value : DOTCapture.BinderOnly.Value source) :
    eraseValueWith sigma (value.rename rho) =
      eraseValueWith (Renaming.precomp rho sigma) value :=
  match value with
  | .var _ => rfl
  | .unit => rfl
  | .lam _ _ body => by
      simp only [DOTCapture.BinderOnly.Value.rename, eraseValueWith,
        eraseTermWith_sourceRename sigma.liftTerm
          (rho.lift (kind := .term)) body,
        Renaming.precomp_liftTerm]
  | @DOTCapture.BinderOnly.Value.staticLam _ sort _interval body => by
      simp only [DOTCapture.BinderOnly.Value.rename, eraseValueWith,
        eraseValueWith_sourceRename (sigma.liftStatic sort)
          (rho.lift (kind := .static sort)) body,
        Renaming.precomp_liftStatic]
  | .pack _ _ _ payload => by
      simp only [DOTCapture.BinderOnly.Value.rename, eraseValueWith,
        eraseValueWith_sourceRename sigma rho payload]

/-- Source renaming changes only the variable projection seen by computation
erasure. -/
@[simp]
def eraseTermWith_sourceRename
    {source middle : DOTCapture.BinderOnly.Sig} {runtimeScope : Nat}
    (sigma : Renaming middle runtimeScope)
    (rho : DOTCapture.BinderOnly.Rename source middle)
    (term : DOTCapture.BinderOnly.Term source) :
    eraseTermWith sigma (term.rename rho) =
      eraseTermWith (Renaming.precomp rho sigma) term :=
  match term with
  | .ret value => by
      simp only [DOTCapture.BinderOnly.Term.rename, eraseTermWith,
        eraseValueWith_sourceRename sigma rho value]
  | .app function argument => by
      simp only [DOTCapture.BinderOnly.Term.rename, eraseTermWith,
        eraseValueWith_sourceRename sigma rho function,
        eraseValueWith_sourceRename sigma rho argument]
  | .let' _ rhs body => by
      simp only [DOTCapture.BinderOnly.Term.rename, eraseTermWith,
        eraseTermWith_sourceRename sigma rho rhs,
        eraseTermWith_sourceRename sigma.liftTerm
          (rho.lift (kind := .term)) body,
        Renaming.precomp_liftTerm]
  | .staticApp _ function _ => by
      simp only [DOTCapture.BinderOnly.Term.rename, eraseTermWith,
        eraseValueWith_sourceRename sigma rho function]
  | @DOTCapture.BinderOnly.Term.«open» _ sort _interval _payloadType _result
      package body => by
      simp only [DOTCapture.BinderOnly.Term.rename, eraseTermWith,
        eraseValueWith_sourceRename sigma rho package,
        eraseTermWith_sourceRename (sigma.liftPayload sort)
          (rho.liftPayload sort) body,
        Renaming.precomp_liftPayload]

end

mutual

/-- Direct erasure is natural in its surrounding runtime scope. -/
def eraseValueWith_runtimeRename
    {scope : DOTCapture.BinderOnly.Sig} {source target : Nat}
    (rho : Renaming scope source)
    (sigma : ManySortedFC.Runtime.Renaming source target)
    (value : DOTCapture.BinderOnly.Value scope) :
    (eraseValueWith rho value).rename sigma =
      eraseValueWith (Renaming.postcomp rho sigma) value :=
  match value with
  | .var _ => rfl
  | .unit => rfl
  | .lam _ _ body => by
      simp only [eraseValueWith, ManySortedFC.Runtime.Tm.rename,
        eraseTermWith_runtimeRename rho.liftTerm sigma.lift body,
        Renaming.postcomp_liftTerm]
  | @DOTCapture.BinderOnly.Value.staticLam _ sort _interval body => by
      simp only [eraseValueWith,
        eraseValueWith_runtimeRename (rho.liftStatic sort) sigma body,
        Renaming.postcomp_liftStatic]
  | .pack _ _ _ payload => by
      simp only [eraseValueWith,
        eraseValueWith_runtimeRename rho sigma payload]

/-- Computation erasure is natural in its surrounding runtime scope. -/
def eraseTermWith_runtimeRename
    {scope : DOTCapture.BinderOnly.Sig} {source target : Nat}
    (rho : Renaming scope source)
    (sigma : ManySortedFC.Runtime.Renaming source target)
    (term : DOTCapture.BinderOnly.Term scope) :
    (eraseTermWith rho term).rename sigma =
      eraseTermWith (Renaming.postcomp rho sigma) term :=
  match term with
  | .ret value => by
      simp only [eraseTermWith,
        eraseValueWith_runtimeRename rho sigma value]
  | .app function argument => by
      simp only [eraseTermWith, ManySortedFC.Runtime.Tm.rename,
        eraseValueWith_runtimeRename rho sigma function,
        eraseValueWith_runtimeRename rho sigma argument]
  | .let' _ rhs body => by
      simp only [eraseTermWith, ManySortedFC.Runtime.Tm.rename,
        eraseTermWith_runtimeRename rho sigma rhs,
        eraseTermWith_runtimeRename rho.liftTerm sigma.lift body,
        Renaming.postcomp_liftTerm]
  | .staticApp _ function _ => by
      simp only [eraseTermWith,
        eraseValueWith_runtimeRename rho sigma function]
  | @DOTCapture.BinderOnly.Term.«open» _ sort _interval _payloadType _result
      package body => by
      simp only [eraseTermWith, ManySortedFC.Runtime.Tm.rename,
        eraseValueWith_runtimeRename rho sigma package,
        eraseTermWith_runtimeRename (rho.liftPayload sort) sigma.lift body,
        Renaming.postcomp_liftPayload]

end

end DOTCaptureToManySortedFC.BinderOnly.SourceErasure
