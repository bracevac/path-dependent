import Coercions.FCsub.Syntax
import Coercions.FCsub.Runtime

/-!
# Erasure from annotated FCsub to its own runtime

All type names, constraint certificates, casts, and static telescope
abstractions/applications disappear.  Existential opening retains exactly the
computational payload as an ordinary runtime `let` binder.
-/

namespace FCsub

namespace Tm

/-- Erase an annotated FCsub term to the standalone FCsub runtime. -/
def erase {scope : Sig} (term : Tm scope) : Runtime.Tm scope :=
  match term with
  | .unit => .unit
  | .var index => .var index
  | .lam _ body => .lam body.erase
  | .app function argument => .app function.erase argument.erase
  | .let' rhs body => .let' rhs.erase body.erase
  | .cast inner _ => inner.erase
  | .pack _ _ _ _ payload => payload.erase
  | @Tm.open _ names constraints _ _ scrutinee body =>
      .let' scrutinee.erase
        (body.erase.subst (Runtime.Subst.dropPayload names constraints))
  | @Tm.slam _ names constraints _ body =>
      body.erase.subst (Runtime.Subst.dropStatic names constraints)
  | .sapp _ function _ _ => function.erase
  | .newtype _ body => body.erase.subst Runtime.Subst.dropNewtype
  | .foldRec _ _ inner => inner.erase
  | .unfoldRec _ _ inner => inner.erase

@[simp]
theorem erase_unit {scope : Sig} :
    (Tm.unit : Tm scope).erase = Runtime.Tm.unit := rfl

@[simp]
theorem erase_var {scope : Sig} (index : BVar scope .term) :
    (Tm.var index).erase = Runtime.Tm.var index := rfl

@[simp]
theorem erase_lam {scope : Sig} (domain : Ty scope)
    (body : Tm (scope ▹ .term)) :
    (Tm.lam domain body).erase = Runtime.Tm.lam body.erase := rfl

@[simp]
theorem erase_app {scope : Sig} (function argument : Tm scope) :
    (Tm.app function argument).erase =
      Runtime.Tm.app function.erase argument.erase := rfl

@[simp]
theorem erase_let {scope : Sig} (rhs : Tm scope)
    (body : Tm (scope ▹ .term)) :
    (Tm.let' rhs body).erase = Runtime.Tm.let' rhs.erase body.erase := rfl

@[simp]
theorem erase_cast {scope : Sig} (term : Tm scope) (evidence : LeCo scope) :
    (Tm.cast term evidence).erase = term.erase := rfl

@[simp]
theorem erase_pack {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints)
    (payloadType : Ty (StaticScope scope names constraints))
    (witnesses : TypeArgs scope names) (evidence : LeArgs scope constraints)
    (payload : Tm scope) :
    (Tm.pack telescope payloadType witnesses evidence payload).erase =
      payload.erase := rfl

@[simp]
theorem erase_open {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints)
    (payloadType : Ty (StaticScope scope names constraints))
    (scrutinee : Tm scope)
    (body : Tm (PayloadScope scope names constraints)) :
    (Tm.open telescope payloadType scrutinee body).erase =
      Runtime.Tm.let' scrutinee.erase
        (body.erase.subst (Runtime.Subst.dropPayload names constraints)) := rfl

@[simp]
theorem erase_slam {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints)
    (body : Tm (StaticScope scope names constraints)) :
    (Tm.slam telescope body).erase =
      body.erase.subst (Runtime.Subst.dropStatic names constraints) := rfl

@[simp]
theorem erase_sapp {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints) (function : Tm scope)
    (witnesses : TypeArgs scope names) (evidence : LeArgs scope constraints) :
    (Tm.sapp telescope function witnesses evidence).erase =
      function.erase := rfl

@[simp]
theorem erase_newtype {scope : Sig} (witness : Ty scope)
    (body : Tm (NewtypeScope scope)) :
    (Tm.newtype witness body).erase =
      body.erase.subst Runtime.Subst.dropNewtype := rfl

@[simp]
theorem erase_foldRec {scope : Sig} {names : Nat}
    (bodies : RecBodies scope names names) (index : Fin names)
    (term : Tm scope) :
    (Tm.foldRec bodies index term).erase = term.erase := rfl

@[simp]
theorem erase_unfoldRec {scope : Sig} {names : Nat}
    (bodies : RecBodies scope names names) (index : Fin names)
    (term : Tm scope) :
    (Tm.unfoldRec bodies index term).erase = term.erase := rfl

end Tm

end FCsub
