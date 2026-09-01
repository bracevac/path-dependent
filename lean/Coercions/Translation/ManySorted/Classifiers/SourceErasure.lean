import Coercions.Translation.ManySorted.Classifiers.Source
import Coercions.ManySortedFC.Runtime

/-!
# Independent erasure of classifier-filter programs

This erasure is defined solely from the surface language.  It does not call
the classifier lowering or inspect a generated target capture.  Classifier
filters are static, while the complete call-by-value term spine is retained.
-/

namespace DOTCaptureToManySortedFC.Classifiers.Source

/-- Erase a source term into the shared runtime. -/
def Term.erase : {scope : Nat} -> Term scope -> ManySortedFC.Runtime.Tm scope
  | _, .var index => .var index
  | _, .unit => .unit
  | _, .lam body => .lam body.erase
  | _, .app function argument => .app function.erase argument.erase
  | _, .let' rhs body => .let' rhs.erase body.erase

/-- The independently defined runtime meaning of a classifier-annotated
source program. -/
def Program.erase {Base : Type} {scope : Nat} (program : Program Base scope) :
    ManySortedFC.Runtime.Tm scope :=
  program.term.erase

@[simp]
theorem Term.erase_var {scope : Nat} (index : Fin scope) :
    (Term.var index).erase = ManySortedFC.Runtime.Tm.var index := rfl

@[simp]
theorem Term.erase_unit {scope : Nat} :
    (Term.unit : Term scope).erase = ManySortedFC.Runtime.Tm.unit := rfl

@[simp]
theorem Term.erase_lam {scope : Nat} (body : Term (scope + 1)) :
    (Term.lam body).erase = ManySortedFC.Runtime.Tm.lam body.erase := rfl

@[simp]
theorem Term.erase_app {scope : Nat} (function argument : Term scope) :
    (Term.app function argument).erase =
      ManySortedFC.Runtime.Tm.app function.erase argument.erase := rfl

@[simp]
theorem Term.erase_let {scope : Nat} (rhs : Term scope)
    (body : Term (scope + 1)) :
    (Term.let' rhs body).erase =
      ManySortedFC.Runtime.Tm.let' rhs.erase body.erase := rfl

@[simp]
theorem Program.erase_eq_term {Base : Type} {scope : Nat}
    (program : Program Base scope) :
    program.erase = program.term.erase := rfl

end DOTCaptureToManySortedFC.Classifiers.Source
