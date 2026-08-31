import Coercions.DOT.Captures.Acyclic.GeneralExpression.Syntax
import Coercions.DOT.Captures.Acyclic.Structural

/-!
# Structural laws for general captured-DOT expressions
-/

namespace DOTCapture.Acyclic.GeneralExpression

namespace ObjectSig

@[simp]
theorem formedType_rename {source target : Scope}
    (signature : ObjectSig source) (rho : Rename source target) :
    formedType (signature.rename rho) = (formedType signature).rename rho := by
  cases signature
  rfl

@[simp]
theorem formedType_weaken {scope : Scope} (signature : ObjectSig scope) :
    formedType signature.weaken = (formedType signature).weaken := by
  exact formedType_rename signature Rename.succ

end ObjectSig

namespace Capture

@[simp]
theorem seq_rename {source target : Scope} (first second : Capture source)
    (rho : Rename source target) :
    (seq first second).rename rho =
      seq (first.rename rho) (second.rename rho) := by
  cases first <;> rfl

end Capture

namespace ObjectArgument

@[simp]
theorem classify_rename {source target : Scope} (term : Term source)
    (rho : Rename source target) :
    classify (term.rename rho) = classify term := by
  cases term with
  | ret value => cases value <;> rfl
  | select => rfl
  | app => rfl
  | let' => rfl

end ObjectArgument

mutual

@[simp]
def Value.rename_id {scope : Scope} (value : Value scope) :
    value.rename Rename.id = value :=
  match value with
  | .var _ => rfl
  | .unit => rfl
  | .lam domain codomain body => by
      simp only [Value.rename, DOTCapture.Acyclic.Ty.rename_id domain,
        DOTCapture.Acyclic.Ty.rename_id codomain,
        DOTCapture.Acyclic.Rename.lift_id, Term.rename_id body]
  | .object signature typeWitness captureWitness payload => by
      simp only [Value.rename,
        DOTCapture.Acyclic.ObjectSig.rename_id signature,
        DOTCapture.Acyclic.Ty.rename_id typeWitness,
        DOTCapture.Acyclic.Capture.rename_id captureWitness,
        Value.rename_id payload]

@[simp]
def Term.rename_id {scope : Scope} (term : Term scope) :
    term.rename Rename.id = term :=
  match term with
  | .ret value => by
      simp only [Term.rename, Value.rename_id value]
  | .select receiver _ => by
      simp only [Term.rename, DOTCapture.Acyclic.Path.rename_id receiver]
  | .app function argument => by
      simp only [Term.rename, Term.rename_id function, Term.rename_id argument]
  | .let' result rhs body => by
      simp only [Term.rename, DOTCapture.Acyclic.Ty.rename_id result,
        Term.rename_id rhs, DOTCapture.Acyclic.Rename.lift_id,
        Term.rename_id body]

end

mutual

@[simp]
def Value.rename_comp {first second third : Scope} (value : Value first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (value.rename rho₁).rename rho₂ = value.rename (rho₁.comp rho₂) :=
  match value with
  | .var _ => rfl
  | .unit => rfl
  | .lam domain codomain body => by
      simp only [Value.rename, DOTCapture.Acyclic.Ty.rename_comp domain,
        DOTCapture.Acyclic.Ty.rename_comp codomain, Term.rename_comp body,
        DOTCapture.Acyclic.Rename.lift_comp]
  | .object signature typeWitness captureWitness payload => by
      simp only [Value.rename,
        DOTCapture.Acyclic.ObjectSig.rename_comp signature,
        DOTCapture.Acyclic.Ty.rename_comp typeWitness,
        DOTCapture.Acyclic.Capture.rename_comp captureWitness,
        Value.rename_comp payload]

@[simp]
def Term.rename_comp {first second third : Scope} (term : Term first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (term.rename rho₁).rename rho₂ = term.rename (rho₁.comp rho₂) :=
  match term with
  | .ret value => by
      simp only [Term.rename, Value.rename_comp value]
  | .select receiver _ => by
      simp only [Term.rename, DOTCapture.Acyclic.Path.rename_comp receiver]
  | .app function argument => by
      simp only [Term.rename, Term.rename_comp function,
        Term.rename_comp argument]
  | .let' result rhs body => by
      simp only [Term.rename, DOTCapture.Acyclic.Ty.rename_comp result,
        Term.rename_comp rhs, Term.rename_comp body,
        DOTCapture.Acyclic.Rename.lift_comp]

end

end DOTCapture.Acyclic.GeneralExpression
