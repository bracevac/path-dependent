import LambdaPToFCo.Direct.Formation

/-!
Focused formation closure is type-directed: in particular, closing a selected
type records a final future value field and never asks well-formedness for an
inhabitant of the hidden selected type.
-/

namespace LambdaPToFCo.Direct.FormationRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal.Formation

/-- The exact singleton constructor retains one formed path result, including
its actual interface, rather than only its erased representation. -/
noncomputable def singleton
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {path : LambdaPFC.Path n} {referentType : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty referentType))
    (referent : Slot sourceContext targetContext referentType) :
    Formation sourceContext targetContext (.Single path)
      (.stable (Single.plan referent.shape.inputTy)) :=
  .singleton typing referent.interface referent.formation

/-- No selected value or selected interface is an argument: the final value
is bound inside the faithful carrier telescope. -/
noncomputable def closeSelected
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    (focus : Telescope sig) {selectedType : Ty focus.scope}
    (selected : Formation sourceContext (focus.context targetContext)
      (.TSel path label) (.opaque selectedType)) :
    Proper sourceContext targetContext (.TSel path label) :=
  Proper.close focus selected

end LambdaPToFCo.Direct.FormationRegression
