import LambdaPToFCo.Direct.Adapter

/-!
# Direct-adapter regression

This regression checks a non-structural conversion and bottom elimination in
the original `SystemFCo`.  Both are ordinary target terms; neither relies on
`SystemFCoExt` or on a new coercion constructor.
-/

namespace LambdaPToFCo.Direct.AdapterRegression

open SystemFCo
open Adapter

/-- A closed value at target Top, obtained with the original structural
Top coercion. -/
def topValue : Exp [] :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

noncomputable def topValue_hasType :
    Exp.HasType Ctx.empty topValue .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

theorem topValue_isValue : Exp.IsValue topValue :=
  .castTop .abs

/-- An ordinary function performs a conversion which the structural
coercion grammar does not provide: `Top` to `Top -> Top`. -/
def topToIdentityFunction : Exp [] :=
  ofBody .top (.abs .top (.var .here))

noncomputable def topToIdentityFunction_hasType :
    Exp.HasType Ctx.empty topToIdentityFunction
      (.arrow .top (.arrow .top .top)) :=
  ofBody_hasType (.abs (.var Ctx.Lookup.here))

/-- Compose the ordinary identity adapter with that non-structural adapter. -/
def composed : Exp [] :=
  compose .top (identity .top) topToIdentityFunction

noncomputable def composed_hasType :
    Exp.HasType Ctx.empty composed
      (.arrow .top (.arrow .top .top)) :=
  compose_hasType (identity_hasType Ctx.empty .top)
    topToIdentityFunction_hasType

noncomputable def applied_hasType :
    Exp.HasType Ctx.empty (apply composed topValue) (.arrow .top .top) :=
  apply_hasType composed_hasType topValue_hasType

/-- Direct adapters execute through the original target beta rule. -/
theorem direct_beta :
    Exp.Step (apply topToIdentityFunction topValue)
      (.abs .top (.var .here)) := by
  simpa only [topToIdentityFunction, Exp.subst]
    using ofBody_apply_step topValue_isValue

/-- In an open original-SystemFCo context, `forall X. X` eliminates to an
arbitrary target type by ordinary type application. -/
abbrev BottomContext : Ctx ([] ,, .var) :=
  Ctx.empty.bindVar bottomTy

def bottomVariable : Exp ([] ,, .var) :=
  .var .here

noncomputable def bottomVariable_hasType :
    Exp.HasType BottomContext bottomVariable (bottomTy : Ty ([] ,, .var)) := by
  have variableTyping :
      Exp.HasType BottomContext bottomVariable
        ((bottomTy : Ty []).weaken .var) :=
    .var Ctx.Lookup.here
  exact variableTyping

noncomputable def bottomToTop_hasType :
    Exp.HasType BottomContext (eliminateBottom bottomVariable .top) .top :=
  eliminateBottom_hasType bottomVariable_hasType

end LambdaPToFCo.Direct.AdapterRegression
