import SystemFCoExt.Reduction

/-! Closed progress for the explicit-coercion target. -/

namespace SystemFCoExt.Exp

/-- Canonical forms include the structural cast wrappers consumed by eliminators. -/
inductive Canonical : Exp sig -> Ty sig -> Prop where
| abs : Canonical (.abs parameter body) (.arrow parameter result)
| tabs : Canonical (.tabs body) (.poly result)
| cabs : Canonical (.cabs source target body) (.qual source target result)
| castTop : IsValue expression ->
    Canonical (.cast expression (.top source)) .top
| castArrow : IsValue expression ->
    Canonical (.cast expression (.arrow domain codomain)) (.arrow parameter result)
| castPoly : IsValue expression ->
    Canonical (.cast expression (.poly body)) (.poly result)
| castQual : IsValue expression ->
    Canonical (.cast expression (.qual argument coercionResult))
      (.qual source target typeResult)

theorem canonical
    (typing : context |-e expression : ty)
    (value : IsValue expression) : Canonical expression ty := by
  cases value with
  | abs => cases typing; exact .abs
  | tabs => cases typing; exact .tabs
  | cabs => cases typing; exact .cabs
  | castTop value =>
      cases typing with
      | cast _ coercionTyping => cases coercionTyping; exact .castTop value
  | castArrow value =>
      cases typing with
      | cast _ coercionTyping => cases coercionTyping; exact .castArrow value
  | castPoly value =>
      cases typing with
      | cast _ coercionTyping => cases coercionTyping; exact .castPoly value
  | castQual value =>
      cases typing with
      | cast _ coercionTyping => cases coercionTyping; exact .castQual value

theorem progress :
    {expression : Exp []} -> {ty : Ty []} ->
    (Ctx.empty |-e expression : ty) ->
    IsValue expression \/ Exists fun next => Step expression next
  | _, _, .var lookup => nomatch lookup
  | _, _, .abs _ => Or.inl .abs
  | _, _, .app functionTyping argumentTyping =>
      match progress functionTyping with
      | Or.inr ⟨_, step⟩ => Or.inr ⟨_, .appFunction step⟩
      | Or.inl functionValue =>
          match progress argumentTyping with
          | Or.inr ⟨_, step⟩ => Or.inr ⟨_, .appArgument functionValue step⟩
          | Or.inl argumentValue =>
              match canonical functionTyping functionValue with
              | .abs => Or.inr ⟨_, .beta argumentValue⟩
              | .castArrow innerValue =>
                  Or.inr ⟨_, .castArrowApp innerValue argumentValue⟩
  | _, _, .tabs _ => Or.inl .tabs
  | _, _, .tapp functionTyping =>
      match progress functionTyping with
      | Or.inr ⟨_, step⟩ => Or.inr ⟨_, .tappFunction step⟩
      | Or.inl functionValue =>
          match canonical functionTyping functionValue with
          | .tabs => Or.inr ⟨_, .typeBeta⟩
          | .castPoly innerValue => Or.inr ⟨_, .castPolyTapp innerValue⟩
  | _, _, .cabs _ => Or.inl .cabs
  | _, _, .capp functionTyping _ =>
      match progress functionTyping with
      | Or.inr ⟨_, step⟩ => Or.inr ⟨_, .cappFunction step⟩
      | Or.inl functionValue =>
          match canonical functionTyping functionValue with
          | .cabs => Or.inr ⟨_, .coercionBeta⟩
          | .castQual innerValue => Or.inr ⟨_, .castQualCapp innerValue⟩
  | _, _, .cast expressionTyping coercionTyping =>
      match progress expressionTyping with
      | Or.inr ⟨_, step⟩ => Or.inr ⟨_, .castExpression step⟩
      | Or.inl value =>
          match coercionTyping with
          | .cvar lookup => nomatch lookup
          | .refl => Or.inr ⟨_, .castRefl value⟩
          | .trans _ _ => Or.inr ⟨_, .castTrans value⟩
          | .top => Or.inl (.castTop value)
          | .bottom => Or.inr ⟨_, .castBottom value⟩
          | .adapter _ => Or.inr ⟨_, .castAdapter value⟩
          | .arrow _ _ => Or.inl (.castArrow value)
          | .poly _ => Or.inl (.castPoly value)
          | .qual _ _ => Or.inl (.castQual value)

theorem well_typed_not_stuck
    (typing : Ctx.empty |-e expression : ty) : Not (IsStuck expression) := by
  intro stuck
  rcases progress typing with value | ⟨next, step⟩
  · exact stuck.1 value
  · exact stuck.2 ⟨next, step⟩

end SystemFCoExt.Exp
