import Coercions.DOT.Captures.BinderOnly.IntervalModel

/-!
# Source interval entailment

`Entails context available required` says that the assumptions supplied by
`available` are sufficient to meet the obligations of `required`.  Both
intervals have the same endpoint-presence shape.  The obligations are checked
after introducing the static name governed by `available`.
-/

namespace DOTCapture.BinderOnly.Interval

/-- Shape-preserving entailment between source intervals.

For every required lower endpoint, the endpoint must include into the newly
bound static name.  For every required upper endpoint, the new name must
include into the endpoint.  Both proofs live under the available interval. -/
inductive Entails {scope : Sig} (context : Ctx scope) {sort : StaticSort} :
    Interval sort scope -> Interval sort scope -> Type where
  | unbounded :
      Entails context (.bounds .none .none) (.bounds .none .none)
  | lower {availableLower requiredLower : StaticExpr sort scope}
      (lowerEvidence :
        Includes
          (context.extendStatic
            (.bounds (.some availableLower) .none))
          requiredLower.weaken
          (StaticExpr.bound
            (.here : BVar (scope ▹ .static sort) (.static sort)))) :
      Entails context
        (.bounds (.some availableLower) .none)
        (.bounds (.some requiredLower) .none)
  | upper {availableUpper requiredUpper : StaticExpr sort scope}
      (upperEvidence :
        Includes
          (context.extendStatic
            (.bounds .none (.some availableUpper)))
          (StaticExpr.bound
            (.here : BVar (scope ▹ .static sort) (.static sort)))
          requiredUpper.weaken) :
      Entails context
        (.bounds .none (.some availableUpper))
        (.bounds .none (.some requiredUpper))
  | between
      {availableLower availableUpper requiredLower requiredUpper :
        StaticExpr sort scope}
      (lowerEvidence :
        Includes
          (context.extendStatic
            (.bounds (.some availableLower) (.some availableUpper)))
          requiredLower.weaken
          (StaticExpr.bound
            (.here : BVar (scope ▹ .static sort) (.static sort))))
      (upperEvidence :
        Includes
          (context.extendStatic
            (.bounds (.some availableLower) (.some availableUpper)))
          (StaticExpr.bound
            (.here : BVar (scope ▹ .static sort) (.static sort)))
          requiredUpper.weaken) :
      Entails context
        (.bounds (.some availableLower) (.some availableUpper))
        (.bounds (.some requiredLower) (.some requiredUpper))

end DOTCapture.BinderOnly.Interval
