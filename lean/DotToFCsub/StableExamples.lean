import DotToFCsub.StableFragment
import DotToFCsub.Examples

/-!
# Stable-fragment source regressions

These certificates place the existing Milestone-3 examples inside the
stable-root fragment.  The later totality regressions consume the same values;
none of the certificates below mentions the FCsub checker.
-/

namespace DotToFCsub.StableExamples

open DotFC
open DotFC.Source
open DotToFCsub.StableFragment

def emptyValid : DotFC.Source.Ctx.nil.Valid := .nil

def emptyStable : StableContext emptyValid := .nil

private noncomputable def stableBotOfWf {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (formation : DotFC.Source.Wf context .bot) : StableWf valid formation := by
  cases formation
  exact .bot

private noncomputable def stableTopOfWf {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (formation : DotFC.Source.Wf context .top) : StableWf valid formation := by
  cases formation
  exact .top

private noncomputable def stableMemberBotTopOfWf {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {label : DotFC.Source.Name}
    (formation : DotFC.Source.Wf context (.member label .bot .top)) :
    StableWf valid formation := by
  cases formation with
  | member lower upper =>
      exact .member (stableBotOfWf lower) (stableTopOfWf upper)

private noncomputable def stableMemberBotBotOfWf {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {label : DotFC.Source.Name}
    (formation : DotFC.Source.Wf context (.member label .bot .bot)) :
    StableWf valid formation := by
  cases formation with
  | member lower upper =>
      exact .member (stableBotOfWf lower) (stableBotOfWf upper)

private noncomputable def stableAllMemberTopOfWf {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {label : DotFC.Source.Name}
    (formation : DotFC.Source.Wf context
      (.all (.member label .bot .top) .top)) : StableWf valid formation := by
  cases formation with
  | all domain codomain =>
      exact .all (stableMemberBotTopOfWf domain) (stableTopOfWf codomain)

def dependentDomainStable :
    StableWf emptyValid DotFC.Source.Examples.dependentDomainWf :=
  .member .bot .top

def dependentBodyContext :
    DotFC.Source.Ctx (([] ▹ .term) ▹ .term) :=
  (DotFC.Source.Ctx.nil.snoc
    DotFC.Source.Examples.dependentDomain).snoc
      (.bot : DotFC.Source.Ty ([] ▹ .term))

def dependentMemberLookup :
    DotFC.Source.Lookup dependentBodyContext (.there .here)
      (.member DotFC.Source.Examples.A .bot .top) :=
  .there .here

def dependentMemberHandle :
    DotFC.Source.Handle dependentBodyContext (.there .here)
      DotFC.Source.Examples.A .bot .top :=
  .direct dependentMemberLookup

def dependentBodyTyping :
    DotFC.Source.HasTy dependentBodyContext (.var .here)
      (.sel (.there .here) DotFC.Source.Examples.A) :=
  .sub (.var .here) (.lower dependentMemberHandle)
    (.sel dependentMemberHandle)

def dependentFunctionTyping :
    DotFC.Source.HasTy DotFC.Source.Ctx.nil
      DotFC.Source.Examples.dependentFunction
      DotFC.Source.Examples.dependentFunctionType :=
  .lam DotFC.Source.Examples.dependentDomainWf
    (.lam .bot dependentBodyTyping)

noncomputable def dependentFunctionStable :
    StableHasTy emptyValid
      dependentFunctionTyping := by
  apply StableHasTy.lam dependentDomainStable
  apply StableHasTy.lam (.bot)
  apply StableHasTy.sub
  · apply StableHasTy.var
    exact stableBotOfWf _
  · apply StableSub.lower
    exact .direct dependentMemberLookup
  · apply StableWf.sel
    exact .direct dependentMemberLookup

def exactObjectStable :
    StableHasTy emptyValid DotFC.Source.Examples.exactObjectTyping :=
  .obj .bot

def exactToAbstractStable :
    StableSub emptyValid DotFC.Source.Examples.exactToAbstract :=
  .member (.refl .bot) (.top .bot)

def abstractObjectStable :
    StableHasTy emptyValid DotFC.Source.Examples.abstractObjectTyping :=
  .sub exactObjectStable exactToAbstractStable (.member .bot .top)

def badBoundsValid : DotFC.Source.Examples.badBoundsContext.Valid :=
  .snoc .nil (.member .top .bot)

def badBoundsContextStable : StableContext badBoundsValid :=
  .snoc .nil (.member .top .bot)

def badBoundsHandleStable :
    StableHandle badBoundsValid DotFC.Source.Examples.badBoundsHandle :=
  by
    simpa only [DotFC.Source.Examples.badBoundsHandle] using
      (StableHandle.direct (valid := badBoundsValid)
        (DotFC.Source.Lookup.here : DotFC.Source.Lookup
          DotFC.Source.Examples.badBoundsContext .here
          (.member DotFC.Source.Examples.A .top .bot)))

def badBoundsStable :
    StableSub badBoundsValid DotFC.Source.Examples.badBounds :=
  .trans (.lower badBoundsHandleStable) (.upper badBoundsHandleStable)

/-! Direct, exposed, and adjusted handles all retain the same kind of root.
The latter two change only the visible bounds. -/

def exactMemberContext : DotFC.Source.Ctx ([] ▹ .term) :=
  DotFC.Source.Ctx.nil.snoc
    (.member DotFC.Source.Examples.A .bot .bot)

def exactMemberValid : exactMemberContext.Valid :=
  .snoc .nil (.member .bot .bot)

def exactMemberContextStable : StableContext exactMemberValid :=
  .snoc .nil (.member .bot .bot)

def exactToAbstractInContext :
    DotFC.Source.Sub exactMemberContext
      (.member DotFC.Source.Examples.A .bot .bot)
      (.member DotFC.Source.Examples.A .bot .top) :=
  .member (.refl .bot) (.top .bot)

def exactToAbstractInContextStable :
    StableSub exactMemberValid exactToAbstractInContext :=
  .member (.refl .bot) (.top .bot)

def exactToAbstractInContextPreserving :
    MemberPreserving exactToAbstractInContext :=
  .member _ _

def exposedMemberHandle :
    DotFC.Source.Handle exactMemberContext .here
      DotFC.Source.Examples.A .bot .top :=
  .expose .here exactToAbstractInContext

def exposedMemberHandleStable :
    StableHandle exactMemberValid exposedMemberHandle := by
  simpa only [exposedMemberHandle] using
    (StableHandle.expose (valid := exactMemberValid)
      (DotFC.Source.Lookup.here : DotFC.Source.Lookup exactMemberContext .here
        (.member DotFC.Source.Examples.A .bot .bot))
      exactToAbstractInContextStable exactToAbstractInContextPreserving)

def abstractMemberContext : DotFC.Source.Ctx ([] ▹ .term) :=
  DotFC.Source.Ctx.nil.snoc
    (.member DotFC.Source.Examples.A .bot .top)

def exactToAbstractAdjustment :
    DotFC.Source.CtxMor exactMemberContext abstractMemberContext :=
  .snoc .id DotFC.Source.Examples.exactToAbstract

def exactToAbstractAdjustmentStable :
    StableCtxMor exactMemberValid exactToAbstractAdjustment :=
  .snocMember .id exactToAbstractStable
    (.member _ _) (.member .bot .bot)

def adjustedMemberHandle :
    DotFC.Source.Handle exactMemberContext .here
      DotFC.Source.Examples.A .bot .top :=
  .adjust exactToAbstractAdjustment .here

def adjustedMemberHandleStable :
    StableHandle exactMemberValid adjustedMemberHandle :=
  .adjust exactToAbstractAdjustmentStable .here .here

/-! Bottom may expose a member in unrestricted DOT, but it cannot fabricate
the stable identity required by the Stage-B layout. -/

def bottomContext : DotFC.Source.Ctx ([] ▹ .term) :=
  DotFC.Source.Ctx.nil.snoc .bot

def bottomContextValid : bottomContext.Valid := .snoc .nil .bot

def bottomToMember : DotFC.Source.Sub bottomContext .bot
    (.member DotFC.Source.Examples.A .bot .top) :=
  .bot (.member .bot .top)

def bottomDerivedHandle : DotFC.Source.Handle bottomContext .here
    DotFC.Source.Examples.A .bot .top :=
  .expose .here bottomToMember

theorem bottom_derived_handle_is_rejected :
    ¬ HandleAdmissible bottomContextValid bottomDerivedHandle :=
  bottomDerivedHandle_not_admissible bottomContextValid .here bottomToMember

theorem exposed_handle_compiler_succeeds :
    (Elaboration.handleMemberUse? exposedMemberHandle).isSome = true := by
  native_decide

theorem adjusted_handle_compiler_succeeds :
    (Elaboration.handleMemberUse? adjustedMemberHandle).isSome = true := by
  native_decide

theorem bottom_derived_handle_compiler_rejects :
    Elaboration.handleMemberUse? bottomDerivedHandle = none := by
  native_decide

/-! The member argument below is deliberately reached through subsumption.
Its stable certificate preserves the original slot while adapting only the
two interval witnesses. -/

def noncanonicalContextValid :
    DotToFCsub.Examples.noncanonicalAppContext.Valid :=
  .snoc
    (.snoc .nil DotToFCsub.Examples.memberFunctionSourceWf)
    (.member .bot .bot)

noncomputable def noncanonicalContextStable :
    StableContext noncanonicalContextValid :=
  .snoc
    (.snoc .nil
      (stableAllMemberTopOfWf
        DotToFCsub.Examples.memberFunctionSourceWf))
    (.member .bot .bot)

noncomputable def noncanonicalFunctionStable :
    StableHasTy noncanonicalContextValid
      (.var DotToFCsub.Examples.noncanonicalFunctionLookup) :=
  .var (stableAllMemberTopOfWf
    (DotFC.Source.Lookup.wf noncanonicalContextValid
      DotToFCsub.Examples.noncanonicalFunctionLookup))

def noncanonicalViewStable :
    StableSub noncanonicalContextValid
      DotToFCsub.Examples.noncanonicalArgumentView :=
  .member (.refl .bot) (.top .bot)

def noncanonicalViewPreserving :
    MemberPreserving DotToFCsub.Examples.noncanonicalArgumentView :=
  .member _ _

noncomputable def noncanonicalArgumentRootStable :
    StableMemberArgument noncanonicalContextValid
      (.var DotToFCsub.Examples.noncanonicalArgumentLookup) :=
  .var DotToFCsub.Examples.noncanonicalArgumentLookup

noncomputable def noncanonicalArgumentStable :
    StableHasTy noncanonicalContextValid
      DotToFCsub.Examples.noncanonicalArgumentTyping :=
  .sub
    (.var (stableMemberBotBotOfWf
      (DotFC.Source.Lookup.wf noncanonicalContextValid
        DotToFCsub.Examples.noncanonicalArgumentLookup)))
    noncanonicalViewStable (.member .bot .top)

noncomputable def noncanonicalMemberArgumentStable :
    StableMemberArgument noncanonicalContextValid
      DotToFCsub.Examples.noncanonicalArgumentTyping :=
  .sub noncanonicalArgumentRootStable noncanonicalViewStable
    noncanonicalViewPreserving (.member .bot .top)

noncomputable def noncanonicalMemberAppStable :
    StableHasTy noncanonicalContextValid
      DotToFCsub.Examples.noncanonicalMemberApp :=
  .appMember noncanonicalFunctionStable noncanonicalArgumentStable
    noncanonicalMemberArgumentStable .top

end DotToFCsub.StableExamples
