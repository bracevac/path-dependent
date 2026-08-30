import Coercions.Translation.ManySorted.BinderOnly.EvidenceElaboration

/-!
# Canonical evidence lookup for translated source contexts

Every source static binder expands to one target name and exactly the
evidence coordinates selected by its interval shape.  This module proves that
`staticSlot` finds those coordinates in `translateContext`, then packages the
result as the canonical `BoundCompiler` used by all later elaboration.
-/

namespace DOTCaptureToManySortedFC.BinderOnly

/-- Exact target lookup data for one present source lower endpoint. -/
structure LowerSlotLookup {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (index : DOTCapture.BinderOnly.BVar scope (.static sort))
    (endpoint : DOTCapture.BinderOnly.StaticExpr sort scope) where
  evidence : ManySortedFC.BVar (sig context)
    (.evidence (.inclusion (translateSort sort)))
  coordinate : (staticSlot context index).lower = some evidence
  binding : (translateContext context).lookup evidence =
    .evidence (.inclusion (translateExpr context endpoint)
      (translateRef context (.bound index)))

/-- Exact target lookup data for one present source upper endpoint. -/
structure UpperSlotLookup {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (index : DOTCapture.BinderOnly.BVar scope (.static sort))
    (endpoint : DOTCapture.BinderOnly.StaticExpr sort scope) where
  evidence : ManySortedFC.BVar (sig context)
    (.evidence (.inclusion (translateSort sort)))
  coordinate : (staticSlot context index).upper = some evidence
  binding : (translateContext context).lookup evidence =
    .evidence (.inclusion (translateRef context (.bound index))
      (translateExpr context endpoint))

@[simp]
theorem source_lookupStatic_extend_there
    {scope : DOTCapture.BinderOnly.Sig}
    {kind : DOTCapture.BinderOnly.BinderKind}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (binding : DOTCapture.BinderOnly.Binding scope kind)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (index : DOTCapture.BinderOnly.BVar scope (.static sort)) :
    (DOTCapture.BinderOnly.Ctx.extend context binding).lookupStatic
        (.there index) =
      (context.lookupStatic index).weaken := by
  unfold DOTCapture.BinderOnly.Ctx.lookupStatic
  rw [DOTCapture.BinderOnly.Ctx.lookup_there]
  generalize found : context.lookup index = result
  cases result with
  | static interval => rfl

namespace TargetSlot

theorem lowerBoundedProposition_shape {scope : ManySortedFC.Sig}
    {sort : ManySortedFC.StaticSort}
    (lower : ManySortedFC.StaticExpr sort scope) :
    ManySortedTranslation.StaticSlot.lowerBoundedProposition lower =
      .inclusion
        (lower.rename (ManySortedFC.Rename.weakenStatic [sort]
          [.inclusion sort]))
        (ManySortedFC.StaticExpr.symbol (.there .here)) := by
  cases sort <;>
    simp [ManySortedTranslation.StaticSlot.lowerBoundedProposition,
      ManySortedTranslation.StaticSlot.exportHead,
      ManySortedFC.StaticExpr.weaken, ManySortedFC.Interval.name,
      ManySortedFC.Proposition.rename, ManySortedFC.evidenceKinds,
      ManySortedFC.symbolKinds, ManySortedFC.Rename.weakenStatic,
      ManySortedFC.Rename.weakenSymbols, ManySortedFC.Rename.weakenMany]
  all_goals
    constructor
    · exact ManySortedFC.StaticExpr.rename_comp lower _ _
    · rfl

theorem betweenLowerProposition_shape {scope : ManySortedFC.Sig}
    {sort : ManySortedFC.StaticSort}
    (lower upper : ManySortedFC.StaticExpr sort scope) :
    ManySortedTranslation.StaticSlot.betweenLowerProposition lower upper =
      .inclusion
        (lower.rename (ManySortedFC.Rename.weakenStatic [sort]
          [.inclusion sort, .inclusion sort]))
        (ManySortedFC.StaticExpr.symbol (.there (.there .here))) := by
  cases sort <;>
    simp [ManySortedTranslation.StaticSlot.betweenLowerProposition,
      ManySortedTranslation.StaticSlot.exportHead,
      ManySortedFC.StaticExpr.weaken, ManySortedFC.Interval.name,
      ManySortedFC.Proposition.rename, ManySortedFC.evidenceKinds,
      ManySortedFC.symbolKinds, ManySortedFC.Rename.weakenStatic,
      ManySortedFC.Rename.weakenSymbols, ManySortedFC.Rename.weakenMany]
  all_goals
    constructor
    · exact ManySortedFC.StaticExpr.rename_comp lower _ _
    · rfl

theorem upperBoundedProposition_shape {scope : ManySortedFC.Sig}
    {sort : ManySortedFC.StaticSort}
    (upper : ManySortedFC.StaticExpr sort scope) :
    ManySortedTranslation.StaticSlot.upperBoundedProposition upper =
      .inclusion
        (ManySortedFC.StaticExpr.symbol (.there .here))
        (upper.rename (ManySortedFC.Rename.weakenStatic [sort]
          [.inclusion sort])) := by
  cases sort <;>
    simp [ManySortedTranslation.StaticSlot.upperBoundedProposition,
      ManySortedTranslation.StaticSlot.exportHead,
      ManySortedFC.StaticExpr.weaken, ManySortedFC.Interval.name,
      ManySortedFC.Proposition.rename, ManySortedFC.evidenceKinds,
      ManySortedFC.symbolKinds, ManySortedFC.Rename.weakenStatic,
      ManySortedFC.Rename.weakenSymbols, ManySortedFC.Rename.weakenMany]
  all_goals
    constructor
    · rfl
    · exact ManySortedFC.StaticExpr.rename_comp upper _ _

theorem betweenUpperProposition_shape {scope : ManySortedFC.Sig}
    {sort : ManySortedFC.StaticSort}
    (lower upper : ManySortedFC.StaticExpr sort scope) :
    ManySortedTranslation.StaticSlot.betweenUpperProposition lower upper =
      .inclusion
        (ManySortedFC.StaticExpr.symbol (.there (.there .here)))
        (upper.rename (ManySortedFC.Rename.weakenStatic [sort]
          [.inclusion sort, .inclusion sort])) := by
  cases sort <;>
    simp [ManySortedTranslation.StaticSlot.betweenUpperProposition,
      ManySortedTranslation.StaticSlot.exportHead,
      ManySortedFC.StaticExpr.weaken, ManySortedFC.Interval.name,
      ManySortedFC.Proposition.rename, ManySortedFC.evidenceKinds,
      ManySortedFC.symbolKinds, ManySortedFC.Rename.weakenStatic,
      ManySortedFC.Rename.weakenSymbols, ManySortedFC.Rename.weakenMany]
  all_goals
    constructor
    · rfl
    · exact ManySortedFC.StaticExpr.rename_comp upper _ _

end TargetSlot

/-- Follow a source lower-bound lookup to the exact target evidence slot. -/
def lowerSlotLookup :
    {scope : DOTCapture.BinderOnly.Sig} →
    (context : DOTCapture.BinderOnly.Ctx scope) →
    {sort : DOTCapture.BinderOnly.StaticSort} →
    (index : DOTCapture.BinderOnly.BVar scope (.static sort)) →
    {endpoint : DOTCapture.BinderOnly.StaticExpr sort scope} →
    {upper : DOTCapture.BinderOnly.Endpoint sort scope} →
    context.lookupStatic index = .bounds (.some endpoint) upper →
      LowerSlotLookup context index endpoint
  | _, .extend outer
      (@DOTCapture.BinderOnly.Binding.static _ sort interval), _, .here,
      endpoint, upper, found => by
      cases interval with
      | bounds lower storedUpper =>
          cases lower with
          | none => cases found
          | some storedLower =>
              have pieces := Eq.mp
                (DOTCapture.BinderOnly.Interval.bounds.injEq _ _ _ _)
                found
              have endpointEquality := Eq.mp
                (DOTCapture.BinderOnly.Endpoint.some.injEq _ _) pieces.1
              cases endpointEquality
              cases storedUpper with
              | none =>
                  exact
                    { evidence := .here
                      coordinate := rfl
                      binding := by
                        have translatedLower :=
                          translateExpr_weaken outer
                            (DOTCapture.BinderOnly.Binding.static
                              (.bounds (.some storedLower) .none))
                            storedLower
                        simp only
                          [DOTCapture.BinderOnly.StaticExpr.weaken] at translatedLower
                        rw [translatedLower]
                        change
                          ((translateContext outer).extendTheory
                            (ManySortedFC.Interval.lowerBounded
                              (translateExpr outer storedLower))).lookup
                              (.here) =
                            ManySortedFC.Binding.evidence
                              (.inclusion
                                ((translateExpr outer storedLower).rename
                                  (ManySortedFC.Rename.weakenStatic
                                    [translateSort sort]
                                    [.inclusion (translateSort sort)]))
                                (ManySortedFC.StaticExpr.symbol
                                  (.there .here)))
                        have lookup :=
                          ManySortedTranslation.StaticSlot.lookup_lowerBounded_lower
                            (translateContext outer)
                            (translateExpr outer storedLower)
                        rw [TargetSlot.lowerBoundedProposition_shape] at lookup
                        exact lookup }
              | some storedUpper =>
                  exact
                    { evidence := .here
                      coordinate := rfl
                      binding := by
                        have translatedLower :=
                          translateExpr_weaken outer
                            (DOTCapture.BinderOnly.Binding.static
                              (.bounds (.some storedLower)
                                (.some storedUpper))) storedLower
                        simp only
                          [DOTCapture.BinderOnly.StaticExpr.weaken] at translatedLower
                        rw [translatedLower]
                        change
                          ((translateContext outer).extendTheory
                            (ManySortedFC.Interval.between
                              (translateExpr outer storedLower)
                              (translateExpr outer storedUpper))).lookup
                              (.here) =
                            ManySortedFC.Binding.evidence
                              (.inclusion
                                ((translateExpr outer storedLower).rename
                                  (ManySortedFC.Rename.weakenStatic
                                    [translateSort sort]
                                    [.inclusion (translateSort sort),
                                      .inclusion (translateSort sort)]))
                                (ManySortedFC.StaticExpr.symbol
                                  (.there (.there .here))))
                        have lookup :=
                          ManySortedTranslation.StaticSlot.lookup_between_lower
                            (translateContext outer)
                            (translateExpr outer storedLower)
                            (translateExpr outer storedUpper)
                        rw [TargetSlot.betweenLowerProposition_shape] at lookup
                        exact lookup }
  | _, .extend outer binding, sort, .there older, endpoint, upper, found => by
      rw [source_lookupStatic_extend_there] at found
      generalize intervalEquation : outer.lookupStatic older = interval
      at found
      cases interval with
      | bounds lower storedUpper =>
          cases lower with
          | none => cases found
          | some storedLower =>
              have pieces := Eq.mp
                (DOTCapture.BinderOnly.Interval.bounds.injEq _ _ _ _)
                found
              have endpointEquality := Eq.mp
                (DOTCapture.BinderOnly.Endpoint.some.injEq _ _) pieces.1
              cases endpointEquality
              let previous := lowerSlotLookup outer older intervalEquation
              exact
                { evidence := (extendRename outer binding).var previous.evidence
                  coordinate := by
                    rw [staticSlot_extend_there]
                    change Option.map (extendRename outer binding).var
                      (staticSlot outer older).lower = _
                    rw [previous.coordinate]
                    rfl
                  binding := by
                    rw [translateContext_lookup_extend, previous.binding]
                    simp only [ManySortedFC.Binding.rename,
                      ManySortedFC.Proposition.rename,
                      translateRef, staticSlot_extend_there,
                      ManySortedTranslation.StaticSlot.expression,
                      ManySortedTranslation.StaticSlot.rename]
                    have lowerEquality :=
                      (translateExpr_weaken outer binding storedLower).symm
                    simp only
                      [DOTCapture.BinderOnly.StaticExpr.weaken] at lowerEquality
                    have referenceEquality :
                        (ManySortedFC.StaticExpr.symbol
                          (staticSlot outer older).name).rename
                            (extendRename outer binding) =
                          ManySortedFC.StaticExpr.symbol
                            ((extendRename outer binding).var
                              (staticSlot outer older).name) := by
                      cases sort <;> rfl
                    rw [lowerEquality, referenceEquality] }

/-- Follow a source upper-bound lookup to the exact target evidence slot. -/
def upperSlotLookup :
    {scope : DOTCapture.BinderOnly.Sig} →
    (context : DOTCapture.BinderOnly.Ctx scope) →
    {sort : DOTCapture.BinderOnly.StaticSort} →
    (index : DOTCapture.BinderOnly.BVar scope (.static sort)) →
    {lower : DOTCapture.BinderOnly.Endpoint sort scope} →
    {endpoint : DOTCapture.BinderOnly.StaticExpr sort scope} →
    context.lookupStatic index = .bounds lower (.some endpoint) →
      UpperSlotLookup context index endpoint
  | _, .extend outer
      (@DOTCapture.BinderOnly.Binding.static _ sort interval), _, .here,
      lower, endpoint, found => by
      cases interval with
      | bounds storedLower upper =>
          cases upper with
          | none => cases found
          | some storedUpper =>
              have pieces := Eq.mp
                (DOTCapture.BinderOnly.Interval.bounds.injEq _ _ _ _)
                found
              have endpointEquality := Eq.mp
                (DOTCapture.BinderOnly.Endpoint.some.injEq _ _) pieces.2
              cases endpointEquality
              cases storedLower with
              | none =>
                  exact
                    { evidence := .here
                      coordinate := rfl
                      binding := by
                        have translatedUpper :=
                          translateExpr_weaken outer
                            (DOTCapture.BinderOnly.Binding.static
                              (.bounds .none (.some storedUpper))) storedUpper
                        simp only
                          [DOTCapture.BinderOnly.StaticExpr.weaken] at translatedUpper
                        rw [translatedUpper]
                        change
                          ((translateContext outer).extendTheory
                            (ManySortedFC.Interval.upperBounded
                              (translateExpr outer storedUpper))).lookup
                              (.here) =
                            ManySortedFC.Binding.evidence
                              (.inclusion
                                (ManySortedFC.StaticExpr.symbol
                                  (.there .here))
                                ((translateExpr outer storedUpper).rename
                                  (ManySortedFC.Rename.weakenStatic
                                    [translateSort sort]
                                    [.inclusion (translateSort sort)])))
                        have lookup :=
                          ManySortedTranslation.StaticSlot.lookup_upperBounded_upper
                            (translateContext outer)
                            (translateExpr outer storedUpper)
                        rw [TargetSlot.upperBoundedProposition_shape] at lookup
                        exact lookup }
              | some storedLower =>
                  exact
                    { evidence := .there .here
                      coordinate := rfl
                      binding := by
                        have translatedUpper :=
                          translateExpr_weaken outer
                            (DOTCapture.BinderOnly.Binding.static
                              (.bounds (.some storedLower)
                                (.some storedUpper))) storedUpper
                        simp only
                          [DOTCapture.BinderOnly.StaticExpr.weaken] at translatedUpper
                        rw [translatedUpper]
                        change
                          ((translateContext outer).extendTheory
                            (ManySortedFC.Interval.between
                              (translateExpr outer storedLower)
                              (translateExpr outer storedUpper))).lookup
                              (.there .here) =
                            ManySortedFC.Binding.evidence
                              (.inclusion
                                (ManySortedFC.StaticExpr.symbol
                                  (.there (.there .here)))
                                ((translateExpr outer storedUpper).rename
                                  (ManySortedFC.Rename.weakenStatic
                                    [translateSort sort]
                                    [.inclusion (translateSort sort),
                                      .inclusion (translateSort sort)])))
                        have lookup :=
                          ManySortedTranslation.StaticSlot.lookup_between_upper
                            (translateContext outer)
                            (translateExpr outer storedLower)
                            (translateExpr outer storedUpper)
                        rw [TargetSlot.betweenUpperProposition_shape] at lookup
                        exact lookup }
  | _, .extend outer binding, sort, .there older, lower, endpoint, found => by
      rw [source_lookupStatic_extend_there] at found
      generalize intervalEquation : outer.lookupStatic older = interval
      at found
      cases interval with
      | bounds storedLower upper =>
          cases upper with
          | none => cases found
          | some storedUpper =>
              have pieces := Eq.mp
                (DOTCapture.BinderOnly.Interval.bounds.injEq _ _ _ _)
                found
              have endpointEquality := Eq.mp
                (DOTCapture.BinderOnly.Endpoint.some.injEq _ _) pieces.2
              cases endpointEquality
              let previous := upperSlotLookup outer older intervalEquation
              exact
                { evidence := (extendRename outer binding).var previous.evidence
                  coordinate := by
                    rw [staticSlot_extend_there]
                    change Option.map (extendRename outer binding).var
                      (staticSlot outer older).upper = _
                    rw [previous.coordinate]
                    rfl
                  binding := by
                    rw [translateContext_lookup_extend, previous.binding]
                    simp only [ManySortedFC.Binding.rename,
                      ManySortedFC.Proposition.rename,
                      translateRef, staticSlot_extend_there,
                      ManySortedTranslation.StaticSlot.expression,
                      ManySortedTranslation.StaticSlot.rename]
                    have upperEquality :=
                      (translateExpr_weaken outer binding storedUpper).symm
                    simp only
                      [DOTCapture.BinderOnly.StaticExpr.weaken] at upperEquality
                    have referenceEquality :
                        (ManySortedFC.StaticExpr.symbol
                          (staticSlot outer older).name).rename
                            (extendRename outer binding) =
                          ManySortedFC.StaticExpr.symbol
                            ((extendRename outer binding).var
                              (staticSlot outer older).name) := by
                      cases sort <;> rfl
                    rw [upperEquality, referenceEquality] }

/-- The translated layout itself supplies every bound-lookup leaf required by
the structural inclusion compiler. -/
def contextBoundCompiler {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope) : BoundCompiler context where
  lower := by
    intro sort reference endpoint bound
    cases reference with
    | bound index =>
        cases bound with
        | bound found =>
            let lookup := lowerSlotLookup context index found
            cases sort <;>
              exact ⟨.var lookup.evidence, .var lookup.binding⟩
  upper := by
    intro sort reference endpoint bound
    cases reference with
    | bound index =>
        cases bound with
        | bound found =>
            let lookup := upperSlotLookup context index found
            cases sort <;>
              exact ⟨.var lookup.evidence, .var lookup.binding⟩

/-- Compile any source inclusion using the evidence coordinates determined by
its translated context. Clients no longer need to construct or pass a layout
dictionary. -/
def compileIncludesTotal {scope : DOTCapture.BinderOnly.Sig}
    {context : DOTCapture.BinderOnly.Ctx scope}
    {sort : DOTCapture.BinderOnly.StaticSort}
    {source target : DOTCapture.BinderOnly.StaticExpr sort scope}
    (inclusion : DOTCapture.BinderOnly.Includes context source target) :
    CompiledInclusion context source target :=
  compileIncludes (contextBoundCompiler context) inclusion

end DOTCaptureToManySortedFC.BinderOnly
