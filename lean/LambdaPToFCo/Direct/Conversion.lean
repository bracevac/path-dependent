import LambdaPToFCo.Direct.Atomic
import LambdaPToFCo.Direct.Structural

/-!
# Sealed ordinary conversions for the direct compiler

This target-only leaf packages ordinary `SystemFCo.Exp` functions with their
extrinsic typing derivations.  The constructors below retain actual hidden
package identities and interval witnesses.  In particular, singleton
retargeting composes the two opened singleton fields instead of inventing an
identity, and interval-bound mapping preserves the selected shape opened from
the source member.

There is no source-language certificate, callback capability, qualified type,
or extension-target syntax in this file.
-/

namespace LambdaPToFCo.Direct.Internal

open SystemFCo

/-- An ordinary target function together with its separate typing theorem.
The constructor is sealed so compiler clients obtain conversions only from
the target constructions in this namespace. -/
structure Conversion (base : Ctx sig) (source target : Ty sig) : Type where
  private mk ::
  function : Exp sig
  functionTyping : Exp.HasType base function (.arrow source target)

namespace Conversion

/-- Ordinary identity implements reflexive source subtyping. -/
noncomputable def refl (base : Ctx sig) (type : Ty sig) :
    Conversion base type type :=
  .mk (Direct.Adapter.identity type)
    (Direct.Adapter.identity_hasType base type)

/-- Ordinary left-to-right function composition. -/
noncomputable def compose {base : Ctx sig} {source middle target : Ty sig}
    (first : Conversion base source middle)
    (second : Conversion base middle target) :
    Conversion base source target :=
  .mk (Direct.Adapter.compose source first.function second.function)
    (Direct.Adapter.compose_hasType first.functionTyping
      second.functionTyping)

/-- Reindex a conversion through a typed target renaming. -/
noncomputable def rename
    {sourceSig targetSig : Sig}
    {sourceContext : Ctx sourceSig} {targetContext : Ctx targetSig}
    {source target : Ty sourceSig}
    (conversion : Conversion sourceContext source target)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Conversion targetContext (source.rename mapping) (target.rename mapping) :=
  .mk (conversion.function.rename mapping)
    (by
      simpa only [Ty.rename] using conversion.functionTyping.rename typed)

/-- Forget all stable observations while retaining the exact hidden identity
and payload opened from the source package. -/
noncomputable def stableTop (base : Ctx sig) (source : Package.Plan sig) :
    Conversion base source.inputTy (Top.plan sig).inputTy :=
  let adapter := Stable.Adapter.toTop base source
  .mk adapter.function adapter.functionTyping

/-- Synthesize a term-only stable interface from the Bottom eliminator while
retaining Bottom's exact hidden identity and payload. -/
noncomputable def stableBottom (base : Ctx sig)
    (target : Package.Plan sig) (ordinary : target.TermOnly) :
    Conversion base (Bot.plan sig).inputTy target.inputTy :=
  let adapter := Stable.Adapter.fromBottom base target ordinary
  .mk adapter.function adapter.functionTyping

/-! ## Bidirectional identity bridges -/

/-- Two sealed ordinary conversions in one common target context. -/
structure Bridge (base : Ctx sig) (left right : Ty sig) : Type where
  leftToRight : Conversion base left right
  rightToLeft : Conversion base right left

namespace Bridge

def symm {base : Ctx sig} {left right : Ty sig}
    (bridge : Bridge base left right) : Bridge base right left where
  leftToRight := bridge.rightToLeft
  rightToLeft := bridge.leftToRight

noncomputable def rename
    {sourceSig targetSig : Sig}
    {sourceContext : Ctx sourceSig} {targetContext : Ctx targetSig}
    {left right : Ty sourceSig}
    (bridge : Bridge sourceContext left right)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Bridge targetContext (left.rename mapping) (right.rename mapping) where
  leftToRight := bridge.leftToRight.rename mapping typed
  rightToLeft := bridge.rightToLeft.rename mapping typed

end Bridge

/-! ## Singleton referent retargeting -/

namespace Singleton

/-! A source singleton refers to the complete package type of its path.
`wrap` and `unwrap` are therefore the exact ordinary-function dictionary
between a represented value and the singleton package that names it.  This
keeps widening honest: it opens the package carried by the singleton instead
of reconstructing or guessing the path's hidden identity. -/

private noncomputable def wrapBody (base : Ctx sig)
    (referent : Ty sig) : Exp (sig ,, .var) :=
  let mapping : Rename sig (sig ,, .var) := Rename.weaken .var
  Direct.Single.exactPackage (referent.rename mapping) (.var .here)
    (by
      have raw : Exp.HasType (base.bindVar referent) (.var .here)
          (referent.weaken .var) := .var Ctx.Lookup.here
      simpa only [Ty.weaken] using raw)

private noncomputable def wrapBody_hasType (base : Ctx sig)
    (referent : Ty sig) :
    Exp.HasType (base.bindVar referent) (wrapBody base referent)
      ((Direct.Single.plan referent).inputTy.rename
        (Rename.weaken .var)) := by
  let mapping : Rename sig (sig ,, .var) := Rename.weaken .var
  rw [Direct.Single.inputTy_rename]
  simpa only [wrapBody] using Direct.Single.exactPackage_hasType
    (referent.rename mapping) (.var .here)
    (by
      have raw : Exp.HasType (base.bindVar referent) (.var .here)
          (referent.weaken .var) := .var Ctx.Lookup.here
      simpa only [Ty.weaken] using raw)

/-- Package one represented value as its exact self-singleton. -/
noncomputable def wrap (base : Ctx sig) (referent : Ty sig) :
    Conversion base referent (Direct.Single.plan referent).inputTy :=
  .mk (Direct.Adapter.ofBody referent (wrapBody base referent))
    (Direct.Adapter.ofBody_hasType (wrapBody_hasType base referent))

private noncomputable def unwrapBody (referent : Ty sig) : Exp (sig ,, .var) :=
  let sourceAt := Direct.Single.plan
    (referent.rename (Rename.weaken .var))
  sourceAt.unpack (.var .here) (referent.rename (Rename.weaken .var))
    (Direct.Single.payloadAsReferent
      (referent.rename (Rename.weaken .var)))

private noncomputable def unwrapBody_hasType (base : Ctx sig)
    (referent : Ty sig) :
    Exp.HasType
      (base.bindVar (Direct.Single.plan referent).inputTy)
      (unwrapBody referent) (referent.rename (Rename.weaken .var)) := by
  let mapping : Rename sig (sig ,, .var) := Rename.weaken .var
  let sourceAt := Direct.Single.plan (referent.rename mapping)
  have variableTyping : Exp.HasType
      (base.bindVar (Direct.Single.plan referent).inputTy) (.var .here)
      sourceAt.inputTy := by
    have raw : Exp.HasType
        (base.bindVar (Direct.Single.plan referent).inputTy) (.var .here)
        ((Direct.Single.plan referent).inputTy.rename mapping) :=
      .var Ctx.Lookup.here
    rwa [Direct.Single.inputTy_rename] at raw
  exact sourceAt.unpack_hasType variableTyping
    (Direct.Single.payloadAsReferent_hasType
      (base.bindVar (Direct.Single.plan referent).inputTy)
      (referent.rename mapping))

/-- Open a singleton and recover the complete package of its referent. -/
noncomputable def unwrap (base : Ctx sig) (referent : Ty sig) :
    Conversion base (Direct.Single.plan referent).inputTy referent :=
  .mk (Direct.Adapter.ofBody (Direct.Single.plan referent).inputTy
      (unwrapBody referent))
    (Direct.Adapter.ofBody_hasType (unwrapBody_hasType base referent))

/-- The package type of a value and its exact self-singleton package are
connected by ordinary target functions in both directions. -/
noncomputable def selfBridge (base : Ctx sig) (referent : Ty sig) :
    Bridge base referent (Direct.Single.plan referent).inputTy where
  leftToRight := wrap base referent
  rightToLeft := unwrap base referent

/-- Retarget one singleton package in place.  The input package is opened,
its actual hidden identity and payload are retained, and its referent fields
are pre/postcomposed with the supplied bridge. -/
private noncomputable def apply (base : Ctx sig) (left right : Ty sig)
    (bridge : Bridge base left right) (package : Exp sig) : Exp sig :=
  let source := Direct.Single.plan left
  let mapping := source.telescope.weaken
  let openedRight := right.rename mapping
  let leftToRight := bridge.leftToRight.function.rename mapping
  let rightToLeft := bridge.rightToLeft.function.rename mapping
  let lowerFunction := Direct.Adapter.compose openedRight rightToLeft
    (Direct.Single.fromReferent left)
  let upperFunction := Direct.Adapter.compose source.identityTy
    (Direct.Single.toReferent left) leftToRight
  let result := Direct.Single.package openedRight source.identityTy
    source.payload (source.payload_hasType base) upperFunction
    (Direct.Adapter.compose_hasType
      (Direct.Single.toReferent_hasType base left)
      (bridge.leftToRight.functionTyping.rename
        (source.telescope.weaken_typed base)))
    lowerFunction
    (Direct.Adapter.compose_hasType
      (bridge.rightToLeft.functionTyping.rename
        (source.telescope.weaken_typed base))
      (Direct.Single.fromReferent_hasType base left))
  source.unpack package (Direct.Single.plan right).inputTy result

private noncomputable def apply_hasType
    (base : Ctx sig) (left right : Ty sig)
    (bridge : Bridge base left right) {package : Exp sig}
    (packageTyping : Exp.HasType base package
      (Direct.Single.plan left).inputTy) :
    Exp.HasType base (apply base left right bridge package)
      (Direct.Single.plan right).inputTy := by
  let source := Direct.Single.plan left
  let mapping := source.telescope.weaken
  let openedRight := right.rename mapping
  let leftToRight := bridge.leftToRight.function.rename mapping
  let rightToLeft := bridge.rightToLeft.function.rename mapping
  let leftToRightTyping := bridge.leftToRight.functionTyping.rename
    (source.telescope.weaken_typed base)
  let rightToLeftTyping := bridge.rightToLeft.functionTyping.rename
    (source.telescope.weaken_typed base)
  let lowerFunction := Direct.Adapter.compose openedRight rightToLeft
    (Direct.Single.fromReferent left)
  let lowerTyping := Direct.Adapter.compose_hasType rightToLeftTyping
    (Direct.Single.fromReferent_hasType base left)
  let upperFunction := Direct.Adapter.compose source.identityTy
    (Direct.Single.toReferent left) leftToRight
  let upperTyping := Direct.Adapter.compose_hasType
    (Direct.Single.toReferent_hasType base left) leftToRightTyping
  let result := Direct.Single.package openedRight source.identityTy
    source.payload (source.payload_hasType base) upperFunction upperTyping
    lowerFunction lowerTyping
  have resultTyping : Exp.HasType (source.context base) result
      ((Direct.Single.plan right).inputTy.rename mapping) := by
    rw [Direct.Single.inputTy_rename]
    exact Direct.Single.package_hasType openedRight source.identityTy
      source.payload (source.payload_hasType base) upperFunction upperTyping
      lowerFunction lowerTyping
  exact source.unpack_hasType packageTyping resultTyping

private noncomputable def function
    (base : Ctx sig) (left right : Ty sig)
    (bridge : Bridge base left right) : Exp sig :=
  let sourceInput := (Direct.Single.plan left).inputTy
  let underInput := base.bindVar sourceInput
  let mapping : Rename sig (sig ,, .var) := Rename.weaken .var
  let bridgeUnderInput := bridge.rename mapping
    (Rename.Typed.weaken base (.var sourceInput))
  Direct.Adapter.ofBody sourceInput
    (apply underInput (left.rename mapping) (right.rename mapping)
      bridgeUnderInput (.var .here))

private noncomputable def function_hasType
    (base : Ctx sig) (left right : Ty sig)
    (bridge : Bridge base left right) :
    Exp.HasType base (function base left right bridge)
      (.arrow (Direct.Single.plan left).inputTy
        (Direct.Single.plan right).inputTy) := by
  apply Direct.Adapter.ofBody_hasType
  let sourceInput := (Direct.Single.plan left).inputTy
  let underInput := base.bindVar sourceInput
  let mapping : Rename sig (sig ,, .var) := Rename.weaken .var
  let bridgeUnderInput := bridge.rename mapping
    (Rename.Typed.weaken base (.var sourceInput))
  have variableTyping : Exp.HasType underInput (.var .here)
      (Direct.Single.plan (left.rename mapping)).inputTy := by
    have raw : Exp.HasType underInput (.var .here)
        ((Direct.Single.plan left).inputTy.rename mapping) :=
      .var Ctx.Lookup.here
    rwa [Direct.Single.inputTy_rename] at raw
  have bodyTyping := apply_hasType underInput (left.rename mapping)
    (right.rename mapping) bridgeUnderInput variableTyping
  rw [← Direct.Single.inputTy_rename] at bodyTyping
  exact bodyTyping

/-- Sealed singleton retargeting.  Reversing the bridge implements the
opposite singleton direction used by source symmetry. -/
noncomputable def retarget (base : Ctx sig) (left right : Ty sig)
    (bridge : Bridge base left right) :
    Conversion base (Direct.Single.plan left).inputTy
      (Direct.Single.plan right).inputTy :=
  .mk (function base left right bridge)
    (function_hasType base left right bridge)

end Singleton

/-! ## Interval-bound mapping -/

namespace Interval

/-- Runtime interval evidence in one target context.  `selected` is the
actual hidden witness opened from the source package. -/
structure Witness (base : Ctx sig) (lower upper : Shape sig) : Type where
  selected : Shape sig
  lowerFunction : Exp sig
  lowerTyping : Exp.HasType base lowerFunction
    (.arrow lower.inputTy selected.inputTy)
  upperFunction : Exp sig
  upperTyping : Exp.HasType base upperFunction
    (.arrow selected.inputTy upper.inputTy)

/-- The stored lower-bound function as a sealed ordinary conversion. -/
noncomputable def lower {base : Ctx sig} {lower upper : Shape sig}
    (witness : Witness base lower upper) :
    Conversion base lower.inputTy witness.selected.inputTy :=
  .mk witness.lowerFunction witness.lowerTyping

/-- The stored upper-bound function as a sealed ordinary conversion. -/
noncomputable def upper {base : Ctx sig} {lower upper : Shape sig}
    (witness : Witness base lower upper) :
    Conversion base witness.selected.inputTy upper.inputTy :=
  .mk witness.upperFunction witness.upperTyping

/-- Contravariantly precompose the lower field and covariantly postcompose
the upper field.  The selected witness is preserved exactly. -/
noncomputable def map {base : Ctx sig}
    {sourceLower sourceUpper targetLower targetUpper : Shape sig}
    (source : Witness base sourceLower sourceUpper)
    (lower : Conversion base targetLower.inputTy sourceLower.inputTy)
    (upper : Conversion base sourceUpper.inputTy targetUpper.inputTy) :
    Witness base targetLower targetUpper where
  selected := source.selected
  lowerFunction := Direct.Adapter.compose targetLower.inputTy
    lower.function source.lowerFunction
  lowerTyping := Direct.Adapter.compose_hasType lower.functionTyping
    source.lowerTyping
  upperFunction := Direct.Adapter.compose source.selected.inputTy
    source.upperFunction upper.function
  upperTyping := Direct.Adapter.compose_hasType source.upperTyping
    upper.functionTyping

/-- Reclose mapped interval evidence as the frozen structural member
telescope. -/
noncomputable def arguments {base : Ctx sig}
    {lower upper : Shape sig} (witness : Witness base lower upper) :
    Telescope.Args base (Pair.Interval.memberTelescope lower upper) :=
  Pair.Interval.memberArguments base lower upper witness.selected
    witness.lowerFunction witness.lowerTyping witness.upperFunction
    witness.upperTyping

end Interval

/-! ## Outer pair repacking -/

namespace Pair

/-- Repack an outer pair after converting its Church representation.  The
source package's actual hidden identity and payload are retained; only its
`I -> representation` observation is postcomposed. -/
private noncomputable def targetArguments (base : Ctx sig)
    (sourceRepresentation targetRepresentation : Telescope sig)
    (representation : Conversion base sourceRepresentation.existsTy
      targetRepresentation.existsTy) :
    Telescope.Args ((Direct.Pair.plan sourceRepresentation).context base)
      (Direct.Pair.plan (targetRepresentation.rename
        (Direct.Pair.plan sourceRepresentation).telescope.weaken)).telescope :=
  let source := Direct.Pair.plan sourceRepresentation
  let mapping := source.telescope.weaken
  let targetAt := targetRepresentation.rename mapping
  let representationFunction := representation.function.rename mapping
  let representationTyping : Exp.HasType (source.context base)
      representationFunction
      (.arrow (Direct.Pair.finalRepresentationTy sourceRepresentation)
        targetAt.existsTy) := by
    simpa only [Direct.Pair.finalRepresentationTy, Ty.rename,
      Package.existsTy_rename] using
        representation.functionTyping.rename
          (source.telescope.weaken_typed base)
  let toTarget := Direct.Adapter.compose source.identityTy
    (Direct.Pair.toRepresentation sourceRepresentation)
    representationFunction
  let toTargetTyping := Direct.Adapter.compose_hasType
    (Direct.Pair.toRepresentation_hasType base sourceRepresentation)
    representationTyping
  .tvar source.identityTy
    (.var source.payload (source.payload_hasType base)
      (.var toTarget (by
        exact (Direct.Pair.toRepresentationField_open targetAt
          source.identityTy source.payload).symm ▸ toTargetTyping) .nil))

private noncomputable def apply (base : Ctx sig)
    (sourceRepresentation targetRepresentation : Telescope sig)
    (representation : Conversion base sourceRepresentation.existsTy
      targetRepresentation.existsTy)
    (package : Exp sig) : Exp sig :=
  let source := Direct.Pair.plan sourceRepresentation
  let mapping := source.telescope.weaken
  let targetAt := targetRepresentation.rename mapping
  let result := (Direct.Pair.plan targetAt).pack
    (targetArguments base sourceRepresentation targetRepresentation
      representation)
  source.unpack package (Direct.Pair.plan targetRepresentation).inputTy result

private noncomputable def apply_hasType (base : Ctx sig)
    (sourceRepresentation targetRepresentation : Telescope sig)
    (representation : Conversion base sourceRepresentation.existsTy
      targetRepresentation.existsTy)
    {package : Exp sig}
    (packageTyping : Exp.HasType base package
      (Direct.Pair.plan sourceRepresentation).inputTy) :
    Exp.HasType base
      (apply base sourceRepresentation targetRepresentation representation
        package)
      (Direct.Pair.plan targetRepresentation).inputTy := by
  let source := Direct.Pair.plan sourceRepresentation
  let mapping := source.telescope.weaken
  let targetAt := targetRepresentation.rename mapping
  let arguments := targetArguments base sourceRepresentation
    targetRepresentation representation
  let result := (Direct.Pair.plan targetAt).pack arguments
  have resultTyping : Exp.HasType (source.context base) result
      ((Direct.Pair.plan targetRepresentation).inputTy.rename mapping) := by
    rw [Direct.Pair.inputTy_rename]
    exact (Direct.Pair.plan targetAt).pack_hasType arguments
  exact source.unpack_hasType packageTyping resultTyping

private noncomputable def function (base : Ctx sig)
    (sourceRepresentation targetRepresentation : Telescope sig)
    (representation : Conversion base sourceRepresentation.existsTy
      targetRepresentation.existsTy) : Exp sig :=
  let sourceInput :=
    (Direct.Pair.plan sourceRepresentation).inputTy
  let underInput := base.bindVar sourceInput
  let mapping : Rename sig (sig ,, .var) := Rename.weaken .var
  let sourceAt := sourceRepresentation.rename mapping
  let targetAt := targetRepresentation.rename mapping
  let representationAt : Conversion underInput sourceAt.existsTy
      targetAt.existsTy :=
    .mk (representation.function.rename mapping)
      (by
        simpa only [Ty.weaken, Ty.rename, Package.existsTy_rename] using
          representation.functionTyping.weaken (.var sourceInput))
  Direct.Adapter.ofBody sourceInput
    (apply underInput sourceAt targetAt representationAt (.var .here))

private noncomputable def function_hasType (base : Ctx sig)
    (sourceRepresentation targetRepresentation : Telescope sig)
    (representation : Conversion base sourceRepresentation.existsTy
      targetRepresentation.existsTy) :
    Exp.HasType base
      (function base sourceRepresentation targetRepresentation
        representation)
      (.arrow (Direct.Pair.plan sourceRepresentation).inputTy
        (Direct.Pair.plan targetRepresentation).inputTy) := by
  apply Direct.Adapter.ofBody_hasType
  let sourceInput := (Direct.Pair.plan sourceRepresentation).inputTy
  let underInput := base.bindVar sourceInput
  let mapping : Rename sig (sig ,, .var) := Rename.weaken .var
  let sourceAt := sourceRepresentation.rename mapping
  let targetAt := targetRepresentation.rename mapping
  let representationAt : Conversion underInput sourceAt.existsTy
      targetAt.existsTy :=
    .mk (representation.function.rename mapping)
      (by
        simpa only [Ty.weaken, Ty.rename, Package.existsTy_rename] using
          representation.functionTyping.weaken (.var sourceInput))
  have variableTyping : Exp.HasType underInput (.var .here)
      (Direct.Pair.plan sourceAt).inputTy := by
    have raw : Exp.HasType underInput (.var .here)
        (sourceInput.rename mapping) := .var Ctx.Lookup.here
    rwa [Direct.Pair.inputTy_rename] at raw
  have bodyTyping := apply_hasType underInput sourceAt targetAt
    representationAt variableTyping
  rw [<- Direct.Pair.inputTy_rename] at bodyTyping
  exact bodyTyping

/-- Lift a representation conversion through the stable outer pair shell. -/
noncomputable def retarget (base : Ctx sig)
    (sourceRepresentation targetRepresentation : Telescope sig)
    (representation : Conversion base sourceRepresentation.existsTy
      targetRepresentation.existsTy) :
    Conversion base (Direct.Pair.plan sourceRepresentation).inputTy
      (Direct.Pair.plan targetRepresentation).inputTy :=
  .mk (function base sourceRepresentation targetRepresentation
    representation)
    (function_hasType base sourceRepresentation targetRepresentation
      representation)

end Pair

end Conversion

end LambdaPToFCo.Direct.Internal
