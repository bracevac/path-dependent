import Coercions.Translation.IntersectionSignatures.Encoding

/-!
# Typed projection morphisms for the intersection-signature slice

Overlapping views have the same name block and use FCsub's proof-relevant
`Telescope.Projection` API directly.  A projection from a disjoint two-name
signature to one component additionally selects an existing source name.
The latter is represented by an ordinary `TelMor.map`: its type argument is
the selected bound source name and its evidence arguments are selected source
assumptions.  No morphism allocates a fresh name.
-/

namespace DotToFCsub.IntersectionSignatures

namespace Morphisms

open Encoding

/-! ## Reusable projection boundary -/

/-- Select existing source names in the complete opened source scope. -/
def selectStaticNames (scope : FCsub.Sig)
    (sourceNames sourceConstraints : Nat) {targetNames : Nat}
    (select : Fin targetNames → Fin sourceNames) :
    FCsub.TypeArgs
      (FCsub.StaticScope scope sourceNames sourceConstraints) targetNames :=
  FCsub.TypeArgs.tabulate fun index =>
    .tvar
      ((FCsub.Rename.weakenN (.evidence .inclusion) sourceConstraints).var
        (FCsub.BVar.bound sourceNames (select index)))

@[simp]
theorem selectStaticNames_get (scope : FCsub.Sig)
    (sourceNames sourceConstraints : Nat) {targetNames : Nat}
    (select : Fin targetNames → Fin sourceNames) (index : Fin targetNames) :
    (selectStaticNames scope sourceNames sourceConstraints select).get index =
      .tvar
        ((FCsub.Rename.weakenN (.evidence .inclusion) sourceConstraints).var
          (FCsub.BVar.bound sourceNames (select index))) := by
  simp [selectStaticNames]

/-- The raw projection syntax used when source and target have different
name arities.  A subsequent checker/declarative proof establishes that the
selected names and assumptions satisfy the particular target telescope. -/
def selectMorphism {scope : FCsub.Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (source : FCsub.Telescope scope sourceNames sourceConstraints)
    (target : FCsub.Telescope scope targetNames targetConstraints)
    (selectName : Fin targetNames → Fin sourceNames)
    (selectConstraint : Fin targetConstraints → Fin sourceConstraints) :
    FCsub.TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints :=
  .map source target
    (selectStaticNames scope sourceNames sourceConstraints selectName)
    (FCsub.LeArgs.selectAssumptions scope sourceNames sourceConstraints
      selectConstraint)

@[simp]
theorem selectMorphism_sourceTelescope {scope : FCsub.Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (source : FCsub.Telescope scope sourceNames sourceConstraints)
    (target : FCsub.Telescope scope targetNames targetConstraints)
    (selectName : Fin targetNames → Fin sourceNames)
    (selectConstraint : Fin targetConstraints → Fin sourceConstraints) :
    (selectMorphism source target selectName selectConstraint).sourceTelescope =
      source := rfl

@[simp]
theorem selectMorphism_targetTelescope {scope : FCsub.Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (source : FCsub.Telescope scope sourceNames sourceConstraints)
    (target : FCsub.Telescope scope targetNames targetConstraints)
    (selectName : Fin targetNames → Fin sourceNames)
    (selectConstraint : Fin targetConstraints → Fin sourceConstraints) :
    (selectMorphism source target selectName selectConstraint).targetTelescope =
      target := rfl

/-- Same-name projections are the standalone FCsub structural API. -/
def constraintMorphism {scope : FCsub.Sig}
    {names sourceConstraints targetConstraints : Nat}
    {source : FCsub.Telescope scope names sourceConstraints}
    {target : FCsub.Telescope scope names targetConstraints}
    (projection : FCsub.Telescope.Projection source target) :
    FCsub.TelMor scope names sourceConstraints names targetConstraints :=
  FCsub.TelMor.ofProjection projection

/-- Every same-name projection is declaratively typed in every context. -/
noncomputable def constraintMorphism_hasType {scope : FCsub.Sig}
    (context : FCsub.Ctx scope)
    {names sourceConstraints targetConstraints : Nat}
    {source : FCsub.Telescope scope names sourceConstraints}
    {target : FCsub.Telescope scope names targetConstraints}
    (projection : FCsub.Telescope.Projection source target) :
    FCsub.TelMor.HasType context (constraintMorphism projection)
      source target :=
  FCsub.TelMor.HasType.ofProjection context projection

/-- Applying a same-name projection preserves the entire witness vector. -/
theorem constraintMorphism_preserves_types {scope : FCsub.Sig}
    {names sourceConstraints targetConstraints : Nat}
    {source : FCsub.Telescope scope names sourceConstraints}
    {target : FCsub.Telescope scope names targetConstraints}
    (projection : FCsub.Telescope.Projection source target)
    (realization : FCsub.Realization scope names sourceConstraints) :
    ((constraintMorphism projection).apply realization).types =
      realization.types := by
  rw [constraintMorphism, FCsub.TelMor.apply_ofProjection]

/-! ## Closed overlapping interface -/

def oneName : FCsub.Ty (FCsub.TypeScope [] 1) :=
  .tvar (.here : FCsub.BVar (FCsub.TypeScope [] 1) .type)

def topMemberTelescope : FCsub.Telescope [] 1 2 :=
  telescopeOfList
    [.inclusion .bot oneName, .inclusion oneName .top]

def bottomMemberTelescope : FCsub.Telescope [] 1 2 :=
  telescopeOfList
    [.inclusion .bot oneName, .inclusion oneName .bot]

def overlappingTelescope : FCsub.Telescope [] 1 4 :=
  telescopeOfList
    [.inclusion .bot oneName, .inclusion oneName .top,
      .inclusion .bot oneName, .inclusion oneName .bot]

def overlapLeftProjection :
    FCsub.Telescope.Projection overlappingTelescope topMemberTelescope where
  constraint := fun index => ⟨index.val, by omega⟩
  preserves := by native_decide

def overlapRightProjection :
    FCsub.Telescope.Projection overlappingTelescope bottomMemberTelescope where
  constraint := fun index => ⟨index.val + 2, by omega⟩
  preserves := by native_decide

def overlapLeftMorphism : FCsub.TelMor [] 1 4 1 2 :=
  constraintMorphism overlapLeftProjection

def overlapRightMorphism : FCsub.TelMor [] 1 4 1 2 :=
  constraintMorphism overlapRightProjection

noncomputable def overlapLeftMorphism_hasType :
    FCsub.TelMor.HasType FCsub.Ctx.nil overlapLeftMorphism
      overlappingTelescope topMemberTelescope :=
  constraintMorphism_hasType FCsub.Ctx.nil overlapLeftProjection

noncomputable def overlapRightMorphism_hasType :
    FCsub.TelMor.HasType FCsub.Ctx.nil overlapRightMorphism
      overlappingTelescope bottomMemberTelescope :=
  constraintMorphism_hasType FCsub.Ctx.nil overlapRightProjection

/-! ## Closed disjoint interface -/

/-- In canonical label order, the head entry/name is newest. -/
def firstOfTwo : FCsub.Ty (FCsub.TypeScope [] 2) :=
  .tvar (.here : FCsub.BVar (FCsub.TypeScope [] 2) .type)

/-- The tail entry/name is the next-older name in the same block. -/
def secondOfTwo : FCsub.Ty (FCsub.TypeScope [] 2) :=
  .tvar (.there .here : FCsub.BVar (FCsub.TypeScope [] 2) .type)

def disjointTelescope : FCsub.Telescope [] 2 4 :=
  telescopeOfList
    [.inclusion .bot firstOfTwo, .inclusion firstOfTwo .top,
      .inclusion .bot secondOfTwo, .inclusion secondOfTwo .bot]

def selectFirstName : Fin 1 → Fin 2 :=
  fun _ => ⟨0, by omega⟩

def selectSecondName : Fin 1 → Fin 2 :=
  fun _ => ⟨1, by omega⟩

def selectFirstConstraints : Fin 2 → Fin 4 :=
  fun index => ⟨index.val, by omega⟩

def selectSecondConstraints : Fin 2 → Fin 4 :=
  fun index => ⟨index.val + 2, by omega⟩

def disjointFirstMorphism : FCsub.TelMor [] 2 4 1 2 :=
  selectMorphism disjointTelescope topMemberTelescope
    selectFirstName selectFirstConstraints

def disjointSecondMorphism : FCsub.TelMor [] 2 4 1 2 :=
  selectMorphism disjointTelescope bottomMemberTelescope
    selectSecondName selectSecondConstraints

theorem disjointFirstMorphism_checks :
    FCsub.checkMorphism FCsub.Ctx.nil disjointFirstMorphism
      disjointTelescope topMemberTelescope = true := by
  native_decide

theorem disjointSecondMorphism_checks :
    FCsub.checkMorphism FCsub.Ctx.nil disjointSecondMorphism
      disjointTelescope bottomMemberTelescope = true := by
  native_decide

def disjointFirstMorphism_hasType :
    FCsub.TelMor.HasType FCsub.Ctx.nil disjointFirstMorphism
      disjointTelescope topMemberTelescope := by
  apply FCsub.TelMor.HasType.map
  apply FCsub.LeArgs.HasType.snoc
  · apply FCsub.LeArgs.HasType.snoc
    · exact FCsub.LeArgs.HasType.nil
    · apply FCsub.LeCo.HasType.var
      rfl
  · apply FCsub.LeCo.HasType.var
    rfl

def disjointSecondMorphism_hasType :
    FCsub.TelMor.HasType FCsub.Ctx.nil disjointSecondMorphism
      disjointTelescope bottomMemberTelescope := by
  apply FCsub.TelMor.HasType.map
  apply FCsub.LeArgs.HasType.snoc
  · apply FCsub.LeArgs.HasType.snoc
    · exact FCsub.LeArgs.HasType.nil
    · apply FCsub.LeCo.HasType.var
      rfl
  · apply FCsub.LeCo.HasType.var
    rfl

/-- The executable proof-producing kernel certifies the disjoint projection. -/
theorem disjointFirstMorphism_typed :
    Nonempty (FCsub.TelMor.HasType FCsub.Ctx.nil disjointFirstMorphism
      disjointTelescope topMemberTelescope) :=
  FCsub.checkMorphism_sound disjointFirstMorphism_checks

/-- The executable proof-producing kernel certifies the second projection. -/
theorem disjointSecondMorphism_typed :
    Nonempty (FCsub.TelMor.HasType FCsub.Ctx.nil disjointSecondMorphism
      disjointTelescope bottomMemberTelescope) :=
  FCsub.checkMorphism_sound disjointSecondMorphism_checks

end Morphisms

end DotToFCsub.IntersectionSignatures
