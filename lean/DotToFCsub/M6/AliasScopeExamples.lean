import DotToFCsub.M6.AliasScope

/-!
# Executable regressions for finite alias scopes

The examples allocate two distinct private names, exercise both orientations
of their equality-derived inclusions, compose two aliases through a shared
anchor, close a nested `newtype` term, and check that the complete static
layer erases to unit.
-/

namespace DotToFCsub.M6.AliasScopeExamples

open FCsub
open AliasScope

def newest : Fin 2 := ⟨0, by omega⟩
def older : Fin 2 := ⟨1, by omega⟩

/-- Two independent member witnesses. -/
def anchors (index : Fin 2) : Ty [] :=
  if index = newest then .top else .bot

abbrev TwoScope : Sig := Scope [] 2

def context : Ctx TwoScope := extend .nil anchors

example : depth (name (scope := []) 2 newest) = 1 := rfl
example : depth (name (scope := []) 2 older) = 3 := rfl
example : depth (equality (scope := []) 2 newest) = 0 := rfl
example : depth (equality (scope := []) 2 older) = 2 := rfl

theorem names_distinct :
    name (scope := []) 2 newest ≠ name 2 older :=
  name_ne (by decide)

theorem equalities_distinct :
    equality (scope := []) 2 newest ≠ equality 2 older :=
  equality_ne (by decide)

/-- The executable equality checker sees the exact generated endpoints. -/
example : checkEquality context (toAnchor 2 newest)
    (aliasTy 2 newest) (anchorTy anchors newest) = true := by
  native_decide

example : checkEquality context (fromAnchor 2 older)
    (anchorTy anchors older) (aliasTy 2 older) = true := by
  native_decide

/-- Lower evidence is anchor-to-alias; upper evidence reverses it. -/
example : checkEvidence context (lower 2 newest)
    (anchorTy anchors newest) (aliasTy 2 newest) = true := by
  native_decide

example : checkEvidence context (upper 2 newest)
    (aliasTy 2 newest) (anchorTy anchors newest) = true := by
  native_decide

/-! Two aliases can be related transitively when their anchors are equal. -/

def sharedAnchors (_index : Fin 2) : Ty [] := .one
def sharedContext : Ctx (Scope [] 2) := extend .nil sharedAnchors

def sharedEquality : EqCo (Scope [] 2) := .refl .one

noncomputable def sharedEquality_hasType :
    EqCo.HasType sharedContext sharedEquality
      (anchorTy sharedAnchors newest) (anchorTy sharedAnchors older) := by
  simpa [sharedEquality, sharedAnchors, anchorTy, Ty.rename] using
    (EqCo.HasType.refl (context := sharedContext) (.one : Ty (Scope [] 2)))

noncomputable def aliasesBetween_hasType :
    EqCo.HasType sharedContext
      (between 2 newest older sharedEquality)
      (aliasTy 2 newest) (aliasTy 2 older) :=
  between_hasType .nil sharedAnchors newest older sharedEquality_hasType

example : checkEquality sharedContext
    (between 2 newest older sharedEquality)
    (aliasTy 2 newest) (aliasTy 2 older) = true := by
  native_decide

/-! The nested static allocation checks and erases without residue. -/

def closedAliases : Tm [] :=
  close anchors (.unit : Tm (Scope [] 2))

noncomputable def closedAliases_hasType :
    Tm.HasType .nil closedAliases .one := by
  apply close_hasType .nil anchors
  simpa [Ty.rename] using
    (Tm.HasType.unit (context := extend (.nil : Ctx []) anchors))

example : checkTerm (.nil : Ctx []) closedAliases .one = true := by
  native_decide

example : closedAliases.erase = Runtime.Tm.unit := rfl

example : strengthen ((.one : Ty []).rename (weaken 2)) = some .one :=
  strengthen_weaken .one 2

end DotToFCsub.M6.AliasScopeExamples
