import Coercions.Translation.RecursiveObjects.Realizability
import Coercions.FCsub.Checker

/-!
# Recursive-object bridge regressions

The accepted example is the source calculus' two-member knot

* `A = Top → self.B`
* `B = Top → self.A`.

Both references occur under arrow heads.  The rejected comparison removes
those arrows and exposes the direct alias cycle `A = self.B; B = self.A`.
-/

namespace DotToFCsub.RecursiveObjects.Examples

open DotFCR.Source
open DotFCR.Source.MutualExample

abbrev Definitions : List (TypeDef ClosedSelfScope) := definitions

def firstPosition : Fin Definitions.length := ⟨0, by decide⟩
def secondPosition : Fin Definitions.length := ⟨1, by decide⟩

/-- Executable label allocation for the two public abstract names. -/
def labels : LabelLayout Definitions where
  index? := fun
    | 0 => some firstPosition
    | 1 => some secondPosition
    | _ + 2 => none
  owns := by native_decide

/-- Let the executable translation itself determine each public exact
witness.  `getD` is harmless here because `witnesses_translate` proves that
both finite positions succeed. -/
def targetWitness (index : Fin Definitions.length) :
    FCsub.Ty (FCsub.TypeScope [] Definitions.length) :=
  (translateTy? (TyEnv.self (target := []) labels)
    (Definitions.get index).witness).getD .top

def witnessTranslation : WitnessTranslation (target := []) Definitions labels where
  witness := targetWitness
  translates := by native_decide

/-- Canonical newest-first order of the two public member positions. -/
def order : PositionOrder Definitions.length where
  positions := [firstPosition, secondPosition]
  nodup := by native_decide
  complete := by native_decide
  length_eq := by native_decide

theorem first_translation_tracks_nested_self :
    translateTy? (TyEnv.self (target := []) labels) firstWitness =
      some (.arr .top
        ((publicName (target := []) secondPosition).weaken
          (kind := .term))) := by
  native_decide

theorem second_translation_tracks_nested_self :
    translateTy? (TyEnv.self (target := []) labels) secondWitness =
      some (.arr .top
        ((publicName (target := []) firstPosition).weaken
          (kind := .term))) := by
  native_decide

/-- The exact-witness block contains self plus both public members. -/
def block : FCsub.RecBodies [] 3 3 :=
  recursiveBlock witnessTranslation.witness

theorem self_is_newest :
    block.get (selfIndex Definitions.length) = .one := by
  native_decide

theorem first_member_is_after_self :
    block.get (memberIndex firstPosition) =
      (targetWitness firstPosition).weaken (kind := .type) := by
  native_decide

theorem member_projections_are_distinct :
    (FCsub.Ty.recProj block (memberIndex firstPosition)) ≠
      FCsub.Ty.recProj block (memberIndex secondPosition) := by
  native_decide

/-- The two arrow-headed member bodies and the unit self body are all
head-contractive. -/
theorem block_guarded : block.headGuarded = true := by
  native_decide

/-- Simultaneous unfolding substitutes both member projections through the
cross references. -/
theorem block_unfolds : ∀ index,
    block.unfoldAt (memberIndex index) =
      (targetWitness index).instantiateNames
        (publicWitnesses targetWitness) := by
  native_decide

def encoding : Encoding (target := []) Definitions where
  labels := labels
  translation := witnessTranslation
  order := order
  guarded := block_guarded
  unfolds := block_unfolds

theorem exactly_two_public_names : Definitions.length = 2 := rfl

theorem exactly_four_public_constraints :
    pairCount encoding.order.positions = 4 := by
  native_decide

theorem advertised_constraint_count :
    pairCount encoding.order.positions = 2 * Definitions.length :=
  encoding.constraint_count

/-- The source recursive object is accepted. -/
def sourceTyping : HasTy Ctx.nil object objectType := objectTyping

/-- The translated package is typed using only ambient unfold evidence. -/
noncomputable def targetTyping :
    FCsub.Tm.HasType FCsub.Ctx.nil encoding.object encoding.objectType :=
  encoding.object_typed

noncomputable def realization : RecursiveObjectRealization encoding :=
  realizeRecursiveObject definitionsValid encoding

theorem closed_consistent : ClosedExactInterfaceConsistent encoding :=
  closed_exact_interface_consistency definitionsValid encoding

theorem first_exact_witness_round_trip :
    Nonempty (ExactWitnessFactorization encoding firstPosition) :=
  ⟨factorExactWitness encoding firstPosition⟩

theorem neither_member_has_bad_bounds :
    (¬ BadBoundsAt encoding firstPosition) ∧
      (¬ BadBoundsAt encoding secondPosition) :=
  ⟨noBadBoundsAt encoding firstPosition,
    noBadBoundsAt encoding secondPosition⟩

theorem operational_correspondence :
    StaticObjectCorrespondence encoding :=
  static_object_correspondence encoding

theorem target_checks :
    FCsub.checkTerm FCsub.Ctx.nil encoding.object encoding.objectType = true := by
  native_decide

theorem evidence_checks_ambiently :
    FCsub.checkArgs FCsub.Ctx.nil encoding.telescope encoding.witnesses
      encoding.evidence = true := by
  native_decide

theorem folded_payload_checks :
    FCsub.checkTerm FCsub.Ctx.nil encoding.payload
      (.recProj encoding.block (selfIndex Definitions.length)) = true := by
  native_decide

/-! ## Direct alias rejection -/

abbrev DirectDefinitions : List (TypeDef ClosedSelfScope) :=
  directAliasDefinitions

def directFirstPosition : Fin DirectDefinitions.length := ⟨0, by decide⟩
def directSecondPosition : Fin DirectDefinitions.length := ⟨1, by decide⟩

def directLabels : LabelLayout DirectDefinitions where
  index? := fun
    | 0 => some directFirstPosition
    | 1 => some directSecondPosition
    | _ + 2 => none
  owns := by native_decide

def directTargetWitness (index : Fin DirectDefinitions.length) :
    FCsub.Ty (FCsub.TypeScope [] DirectDefinitions.length) :=
  (translateTy? (TyEnv.self (target := []) directLabels)
    (DirectDefinitions.get index).witness).getD .top

theorem direct_witnesses_translate : ∀ index,
    translateTy? (TyEnv.self (target := []) directLabels)
        (DirectDefinitions.get index).witness =
      some (directTargetWitness index) := by
  native_decide

/-- The naked mutually recursive names become naked recursive target names,
so the FCsub block guard independently rejects the cycle. -/
theorem direct_block_rejected :
    (recursiveBlock directTargetWitness).headGuarded = false := by
  native_decide

theorem no_guarded_direct_block :
    (recursiveBlock directTargetWitness).headGuarded = true → False := by
  intro guarded
  have rejected := direct_block_rejected
  rw [guarded] at rejected
  contradiction

/-- The source checker rejects the same cycle before bridge construction. -/
theorem no_source_direct_object :
    TypeDefs.RecValid Ctx.nil DirectDefinitions → False :=
  directAlias_not_valid

end DotToFCsub.RecursiveObjects.Examples
