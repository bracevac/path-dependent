import Coercions.Translation.IntersectionSignatures.Morphisms

/-!
# Executable intersection-signature regressions

These checks cross both phases: `DotFCI` first collects and normalizes member
signatures, then the intersection-signature bridge allocates one FCsub name per normalized label
and emits every directed interval constraint.  The overlap examples also
package and project the resulting interface through the proof-producing
FCsub checker, while erasure confirms that the static work remains runtime
unit.
-/

namespace DotToFCsub.IntersectionSignatures

namespace Examples

open DotFCI.Source
open Encoding
open Morphisms

def A : Name := 0
def B : Name := 1

def aTop : DotFCI.Source.Ty [] := .member A .bot .top
def aBottom : DotFCI.Source.Ty [] := .member A .bot .bot
def bBottom : DotFCI.Source.Ty [] := .member B .bot .bot

def overlap : DotFCI.Source.Ty [] := .inter aTop aBottom
def disjoint : DotFCI.Source.Ty [] := .inter aTop bBottom

def aTopSignature : Signature [] := .singleton A .bot .top
def aBottomSignature : Signature [] := .singleton A .bot .bot
def bBottomSignature : Signature [] := .singleton B .bot .bot

def overlapSignature : Signature [] :=
  aTopSignature.merge aBottomSignature

def disjointSignature : Signature [] :=
  aTopSignature.merge bBottomSignature

theorem collect_overlap :
    DotFCI.Source.collect? overlap = some overlapSignature := by
  native_decide

theorem collect_disjoint :
    DotFCI.Source.collect? disjoint = some disjointSignature := by
  native_decide

def overlapEncoding : Encoding overlapSignature :=
  ⟨4, overlappingTelescope⟩

def disjointEncoding : Encoding disjointSignature :=
  ⟨4, disjointTelescope⟩

theorem encode_overlap :
    encode? overlapSignature = some overlapEncoding := by
  native_decide

theorem encode_disjoint :
    encode? disjointSignature = some disjointEncoding := by
  native_decide

/-- Two occurrences of label `A` allocate one identity. -/
theorem overlap_exactly_one_name : overlapEncoding.names = 1 := by
  native_decide

/-- Both lower/upper pairs are retained: two occurrences, four constraints. -/
theorem overlap_exactly_four_constraints :
    overlapEncoding.constraints = 4 := rfl

theorem overlap_labels_exactly_A : overlapSignature.labels = [A] := by
  native_decide

/-- Disjoint labels allocate two identities while retaining four constraints. -/
theorem disjoint_exactly_two_names : disjointEncoding.names = 2 := by
  native_decide

theorem disjoint_exactly_four_constraints :
    disjointEncoding.constraints = 4 := rfl

theorem disjoint_labels_exactly_A_B : disjointSignature.labels = [A, B] := by
  native_decide

/-! ## Exact identity reuse by overlap projections -/

def overlapSourceName :
    FCsub.BVar (FCsub.StaticScope [] 1 4) .type :=
  (FCsub.Rename.weakenN (.evidence .inclusion) 4).var
    (FCsub.BVar.bound 1 ⟨0, by omega⟩)

def overlapLeftProjectionNames :
    FCsub.TypeArgs (FCsub.StaticScope [] 1 4) 1 :=
  FCsub.TypeArgs.boundNames [] 1 4

def overlapRightProjectionNames :
    FCsub.TypeArgs (FCsub.StaticScope [] 1 4) 1 :=
  FCsub.TypeArgs.boundNames [] 1 4

theorem overlapLeftMorphism_uses_source_bound_names :
    overlapLeftMorphism =
      .map overlappingTelescope topMemberTelescope
        overlapLeftProjectionNames
        (FCsub.LeArgs.selectAssumptions [] 1 4
          overlapLeftProjection.constraint) := rfl

theorem overlapRightMorphism_uses_source_bound_names :
    overlapRightMorphism =
      .map overlappingTelescope bottomMemberTelescope
        overlapRightProjectionNames
        (FCsub.LeArgs.selectAssumptions [] 1 4
          overlapRightProjection.constraint) := rfl

/-- Both target views receive the exact same source vector, not copies. -/
theorem overlap_projection_name_vectors_identical :
    overlapLeftProjectionNames = overlapRightProjectionNames := rfl

/-- At the element level, both projections refer to the same source `BVar`. -/
theorem overlap_projections_use_exact_source_BVar :
    overlapLeftProjectionNames.get ⟨0, by omega⟩ =
        .tvar overlapSourceName ∧
      overlapRightProjectionNames.get ⟨0, by omega⟩ =
        .tvar overlapSourceName := by
  native_decide

/-! ## Checked package and erased projections -/

def overlapWitnesses : FCsub.TypeArgs [] 1 :=
  .snoc .nil .bot

/-- Newest-first evidence order follows `telescopeOfList`: lower₁, upper₁,
lower₂, upper₂. -/
def overlapEvidence : FCsub.LeArgs [] 4 :=
  .snoc
    (.snoc
      (.snoc
        (.snoc .nil (.refl .bot))
        (.refl .bot))
      (.top .bot))
    (.refl .bot)

def overlapPackage : FCsub.Tm [] :=
  .pack overlappingTelescope .one overlapWitnesses overlapEvidence .unit

def overlapExists : FCsub.Ty [] :=
  .existsT overlappingTelescope .one

theorem overlapPackage_checks :
    FCsub.checkTerm FCsub.Ctx.nil overlapPackage overlapExists = true := by
  native_decide

theorem overlapPackage_typed :
    Nonempty (FCsub.Tm.HasType FCsub.Ctx.nil overlapPackage overlapExists) :=
  FCsub.checkTerm_sound overlapPackage_checks

def overlapLeftEvidence : FCsub.LeCo [] :=
  .existsT overlapLeftMorphism .one .one (.refl .one)

def overlapRightEvidence : FCsub.LeCo [] :=
  .existsT overlapRightMorphism .one .one (.refl .one)

def topMemberExists : FCsub.Ty [] :=
  .existsT topMemberTelescope .one

def bottomMemberExists : FCsub.Ty [] :=
  .existsT bottomMemberTelescope .one

theorem overlapLeftEvidence_checks :
    FCsub.checkEvidence FCsub.Ctx.nil overlapLeftEvidence
      overlapExists topMemberExists = true := by
  native_decide

theorem overlapRightEvidence_checks :
    FCsub.checkEvidence FCsub.Ctx.nil overlapRightEvidence
      overlapExists bottomMemberExists = true := by
  native_decide

def overlapLeftCast : FCsub.Tm [] :=
  .cast overlapPackage overlapLeftEvidence

def overlapRightCast : FCsub.Tm [] :=
  .cast overlapPackage overlapRightEvidence

theorem overlapLeftCast_checks :
    FCsub.checkTerm FCsub.Ctx.nil overlapLeftCast topMemberExists = true := by
  native_decide

theorem overlapRightCast_checks :
    FCsub.checkTerm FCsub.Ctx.nil overlapRightCast bottomMemberExists = true := by
  native_decide

/-- The package has only its unit payload at runtime. -/
theorem erase_overlapPackage_is_unit :
    overlapPackage.erase = FCsub.Runtime.Tm.unit := rfl

/-- Constraint projection and the existential cast both erase. -/
theorem erase_overlapLeftCast_is_unit :
    overlapLeftCast.erase = FCsub.Runtime.Tm.unit := rfl

theorem erase_overlapRightCast_is_unit :
    overlapRightCast.erase = FCsub.Runtime.Tm.unit := rfl

/-! ## Disjoint name selection and merge laws -/

def disjointFirstSourceName :
    FCsub.BVar (FCsub.StaticScope [] 2 4) .type :=
  (FCsub.Rename.weakenN (.evidence .inclusion) 4).var
    (FCsub.BVar.bound 2 ⟨0, by omega⟩)

def disjointSecondSourceName :
    FCsub.BVar (FCsub.StaticScope [] 2 4) .type :=
  (FCsub.Rename.weakenN (.evidence .inclusion) 4).var
    (FCsub.BVar.bound 2 ⟨1, by omega⟩)

theorem disjointFirstProjection_reuses_source_BVar :
    (selectStaticNames [] 2 4 selectFirstName).get ⟨0, by omega⟩ =
      .tvar disjointFirstSourceName := by
  native_decide

theorem disjointSecondProjection_reuses_source_BVar :
    (selectStaticNames [] 2 4 selectSecondName).get ⟨0, by omega⟩ =
      .tvar disjointSecondSourceName := by
  native_decide

theorem disjoint_order_equiv :
    aTopSignature.merge bBottomSignature ≈ₛ
      bBottomSignature.merge aTopSignature :=
  Signature.merge_comm aTopSignature bBottomSignature
    (Signature.singleton_normalized A .bot .top)
    (Signature.singleton_normalized B .bot .bot)

/-- Canonical label sorting makes the disjoint order regression executable-
identical at the target boundary, not only permutation-equivalent. -/
theorem disjoint_order_encoding_equal :
    encode? (aTopSignature.merge bBottomSignature) =
      encode? (bBottomSignature.merge aTopSignature) := by
  native_decide

theorem three_member_association_equiv :
    ((aTopSignature.merge aBottomSignature).merge bBottomSignature) ≈ₛ
      (aTopSignature.merge (aBottomSignature.merge bBottomSignature)) :=
  Signature.merge_assoc aTopSignature aBottomSignature bBottomSignature
    (Signature.singleton_normalized A .bot .top)
    (Signature.singleton_normalized A .bot .bot)
    (Signature.singleton_normalized B .bot .bot)

/-- In this concrete association regression, canonical collection is even
definitionally equal, so both encodings are executable-identical. -/
theorem three_member_association_encoding_equal :
    encode?
        ((aTopSignature.merge aBottomSignature).merge bBottomSignature) =
      encode?
        (aTopSignature.merge (aBottomSignature.merge bBottomSignature)) := by
  native_decide

end Examples

end DotToFCsub.IntersectionSignatures
