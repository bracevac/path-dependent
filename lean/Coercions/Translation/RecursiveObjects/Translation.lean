import Coercions.Translation.RecursiveObjects.MemberLayout
import Coercions.FCsub.Typing

/-!
# Type-preserving recursive package translation

For `n` exact source definitions the public interface binds `n` abstract
names and contributes two directed constraints per definition.  The package
witness for public member `i` is recursive projection `i.succ`; its lower and
upper certificates are respectively symmetry of canonical unfolding and
canonical unfolding.  Both certificates are checked in the ambient context,
never under the package telescope.
-/

namespace DotToFCsub.RecursiveObjects

open DotFCR.Source

/-! ## Complete public member order -/

/-- An explicit order containing every public position exactly once.  The
length equation makes the advertised `2 * n` interface size available
without hiding the construction behind a quotient or finite-set choice. -/
structure PositionOrder (members : Nat) : Type where
  positions : List (Fin members)
  nodup : positions.Nodup
  complete : ∀ index, index ∈ positions
  length_eq : positions.length = members

/-! ## Paired telescope construction -/

/-- Two constraints for every member of an explicit public order. -/
def pairCount {members : Nat} : List (Fin members) → Nat
  | [] => 0
  | _ :: remaining => (pairCount remaining + 1) + 1

@[simp]
theorem pairCount_cons {members : Nat} (index : Fin members)
    (remaining : List (Fin members)) :
    pairCount (index :: remaining) = (pairCount remaining + 1) + 1 := rfl

theorem pairCount_eq_two_mul_length {members : Nat}
    (positions : List (Fin members)) :
    pairCount positions = 2 * positions.length := by
  induction positions with
  | nil => rfl
  | cons index remaining induction =>
      simp only [pairCount, List.length_cons, induction]
      omega

theorem pairCount_order {members : Nat} (order : PositionOrder members) :
    pairCount order.positions = 2 * members := by
  rw [pairCount_eq_two_mul_length, order.length_eq]

/-- Lower bound for one exact public member: its translated witness is below
the public abstract name. -/
def lowerProposition {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members))
    (index : Fin members) :
    FCsub.Proposition (FCsub.TypeScope target members) :=
  .inclusion (witness index) (publicName (target := target) index)

/-- Upper bound for one exact public member. -/
def upperProposition {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members))
    (index : Fin members) :
    FCsub.Proposition (FCsub.TypeScope target members) :=
  .inclusion (publicName (target := target) index) (witness index)

/-- Canonical lower certificate for an exact member. -/
def lowerCertificate {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members))
    (index : Fin members) : FCsub.LeCo target :=
  .eqToLe (.symm (.unfoldRec (recursiveBlock witness) (memberIndex index)))

/-- Canonical upper certificate for an exact member. -/
def upperCertificate {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members))
    (index : Fin members) : FCsub.LeCo target :=
  .eqToLe (.unfoldRec (recursiveBlock witness) (memberIndex index))

/-- Emit the exact lower/upper pair for every member in newest-first order. -/
def publicTelescopeFor {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members)) :
    (positions : List (Fin members)) →
      FCsub.Telescope target members (pairCount positions)
  | [] => .nil
  | index :: remaining =>
      .snoc
        (.snoc (publicTelescopeFor witness remaining)
          (lowerProposition witness index))
        (upperProposition witness index)

/-- Exact witness evidence emitted in the same structural order as
`publicTelescopeFor`. -/
def publicEvidenceFor {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members)) :
    (positions : List (Fin members)) →
      FCsub.LeArgs target (pairCount positions)
  | [] => .nil
  | index :: remaining =>
      .snoc
        (.snoc (publicEvidenceFor witness remaining)
          (lowerCertificate witness index))
        (upperCertificate witness index)

/-- Shift an older constraint position past one newly emitted lower/upper
pair. -/
def shiftPairSlot {count : Nat} (slot : Fin count) :
    Fin ((count + 1) + 1) :=
  ⟨slot.val + 2, by omega⟩

@[simp]
theorem telescope_get_shiftPair {target : FCsub.Sig} {members count : Nat}
    (telescope : FCsub.Telescope target members count)
    (lower upper : FCsub.Proposition (FCsub.TypeScope target members))
    (slot : Fin count) :
    (FCsub.Telescope.snoc (FCsub.Telescope.snoc telescope lower) upper).get
        (shiftPairSlot slot) =
      telescope.get slot := by
  cases slot
  rfl

@[simp]
theorem evidence_get_shiftPair {target : FCsub.Sig} {count : Nat}
    (evidence : FCsub.LeArgs target count)
    (lower upper : FCsub.LeCo target) (slot : Fin count) :
    (FCsub.LeArgs.snoc (FCsub.LeArgs.snoc evidence lower) upper).get
        (shiftPairSlot slot) =
      evidence.get slot := by
  cases slot
  rfl

/-- A member's concrete newest-first lower/upper slots in a generated public
interface.  These equations connect factorization certificates to the actual
`Telescope.get` and `LeArgs.get` positions, not merely to equal-looking
syntax. -/
structure EmittedPairAt {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members))
    (positions : List (Fin members)) (index : Fin members) : Type where
  lowerSlot : Fin (pairCount positions)
  upperSlot : Fin (pairCount positions)
  telescopeLower : (publicTelescopeFor witness positions).get lowerSlot =
    lowerProposition witness index
  telescopeUpper : (publicTelescopeFor witness positions).get upperSlot =
    upperProposition witness index
  evidenceLower : (publicEvidenceFor witness positions).get lowerSlot =
    lowerCertificate witness index
  evidenceUpper : (publicEvidenceFor witness positions).get upperSlot =
    upperCertificate witness index

/-- List membership compiles to exact telescope/evidence slots. -/
theorem emittedPairAt_of_mem {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members))
    (positions : List (Fin members)) (index : Fin members)
    (member : index ∈ positions) :
    Nonempty (EmittedPairAt witness positions index) := by
  induction positions with
  | nil => simp at member
  | cons head remaining induction =>
      rw [List.mem_cons] at member
      rcases member with equal | member
      · subst head
        exact ⟨
          { lowerSlot := ⟨1, by simp [pairCount]⟩
            upperSlot := ⟨0, by simp [pairCount]⟩
            telescopeLower := rfl
            telescopeUpper := rfl
            evidenceLower := rfl
            evidenceUpper := rfl }⟩
      · rcases induction member with ⟨older⟩
        exact ⟨
          { lowerSlot := shiftPairSlot older.lowerSlot
            upperSlot := shiftPairSlot older.upperSlot
            telescopeLower := by
              simpa [publicTelescopeFor] using older.telescopeLower
            telescopeUpper := by
              simpa [publicTelescopeFor] using older.telescopeUpper
            evidenceLower := by
              simpa [publicEvidenceFor] using older.evidenceLower
            evidenceUpper := by
              simpa [publicEvidenceFor] using older.evidenceUpper }⟩

/-! ## Guarded recursive encoding certificate -/

/-- A complete recursive encoding.  `unfolds` is the central representation
equation: shifting a public witness once to make room for self, then unfolding
the corresponding recursive projection, agrees with instantiating all public
names by the member projections. -/
structure Encoding {target : FCsub.Sig}
    (definitions : List (TypeDef ClosedSelfScope)) : Type where
  labels : LabelLayout definitions
  translation : WitnessTranslation (target := target) definitions labels
  order : PositionOrder definitions.length
  guarded : (recursiveBlock translation.witness).headGuarded = true
  unfolds : ∀ index,
    (recursiveBlock translation.witness).unfoldAt (memberIndex index) =
      (translation.witness index).instantiateNames
        (publicWitnesses translation.witness)

namespace Encoding

def members {target : FCsub.Sig}
    {definitions : List (TypeDef ClosedSelfScope)}
    (_encoding : Encoding (target := target) definitions) : Nat :=
  definitions.length

def block {target : FCsub.Sig}
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := target) definitions) :
    FCsub.RecBodies target (definitions.length + 1)
      (definitions.length + 1) :=
  recursiveBlock encoding.translation.witness

def witnesses {target : FCsub.Sig}
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := target) definitions) :
    FCsub.TypeArgs target definitions.length :=
  publicWitnesses encoding.translation.witness

def telescope {target : FCsub.Sig}
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := target) definitions) :
    FCsub.Telescope target definitions.length
      (pairCount encoding.order.positions) :=
  publicTelescopeFor encoding.translation.witness encoding.order.positions

def evidence {target : FCsub.Sig}
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := target) definitions) :
    FCsub.LeArgs target (pairCount encoding.order.positions) :=
  publicEvidenceFor encoding.translation.witness encoding.order.positions

/-- The self projection weakened below the complete public static interface.
Instantiating the interface returns the same ambient recursive projection. -/
def payloadType {target : FCsub.Sig}
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := target) definitions) :
    FCsub.Ty (FCsub.StaticScope target definitions.length
      (pairCount encoding.order.positions)) :=
  (FCsub.Ty.recProj encoding.block (selfIndex definitions.length)).rename
    (FCsub.Rename.weakenStatic definitions.length
      (pairCount encoding.order.positions))

/-- Public recursive object type.  Its static interface carries the folded
self projection as the (runtime-erased) payload type. -/
def objectType {target : FCsub.Sig}
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := target) definitions) : FCsub.Ty target :=
  .existsT encoding.telescope encoding.payloadType

/-- Fold the runtime unit into the extra self projection. -/
def payload {target : FCsub.Sig}
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := target) definitions) : FCsub.Tm target :=
  .foldRec encoding.block (selfIndex definitions.length) .unit

/-- Translation of a recursive object.  Every witness and certificate is
ambient; the package contains no definition-level runtime data. -/
def object {target : FCsub.Sig}
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := target) definitions) : FCsub.Tm target :=
  .pack encoding.telescope encoding.payloadType encoding.witnesses
    encoding.evidence
    encoding.payload

/-- The public interface contains exactly two constraints for each source
definition. -/
theorem constraint_count {target : FCsub.Sig}
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := target) definitions) :
    pairCount encoding.order.positions = 2 * definitions.length :=
  pairCount_order encoding.order

end Encoding

@[simp]
theorem publicName_instantiateNames {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members))
    (index : Fin members) :
    (publicName (target := target) index).instantiateNames
        (publicWitnesses witness) =
      FCsub.Ty.recProj (recursiveBlock witness) (memberIndex index) := by
  unfold FCsub.Ty.instantiateNames
  exact publicName_instantiate witness index

/-! ## Ambient evidence typing -/

private def lowerEvidence_typed {target : FCsub.Sig}
    {context : FCsub.Ctx target} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members))
    (guarded : (recursiveBlock witness).headGuarded = true)
    (unfolds : ∀ index,
      (recursiveBlock witness).unfoldAt (memberIndex index) =
        (witness index).instantiateNames (publicWitnesses witness))
    (index : Fin members) :
    FCsub.LeCo.HasType context
      (.eqToLe (.symm (.unfoldRec (recursiveBlock witness)
        (memberIndex index))))
      ((witness index).instantiateNames (publicWitnesses witness))
      ((publicName (target := target) index).instantiateNames
        (publicWitnesses witness)) := by
  rw [publicName_instantiateNames]
  rw [← unfolds index]
  exact .eqToLe (.symm (.unfoldRec guarded))

private def upperEvidence_typed {target : FCsub.Sig}
    {context : FCsub.Ctx target} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members))
    (guarded : (recursiveBlock witness).headGuarded = true)
    (unfolds : ∀ index,
      (recursiveBlock witness).unfoldAt (memberIndex index) =
        (witness index).instantiateNames (publicWitnesses witness))
    (index : Fin members) :
    FCsub.LeCo.HasType context
      (.eqToLe (.unfoldRec (recursiveBlock witness) (memberIndex index)))
      ((publicName (target := target) index).instantiateNames
        (publicWitnesses witness))
      ((witness index).instantiateNames (publicWitnesses witness)) := by
  rw [publicName_instantiateNames]
  rw [← unfolds index]
  exact .eqToLe (.unfoldRec guarded)

/-- Every public lower/upper certificate checks in the unchanged ambient
context.  This theorem is intentionally quantified over `context`; no
telescope evidence assumption occurs in the induction. -/
noncomputable def publicEvidenceFor_typed {target : FCsub.Sig}
    {context : FCsub.Ctx target} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members))
    (positions : List (Fin members))
    (guarded : (recursiveBlock witness).headGuarded = true)
    (unfolds : ∀ index,
      (recursiveBlock witness).unfoldAt (memberIndex index) =
        (witness index).instantiateNames (publicWitnesses witness)) :
    FCsub.LeArgs.HasType context (publicTelescopeFor witness positions)
      (publicWitnesses witness) (publicEvidenceFor witness positions) := by
  induction positions with
  | nil => exact .nil
  | cons index remaining induction =>
      exact .snoc
        (.snoc induction
          (lowerEvidence_typed witness guarded unfolds index))
        (upperEvidence_typed witness guarded unfolds index)

noncomputable def Encoding.evidence_typed {target : FCsub.Sig}
    {context : FCsub.Ctx target}
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := target) definitions) :
    FCsub.LeArgs.HasType context encoding.telescope encoding.witnesses
      encoding.evidence :=
  publicEvidenceFor_typed encoding.translation.witness
    encoding.order.positions encoding.guarded encoding.unfolds

/-- The erased unit payload inhabits the self projection by an explicit fold. -/
def Encoding.payload_typed {target : FCsub.Sig}
    {context : FCsub.Ctx target}
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := target) definitions) :
    FCsub.Tm.HasType context encoding.payload
      (FCsub.Ty.recProj encoding.block (selfIndex definitions.length)) := by
  apply FCsub.Tm.HasType.foldRec encoding.guarded
  simpa [Encoding.block] using (FCsub.Tm.HasType.unit (context := context))

/-- Guarded package formation for the recursive-object translation. -/
noncomputable def Encoding.object_typed {target : FCsub.Sig}
    {context : FCsub.Ctx target}
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := target) definitions) :
    FCsub.Tm.HasType context encoding.object encoding.objectType := by
  apply FCsub.Tm.HasType.pack encoding.evidence_typed
  simpa [Encoding.object, Encoding.payload, Encoding.objectType,
    Encoding.payloadType, Encoding.telescope, Encoding.witnesses]
    using encoding.payload_typed (context := context)

/-- Package evidence is recoverably ambient-only from the final typing
derivation; the recursive object cannot discharge its own interval bounds. -/
theorem Encoding.evidence_is_ambient {target : FCsub.Sig}
    {context : FCsub.Ctx target}
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := target) definitions) :
    Nonempty (FCsub.LeArgs.HasType context encoding.telescope
      encoding.witnesses encoding.evidence) :=
  FCsub.Tm.HasType.pack_arguments_outer encoding.object_typed

end DotToFCsub.RecursiveObjects
