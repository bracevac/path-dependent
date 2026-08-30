import FCsub.ClosedArtifact

/-!
# Closed-artifact checker regressions

These tests construct proof-free FCsub artifacts directly, without invoking a
source compiler.  They therefore test the independent boundary: intrinsic
scoping admits the data, while the executable FCsub checker still rejects a
wrong claimed type, a coercion with a tampered source endpoint, and unguarded
recursive equality evidence.
-/

namespace DotToFCsub.M7.ArtifactRegressions

open FCsub

/-! ## Positive closed artifact -/

/-- The smallest closed proof-free artifact. -/
def unitArtifact : ClosedArtifact :=
  { term := .unit
    type := .one }

theorem unit_artifact_is_accepted : unitArtifact.check = true := by
  native_decide

theorem unit_artifact_erases_to_unit :
    unitArtifact.erase = (Runtime.Tm.unit : Runtime.Tm []) := by
  native_decide

/-- Acceptance has the standalone declarative typing consequence supplied by
the closed-artifact soundness wrapper; no derivation was stored in the data. -/
theorem unit_artifact_has_type :
    Nonempty (Tm.HasType ClosedArtifact.emptyContext
      unitArtifact.term unitArtifact.type) :=
  ClosedArtifact.check_sound unit_artifact_is_accepted

/-! ## Claimed-type tampering -/

/-- Change only the claimed type.  Unit has type `one`; the checker does not
insert an implicit coercion to `top`. -/
def wrongClaimedType : ClosedArtifact :=
  unitArtifact.withType .top

theorem wrong_claimed_type_is_rejected :
    wrongClaimedType.check = false := by
  native_decide

/-! ## Explicit coercion endpoint tampering -/

/-- A valid explicit coercion from `one` to `top`. -/
def validTopCast : ClosedArtifact :=
  { term := .cast .unit (.top .one)
    type := .top }

theorem valid_top_cast_is_accepted : validTopCast.check = true := by
  native_decide

/-- Preserve intrinsic scope and the target endpoint, but change the explicit
coercion's source endpoint from `one` to `bot`.  The certificate remains valid
as a `bot <= top` certificate in isolation, yet it cannot consume the unit
term and the whole artifact must be rejected. -/
def endpointTamperedCast : ClosedArtifact :=
  validTopCast.mapTerm fun _ => .cast .unit (.top .bot)

theorem endpoint_tampered_cast_is_rejected :
    endpointTamperedCast.check = false := by
  native_decide

theorem tampered_evidence_still_has_advertised_endpoints :
    checkEvidence Ctx.nil (.top (.bot : Ty [])) .bot .top = true := by
  native_decide

/-! ## Unguarded recursive equality evidence -/

/-- A one-name block whose body is an unguarded reference to its own name. -/
def unguardedBodies : RecBodies [] 1 1 :=
  .snoc .nil (.tvar .here)

def onlyRecursiveIndex : Fin 1 := ⟨0, by decide⟩

theorem unguarded_block_fails_guard :
    unguardedBodies.headGuarded = false := by
  native_decide

/-- The syntax is closed and arity-correct, but the equality checker rejects
the unguarded unfold certificate. -/
theorem unguarded_unfold_equality_is_rejected :
    checkEquality Ctx.nil
      (.unfoldRec unguardedBodies onlyRecursiveIndex)
      (.recProj unguardedBodies onlyRecursiveIndex)
      (unguardedBodies.unfoldAt onlyRecursiveIndex) = false := by
  native_decide

end DotToFCsub.M7.ArtifactRegressions
