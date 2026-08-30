import Coercions.FCsub.CheckerCompleteness
import Coercions.FCsub.Erasure
import Coercions.FCsub.Simulation

/-!
# Proof-free closed FCsub artifacts

`ClosedArtifact` is the serialization boundary for generated FCsub code.  It
contains only intrinsically closed syntax: no typing derivation, source term,
or compiler proof is retained.  The standalone FCsub checker is therefore the
independent consumer of an artifact.

The small update API is intentional.  Regression tests can replace either
component (or transform both components) and rerun the same executable check;
there is no proof field that must be rebuilt after tampering.
-/

namespace FCsub

/-- A closed annotated term paired with its claimed closed type.

Both fields are data.  In particular, constructing this record makes no claim
that the term checks at the recorded type. -/
structure ClosedArtifact where
  term : Tm []
  type : Ty []
deriving DecidableEq

namespace ClosedArtifact

/-- The empty standalone FCsub context used to validate closed artifacts. -/
def emptyContext : Ctx [] := .nil

/-- Infer the type of the recorded term without trusting the recorded type. -/
def synth (artifact : ClosedArtifact) : Option (Ty []) :=
  synthTm emptyContext artifact.term

/-- Independently validate the recorded term against the recorded type. -/
def check (artifact : ClosedArtifact) : Bool :=
  checkTerm emptyContext artifact.term artifact.type

/-- Erase all FCsub annotations and certificates from the recorded term. -/
def erase (artifact : ClosedArtifact) : Runtime.Tm [] :=
  artifact.term.erase

/-- Replace the annotated term while retaining the claimed type. -/
def withTerm (artifact : ClosedArtifact) (term : Tm []) : ClosedArtifact :=
  { artifact with term := term }

/-- Replace the claimed type while retaining the annotated term. -/
def withType (artifact : ClosedArtifact) (type : Ty []) : ClosedArtifact :=
  { artifact with type := type }

/-- Transform only the annotated term.  Useful for certificate tampering. -/
def mapTerm (artifact : ClosedArtifact) (transform : Tm [] -> Tm []) :
    ClosedArtifact :=
  artifact.withTerm (transform artifact.term)

/-- Transform only the claimed type. -/
def mapType (artifact : ClosedArtifact) (transform : Ty [] -> Ty []) :
    ClosedArtifact :=
  artifact.withType (transform artifact.type)

/-- Transform both proof-free components at once. -/
def bimap (artifact : ClosedArtifact) (termTransform : Tm [] -> Tm [])
    (typeTransform : Ty [] -> Ty []) : ClosedArtifact :=
  { term := termTransform artifact.term
    type := typeTransform artifact.type }

@[simp]
theorem synth_eq (artifact : ClosedArtifact) :
    artifact.synth = synthTm emptyContext artifact.term := rfl

@[simp]
theorem check_eq (artifact : ClosedArtifact) :
    artifact.check = checkTerm emptyContext artifact.term artifact.type := rfl

@[simp]
theorem erase_eq (artifact : ClosedArtifact) :
    artifact.erase = artifact.term.erase := rfl

/-- Checker acceptance produces a declarative typing derivation, without one
being stored in the artifact. -/
theorem check_sound {artifact : ClosedArtifact}
    (accepted : artifact.check = true) :
    Nonempty (Tm.HasType emptyContext artifact.term artifact.type) :=
  checkTerm_sound accepted

/-- Every declaratively well-typed closed pair is accepted by the executable
checker. -/
theorem check_complete {artifact : ClosedArtifact}
    (typing : Tm.HasType emptyContext artifact.term artifact.type) :
    artifact.check = true :=
  checkTerm_iff.mpr ⟨typing⟩

/-- The closed artifact checker is exact with respect to declarative typing. -/
theorem check_iff {artifact : ClosedArtifact} :
    artifact.check = true <->
      Nonempty (Tm.HasType emptyContext artifact.term artifact.type) :=
  checkTerm_iff

/-- A one-step annotated computation of the artifact is simulated after
erasure.  This wrapper keeps clients on the closed-artifact boundary. -/
theorem erase_simulates_step {artifact : ClosedArtifact} {next : Tm []}
    (step : Tm.Step artifact.term next) :
    Runtime.Steps artifact.erase next.erase :=
  step.erase_simulates

end ClosedArtifact

end FCsub
