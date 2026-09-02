import Coercions.Translation.ManySorted.Classifiers.Lowering
import Coercions.ManySortedFC.Evidence

/-!
# Kind-bounded capture variables

The classifiers paper quantifies over capture sets with a closed classifier
kind bound.  It does not quantify over classifiers or kinds.  This file gives
that source binder its small target interface: one ordinary capture symbol and
one `captureHasKind` assumption about that symbol.

For a source binder `c : K`, lowering produces the local theory

```text
c : Capture
kind_c : captureHasKind(c, K)
```

The classifier kind `K` remains ground data throughout.
-/

namespace DOTCaptureToManySortedFC.Classifiers.CaptureBounds

namespace Source

abbrev Kind := ManySortedFC.Classifier.Kind

/-- A source capture-set binder with a closed classifier-kind bound. -/
structure Binder where
  bound : Kind
deriving DecidableEq

end Source

open ManySortedFC

/-- Lower `c : K` to one capture symbol plus its checked ground-kind
assumption.  No classifier or kind symbol is allocated. -/
def lower {scope : Sig} (binder : Source.Binder) :
    Theory scope [.capture] [.captureHasKind] :=
  .cons (.captureHasKind (.cvar .here) binder.bound) .nil

/-- The capture symbol exposed after opening a lowered kind-bounded binder. -/
def openedCapture {scope : Sig} :
    Capture (StaticScope scope [.capture] [.captureHasKind]) :=
  .cvar (.there .here)

/-- The exact kinding assumption exposed after opening the binder. -/
def openedKindEvidence {scope : Sig} :
    Evidence .captureHasKind
      (StaticScope scope [.capture] [.captureHasKind]) :=
  .var .here

def opened_kind_evidence_has_exact_endpoint {scope : Sig}
    (context : Ctx scope) (binder : Source.Binder) :
    Evidence.Proves (context.extendTheory (lower binder))
      (openedKindEvidence (scope := scope))
      (.captureHasKind (openedCapture (scope := scope)) binder.bound) := by
  exact .var rfl

end DOTCaptureToManySortedFC.Classifiers.CaptureBounds
