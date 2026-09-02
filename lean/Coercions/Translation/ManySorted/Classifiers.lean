import Coercions.Translation.ManySorted.Classifiers.Source
import Coercions.Translation.ManySorted.Classifiers.SourceErasure
import Coercions.Translation.ManySorted.Classifiers.Lowering
import Coercions.Translation.ManySorted.Classifiers.CaptureBounds
import Coercions.Translation.ManySorted.Classifiers.Examples
import Coercions.Translation.ManySorted.Classifiers.CaptureKindingExamples

/-!
# Ground classifier projection and kind-bounded captures

The source-facing `.only`/`.except` layer lowers a whole chain to one ground
classifier kind and one target `Capture.project`. A source binder `c : K`
lowers to an ordinary target capture symbol plus `captureHasKind(c, K)`
evidence; no classifier or kind symbol is allocated. A checked callback
example uses projection completeness to justify a nonempty filtered closure,
has literal source/target erasure equality, and performs real beta steps.

This layer does not define the full Capless(K) source calculus, classifier
inference, handler/intercept semantics, labels, or the paper's safety proof.
-/
