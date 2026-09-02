import Coercions.Translation.ManySorted.StaticSlot
import Coercions.Translation.ManySorted.BinderOnly.Layout
import Coercions.Translation.ManySorted.BinderOnly.LayoutExamples
import Coercions.Translation.ManySorted.BinderOnly.EvidenceElaboration
import Coercions.Translation.ManySorted.BinderOnly.LayoutMetatheory
import Coercions.Translation.ManySorted.BinderOnly.ContextEvidence
import Coercions.Translation.ManySorted.BinderOnly.EvidenceExamples
import Coercions.Translation.ManySorted.BinderOnly.ModelElaboration
import Coercions.Translation.ManySorted.BinderOnly.StaticSubstitutionMetatheory
import Coercions.Translation.ManySorted.BinderOnly.ModelExamples
import Coercions.Translation.ManySorted.BinderOnly.IntervalMorphismElaboration
import Coercions.Translation.ManySorted.BinderOnly.AdapterElaboration
import Coercions.Translation.ManySorted.BinderOnly.QuantifiedCoercionExamples
import Coercions.Translation.ManySorted.BinderOnly.TermElaboration
import Coercions.Translation.ManySorted.BinderOnly.DecisiveExamples
import Coercions.Translation.ManySorted.BinderOnly.SourceErasure
import Coercions.Translation.ManySorted.BinderOnly.TermElaborationErasure
import Coercions.DOT.Captures.ModalIntersections.BinderEmbeddingErasure
import Coercions.Translation.ManySorted.Acyclic
import Coercions.Translation.ManySorted.Intersections
import Coercions.Translation.ManySorted.ModalIntersections
import Coercions.Translation.ManySorted.RecursiveObjects
import Coercions.Translation.ManySorted.Classifiers
import Coercions.Translation.ManySorted.CheckedFrontend
import Coercions.Translation.ManySorted.CertificateStudy

/-!
# Shared bridge infrastructure for translations into many-sorted FC

This root collects the binder-only bridge, the acyclic compiler case study,
the cumulative captured-intersection compiler, and a separate guarded
recursive type-member object-literal case study. It remains separate from the
independently buildable target library.
The classifier case study adds ground `.only`/`.except` capture filters and
kind-bounded capture symbols. Its checked target callback uses a nonempty
projected closure; classifiers and kinds themselves are not target symbols.

The Stage 8 front end checks an intrinsically scoped annotated source fragment
from first-order certificates before invoking the cumulative compiler.  Its
successful result contains both the source typing derivation and independent
target-checker acceptance.  The certificate study records reproducible
checker, certificate, normalization, adapter, and runtime measurements and a
same-root read-only benchmark that executes both callbacks sequentially.
-/
