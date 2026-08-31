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
import Coercions.Translation.ManySorted.BinderOnly.SourceErasure
import Coercions.Translation.ManySorted.BinderOnly.TermElaborationErasure
import Coercions.Translation.ManySorted.Acyclic
import Coercions.Translation.ManySorted.Intersections

/-!
# Shared bridge infrastructure for translations into many-sorted FC

This root collects the binder-only bridge, the acyclic compiler case study,
and the cumulative captured-intersection compiler. It remains separate from
the independently buildable target library.
-/
