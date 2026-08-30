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
import Coercions.Translation.ManySorted.BinderOnly.AdapterElaboration
import Coercions.Translation.ManySorted.BinderOnly.TermElaboration
import Coercions.Translation.ManySorted.BinderOnly.SourceErasure

/-!
# Shared bridge infrastructure for translations into many-sorted FC

This local root collects source-independent translation infrastructure.  It
is separate from the target library: binder-only source syntax and future DOT
path/member layouts both reuse the sort-indexed static-slot abstraction.
-/
