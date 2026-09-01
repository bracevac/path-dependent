import Coercions.Translation.ManySorted.ModalIntersections.Layout
import Coercions.Translation.ManySorted.ModalIntersections.Preparation
import Coercions.Translation.ManySorted.ModalIntersections.PreparationExamples
import Coercions.Translation.ManySorted.ModalIntersections.ModalProvenance
import Coercions.Translation.ManySorted.ModalIntersections.ModalProvenanceExamples
import Coercions.Translation.ManySorted.ModalIntersections.CompilerContext
import Coercions.Translation.ManySorted.ModalIntersections.CompilerContextExamples

/-!
# Cumulative captured-DOT compiler foundation

This layer fixes the combined source-to-target layout, prepares lexical and
object theories names first, tracks proof-relevant modal coordinates, and
records independently checked target contexts.  The recursive term compiler
is built on these exact artifacts.
-/
