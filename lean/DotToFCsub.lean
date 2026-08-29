import DOT
import FCsub
import DotToFCsub.MemberEncoding
import DotToFCsub.Layout
import DotToFCsub.SourceContext
import DotToFCsub.Elaboration
import DotToFCsub.ElaborationErasure
import DotToFCsub.BridgeMetatheory
import DotToFCsub.LayoutMetatheory
import DotToFCsub.StableFragment
import DotToFCsub.StableTranslation
import DotToFCsub.StableContextMetatheory
import DotToFCsub.StableOpening
import DotToFCsub.OperationalCorrespondence
import DotToFCsub.StableSubTotality
import DotToFCsub.StableTermTotality
import DotToFCsub.StableOperationalCorrespondence
import DotToFCsub.Examples
import DotToFCsub.StableExamples
import DotToFCsub.StableTotalityExamples
import DotToFCsub.M4
import DotToFCsub.M5

/-!
Integration root for the DOT-to-FCsub bridge.  Bridge modules are imported
here only after the standalone FCsub kernel and its metatheory compile alone.
-/
