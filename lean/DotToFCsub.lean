import DOT
import FCsub
import DotToFCsub.MemberEncoding
import DotToFCsub.Layout
import DotToFCsub.SourceContext
import DotToFCsub.Elaboration
import DotToFCsub.ElaborationErasure
import DotToFCsub.BridgeMetatheory
import DotToFCsub.Examples

/-!
Integration root for the DOT-to-FCsub bridge.  Bridge modules are imported
here only after the standalone FCsub kernel and its metatheory compile alone.
-/
