import DotToFCsub.M6.AliasScope
import DotToFCsub.M6.AliasScopeExamples
import DotToFCsub.M6.PathLayout
import DotToFCsub.M6.PathEquality
import DotToFCsub.M6.Translation
import DotToFCsub.M6.Realizability
import DotToFCsub.M6.OperationalCorrespondence
import DotToFCsub.M6.Examples

/-!
Milestone 6: finite transparent paths and singleton views compile to
syntactically distinct FCsub names connected by explicit, erasable equality
coercions.  The supported boundary requires proof-relevant path traces;
opaque and dynamically computed receivers remain outside this slice.
-/
