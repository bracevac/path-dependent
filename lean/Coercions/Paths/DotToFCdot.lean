import Coercions.Paths.DotToFCdot.Types
import Coercions.Paths.DotToFCdot.TypesLemmas
import Coercions.Paths.DotToFCdot.Evidence
import Coercions.Paths.DotToFCdot.Terms
import Coercions.Paths.DotToFCdot.Blocks
import Coercions.Paths.DotToFCdot.EvidenceTyped
import Coercions.Paths.DotToFCdot.TermsTyped
import Coercions.Paths.DotToFCdot.Erasure
import Coercions.Paths.DotToFCdot.Safety
import Coercions.Paths.DotToFCdot.Consistency
import Coercions.Paths.DotToFCdot.Examples
import Coercions.Paths.DotToFCdot.Pages
import Coercions.Paths.DotToFCdot.Acceptance
/-!
Import root for the translation from DOT-MNF to FCdot (Plan III §8), at stage P3 of paths
(`plan-5g-paths-stages.md` §P3).  `Examples` holds Z1 to Z9 of P2.9.  `Pages` holds the
target side of the P3 pages and is imported after it.  `Acceptance` holds the two gDOT
acceptance tests and P1e, and is imported last.
-/
