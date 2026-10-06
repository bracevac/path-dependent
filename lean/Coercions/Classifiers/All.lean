import Coercions.Classifiers.Cls
import Coercions.Classifiers.DotMNF
import Coercions.Classifiers.FCdot
import Coercions.Classifiers.DotToFCdot
import Coercions.Classifiers.Runtime

/-!
Capability classifiers for DOT.  This copies the base translation
(`Coercions.DotMNF`, `Coercions.FCdot`, `Coercions.DotToFCdot`,
`Coercions.Runtime`) at the commit recorded in `BASE`, and extends it with a
sort of classifiers that track which capabilities a term may use.
-/
