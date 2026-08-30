import Coercions.Translation.PathAliases.AliasScope
import Coercions.Translation.PathAliases.AliasScopeRegressions
import Coercions.Translation.PathAliases.PathLayout
import Coercions.Translation.PathAliases.CoResolvedEquality
import Coercions.Translation.PathAliases.Translation
import Coercions.Translation.PathAliases.Realizability
import Coercions.Translation.PathAliases.OperationalCorrespondence
import Coercions.Translation.PathAliases.Examples

/-!
Finite transparent paths and singleton views compile to
syntactically distinct FCsub names connected by explicit, erasable equality
coercions.  The supported boundary requires proof-relevant path traces;
opaque and dynamically computed receivers remain outside this slice.
-/
