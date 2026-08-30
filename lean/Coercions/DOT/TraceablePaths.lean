import Coercions.DOT.TraceablePaths.Source.Syntax
import Coercions.DOT.TraceablePaths.Source.Trace
import Coercions.DOT.TraceablePaths.Source.Typing
import Coercions.DOT.TraceablePaths.Source.Runtime
import Coercions.DOT.TraceablePaths.Source.Examples

/-!
The standalone traceable-path DOT source root.  `DotFCRP` extends recursive
type-member DOT with certified finite transparent aliases, nested stable
paths, path-dependent selections, and singleton identities.  Opaque/dynamic
receiver resolution is deliberately outside this lean slice.
-/
