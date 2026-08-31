import Coercions.DOT.Captures.BinderOnly
import Coercions.DOT.Captures.Acyclic
import Coercions.DOT.Captures.Acyclic.GeneralExpression

/-!
Standalone import root for DOT with captures.  It exposes both the
binder-only interval foundation and the first acyclic object layer with
genuine type members `x.A`, capture members `x.C`, and the value member
`x.v : (x.A)^{x.C}`.  Intersections and recursive self types extend this
source family rather than introducing a separate calculus.

This root intentionally has no dependency on either FC target.
-/
