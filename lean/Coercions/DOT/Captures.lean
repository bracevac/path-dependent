import Coercions.DOT.Captures.BinderOnly
import Coercions.DOT.Captures.Acyclic
import Coercions.DOT.Captures.Acyclic.GeneralExpression
import Coercions.DOT.Captures.Intersections

/-!
Standalone import root for DOT with captures. It exposes the binder-only
interval foundation, the acyclic object layer, and the cumulative
captured-intersection source extension. Objects have genuine type members
`x.A`, capture members `x.C`, and one runtime payload.

This root intentionally has no dependency on either FC target.
-/
