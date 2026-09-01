import Coercions.DOT.Captures.BinderOnly
import Coercions.DOT.Captures.Acyclic
import Coercions.DOT.Captures.Acyclic.GeneralExpression
import Coercions.DOT.Captures.Intersections
import Coercions.DOT.Captures.ModalIntersections

/-!
Standalone import root for DOT with captures. It exposes the binder-only
interval foundation, the acyclic object layer, and the cumulative
captured-intersection source extension, together with its heterogeneous
access-only modal syntax and judgments. Objects have genuine type members
`x.A`, capture members `x.C`, and one runtime payload. Modal locks may assume
separation and access modes, but cannot create disjointness or freshness.

This root intentionally has no dependency on either FC target.
-/
