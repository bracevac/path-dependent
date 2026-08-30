import Coercions.DOT.Captures.BinderOnly

/-!
Standalone import root for DOT with captures.  The current formalized layer is
the variable-path, binder-only restriction; type members `x.A`, capture
members `x.C`, intersections, and recursive self types extend this source
family rather than introducing a separate calculus.

This root intentionally has no dependency on either FC target.
-/
