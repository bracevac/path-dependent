import Coercions.DOT.Captures.Acyclic.Scope
import Coercions.DOT.Captures.Acyclic.Syntax
import Coercions.DOT.Captures.Acyclic.Context
import Coercions.DOT.Captures.Acyclic.MemberTyping
import Coercions.DOT.Captures.Acyclic.ObjectTyping
import Coercions.DOT.Captures.Acyclic.Structural
import Coercions.DOT.Captures.Acyclic.Examples
import Coercions.DOT.Captures.Acyclic.ComputationalExamples

/-!
Standalone source root for the first actual acyclic DOT layer with captures.

It contains genuine path-dependent type and capture selections (`x.A` and
`x.C`) and the fixed value member `x.v : (x.A)^{x.C}`.  This root has no
dependency on either coercion target or on a translation.
-/
