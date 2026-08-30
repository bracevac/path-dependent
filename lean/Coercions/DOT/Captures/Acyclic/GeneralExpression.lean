import Coercions.DOT.Captures.Acyclic.GeneralExpression.Syntax
import Coercions.DOT.Captures.Acyclic.GeneralExpression.Structural
import Coercions.DOT.Captures.Acyclic.GeneralExpression.Typing
import Coercions.DOT.Captures.Acyclic.GeneralExpression.Embedding

/-!
Standalone source root for general-expression acyclic captured DOT.

The layer retains stable-path selection and value-only object construction,
while admitting computations in both application positions and at
object-opening let boundaries.  The source-owned embedding module relates the
older value-MNF core to this surface at syntax and typing.  Operational
erasure and executable examples remain separate imports so this source root
has no dependency on either an FC target or a translation.

This remains the acyclic fixed-member case-study language: paths are
variables, objects have the fixed `{A, C, v}` signature and value payloads,
lambda parameters are plain, and an object-opening let requires the exact
formed-object type.  Recursive objects, intersections, arbitrary members, and
full DOT are outside this surface.
-/
