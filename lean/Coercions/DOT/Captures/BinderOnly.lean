import Coercions.DOT.Captures.BinderOnly.Scope
import Coercions.DOT.Captures.BinderOnly.Syntax
import Coercions.DOT.Captures.BinderOnly.Context
import Coercions.DOT.Captures.BinderOnly.StaticJudgments
import Coercions.DOT.Captures.BinderOnly.Term
import Coercions.DOT.Captures.BinderOnly.Substitution
import Coercions.DOT.Captures.BinderOnly.IntervalModel
import Coercions.DOT.Captures.BinderOnly.IntervalEntailment
import Coercions.DOT.Captures.BinderOnly.Subtyping
import Coercions.DOT.Captures.BinderOnly.Typing

/-!
The standalone binder-only source foundation for DOT with type and capture
intervals, proof-relevant static judgments, and ANF typing.  This import root
intentionally has no dependency on ManySortedFC.
-/
