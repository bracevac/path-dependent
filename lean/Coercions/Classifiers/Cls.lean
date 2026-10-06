import Coercions.Classifiers.Cls.Core
import Coercions.Classifiers.Cls.Kind
import Coercions.Classifiers.Cls.Ops

/-!
The classifier data: the classifier tree with its decidable subclass order,
kinds as lists of holed subtrees with membership, emptiness, intersection and
union, and the derived operations subtraction, subkinding and kind
disjointness, together with the example classifiers.  These files import
nothing else from the development, so they sit below everything else, and
`FCdot/Syntax.lean` and `DotMNF/Syntax.lean` import them.
-/
