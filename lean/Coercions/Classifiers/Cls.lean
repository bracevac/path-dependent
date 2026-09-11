import Coercions.Classifiers.Cls.Core
import Coercions.Classifiers.Cls.Kind
import Coercions.Classifiers.Cls.Ops

/-!
The classifier data of plan V-C stage K0.1: the classifier tree with its
decidable subclass order, kinds as lists of holed subtrees with membership,
emptiness, intersection and union, and the derived operations subtraction,
subkinding and kind disjointness with the example classifiers.  The files
import nothing of the tree, so they sit below the whole development, and
`FCdot/Syntax.lean` and `DotMNF/Syntax.lean` import them.
-/
