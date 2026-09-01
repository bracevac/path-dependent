import Coercions.ManySortedFC.Classifier.Core
import Coercions.ManySortedFC.Classifier.Kind
import Coercions.ManySortedFC.Classifier.Intersection
import Coercions.ManySortedFC.Classifier.Subtract
import Coercions.ManySortedFC.Classifier.Semantics
import Coercions.ManySortedFC.Classifier.Subkind
import Coercions.ManySortedFC.Classifier.Disjoint
import Coercions.ManySortedFC.Classifier.Basic

/-!
# Closed classifier-kind algebra

An isolated, executable algebra of concrete classifier paths and ground
`only`/`except` kinds.  The development proves exact membership semantics for
intersection and subtraction, executable subkinding and disjointness, and the
small extensional law package needed by classifier projection.
-/
