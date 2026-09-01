import Coercions.Translation.ManySorted.Classifiers.Source
import Coercions.Translation.ManySorted.Classifiers.SourceErasure
import Coercions.Translation.ManySorted.Classifiers.Lowering
import Coercions.Translation.ManySorted.Classifiers.Examples

/-!
# Closed classifier projection case study

The source-facing `.only`/`.except` layer lowers a whole chain to one ground
classifier kind and one target `Capture.project`.  A representative target
term is checked independently; the paired source and target programs have
literally equal erasures and execute through ordinary shared-runtime beta and
zeta steps.  This layer does not define a general term compiler, classifier
inference, kind-bounded variables, handlers or intercepts, or full Capless(K)
typing.
-/
