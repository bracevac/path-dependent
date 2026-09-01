import Coercions.Translation.ManySorted.BindableClassifiers.CompilerExamples

/-!
# Bindable classifier kinds

The cumulative captured-object compiler binds classifier names in object
theories alongside type and capture names. Before cumulative compilation,
the classifier preprocessor uses `Classifiers.Lowering.lowerWith` to collapse
each ground `only`/`except` chain to one scoped capture projection. Abstract
classifier names remain valid projection operands, but are rejected as
`only`/`except` operands because the ground algebra has no symbolic
subtraction. The resulting mixed theory and capture syntax compile to an
independently checked ManySortedFC artifact. The end-to-end example opens one
object, projects a cross-shape theory view, passes one callback payload, and
executes it after erasure.
-/
