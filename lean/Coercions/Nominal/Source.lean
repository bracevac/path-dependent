import Coercions.Nominal.Source.Syntax
import Coercions.Nominal.Source.Binding
import Coercions.Nominal.Source.Repl
import Coercions.Nominal.Source.Typing
import Coercions.Nominal.Source.Derived
import Coercions.Nominal.Source.Lookup
import Coercions.Nominal.Source.Reduction
import Coercions.Nominal.Source.Model
import Coercions.Nominal.Source.Examples
import Coercions.Nominal.Source.Programs
import Coercions.Nominal.Source.Erasure

/-!
Import root for the source of PDot: pDOT transcribed from `Definitions.v`, `Lookup.v` and
`Reduction.v` of its Coq formalization.  `Model` and `Examples` add path models of a fixed context
and the small and negative examples.  `Programs` types the programs E1 to E8, three of them the
example lemmas of the Coq files.
-/
