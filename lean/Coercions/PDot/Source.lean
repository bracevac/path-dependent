import Coercions.PDot.Source.Syntax
import Coercions.PDot.Source.Binding
import Coercions.PDot.Source.Repl
import Coercions.PDot.Source.Typing
import Coercions.PDot.Source.Derived
import Coercions.PDot.Source.Lookup
import Coercions.PDot.Source.Reduction
import Coercions.PDot.Source.Model
import Coercions.PDot.Source.Examples
import Coercions.PDot.Source.Programs
import Coercions.PDot.Source.Erasure

/-!
Import root for the source of PDot: pDOT transcribed from `Definitions.v`, `Lookup.v` and
`Reduction.v` of its Coq formalization.  `Model` and `Examples` add path models of a fixed context
and the small and negative examples.  `Programs` types the programs E1 to E8, three of them the
example lemmas of the Coq files.
-/
