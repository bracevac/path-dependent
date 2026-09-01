import Coercions.Translation.ManySorted.RecursiveObjects.Source
import Coercions.Translation.ManySorted.RecursiveObjects.SourceExamples
import Coercions.Translation.ManySorted.RecursiveObjects.SourceErasure
import Coercions.Translation.ManySorted.RecursiveObjects.Encoding
import Coercions.Translation.ManySorted.RecursiveObjects.EncodingExamples
import Coercions.Translation.ManySorted.RecursiveObjects.Model
import Coercions.Translation.ManySorted.RecursiveObjects.ModelExamples
import Coercions.Translation.ManySorted.RecursiveObjects.Inertness
import Coercions.Translation.ManySorted.RecursiveObjects.InertnessExamples

/-!
# Type-recursive cumulative captured objects

Stage 6A adds simultaneous guarded recursion for exact type members while
capture members, the unique representation-capture name, and the unit runtime
payload remain acyclic.  Recursive packages reuse the cumulative
`ObjectContract`; their model and term syntax cross the standalone target
checkers and erase exactly to the independently defined source runtime term.
-/
