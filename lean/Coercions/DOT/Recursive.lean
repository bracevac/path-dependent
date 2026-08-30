import Coercions.DOT.Recursive.Source.Syntax
import Coercions.DOT.Recursive.Source.Typing
import Coercions.DOT.Recursive.Source.Runtime
import Coercions.DOT.Recursive.Legacy

/-!
The standalone recursive DOT source root.  It is a conservative extension of
`DotFCI`: recursive objects contain only static type definitions, share one
guarded self binder, and erase to unit.
-/
