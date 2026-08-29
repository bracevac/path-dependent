import DotFCR.Source.Syntax
import DotFCR.Source.Typing
import DotFCR.Source.Runtime
import DotFCR.Legacy

/-!
The standalone recursive DOT source root.  It is a conservative extension of
`DotFCI`: recursive objects contain only static type definitions, share one
guarded self binder, and erase to unit.
-/
