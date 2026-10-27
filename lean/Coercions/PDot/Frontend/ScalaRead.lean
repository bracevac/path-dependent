import Coercions.ScalaSyntax.Read
import Coercions.PDot.Frontend.ScalaRead.Ast
import Coercions.PDot.Frontend.ScalaRead.Parse
import Coercions.PDot.Frontend.ScalaRead.Scope
import Coercions.PDot.Frontend.ScalaRead.Print
import Coercions.PDot.Frontend.ScalaRead.Tests

/-!
# The pDOT Scala reader

The root of the `PDotScalaRead` library, the reader of the pDOT Scala subset
of plan XI (stage XS1a).  It reads the characters of a `.scala` file into a
tree of its own, on the lexer and the column rule of the vanilla reader
`ScalaSyntax`, imported unchanged.  The modules of
`lean/Coercions/PDot/Frontend/ScalaRead/`:

* `Ast` is the syntax tree of the subset, with the position of every node that
  a check can refuse, paths of any length, and positions erased.
* `Parse` is the parser: the shared lexer, the self-name pass, the column
  rule, and a recursive descent on fuel from the tokens to the tree, with a
  position and a reason for every refusal.
* `Scope` is the context of a name, the kind table of paths, the shortest
  unstable prefix, the module chains of a file, the refusals of the walk with
  their entry point `check`, and the label table `labels`.
* `Print` is the printer: `print` writes a tree as the text of a `.scala`
  file, which reads back to the same tree up to positions.
* `Tests` is the string checks, by `#eval expect`.

Every definition of the library is structural, which the last line checks.
-/

#assert_no_wf PDotFrontend.ScalaRead
