import Coercions.ScalaSyntax.Read
import Coercions.ScalaSyntax.Lex
import Coercions.ScalaSyntax.Ast
import Coercions.ScalaSyntax.Parse
import Coercions.ScalaSyntax.Scope
import Coercions.ScalaSyntax.Print
import Coercions.ScalaSyntax.Tests

/-!
# The Scala reader

The root of the `ScalaSyntax` library, the reader that the Scala-syntax front
ends of plan IX share.  It reads the characters of a `.scala` file into a
syntax tree, and each front end translates that tree into its own surface
syntax.  The modules of `lean/Coercions/ScalaSyntax/`:

* `Lex` is the lexer, with the position of every token and of every refusal,
  and the column rule, which admits only layouts that scalac reads alike with
  and without `-no-indent`.  It imports Lean core only.
* `Ast` is the syntax tree, the union of the four subsets, with the position
  of every node that a check can refuse.
* `Parse` is the parser, a recursive descent on fuel from the tokens to the
  tree, with a position and a reason for every refusal.
* `Scope` is the checks on the tree, names and scopes as Scala reads them,
  cycles, literals under written types, and the label table.
* `Print` is the printer, from the tree back to the characters of a file in
  the layout of the column rule, so that reading the text gives the tree back.
* `Read` is the meta side: the package root, reading and listing files at
  elaboration, refusals reported at a command, the characters of a file as a
  definition for the kernel, and the commands `#assert_no_wf` and
  `#assert_axioms`.
* `Tests` is the string checks, by `#eval expect`.

Every definition of the library is structural, which the last line checks.
-/

#assert_no_wf ScalaSyntax
