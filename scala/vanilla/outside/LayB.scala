import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-10 rule 2, a continuation line after a line that can end a statement
// from: notes-scala-xv1/corpus/outside/LayB.scala, the judge's LayB.  B: a more indented line that starts with '(' after a line that can end a statement.
object LayB {
  val program = (f: Any => { val a: Any }) => (w: Any) => {
    val r = f
      (w)
    r
  }
}
