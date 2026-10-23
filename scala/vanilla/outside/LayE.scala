import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-10 rule 2, a more indented name after a statement
// from: notes-scala-xv0/LayE.scala, the judge's LayE.  E: a more indented identifier after a line that can end a statement.
object LayE {
  val program = (f: Any) => (w: Any) => {
    val r = f
      w // warn
    r
  }
}
