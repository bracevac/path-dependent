import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-10 rule 1, a statement left of the block's column
// from: notes-scala-xv0/LayD.scala, the judge's LayD.  D: a statement less indented than the block's first statement.
object LayD {
  val program = (w: Any) => {
      val r = w
    r // warn
  }
}
