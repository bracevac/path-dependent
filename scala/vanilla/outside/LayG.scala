import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-10 (XV0), a comment before the first token of a line
// from: notes-scala-xv0/scalac-g1/LayG.scala, XV0 g1.  G: a comment before the first token of a line.  The token sits at the block's column.
object LayG {
  val program = (w: Any) => {
      val r = w
 /*x*/r // warn
  }
}
