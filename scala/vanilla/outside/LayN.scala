import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-10 (XV0), `;` on a continuation line
// from: notes-scala-xv0/scalac-g1/LayN.scala, XV0 g1.  N: a semicolon on a continuation line after '='.
object LayN {
  val program = (w: Any) => {
    val a =
      w; val b = w // warn
    a
  }
}
