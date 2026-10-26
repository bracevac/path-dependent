import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-10 rule 2, a leading `.` on a more indented line
// from: notes-scala-xv0/LayF.scala, the judge's LayF.  F: a leading '.' on a more indented line.
object LayF {
  val program = (x: { val a: { val b: Any } }) => {
    val r = x
      .a
    r
  }
}
