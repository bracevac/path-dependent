import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, a val whose right side names a later val (rule 9)
// from: notes-scala-xv0/scalac-g3/V18.scala, d2 V18
object V18 {
  val program =
    (c: Any) => {
      val a: Any = b // error
      val b: Any = c
      a
    }
}
