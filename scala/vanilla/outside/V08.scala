import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, a val whose right side names it (rule 9)
// from: notes-scala-xv0/scalac-g3/V08.scala, d2 V08
object V08 {
  val program =
    (x: { val a: Any }) => {
      val x = x.a // error
      x
    }
}
