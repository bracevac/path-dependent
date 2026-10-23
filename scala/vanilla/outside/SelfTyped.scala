import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, a typed val whose right side names it (rule 9)
// from: notes-scala-xv0/scalac-g3/SelfTyped.scala, XV0 g3
object SelfTyped {
  val program =
    (x: Any) => {
      val y: Any = y // error
      x
    }
}
