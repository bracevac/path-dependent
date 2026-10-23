import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, a name bound nowhere (rule 1)
// from: notes-scala-xv0/scalac-g3/NotFound.scala, XV0 g3
object NotFound {
  val program =
    (x: Any) =>
      y // error
}
