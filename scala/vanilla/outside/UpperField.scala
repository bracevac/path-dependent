import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-13, a field that starts upper case (rule 7)
// from: notes-scala-xv0/scalac-g3/UpperField.scala, XV0 g3
object UpperField {
  val program =
    (x: { val A: Any }) =>
      x
}
