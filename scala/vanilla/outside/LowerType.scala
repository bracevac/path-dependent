import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-13, a type member that starts lower case (rule 7)
// from: notes-scala-xv0/scalac-g3/LowerType.scala, XV0 g3
object LowerType {
  val program =
    (x: { type a }) =>
      x
}
