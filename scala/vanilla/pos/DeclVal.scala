import scala.reflect.Selectable.reflectiveSelectable

// from: notes-scala-xv1/j/DeclVal.scala, the judge's J programs as XV1 g1 wrote them
object DeclVal {
  val program = (x: { type A }) => {
    val y = x
    (z: y.A) => z
  }
}
