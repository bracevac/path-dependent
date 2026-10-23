import scala.reflect.Selectable.reflectiveSelectable

// from: notes-scala-xv1/j/J1ValLast.scala, the judge's J programs as XV1 g1 wrote them
object J1ValLast {
  val program = (x: { val a: Any }) => {
    val y: { val a: Any } = x
    y
  }
}
