import scala.reflect.Selectable.reflectiveSelectable

// from: notes-scala-xv1/j/J1ValSel.scala, the judge's J programs as XV1 g1 wrote them
object J1ValSel {
  val program = (x: { val a: Any }) => {
    val y: { val a: Any } = x
    y.a
  }
}
