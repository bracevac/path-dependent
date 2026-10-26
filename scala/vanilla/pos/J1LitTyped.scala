import scala.reflect.Selectable.reflectiveSelectable

// from: notes-scala-xv1/j/J1LitTyped.scala, the judge's J programs as XV1 g1 wrote them
object J1LitTyped {
  val program = (n: { val b: Any }) => (new Object {
    z =>
    val a: { val b: Any } = n
  }: { val a: { val b: Any } })
}
