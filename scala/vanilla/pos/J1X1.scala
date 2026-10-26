import scala.reflect.Selectable.reflectiveSelectable

// from: notes-scala-xv1/j/J1X1.scala, the judge's J programs as XV1 g1 wrote them
object J1X1 {
  val program = (x: Any) => (new Object {
    z =>
    type A = Any
    val a = x
  }: { val a: Any })
}
