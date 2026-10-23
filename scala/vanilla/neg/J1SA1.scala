import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-scala-xv1/j/J1SA1.scala, the judge's J programs as XV1 g1 wrote them
object J1SA1 {
  val program = (x: Any) => (new Object {
    z =>
    val a = y => y // error
  }: { val a: Any => Any })
}
