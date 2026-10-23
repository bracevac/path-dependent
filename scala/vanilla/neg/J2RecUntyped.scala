import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-scala-xv1/j/J2RecUntyped.scala, the judge's J programs as XV1 g1 wrote them
object J2RecUntyped {
  val program: { val a: Any } = new Object {
    z =>
    val a = z.a // error
  }
}
