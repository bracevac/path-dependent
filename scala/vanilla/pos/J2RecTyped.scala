import scala.reflect.Selectable.reflectiveSelectable

// from: notes-scala-xv1/j/J2RecTyped.scala, the judge's J programs as XV1 g1 wrote them
object J2RecTyped {
  val program: { val a: Any } = new Object {
    z =>
    val a: Any = z.a
  }
}
