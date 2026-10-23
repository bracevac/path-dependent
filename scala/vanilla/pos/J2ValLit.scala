import scala.reflect.Selectable.reflectiveSelectable

// from: notes-scala-xv1/j/J2ValLit.scala, the judge's J programs as XV1 g1 wrote them
object J2ValLit {
  val program = (n: { val b: Any }) => {
    val o: { val a: { val b: Any } } = new Object {
      z =>
      val a = n
    }
    o.a
  }
}
