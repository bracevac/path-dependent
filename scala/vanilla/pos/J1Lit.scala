import scala.reflect.Selectable.reflectiveSelectable

// from: notes-scala-xv1/j/J1Lit.scala, the judge's J programs as XV1 g1 wrote them
object J1Lit {
  val program = (n: { val b: Any }) => (new Object {
    z =>
    val a = n
  }: { val a: { val b: Any } })
}
