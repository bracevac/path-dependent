import scala.reflect.Selectable.reflectiveSelectable

// from: notes-scala-xv1/j/J4E6Typed.scala, the judge's J programs as XV1 g1 wrote them
object J4E6Typed {
  val program = (n: { val a: Any }) => (new Object {
    x =>
    type T = { val a: Any }
    val v: x.T = n
  }: { type T = { val a: Any }; val v: this.T })
}
