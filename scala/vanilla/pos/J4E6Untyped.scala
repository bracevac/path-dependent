import scala.reflect.Selectable.reflectiveSelectable

// from: notes-scala-xv1/j/J4E6Untyped.scala, the judge's J programs as XV1 g1 wrote them
object J4E6Untyped {
  val program = (n: { val a: Any }) => (new Object {
    x =>
    type T = { val a: Any }
    val v = n
  }: { type T = { val a: Any }; val v: this.T })
}
