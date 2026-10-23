import scala.reflect.Selectable.reflectiveSelectable

// from: notes-scala-xv1/j/J1SelfSel.scala, the judge's J programs as XV1 g1 wrote them
object J1SelfSel {
  val program = (x: Any) => (new Object {
    z =>
    type A = Any
    val a: z.A = x
  }: { type A; val a: this.A })
}
