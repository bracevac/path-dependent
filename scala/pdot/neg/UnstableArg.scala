import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-pdot-frontend/scratch-refute-d2/sc/V01_UnstableArg.scala, refute-d2 V01_UnstableArg
object UnstableArg {
  def f(x: { type A })(y: x.A): x.A = y
  def g(o: { val a: { type A }; val b: this.a.A }): Any = f(o.a)(o.b) // error
  object u { type U = Any }
  val program = u
}
