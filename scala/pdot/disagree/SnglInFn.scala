import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: pDOT subtyping widens no singleton, so Any => q.type is no subtype of Any => { type B }
// from: notes-pdot-frontend/scratch-d2/sc/M49_SnglInFn.scala, d2 M49_SnglInFn
object SnglInFn {
  object q { type B = Any; val me: this.type = this }
  val g: Any => q.type = (x: Any) => q.me
  def k(u: Any): Any => { type B } = g
  val program = k(q)
}
