import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-pdot-frontend/scratch-d2/sc/M21_ParamAlias.scala, d2 M21_ParamAlias, reshaped: the def kept, `val program = u` added last (the probe had no program)
object ParamAlias {
  def f(q: { type B }) = {
    val y = q
    (z: y.B) => (z: q.B) // error
  }
  object u { type U = Any }
  val program = u
}
