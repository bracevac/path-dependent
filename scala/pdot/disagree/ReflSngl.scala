import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: pDOT has no rule x : x.type, here through def id(x: Any): x.type = x (pDOT N4)
// from: notes-pdot-frontend/scratch-d2/sc/M15_ReflSngl.scala, d2 M15_ReflSngl
object ReflSngl {
  def id(x: Any): x.type = x
  object o { type B = Any }
  val program: o.type = id(o)
}
