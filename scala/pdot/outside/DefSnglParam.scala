import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-P, a def takes one parameter per list, and a refinement declares no def
// from: notes-pdot-frontend/scratch-refute-d2/sc/P01_DefSnglParam.scala, refute-d2 P01_DefSnglParam
object DefSnglParam {
  object q { type B = Any }
  object o { def f(u: Any): Any = u }
  def use(x: { def f(u: q.type): Any }): Any = x
  val program = use(o) // error
}
