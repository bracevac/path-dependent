import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-D, a name is a method everywhere or a value everywhere
// from: notes-pdot-frontend/scratch-d2/sc/M06_ObjArgVal.scala, d2 M06_ObjArgVal
object ObjArgVal {
  object core { object types { type A = Any; def f(u: Any): Any = u } }
  def g(x: { type A; val f: Any => Any }): Any = x.f(x)
  val program = g(core.types) // error
}
