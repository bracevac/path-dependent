import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d2/sc/M18_ObjAsVal.scala, d2 M18_ObjAsVal
object ObjAsVal {
  object core { object types { type A = Any } }
  def g(x: { val types: { type A } }): Any = x.types
  val program = g(core)
}
