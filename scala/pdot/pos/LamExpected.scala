import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d2/sc/M25_LamExpected.scala, d2 M25_LamExpected
object LamExpected {
  object core { object types { type A = Any } }
  def ap(f: core.types.A => Any): Any = f(core)
  val program = ap(x => x)
}
