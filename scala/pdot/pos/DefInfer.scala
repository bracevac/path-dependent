import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d2/sc/M41_DefInfer.scala, d2 M41_DefInfer
object DefInfer {
  object core { object types { type A = Any } }
  object o {
    def get(t: core.types.A) = t
  }
  def use(t: core.types.A): core.types.A = o.get(t)
  val program = o
}
