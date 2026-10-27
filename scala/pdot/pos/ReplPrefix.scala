import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d2/sc/Proto_Repl.scala, d2 Proto_Repl
object ReplPrefix {
  object core {
    object types {
      type A = Any
    }
  }
  def h(x: core.type)(t: x.types.A): core.types.A = t
  val program = core
}
