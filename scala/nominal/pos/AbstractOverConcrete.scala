import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal-n6/revise/sc/N04AbstractOverConcrete.scala, N6 reviser
object AbstractOverConcrete {
  class P { def m(u: Any): Any = u }
  abstract class Q extends P { def m(u: Any): Any }
  val program = AbstractOverConcrete
}
