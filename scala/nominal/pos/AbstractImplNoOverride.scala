import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d2/sc/K28AbstractImplNoOverride.scala, d2 K28AbstractImplNoOverride
object AbstractImplNoOverride {
  object m {
    trait T {
      def f(u: Any): Any
    }
    class A extends T {
      def f(u: Any): Any = u
    }
  }
  val program: m.T = new m.A
}
