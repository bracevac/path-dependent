import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d2/sc/K19ConcreteVsAbstract.scala, d2 K19ConcreteVsAbstract
object ConcreteVsAbstract {
  object m {
    type A = { val a: Any }
    trait L {
      def foo(u: Any): Any = u
    }
    trait R {
      def foo(u: Any): A
    }
    class C extends R with L // error
  }
  val program = m
}
