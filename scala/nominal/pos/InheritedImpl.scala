import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d2/sc/K18InheritedImpl.scala, d2 K18InheritedImpl
object InheritedImpl {
  object m {
    type A = { val a: Any }
    trait L {
      def foo(u: Any): A
    }
    trait R {
      def foo(u: Any): Any
    }
    class C(val k: A) extends R with L {
      def foo(u: Any): A = k
    }
    class D(val k: A) extends L with R {
      def foo(u: Any): A = k
    }
  }
  val program = (k: m.A) => {
    val c: m.R = new m.C(k)
    val d: m.L = new m.D(k)
    d
  }
}
