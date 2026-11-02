import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-refute-d2/sc/R05ParamWiden.scala, refute-d2 R05ParamWiden
object ParamWiden {
  object m {
    class D
    trait T {
      def put(x: D): Any
    }
    class C extends T { // error
      def put(x: Any): Any = x
    }
  }
  val program = new m.C
}
