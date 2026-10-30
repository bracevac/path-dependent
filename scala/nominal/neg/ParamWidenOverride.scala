import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-refute-d2/sc/R05bParamWidenOverride.scala, refute-d2 R05bParamWidenOverride
object ParamWidenOverride {
  object m {
    class D
    class A {
      def put(x: D): Any = x
    }
    class C extends A {
      override def put(x: Any): Any = x // error
    }
  }
  val program = new m.C
}
