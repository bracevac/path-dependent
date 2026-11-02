import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-refute-d2/sc/R03AbstractTypeMethod.scala, refute-d2 R03AbstractTypeMethod
object AbstractTypeMethod {
  object m {
    trait T {
      type L
      def get(u: Any): L
    }
    class C extends T {
      def get(u: Any): Any = u // error
    }
  }
  val program = new m.C
}
