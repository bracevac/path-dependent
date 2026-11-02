import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-refute-d2/sc/R13ValThroughVal.scala, refute-d2 R13ValThroughVal
object ValThroughVal {
  object m {
    class D(val d: Any)
    class C(val x: D) {
      val g: Any = x
      val f: D = g // error
    }
  }
  val program = (k: m.D) => new m.C(k)
}
