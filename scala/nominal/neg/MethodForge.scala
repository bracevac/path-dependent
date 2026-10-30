import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-refute-d1/sc/MethodForge.scala, refute-d1 MethodForge
object MethodForge {
  class C(val v: Any) {
    def forge(u: Any): C = {
      val r: { val v: Any } = new Object { val v: Any = u }
      r // error
    }
  }
  val program = new C(MethodForge)
}
