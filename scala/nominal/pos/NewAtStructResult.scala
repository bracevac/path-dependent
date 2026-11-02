import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-refute-d2/sc/R12NewAtStructResult.scala, refute-d2 R12NewAtStructResult
object NewAtStructResult {
  object m {
    class C(val v: Any)
    def mk(u: Any): { val v: Any } = new C(u)
  }
  val program = m.mk(m)
}
