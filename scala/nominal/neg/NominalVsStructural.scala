import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-scout/sc/S17NominalVsStructural.scala, scout S17NominalVsStructural, reshaped: Int replaced by Any, `def v` given a parameter, the wrapper fields moved into program
object NominalVsStructural {
  trait T {
    def v(u: Any): Any
  }
  class C extends T {
    def v(u: Any): Any = u
  }
  class D {
    def v(u: Any): Any = u
  }
  val program = {
    val ok: T = new C
    val bad: T = new D // error
    ok.v(ok)
  }
}
