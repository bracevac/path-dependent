import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p2, review Priority 2, probe Q12, a plain parameter used in a method body and a val right side
object PlainParamBodyUse {
  class C(x: { type T; val v: T }) {
    def f(u: Any): Any = { val z: x.T = x.v; ((w: x.T) => w)(z) }
    val g: Any = x
  }
  val program = (x: { type T; val v: T }) => new C(x).f(x)
}
