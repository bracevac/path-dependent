import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p2, review Priority 2, probe Q11, a plain parameter passed to a parent val parameter that the parent's signatures name
object PlainParamToParentVal {
  class P(val a: { type T }) { type U = a.T }
  class C(x: { type T }) extends P(x) { def f(u: U): Any = u }
  val program = (x: { type T }) => new C(x)
}
