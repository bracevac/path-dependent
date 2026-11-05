import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p2, review r1 of Priority 2, probes R01, R04, R16, R27, repair 2 probe S42, scalac makes a second walk at an alias in the type of a plain parameter
object PlainParamAlias {
  class C(x: { type T = Any }) { type U = x.T }
  abstract class C2(x: { type T = Any }, val y: x.T)
  abstract class C3(x: { type S = Any; type T = this.S }) { type U = x.T }
  abstract class C4(x: { type T = Any } & { type S }) { val y: Any & x.T }
  abstract class C5(y: { type S = Any }, x: { type T = y.S }) { def f(u: x.T): x.T }
  val program = (u: { type T = Any }) => new C(u)
}
