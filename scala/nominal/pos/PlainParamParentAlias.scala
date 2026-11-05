import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p2/review-probes/r2, probes W25, W60, review r3 probe X51, repair 4 probe Y10, an inherited alias that names a plain parameter of its class
object PlainParamParentAlias {
  abstract class P(p: { type S = Any }) { type T = p.S }
  abstract class K(q: { type S = Any }) extends P(q)
  abstract class C(x: K) {
    type U = x.T
  }
  trait Q
  abstract class K2(q: { type S = Any }) extends P(q) with Q
  abstract class C2(x: K2, val y: x.T)
  abstract class K3(p: { type S }, r: { type S = Any }) extends P(r)
  abstract class C3(x: K3) { type U = x.T }
  abstract class K4(r: { type S = Any }) extends K(r)
  abstract class C4(x: K4) { type U = x.T }
  val program = PlainParamParentAlias
}
