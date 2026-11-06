import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p2, review Priority 2, probes Q20a, Q20d, Q31, Q32, public signatures on a val parameter
object ValParamSignatures {
  class C(val x: { type T }) { type T = x.T }
  abstract class D(val x: { type T }) {
    type U <: x.T
    def get(u: x.T): x.type
    val y: x.type
  }
  class E(val x: { type T }, val y: x.T)
  class F(val x: { type T }, y: x.T) { type T = x.T }
  val program = (x: { type T }) => new C(x)
}
