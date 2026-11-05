import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p2, review Priority 2, probes Q17, Q18, Q25, Q29, Q34, a binder or member of the same name hides the plain parameter
object PlainParamShadowed {
  abstract class C1(x: Any) { def get(x: Any): x.type }
  abstract class C2(x: { type T }) { type F = (x: { type T }) => x.T }
  abstract class C3(x: Any) { val y: { val x: Any; val z: x.type } }
  abstract class C4(x: { type T }) { def f(x: { type T })(y: x.T): x.T }
  class C5(x: { type T }, val y: (x: { type T }) => x.T)
  val program = PlainParamShadowed
}
