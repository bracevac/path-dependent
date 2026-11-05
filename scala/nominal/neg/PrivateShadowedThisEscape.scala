import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review Priority 2, repair 1, probe V25, this.x beside a method parameter x
object PrivateShadowedThisEscape {
  abstract class C(x: { type T }) { def f(x: { type T }): this.x.T } // error
  val program = PrivateShadowedThisEscape
}
