import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p1, review r1 of repair 1 probe C9UnstReflAliasInherited, the unstable argument given to an abstract class that passes it on, built by new
object UnstableInheritedBadArg {
  class D(val a: { type T }, val v: a.T)
  abstract class E(b: { type T }, u: b.T) extends D(b, u)
  class L(x: { val y: { type T }; type U = y.T }, w: x.U) extends E(x.y, w) // error
  val program = (x: { val y: { type T }; type U = y.T }) => (w: x.U) => new L(x, w).v
}
