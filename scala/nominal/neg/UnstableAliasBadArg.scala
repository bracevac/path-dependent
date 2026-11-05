import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p1, review r1 of repair 1 probe C8UnstReflAliasNew, a dependent argument typed through an alias of the unstable path, built by new
object UnstableAliasBadArg {
  class D(val a: { type T }, val v: a.T)
  class L(x: { val y: { type T }; type U = y.T }, w: x.U) extends D(x.y, w) // error
  val program = (x: { val y: { type T }; type U = y.T }) => (w: x.U) => new L(x, w).v
}
