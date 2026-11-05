import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p1, review Priority 1 review r2 probe X33DepChainSnglAbsOk, a singleton parameter after a dependent one, abstract and concrete
object SingletonDependentArg {
  class D(val a: { type T }, val v: a.T, val u: v.type)
  abstract class K(b: { type T }, w: b.T) extends D(b, w, w)
  class L(b: { type T }, w: b.T) extends D(b, w, w)
  val program = SingletonDependentArg
}
