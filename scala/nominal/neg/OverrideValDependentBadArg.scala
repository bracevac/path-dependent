import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p1, review Priority 1 review r2 probe Y02OvValDepConcBad, a dependent parameter whose val parameter a concrete class overrides
object OverrideValDependentBadArg {
  class D(val a: { type T }, val v: a.T)
  class K(b: { type T }, c: { type T }, w: c.T) extends D(b, w) { // error
    override val a: { type T } = c
  }
  val program = OverrideValDependentBadArg
}
