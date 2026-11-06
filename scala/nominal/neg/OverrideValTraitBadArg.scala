import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p1, review Priority 1 review r2 probe Y10OvValTraitDepConcBad, a trait of the linearization overrides the val parameter
object OverrideValTraitBadArg {
  object m {
    type T = Any
  }
  class D(val a: { type T }, val v: a.T)
  trait Tr extends D {
    override val a: m.type = m
  }
  class K(b: { type T }, w: Any) extends D(b, w) with Tr // error
  val program = OverrideValTraitBadArg
}
