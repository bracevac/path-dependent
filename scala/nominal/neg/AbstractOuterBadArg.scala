import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p1, review Priority 1, a parent parameter type read at the parent's object, not the class's
object AbstractOuterBadArg {
  object m {
    type T = Nothing
    class D(val v: T)
  }
  object k {
    type T = Any
    abstract class K extends m.D(AbstractOuterBadArg) // error
  }
  val program = AbstractOuterBadArg
}
