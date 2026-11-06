import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p1, review Priority 1, a parent parameter type read at the parent's object, not the class's
object AbstractOuterArg {
  object m {
    type T = Any
    class D(val v: T)
  }
  object k {
    type T = Nothing
    abstract class K extends m.D(AbstractOuterArg)
    class L extends m.D(AbstractOuterArg)
  }
  val program = AbstractOuterArg
}
