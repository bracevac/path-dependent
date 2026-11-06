import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/claude-review-followup.md, Priority 1, the smaller case
object AbstractBadArg {
  class A(val x: Nothing)
  abstract class B extends A(AbstractBadArg) // error
  val program = AbstractBadArg
}
