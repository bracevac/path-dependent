import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/claude-review-followup.md, Priority 1
object AbstractNominalArg {
  class A
  class B
  class P(val x: A)
  abstract class Q(x: B) extends P(x) // error
  val program = AbstractNominalArg
}
