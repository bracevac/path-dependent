import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/claude-review-followup.md, Priority 2
object PrivateTypeEscapeUsed {
  class C(x: { type T }) { type T = x.T } // error
  val program = (x: { type T }) => new C(x)
}
