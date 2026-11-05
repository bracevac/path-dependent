import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/claude-review-followup.md, Priority 2, a type bound
object PrivateBoundEscape {
  abstract class C(x: { type T }) { type T <: x.T } // error
  val program = PrivateBoundEscape
}
