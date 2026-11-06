import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/claude-review-followup.md, Priority 2, an abstract method result
object PrivateDefEscape {
  abstract class C(x: Any) { def get(u: Any): x.type } // error
  val program = PrivateDefEscape
}
