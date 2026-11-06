import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/claude-review-followup.md, Priority 2, an abstract val type
object PrivateValEscape {
  abstract class C(x: Any) { val y: x.type } // error
  val program = PrivateValEscape
}
