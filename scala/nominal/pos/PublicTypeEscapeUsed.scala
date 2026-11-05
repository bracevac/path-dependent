import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/claude-review-followup.md, Priority 2
object PublicTypeEscapeUsed {
  class C(val x: { type T }) { type T = x.T }
  val program = (x: { type T }) => new C(x)
}
