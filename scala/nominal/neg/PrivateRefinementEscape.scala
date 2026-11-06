import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review Priority 2, probe Q16, inside a refinement
object PrivateRefinementEscape {
  abstract class C(x: { type T }) { type U = { type V = x.T } } // error
  val program = PrivateRefinementEscape
}
