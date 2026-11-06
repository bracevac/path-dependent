import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review r4 of Priority 2, probe Z71, an earlier val parameter named in the type of a later one, selected on the path
object PrivateEarlierParamEscape {
  abstract class D(val a: { type S }, val w: { type S = a.S })
  abstract class C(x: D) { type U = x.w.S } // error
  val program = PrivateEarlierParamEscape
}
