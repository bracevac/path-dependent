import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review r3 of Priority 2, probe X49, the same in a val parameter of the head
object PrivateParentValHeadEscape {
  abstract class E { val w: { type S }; type T = w.S }
  abstract class D(w: { type S = Any }) extends E
  abstract class C(x: D, val y: x.T) // error
  val program = PrivateParentValHeadEscape
}
