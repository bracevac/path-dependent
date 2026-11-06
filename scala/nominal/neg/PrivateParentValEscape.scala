import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review r3 of Priority 2, probe X47, a plain parameter of a subclass does not hide the val of its parent that the parent's alias names
object PrivateParentValEscape {
  abstract class E { val w: { type S }; type T = w.S }
  abstract class D(w: { type S = Any }) extends E
  abstract class C(x: D) { type U = x.T } // error
  val program = PrivateParentValEscape
}
