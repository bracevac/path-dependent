import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review r3 of Priority 2, probe X53, a path that selects the inherited val past the plain parameter of the same name
object PrivateParentValPathEscape {
  abstract class E { val w: { type S } }
  abstract class D(w: { type S = Any }) extends E
  abstract class C(x: D) { type U = x.w.S } // error
  val program = PrivateParentValPathEscape
}
