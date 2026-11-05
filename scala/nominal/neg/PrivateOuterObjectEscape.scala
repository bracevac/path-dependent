import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review r4 of Priority 2, probe Z28, the type of a val parameter of another class read in its head, where a val of its body does not hide the outer object
object PrivateOuterObjectEscape {
  object o { type R = { type S } }
  object oo { type R = { type S = Any } }
  abstract class D(val w: o.R) { val o: oo.type }
  abstract class C(x: D) { type U = x.w.S } // error
  val program = PrivateOuterObjectEscape
}
