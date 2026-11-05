import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review r4 of Priority 2, probe Z72, the same for a val parameter of a parent
object PrivateParentOuterObjectEscape {
  object o { type R = { type S } }
  object oo { type R = { type S = Any } }
  abstract class E(val w: o.R) { val o: oo.type }
  abstract class D(q: o.R) extends E(q)
  abstract class C(x: D) { type U = x.w.S } // error
  val program = PrivateParentOuterObjectEscape
}
