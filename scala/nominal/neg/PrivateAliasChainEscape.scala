import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review Priority 2, probe Q08, an alias of an alias, reported at the first alias only
object PrivateAliasChainEscape {
  class C(x: { type T }) {
    type U = x.T // error
    type V = U
  }
  val program = (x: { type T }) => new C(x)
}
