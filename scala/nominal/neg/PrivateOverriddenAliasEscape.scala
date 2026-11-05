import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review r4 of Priority 2, probe Z50, an inherited alias that a subclass of its class declares again as an abstract type
object PrivateOverriddenAliasEscape {
  abstract class E { type T = Any }
  abstract class G extends E { type T }
  abstract class D extends G
  abstract class C(x: D) { type U = x.T } // error
  val program = PrivateOverriddenAliasEscape
}
