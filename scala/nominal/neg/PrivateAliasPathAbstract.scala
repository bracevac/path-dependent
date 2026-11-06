import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2/repair2, probe S58, the alias of a class selects on a val of the class, whose alias names an abstract member of the class
object PrivateAliasPathAbstract {
  abstract class D { type V; val w: { type S = V }; type T = w.S }
  abstract class C(x: D) {
    type U = x.T // error
  }
  val program = PrivateAliasPathAbstract
}
