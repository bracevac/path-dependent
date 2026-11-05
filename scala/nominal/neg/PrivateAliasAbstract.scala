import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review r1 of Priority 2, probe R07, the alias names an abstract member on the same parameter
object PrivateAliasAbstract {
  abstract class C(x: { type S; type T = this.S }) {
    type U = x.T // error
  }
  val program = PrivateAliasAbstract
}
