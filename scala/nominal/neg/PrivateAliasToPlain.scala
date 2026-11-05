import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2/repair2, probe S31, the alias names an abstract member of an earlier plain parameter, reported at the first
object PrivateAliasToPlain {
  abstract class C(y: { type S }, x: { type T = y.S }) {
    val z: x.T // error
  }
  val program = PrivateAliasToPlain
}
