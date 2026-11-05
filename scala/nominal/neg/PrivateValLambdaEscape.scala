import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review Priority 2, probe Q33, a concrete val type
object PrivateValLambdaEscape {
  class C(x: { type T }) { val f: x.T => Any = (y: x.T) => y } // error
  val program = (x: { type T }) => new C(x)
}
