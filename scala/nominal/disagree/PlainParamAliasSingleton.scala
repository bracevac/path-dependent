import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: OV-Private makes no second walk on a parameter typed by a singleton other than an object's (ScalaClasses.lean, memTyp), and scalac finds the alias in the type of y
// from: notes-nominal/review/p2/repair2, probe S13SnglValParam
object PlainParamAliasSingleton {
  abstract class C(val y: { type T = Any }, x: y.type) {
    type U = x.T
  }
  val program = PlainParamAliasSingleton
}
