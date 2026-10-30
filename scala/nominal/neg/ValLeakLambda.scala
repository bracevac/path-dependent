import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-refute-d1/sc/ValLeakLambda.scala, refute-d1 ValLeakLambda
object ValLeakLambda {
  class C {
    type L
    val f: Any => L = (x: Any) => x // error
  }
  val program = new C
}
