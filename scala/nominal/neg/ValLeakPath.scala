import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-refute-d1/sc/ValLeakPath.scala, refute-d1 ValLeakPath
object ValLeakPath {
  class C {
    type L
    val a: L = ValLeakPath // error
  }
  val program = new C
}
