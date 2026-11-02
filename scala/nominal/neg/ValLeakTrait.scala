import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-refute-d1/sc/ValLeakTrait.scala, refute-d1 ValLeakTrait
object ValLeakTrait {
  trait Box { type Elem; val elem: Elem }
  class Bad extends Box { val elem: Elem = ValLeakTrait } // error
  val program = new Bad
}
