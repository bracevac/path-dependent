import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d1/sc/AbstractLeak.scala, d1 AbstractLeak
object AbstractLeak {
  class C {
    type L
    def give(u: Any): L = u // error
  }
  val program = new C
}
