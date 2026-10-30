import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d1/sc/CrossInstance.scala, d1 CrossInstance
object CrossInstance {
  class C {
    type L
    def take(x: L): Any = x
  }
  val program = (c: C) => (d: C) => (y: d.L) => c.take(y) // error
}
