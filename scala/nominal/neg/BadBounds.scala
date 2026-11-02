import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d1/sc/BadBounds.scala, d1 BadBounds
object BadBounds {
  class C { type L >: Any <: Nothing } // error
  val program = (c: C) => c
}
