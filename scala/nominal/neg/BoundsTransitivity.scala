import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d3/sc/K16BoundsTransitivity.scala, d3 K16BoundsTransitivity (thesis p.102)
object BoundsTransitivity {
  object u { type T = Any }
  trait A {
    type S
    type T
    type M >: S <: T
    def id(x: S): T = x // error
    def conv(x: S): M = x
  }
  val program = u
}
