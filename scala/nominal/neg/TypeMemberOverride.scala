import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-scout/sc/S23TypeMemberOverride.scala, scout S23TypeMemberOverride, its rejected part, reshaped: AnyRef replaced by Any and String by a refinement, the accepted class C dropped, `val program = o`
object TypeMemberOverride {
  object o { type T = Any }
  trait T {
    type L <: Any
  }
  trait U extends T {
    type L <: { type T }
  }
  class D extends U {
    type L = Any // error
  }
  val program = o
}
