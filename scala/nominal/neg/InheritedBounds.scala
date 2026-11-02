import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal-n6/revise/sc/N08InheritedBounds.scala, N6 reviser
object InheritedBounds {
  object u { type V = Any }
  trait L { type X >: u.type }
  trait R { type X <: Nothing }
  trait K extends L with R // error
  val program: Any = u
}
