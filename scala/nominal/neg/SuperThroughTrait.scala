import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal-n6/revise/sc/N02SuperThroughTrait.scala, N6 reviser
object SuperThroughTrait {
  class B(val x: Any)
  trait T extends B
  class K extends T // error
  val program: Any = new K
}
