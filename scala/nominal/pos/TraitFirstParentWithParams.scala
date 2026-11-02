import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal-n6/revise/sc/N01TraitFirstParentWithParams.scala, N6 reviser
object TraitFirstParentWithParams {
  class D(val x: Any)
  trait T extends D
  class K(val y: Any) extends D(y) with T
  val program: Any = new K(TraitFirstParentWithParams)
}
