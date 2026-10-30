import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d1/sc/DiamondOverride.scala, d1 DiamondOverride
object DiamondOverride {
  class Base { def m(u: Any): Any = u }
  trait L extends Base { override def m(u: Any): Any = u }
  trait R extends Base { override def m(u: Any): Any = DiamondOverride }
  class C extends Base with L with R
  val program = new C
}
