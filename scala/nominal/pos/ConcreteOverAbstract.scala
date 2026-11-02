import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-refute-d1/sc/ConcreteOverAbstract.scala, refute-d1 ConcreteOverAbstract
object ConcreteOverAbstract {
  class K
  trait L { def m(u: Any): K = new K }
  trait R { def m(u: Any): Any }
  class C extends L with R
  val program = new C
}
