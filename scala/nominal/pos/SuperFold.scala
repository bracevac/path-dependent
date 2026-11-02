import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal-n6/revise/sc/N03SuperFold.scala, N6 reviser
object SuperFold {
  class A0
  class B0 extends A0
  trait T1 extends B0
  trait T2 extends A0
  class K extends T2 with T1
  val program: Any = new K
}
