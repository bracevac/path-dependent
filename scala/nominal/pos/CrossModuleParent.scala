import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d2/sc/K25CrossModuleParent.scala, d2 K25CrossModuleParent
object CrossModuleParent {
  object a {
    trait T {
      val v: Any
    }
  }
  object b {
    class C(val v: Any) extends a.T
  }
  val program: a.T = new b.C(a)
}
