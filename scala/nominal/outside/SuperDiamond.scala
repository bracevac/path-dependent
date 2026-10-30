import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-SU, `super` is outside the subset
// from: notes-nominal/scratch-scout/sc/S06Diamond.scala, scout S06Diamond, reshaped: String replaced by Any, `def m` given a parameter, the string concatenation and main dropped
object SuperDiamond {
  class Base {
    def m(u: Any): Any = u
  }
  trait L extends Base {
    override def m(u: Any): Any = super.m(u)
  }
  trait R extends Base {
    override def m(u: Any): Any = super.m(u)
  }
  class C extends Base with L with R
  val program = {
    val c = new C
    c.m(c)
  }
}
