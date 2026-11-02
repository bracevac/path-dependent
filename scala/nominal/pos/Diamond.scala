import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d3/sc/K06Diamond.scala, d3 K06Diamond
object Diamond {
  object u { type T = Any }
  object w { type T = Any }
  trait Base {
    def m(x: Any): Any
  }
  trait L extends Base {
    override def m(x: Any): Any = u
  }
  trait R extends Base {
    override def m(x: Any): Any = w
  }
  class C extends Base with L with R
  val program: Any = {
    val c: Base = new C
    c.m(u)
  }
}
