import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-judge/sc/JS01ValLowerBound.scala, judge JS01ValLowerBound
object ValLowerBound {
  object o {
    type T = Any
  }
  class C {
    type L >: o.type
    val v: L = o
  }
  val program = {
    val c = new C
    c.v
  }
}
