import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-CC, a class, trait or object inside a class or trait is outside the subset
// from: notes-nominal/scratch-scout/sc/S16ClassInClassPath.scala, scout S16ClassInClassPath, its accepted part, reshaped: Int replaced by Any, the wrapper fields moved into program, the faulty i2 replaced by an accepted one, the projection Outer#Inner dropped
object ClassInClassPath {
  class Outer {
    class Inner(val v: Any)
  }
  val program = {
    val o1 = new Outer
    val o2 = new Outer
    val i1: o1.Inner = new o1.Inner(o1)
    val i2: o2.Inner = new o2.Inner(o2)
    i1.v
  }
}
