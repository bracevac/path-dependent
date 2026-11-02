import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-AN, an anonymous class is outside the subset
// from: notes-nominal/scratch-scout/sc/S24AnonSubclass.scala, scout S24AnonSubclass, reshaped: Int replaced by Any, `def get` given a parameter, the wrapper field moved into program
object AnonSubclass {
  class C(val v: Any) {
    def get(u: Any): Any = v
  }
  val program = {
    val c: C = new C(AnonSubclass) { override def get(u: Any): Any = u }
    c.get(c)
  }
}
