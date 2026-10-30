import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-LC, a class or trait is a member of the wrapper or of an object
// from: notes-nominal/scratch-scout/sc/S26LocalClassEscape.scala, scout S26LocalClassEscape, reshaped: Int replaced by an object o, the def P.v declared as a val, the wrapper fields moved into program
object LocalClassEscape {
  object o { type T = Any }
  trait P {
    val v: Any
  }
  def g(x: Any) = {
    class L(val v: Any) extends P
    new L(x)
  }
  def k(x: Any) = {
    class L(val v: Any)
    new L(x)
  }
  val program = {
    val h1: o.type = g(o) // error
    val h2: o.type = k(o) // error
    g(o).v
  }
}
