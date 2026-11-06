import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p1, review Priority 1 review r2 probe X04mSnglUnusedNewOk, one path given at a parameter and at its singleton, an unused abstract and a concrete class
object SingletonTwiceArg {
  class D(val a: Any, val b: a.type)
  abstract class K(x: Any) extends D(x, x)
  class L(z: Any) extends D(z, z)
  val program = (z: Any) => new L(z).b
}
