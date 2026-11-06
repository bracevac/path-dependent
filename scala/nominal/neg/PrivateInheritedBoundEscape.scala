import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review r3 of Priority 2, probe X31, an inherited alias that meets a bound of another class of the linearization
object PrivateInheritedBoundEscape {
  abstract class E { type T = Any }
  trait F { type T <: { val a: Any } }
  abstract class D extends E with F
  abstract class C(x: D) { type U = x.T } // error
  val program = PrivateInheritedBoundEscape
}
