import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-refute-d3/sc/X10TraitTwoCtorsSameShape.scala, refute-d3 X10TraitTwoCtorsSameShape
object TwoCtorsSameShape {
  object u { type T = Any }
  class A(val v: Any)
  class B(val v: Any)
  val program: A = new B(u) // error
}
