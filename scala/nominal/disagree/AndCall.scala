import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: pDOT has no rule from an intersection of method types to a method of the intersection (And-Fun, thesis p.124)
// from: notes-nominal/scratch-refute-d1/sc/AndCall.scala, refute-d1 AndCall, the shape of d3 K17AndFun and d2 K09IntersectionMethods
object AndCall {
  trait A0
  trait B0
  trait L { def foo(u: Any): A0 }
  trait R { def foo(u: Any): B0 }
  val program = (x: L & R) => (x.foo(x): A0 & B0)
}
