import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-CI, cyclic inheritance (scalac E110)
// from: notes-nominal/scratch-refute-d3/sc/X08CyclicInherit.scala, refute-d3 X08CyclicInherit
object CyclicInherit {
  object u { type T = Any }
  trait A extends B // error
  trait B extends A
  val program: Any = u
}
