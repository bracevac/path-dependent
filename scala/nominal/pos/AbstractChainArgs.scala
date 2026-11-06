import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p1, review Priority 1 repair 1, a chain of abstract classes each passing its parameter to its parent (probe C9NonDep3)
object AbstractChainArgs {
  class A
  class E(val a: A)
  abstract class D(val b: A) extends E(b)
  abstract class K(val c: A) extends D(c)
  abstract class J(val d: A) extends K(d)
  val program = AbstractChainArgs
}
