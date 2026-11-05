import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p1, review Priority 1 repair 3, a parent's val parameter overridden by an abstract and a concrete class, built by new
object OverrideValArg {
  class A
  class B extends A
  class D(val a: A)
  abstract class Q(x: B, y: A) extends D(x) {
    override val a: A = y // warn
  }
  class K(x: B, y: A) extends D(x) {
    override val a: A = y // warn
  }
  val program = (x: B) => (y: A) => new K(x, y).a
}
