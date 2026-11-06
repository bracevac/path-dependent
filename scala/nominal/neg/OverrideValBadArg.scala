import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p1, review Priority 1 review r2 probe Y01bOvValConcNewBad, a concrete class overrides the val parameter it gives a bad argument, built by new
object OverrideValBadArg {
  class A
  class B
  class D(val a: A)
  class K(x: B, y: A) extends D(x) { // error
    override val a: A = y
  }
  val program = (x: B) => (y: A) => new K(x, y).a
}
