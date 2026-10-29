import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-pdot-frontend/scratch-refute-d2/sc/U01_BareInRefine.scala, refute-d2 U01_BareInRefine
object BareInRefine {
  object o {
    type A = Nothing
    type T = { type A >: Any; val x: A }
  }
  def f(t: o.T): Nothing = t.x // error
  val program = o
}
