import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-pdot-frontend/scratch-d3/sc/P16N1Lam.scala, d3 P16N1Lam
object N1Lam {
  val program: { val b: { val c: Any } } = new Object {
    val b: { val c: Any } = (y: Any) => y // error
  }
}
