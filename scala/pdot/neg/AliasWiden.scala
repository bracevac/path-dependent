import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-pdot-frontend/scratch-d3/sc/A11AliasValWiden.scala, d3 A11AliasValWiden
object AliasWiden {
  val program = (x: { type B }) => {
    val y = x
    (z: y.B) => (z: x.B) // error
  }
}
