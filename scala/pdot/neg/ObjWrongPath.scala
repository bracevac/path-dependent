import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-pdot-frontend/scratch-d3/sc/P11ObjWrongPath.scala, d3 P11ObjWrongPath
object ObjWrongPath {
  object a {
    type T = { val v: Any }
  }
  object b {
    type T = { val w: Any }
  }
  val program = (x: a.T) => (x: b.T) // error
}
