import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/sc/C06ObjForward.scala, d3 C06ObjForward
object ObjForward {
  object a {
    type T = b.U
  }
  object b {
    type U = { val v: Any }
  }
  val program = (x: a.T) => x.v
}
