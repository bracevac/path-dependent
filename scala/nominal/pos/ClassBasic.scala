import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d1/sc/ClassBasic.scala, d1 ClassBasic
object ClassBasic {
  class Cell(val v: Any) {
    def get(u: Any): Any = v
    def put(w: Any): Cell = new Cell(w)
  }
  val program = {
    val c = new Cell(ClassBasic)
    val d: Cell = c.put(c)
    d.get(d)
  }
}
