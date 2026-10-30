import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d1/sc/Running.scala, d1 Running
object Running {
  trait Shape {
    type Unit
    def area(u: Any): Any
    def me(u: Any): Shape = this
    def self2(u: Any): this.type = this
  }
  class Square(val side: Any) extends Shape {
    type Unit = Any
    def area(u: Any): Any = side
  }
  object geo {
    class Point(val x: Any) { def move(d: Any): Point = new Point(d) }
  }
  val program = {
    val s: Shape = new Square(geo)
    val p: geo.Point = new geo.Point(s)
    val q = s.me(p)
    val w: q.type = q.self2(p)
    val a = p.move(w)
    a.x
  }
}
