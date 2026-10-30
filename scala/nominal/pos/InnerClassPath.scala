import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d1/sc/InnerClassPath.scala, d1 InnerClassPath
object InnerClassPath {
  object geo {
    class Point(val x: Any) { def move(d: Any): Point = new Point(d) }
  }
  val program = {
    val a: geo.type = geo
    val p: a.Point = new geo.Point(geo)
    val q: geo.Point = p.move(p)
    q
  }
}
