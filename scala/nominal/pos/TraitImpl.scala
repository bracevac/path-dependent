import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d1/sc/TraitImpl.scala, d1 TraitImpl
object TraitImpl {
  trait Shape { def area(u: Any): Any }
  class Square(val side: Any) extends Shape { def area(u: Any): Any = side }
  val program = {
    val s: Shape = new Square(TraitImpl)
    s.area(s)
  }
}
