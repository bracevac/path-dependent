import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d1/sc/TypeMemberBounds.scala, d1 TypeMemberBounds
object TypeMemberBounds {
  trait Box {
    type Elem <: Any
    val elem: Elem
    def get(u: Any): Elem = elem
  }
  class AnyBox(val elem: Any) extends Box { type Elem = Any }
  val program = {
    val b: Box = new AnyBox(TypeMemberBounds)
    val e: b.Elem = b.get(b)
    e
  }
}
