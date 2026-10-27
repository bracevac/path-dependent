import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-judge/sc/J04ObjInLit.scala, judge J04ObjInLit
object ObjInLit {
  val program = (new Object {
    object a {
      type A = Any
    }
  }: { val a: { type A } })
}
