import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-judge/sc/J01NestedBare.scala, judge J01NestedBare
object NestedBare {
  val program = (t: { type A; val x: { val y: A } }) => (t.x.y: t.A)
}
