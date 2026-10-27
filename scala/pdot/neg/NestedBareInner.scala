import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-pdot-frontend/scratch-judge/sc/J02NestedBareInner.scala, judge J02NestedBareInner
object NestedBareInner {
  val program = (t: { type A; val x: { type A; val y: A } }) => (t.x.y: t.A) // error
}
