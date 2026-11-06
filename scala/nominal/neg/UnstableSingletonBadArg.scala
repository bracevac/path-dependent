import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p1, review Priority 1 repair 1, an unstable parent argument at a singleton parameter, built by new
object UnstableSingletonBadArg {
  class A
  class P(val v: UnstableSingletonBadArg.type)
  class L(x: { val y: A }) extends P(x.y) // error
  val program = (x: { val y: A }) => new L(x)
}
