import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p1, review Priority 1 repair 1, an unstable parent argument of the wrong class, abstract and concrete
object UnstableBadArg {
  class A
  class C
  class P(val v: A)
  abstract class K(x: { val y: C }) extends P(x.y) // error
  class L(x: { val y: C }) extends P(x.y) // error
  val program = UnstableBadArg
}
