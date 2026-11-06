import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p1, review Priority 1 repair 2, an unstable argument whose type member is an alias, a dependent argument at that alias, abstract and concrete, built by new
object UnstableAliasArg {
  class A
  class D(val a: { type T = A }, val v: a.T)
  abstract class K(x: { val y: { type T = A } }, w: A) extends D(x.y, w)
  class L(x: { val y: { type T = A } }, w: A) extends D(x.y, w)
  val program = (x: { val y: { type T = A } }) => (w: A) => new L(x, w).v
}
