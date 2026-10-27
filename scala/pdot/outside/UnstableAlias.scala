import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-S, `x.a` is not a valid type prefix, since it is not an immutable path (scalac E083)
// from: notes-pdot-frontend/scratch-refute-d2/sc/P04_UnstableAlias.scala, refute-d2 P04_UnstableAlias
object UnstableAlias {
  object o { type T = { val a: { type A } } }
  def f(x: o.T)(y: x.a.A): Any = y // error
  object u { type U = Any }
  val program = u
}
