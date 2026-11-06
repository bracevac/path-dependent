import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: the second walk of OV-Private does not follow a type member of a class that names the declared type of a `val` (ScalaClasses.lean, memTyp), here R of D as the type of w, and scalac finds the alias S in R
// from: notes-nominal/review/p2/repair2, probe S68ClsValOfOwnAlias
object PlainParamAliasValAlias {
  abstract class D { type R = { type S = Any }; val w: R; type T = w.S }
  abstract class C(x: D) {
    type U = x.T
  }
  val program = PlainParamAliasValAlias
}
