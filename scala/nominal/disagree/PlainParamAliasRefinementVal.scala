import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: the second walk of OV-Private selects no `val` of a refinement (ScalaClasses.lean, memVal), and scalac selects w in the type of x and finds the alias S
// from: notes-nominal/review/p2/review-probes/r2, probe W13dRefValNoParamClash
object PlainParamAliasRefinementVal {
  abstract class C(x: { val w: { type S = Any }; type T = w.S }) {
    type U = x.T
  }
  val program = PlainParamAliasRefinementVal
}
