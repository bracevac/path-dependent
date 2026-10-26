import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-13, a bare name of a member of an enclosing refinement, in an inner one (rule 3)
// from: notes-scala-xv2/refute/hand/RefOuterBare.scala, refute-stage3 R2
object RefOuterBare {
  val program =
    (x: { val a: { type B }; val c: { val d: a.B } }) =>
      x
}
