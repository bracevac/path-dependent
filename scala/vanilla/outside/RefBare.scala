import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-13, a bare member name in a refinement (rule 3)
// from: notes-scala-xv0/scalac-g3/RefBare.scala, XV0 g3
object RefBare {
  val program =
    (y: { val a: { type T }; type B = a.T }) =>
      y
}
