import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, a variable hidden by a member of an enclosing refinement (rule 2)
// from: notes-scala-xv0/scalac-g3/RefMember.scala, XV0 g3
object RefMember {
  val program =
    (a: { type T }) =>
      (y: { val a: Any; type B = a.T }) => // error
        y
}
