import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, a variable hidden by a member of an enclosing object (rule 2)
// from: notes-scala-xv0/scalac-g3/M1.scala, refute-d1 M1
object M1 {
  val program =
    (a: Any => Any) =>
      (new Object {
        s =>
        val a: Any = s
        val b: Any => Any = a // error
      }: { val a: Any; val b: Any => Any })
}
