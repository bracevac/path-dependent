import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, two members of one name in one literal (rule 8)
// from: notes-scala-xv0/scalac-g3/DupLit.scala, XV0 g3
object DupLit {
  val program =
    (n: Any) =>
      (new Object {
        val a = n
        val a = n // error
      }: { val a: Any })
}
