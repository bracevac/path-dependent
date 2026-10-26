import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, a self name that is a member's name (rule 8)
// from: notes-scala-xv0/scalac-g3/SelfMember.scala, XV0 g3
object SelfMember {
  val program =
    (n: Any) =>
      (new Object {
        a => // error
        val a = n
      }: { val a: Any })
}
