import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, a member of every Scala object as a name (rule 7)
// from: notes-scala-xv0/scalac-g3/ObjMember.scala, refute-d3 ObjMember
object ObjMember {
  val program: Any =
    new Object {
      val toString = // error
        (n: Any) =>
          n
    }
}
