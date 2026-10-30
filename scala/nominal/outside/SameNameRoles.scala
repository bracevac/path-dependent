import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-CN, a class or trait name is not a type member name anywhere in the file
// from: notes-nominal/scratch-d2/sc/K29SameNameRoles.scala, d2 K29SameNameRoles
object SameNameRoles {
  object a {
    class C(val v: Any)
  }
  object b {
    type C = { val v: Any }
  }
  val program = (x: a.C) => (x: b.C)
}
