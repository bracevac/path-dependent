import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-CN, a class or trait name is not a type member name anywhere in the file
// from: notes-nominal/scratch-d2/sc/K16RefineClassAsType.scala, d2 K16RefineClassAsType
object RefineClassAsType {
  object m {
    class C(val v: Any)
    def s(u: Any): { val v: Any } = new Object { val v: Any = u }
  }
  val program = (y: m.type & { type C = Any }) => {
    val w = m.s(m)
    val c: y.C = w // error
    val d: m.C = c
    d
  }
}
