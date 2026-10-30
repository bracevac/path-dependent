import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: pDOT has no subtyping from a mu type to a record (no Bind1, facts 1.2.8), so { val v: Any } => Any is no subtype of m.C => Any
// from: notes-nominal/scratch-refute-d2/sc/R11FunStructParam.scala, refute-d2 R11FunStructParam
object FunStructParam {
  object m {
    class C(val v: Any)
  }
  val program = (g: { val v: Any } => Any) => {
    val h: m.C => Any = g
    h
  }
}
