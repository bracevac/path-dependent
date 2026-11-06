import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p1, review Priority 1, a module alias as the argument of a dependent parent parameter
object AbstractModuleArg {
  object m {
    type T = Any
    class D(val a: { type T }, val v: a.T)
  }
  object k {
    val n: m.type = m
    abstract class K extends m.D(n, AbstractModuleArg)
    class L extends m.D(n, AbstractModuleArg)
  }
  val program = AbstractModuleArg
}
