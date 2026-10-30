import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-refute-d3/sc/X07K07Singleton.scala, refute-d3 X07K07Singleton, its fault in the module, reshaped: the fault in program dropped, `val program = m`
object StructInModule {
  object u { type T = Any }
  object m {
    class C(val v: Any)
    def bad(x: Any): C = new Object { val v: x.type = x } // error
  }
  val program = m
}
