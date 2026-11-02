import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-refute-d3/sc/X07K07Singleton.scala, refute-d3 X07K07Singleton, its fault in program, reshaped: the def bad and its fault dropped
object StructInProgram {
  object u { type T = Any }
  object m {
    class C(val v: Any)
  }
  val program: m.C = new Object { val v: u.type = u } // error
}
