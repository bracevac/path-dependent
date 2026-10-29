import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-P, a def takes one parameter per list, and a refinement declares no def
// from: notes-pdot-frontend/scratch-d3/sc/C19ObjParamless.scala, d3 C19ObjParamless
object Paramless {
  object o {
    def b: Any = o
  }
  val program = o.b
}
