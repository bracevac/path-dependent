import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-R, a field holds a path or a value in pDOT: move the computation into `program`
// from: notes-pdot-frontend/scratch-d2/sc/M26_WrapperVal.scala, d2 M26_WrapperVal
object WrapperVal {
  object core { def f(u: Any): Any = u }
  val r = core.f(core)
  val program = r
}
