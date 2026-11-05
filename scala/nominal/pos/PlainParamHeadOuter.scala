import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p2, review Priority 2, probes Q28, Q35, a val parameter typed by an outer object named as a plain parameter
object PlainParamHeadOuter {
  object x { type A = Any }
  class C(x: Any, val y: this.x.type)
  class D(x: Any, val y: PlainParamHeadOuter.x.type)
  val program = (u: Any) => new D(u, x)
}
