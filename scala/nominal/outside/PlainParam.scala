import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-PA, `x` is a constructor parameter, not a member: write `val x` (scalac E173)
// from: notes-nominal/scratch-refute-d3/sc/X04PlainParam.scala, refute-d3 X04PlainParam
object PlainParam {
  object u { type T = Any }
  class C(x: Any) {
    def get(y: Any): Any = x
  }
  val ok: Any = new C(u).get(u)
  val program: Any = new C(u).x // error
}
