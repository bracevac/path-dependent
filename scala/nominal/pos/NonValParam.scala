import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d1/sc/NonValParam.scala, d1 NonValParam
object NonValParam {
  class C(x: Any) { def get(u: Any): Any = x }
  val program = new C(NonValParam)
}
