import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-W, a member of a class or trait has a written type in this stage
// from: notes-nominal/scratch-d1/sc/ImplicitAny.scala, d1 ImplicitAny
object ImplicitAny {
  class C(val v: Any) { def get(u: Any) = v }
  val program = new C(ImplicitAny).get(ImplicitAny)
}
