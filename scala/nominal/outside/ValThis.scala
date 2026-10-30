import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-VT, a `val` of a class or trait does not read `this`
// from: notes-nominal/scratch-refute-d1/sc/ValThis.scala, refute-d1 ValThis
object ValThis {
  trait T { val me: T = this }
  class C extends T
  val program = {
    val c = new C
    c.me
  }
}
