import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-CC, a class, trait or object inside a class or trait is outside the subset
// from: notes-nominal/scratch-d1/sc/ClassInClass.scala, d1 ClassInClass
object ClassInClass {
  class Outer { class Inner(val v: Any) }
  val program = {
    val o1 = new Outer
    val i: o1.Inner = new o1.Inner(o1)
    i
  }
}
