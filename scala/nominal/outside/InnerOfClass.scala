import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-CC, a class, trait or object inside a class or trait is outside the subset
// from: notes-nominal/scratch-d2/sc/K04InnerOfClass.scala, d2 K04InnerOfClass
object InnerOfClass {
  object m {
    class Outer {
      class Inner(val v: Any)
    }
  }
  val program = {
    val o1 = new m.Outer
    val o2 = new m.Outer
    val i: o2.Inner = new o1.Inner(m) // error
    i
  }
}
