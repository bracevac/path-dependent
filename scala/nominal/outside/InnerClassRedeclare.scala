import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-CC, a class, trait or object inside a class or trait is outside the subset
// from: notes-nominal/scratch-refute-d2/sc/R01cOverrideClassUse.scala, refute-d2 R01cOverrideClassUse
object InnerClassRedeclare {
  object m {
    class Outer {
      class Inner(val x: Any)
    }
    class Outer2 extends Outer {
      override class Inner(val y: Any) // error
    }
  }
  val program = {
    val o2 = new m.Outer2
    val o: m.Outer = o2
    val j = new o.Inner(m)
    j.x
  }
}
