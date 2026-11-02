import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-CC, a class, trait or object inside a class or trait is outside the subset
// from: notes-nominal/scratch-refute-d2/sc/R02bTwoTraitsUse.scala, refute-d2 R02bTwoTraitsUse
object TwoTraitsSameInner {
  object m {
    trait A {
      class E(val x: Any)
    }
    trait B {
      class E(val y: Any)
    }
    class C extends A with B // error
  }
  val program = {
    val c: m.A = new m.C
    val e = new c.E(m)
    e.x
  }
}
