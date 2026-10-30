import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-refute-d2/sc/R08ConcreteBeforeAbstract.scala, refute-d2 R08ConcreteBeforeAbstract
object ConcreteBeforeAbstract {
  object m {
    trait A {
      type T = Any
    }
    trait B {
      type T
    }
    class C extends A with B
  }
  val program = new m.C
}
