import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-CC, a class, trait or object inside a class or trait is outside the subset
// from: notes-nominal/scratch-refute-d2/sc/R14BlockEscapeInner.scala, refute-d2 R14BlockEscapeInner
object BlockEscapeInner {
  object m {
    class Outer {
      class Inner(val x: Any)
    }
  }
  val program = {
    val i = {
      val o = new m.Outer
      new o.Inner(m)
    }
    i.x
  }
}
