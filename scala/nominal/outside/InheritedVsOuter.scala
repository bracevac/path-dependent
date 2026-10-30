import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-BN, a reference is ambiguous: it is both defined in an enclosing object and inherited (scalac E049)
// from: notes-nominal/scratch-refute-d1/sc/InheritedVsOuter.scala, refute-d1 InheritedVsOuter
object InheritedVsOuter {
  trait T { val v: Any = InheritedVsOuter }
  object o {
    val v: Any = o
    class C extends T { def get(u: Any): Any = v } // error
  }
  val program = o
}
