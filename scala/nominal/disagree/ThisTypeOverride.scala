import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: pDOT subtyping widens no singleton, so a result at this.type does not match the result B of the overridden def (scala/pdot/TABLE.md:68, row SnglInFn)
// from: notes-nominal/scratch-d2/sc/K10ThisTypeOverride.scala, d2 K10ThisTypeOverride, the shape of refute-d2 R10SingletonResult
object ThisTypeOverride {
  object m {
    trait B {
      def me(u: Any): B
    }
    class C extends B {
      def me(u: Any): this.type = this
    }
  }
  val program = {
    val c = new m.C
    val d: c.type = c.me(m)
    d
  }
}
