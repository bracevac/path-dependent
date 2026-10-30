import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-PP, a parent is a class or trait of this file reached through objects
// from: notes-nominal/scratch-refute-d3/sc/X09ParentThroughAlias.scala, refute-d3 X09ParentThroughAlias
object ParentThroughAlias {
  object u { type T = Any }
  object m {
    class C(val v: Any)
  }
  object k {
    val a: m.type = m
    class D(val w: Any) extends a.C(w)
  }
  val program: m.C = new k.D(u)
}
