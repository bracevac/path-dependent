import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-scout/sc/S09MemberBoundsThisL.scala, scout S09MemberBoundsThisL, its accepted part, reshaped: Int replaced by an object o, the defs given a parameter, the wrapper fields moved into program, the cross call dropped
object TypeMemberThisL {
  object o { type T = Any }
  class C {
    type L >: o.type <: Any
    def take(x: this.L): Any = x
    def give(u: Any): this.L = o
  }
  val program = {
    val c = new C
    val a: Any = c.take(c.give(o))
    c.take(o)
  }
}
