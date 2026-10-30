import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-scout/sc/S09MemberBoundsThisL.scala, scout S09MemberBoundsThisL, its rejected part, reshaped: Int replaced by an object o, the defs given a parameter, only the cross call kept, in program
object OtherInstanceL {
  object o { type T = Any }
  class C {
    type L >: o.type <: Any
    def take(x: this.L): Any = x
    def give(u: Any): this.L = o
  }
  val program = {
    val c = new C
    val d = new C
    c.take(d.give(o)) // error
  }
}
