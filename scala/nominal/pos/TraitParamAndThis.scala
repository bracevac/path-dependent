import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-scout/sc/S20TraitParamAndThis.scala, scout S20TraitParamAndThis, reshaped: Int replaced by Any, the parameterless defs given a parameter, `def id: Int` declared as `val id: Any`, the chain of calls in program bound by vals
object TraitParamAndThis {
  trait T {
    val id: Any
    def me(u: Any): T = this
  }
  class C(val id: Any) extends T
  val program = {
    val c = new C(TraitParamAndThis)
    val t: T = c.me(c)
    t.id
  }
}
