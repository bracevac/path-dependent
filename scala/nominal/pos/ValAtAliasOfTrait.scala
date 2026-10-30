import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-judge/sc/JS02ValAtAliasOfTrait.scala, judge JS02ValAtAliasOfTrait
object ValAtAliasOfTrait {
  object o {
    type T = Any
  }
  trait T {
    type L
    val v: L
  }
  class C(val w: Any) extends T {
    type L = Any
    val v: L = w
  }
  val program = {
    val c = new C(o)
    val t: T = c
    t.v
  }
}
