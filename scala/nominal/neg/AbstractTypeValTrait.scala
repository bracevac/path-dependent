import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-refute-d2/sc/R04bAbstractTypeValTrait.scala, refute-d2 R04bAbstractTypeValTrait
object AbstractTypeValTrait {
  object m {
    trait T {
      type L
      val v: L
    }
    class C(val w: Any) extends T {
      val v: Any = w // error
    }
  }
  val program = new m.C(m)
}
