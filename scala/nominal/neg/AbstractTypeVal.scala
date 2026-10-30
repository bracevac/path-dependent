import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-refute-d2/sc/R04AbstractTypeVal.scala, refute-d2 R04AbstractTypeVal
object AbstractTypeVal {
  object m {
    class C(val w: Any) {
      type L
      val v: L = w // error
    }
  }
  val program = new m.C(m)
}
