import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d2/sc/K17DepCtorParams.scala, d2 K17DepCtorParams
object DepCtorParams {
  object m {
    trait M {
      type T
    }
    class C(val o: M, val v: o.T)
  }
  val program = m
}
