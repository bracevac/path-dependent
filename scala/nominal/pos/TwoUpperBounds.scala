import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-refute-d2/sc/R09TwoUpperBounds.scala, refute-d2 R09TwoUpperBounds
object TwoUpperBounds {
  object m {
    type P = { val p: Any }
    type Q = { val q: Any }
    trait L {
      type T <: P
    }
    trait R {
      type T <: Q
    }
    trait C extends L with R {
      def f(x: T): P = x
    }
  }
  val program = m
}
