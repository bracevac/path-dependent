import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-refute-d1/sc/CovOverrideCall.scala, refute-d1 CovOverrideCall
object CovOverrideCall {
  trait Shape { def me(u: Any): Shape }
  class Square extends Shape { def me(u: Any): Square = this }
  val program = (s: Square) => (s.me(s): Square)
}
