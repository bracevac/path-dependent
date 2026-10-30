import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-OE, an object that extends a class or trait is outside the subset
// from: notes-nominal/scratch-scout/sc/S12ObjectExtendsTrait.scala, scout S12ObjectExtendsTrait, its accepted part, reshaped: Int replaced by u.type, the wrapper fields moved into program, the faulty `val u: t.A = o.a` dropped
object ObjectExtendsTrait {
  object u { type T = Any }
  trait T {
    type A
    val a: A
  }
  object o extends T {
    type A = u.type
    val a: A = u
  }
  val program = {
    val x: u.type = o.a
    val t: T = o
    t
  }
}
