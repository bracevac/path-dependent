import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-AN, an anonymous class is outside the subset
// from: notes-nominal/scratch-d1/sc/AnonTrait.scala, d1 AnonTrait
object AnonTrait {
  trait T { def m(u: Any): Any }
  val program = {
    val t: T = new T { def m(u: Any): Any = u }
    t.m(t)
  }
}
