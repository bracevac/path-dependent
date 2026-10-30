import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-AN, an anonymous class is outside the subset
// from: notes-nominal/scratch-scout/sc/S13NewTraitRefinement.scala, scout S13NewTraitRefinement, reshaped: Int and String replaced by u.type and w.type, `def get` given a parameter, the wrapper fields moved into program
object NewTraitRefinement {
  object u { type T = Any }
  object w { type T = Any }
  trait T {
    type A
    val a: A
    def get(x: Any): A
  }
  val program = {
    val t = new T { type A = u.type; val a: A = u; def get(x: Any): A = a }
    val r: u.type = t.get(u)
    val t2: T = new T { type A = w.type; val a: A = w; def get(x: Any): A = a }
    val v: t2.A = t2.get(u)
    v
  }
}
