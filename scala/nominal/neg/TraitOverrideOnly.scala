import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d3/sc/K13TraitOverrideOnly.scala, d3 K13TraitOverrideOnly
object TraitOverrideOnly {
  object u { type T = Any }
  trait T {
    def get(x: Any): u.type
  }
  trait U extends T {
    def get(x: Any): Any // error
  }
  val program = u
}
