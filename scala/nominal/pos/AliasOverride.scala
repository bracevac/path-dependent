import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-refute-d1/sc/AliasOverride.scala, refute-d1 AliasOverride
object AliasOverride {
  trait T { type L = Any }
  class C extends T { override type L = Any }
  val program = new C
}
