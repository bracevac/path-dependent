import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-refute-d1/sc/AliasRedef.scala, refute-d1 AliasRedef
object AliasRedef {
  trait T { type L = Any }
  class C extends T { type L = Any }
  val program = new C
}
