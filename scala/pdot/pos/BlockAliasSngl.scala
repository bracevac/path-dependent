import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-refute-d2/sc/S01_BlockAliasSngl.scala, refute-d2 S01_BlockAliasSngl
object BlockAliasSngl {
  object core { type A = Any }
  val program = {
    val c = core
    (q: c.type) => (q: core.type)
  }
}
