import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/sc/D01AliasObjInfer.scala, d3 D01AliasObjInfer
object AliasObj {
  object core {
    object types {
      type T = { val v: Any }
    }
  }
  val program = {
    val c = core
    (t: c.types.type) => (t: core.types.type)
  }
}
