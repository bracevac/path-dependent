import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/sc/G01DepFnDomain.scala, d3 G01DepFnDomain
object DepDomain {
  object core {
    object types {
      type T = { val v: Any }
    }
  }
  val program = {
    val f = (x: { val types: { type T } }) => x
    f(core)
  }
}
