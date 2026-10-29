import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-pdot-frontend/scratch-d2/sc/M42_LamNoType.scala, d2 M42_LamNoType
object LamNoType {
  val program = {
    val f = x => x // error
    f
  }
}
