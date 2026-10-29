import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-pdot-frontend/scratch-d2/sc/M40_RecNoType.scala, d2 M40_RecNoType
object RecNoType {
  object loop {
    def go(u: Any) = loop.go(u) // error
  }
  val program = loop
}
