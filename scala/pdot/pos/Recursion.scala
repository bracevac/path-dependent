import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d2/sc/M28_Recursion.scala, d2 M28_Recursion
object Recursion {
  object loop {
    def go(u: Any): Any = loop.go(u) // warn
  }
  val program = loop
}
