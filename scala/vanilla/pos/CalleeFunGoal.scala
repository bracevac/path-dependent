import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.CalleeFunGoalSrc
object CalleeFunGoal {
  val program =
    (g: { val a: Any } => Any) => {
      val h: { val a: Any; val b: Any } => Any = (x: { val a: Any; val b: Any }) => g(x)
      h
    }
}
