import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.CalleeTopGoalSrc
object CalleeTopGoal {
  val program =
    (g: { val a: Any } => Any) => {
      val h: Any = (x: { val a: Any }) => g(x)
      h
    }
}
