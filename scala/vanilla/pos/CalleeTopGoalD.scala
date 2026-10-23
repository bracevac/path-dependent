import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.CalleeTopGoalSrcD
object CalleeTopGoalD {
  val program =
    (g: { val a: Any } => Any) => {
      val h: Any = x => g(x)
      h
    }
}
