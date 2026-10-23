import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.CalleeFunGoalSrcD
object CalleeFunGoalD {
  val program =
    (g: { val a: Any } => Any) => {
      val h: { val a: Any; val b: Any } => Any = x => g(x)
      h
    }
}
