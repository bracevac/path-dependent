import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.AliasSrcD
object AliasD {
  val program =
    (y: { type A = Any => Any }) => {
      val f: y.A = x => x
      f
    }
}
