import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.E1ssrc
object E1s {
  val program =
    (x: { type A >: Any <: Nothing }) => {
      val y: { type B = { val a: Any } } = {
        val u: x.A = {
          val t: Any = x
          t
        }
        u
      }
      y
    }
}
