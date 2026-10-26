import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.E4src
object E4 {
  val program =
    (x: { type B >: { type A } <: { type A >: { val a: Any } } }) =>
      (w: { type A }) =>
        (n: { val a: Any }) => {
          val g = (y: w.A) => y
          g(n) // error
        }
}
