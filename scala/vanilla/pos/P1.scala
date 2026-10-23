import scala.reflect.Selectable.reflectiveSelectable

// from: Frontend.P1src through toScalaWith true (D-12)
object P1 {
  val program =
    (f: (y: { val b: Any; val v: Any; type A <: { val a: Any } }) => y.A) => {
      val g: { val b: Any; val v: Any; type A <: { val a: Any } } => { val a: Any } = f
      g
    }
}
