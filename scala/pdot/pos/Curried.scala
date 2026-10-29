import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d2/sc/M12_Curried.scala, d2 M12_Curried
object Curried {
  object q { type B = Any }
  def f(x: { type B })(y: x.B): x.B = y
  val program = f(q)(q)
}
