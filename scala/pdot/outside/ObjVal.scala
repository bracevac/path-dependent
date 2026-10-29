import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-L, a member that holds an object literal is a nested `object`
// from: notes-pdot-frontend/scratch-d1/sc/ObjVal.scala, d1 S/sc/ObjVal, reshaped: the second val and the selection o.a.A dropped, the field asked at the literal's own type instead, so R-S does not apply too
object ObjVal {
  object o {
    val a: { type A } = new Object { type A = Any }
  }
  val program = (o.a: { type A = Any }) // error
}
