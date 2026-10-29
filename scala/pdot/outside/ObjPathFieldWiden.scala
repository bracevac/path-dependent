import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-V, a field that holds a path is an alias in pDOT: write `val a: p.type = p`
// from: notes-pdot-frontend/scratch-d1/sc/ObjPathFieldWiden.scala, d1 S/sc/ObjPathFieldWiden, reshaped: the object moved out of the block into the stem (R-O), the field typed `{ type A }` and asked at p.type, so R-S does not apply too
object ObjPathFieldWiden {
  object p { type A = Any }
  object o {
    val c: { type A } = p
  }
  val program = (o.c: p.type) // error
}
