import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-refute-d3/sc/R05ObjAgainstAlias.scala, refute-d3 R05ObjAgainstAlias
object ObjAgainstAlias {
  object q {
    type B = Any
  }
  object r {
    type A = { val a: { type B } }
  }
  object o {
    val a: q.type = q
  }
  val program = (o: r.A)
}
