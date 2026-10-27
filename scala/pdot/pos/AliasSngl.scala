import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/sc/A10AliasValSngl.scala, d3 A10AliasValSngl
object AliasSngl {
  val program = (x: { type B }) => {
    val y: x.type = x
    (z: y.B) => (z: x.B)
  }
}
