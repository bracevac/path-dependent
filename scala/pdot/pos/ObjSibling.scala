import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/sc/M03ObjNestedSibling.scala, d3 M03ObjNestedSibling
object ObjSibling {
  object core {
    object types {
      type Type = Any
    }
    object symbols {
      type Symbol = { val tpe: types.Type }
    }
  }
  val program = (s: core.symbols.Symbol) => s.tpe
}
