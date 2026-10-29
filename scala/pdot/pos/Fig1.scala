import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/sc/C01Fig1.scala, d3 C01Fig1
object Fig1 {
  object dotty {
    object core {
      object types {
        type Type = Any
        type TypeRef = core.types.Type & { val symb: core.symbols.Symbol }
      }
      object symbols {
        type Symbol = { val tpe: core.types.Type }
      }
    }
  }
  val program = (r: dotty.core.types.TypeRef) => (r.symb.tpe: dotty.core.types.Type)
}
