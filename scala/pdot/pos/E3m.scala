import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d2/sc/M24_E3m.scala, d2 M24_E3m
object E3m {
  object dotty {
    object core {
      object types {
        type Tpe = Any
        type TypeRef = types.Tpe & { val symb: core.symbols.Symbol }
        def typeRef(s: core.symbols.Symbol): types.TypeRef = new Object {
          val symb: s.type = s
        }
      }
      object symbols {
        type Symbol = { val tpe: core.types.Tpe }
        def symbol(u: core.types.Tpe): symbols.Symbol = new Object {
          val tpe: u.type = u
        }
      }
    }
  }
  val program = {
    val s = dotty.core.symbols.symbol(dotty)
    dotty.core.types.typeRef(s)
  }
}
