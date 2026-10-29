import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d1/sc/ModAlias.scala, d1 S/sc/ModAlias
object ModAlias {
  object core {
    object types {
      type Type = { type Name }
    }
    object symbols {
      type Symbol = { val tpe: core.types.Type }
    }
  }
  val program = {
    val c: core.type = core
    (s: c.symbols.Symbol) => (t: c.types.Type) => (u: t.type) => (n: u.Name) => (n: t.Name)
  }
}
