import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-refute-d3/sc/R20KeepNestedObj.scala, refute-d3 R20KeepNestedObj
object KeepNestedObj {
  object o {
    object a {
      type A = Any
    }
  }
  val program = (x: o.a.type) => {
    val y = x
    (y: o.a.type)
  }
}
