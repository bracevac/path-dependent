import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-OE, an object that extends a class or trait is outside the subset
// from: notes-nominal/scratch-d1/sc/ObjExtends.scala, d1 ObjExtends
object ObjExtends {
  trait T { def m(u: Any): Any }
  object o extends T { def m(u: Any): Any = u }
  val program = o.m(o)
}
