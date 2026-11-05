import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p2, review r1 of Priority 2, probe R25, repair 2 probes S01, S09, S10, S59, an alias of an object, where nothing stands for the parameter
object PlainParamAliasObject {
  object o { type S = Any; type T = this.S; type R = { type V = Any } }
  object p { object m { type T = Any } }
  type Q = { type V = Any }
  abstract class C1(x: o.type) { type U = x.T }
  abstract class C2(x: o.R) { type U = x.V }
  abstract class C3(x: Q) { type U = x.V }
  abstract class C4(x: p.type) { type U = x.m.T }
  val program = PlainParamAliasObject
}
