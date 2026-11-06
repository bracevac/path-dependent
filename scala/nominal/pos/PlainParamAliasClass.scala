import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p2, review r1 of Priority 2, probes R05, R06, repair 2 probes S07, S48, S66, an alias of a class, read in its body on the path
object PlainParamAliasClass {
  class D { type T = Any }
  class E extends D
  class F(val w: { type S = Any }) { type T = w.S }
  abstract class G { val w: { type S = Any }; type T = w.S }
  abstract class C1(x: D) { type U = x.T }
  abstract class C2(x: E) { type U = x.T }
  abstract class C3(x: F) { type U = x.T }
  abstract class C4(x: G) { type U = x.T }
  abstract class C5(z: { type S = Any }, x: C5) { type U = x.T; type T = z.S }
  val program = PlainParamAliasClass
}
