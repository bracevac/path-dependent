import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p2, repair 2 probe S72HeadThisOuter, review r4 probes Z45, Z70, repair 5 probes A02, A05, A10, the type of a parameter of another class read in that class's head
object PlainParamAliasHeadName {
  type R = Any
  abstract class D(val w: { type S = R }) { type R }
  abstract class C(x: D) {
    type U = x.w.S
  }
  object o { type R = { type S = Any } }
  object oo { type R = { type S } }
  abstract class E2 { val o: oo.type }
  abstract class D2(val w: o.R) extends E2
  abstract class C2(x: D2) { type U = x.w.S }
  abstract class D3(val a: { type S = Any }, val w: { type S = a.S })
  abstract class C3(x: D3) { type U = x.w.S }
  abstract class D4(val w: this.o.R) { val o: oo.type }
  abstract class C4(x: D4) { type U = x.w.S }
  abstract class D5(p: o.R) { val o: oo.type; type T = p.S }
  abstract class C5(x: D5) { type U = x.T }
  abstract class E6(val w: o.R) { val o: oo.type }
  abstract class D6(q: o.R) extends E6(q)
  abstract class C6(x: D6) { type U = x.w.S }
  val program = PlainParamAliasHeadName
}
