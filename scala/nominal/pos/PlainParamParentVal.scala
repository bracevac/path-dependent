import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p2, review r3 of Priority 2, probes X50, X54, X57, repair 4 probes Y01, Y02, Y04, Y09, a plain parameter of a subclass beside a val of its parent of the same name
object PlainParamParentVal {
  object o { type S = Any }
  abstract class E { val w: { type S } }
  abstract class D1(w: { type S = Any }) extends E { type T = w.S }
  abstract class C1(x: D1) { type U = x.T }
  abstract class D2(w: { type S = Any }) extends E { type T = this.w.S }
  abstract class C2(x: D2) { type U = x.T }
  abstract class E3 { val w: { type S = Any }; type T = w.S }
  abstract class D3(w: { type S }) extends E3
  abstract class C3(x: D3) { type U = x.T }
  abstract class D4(w: { type S = Any }) extends E
  abstract class C4(val x: D4) { type U = x.w.S }
  abstract class D5(w: o.type) extends E
  abstract class C5(val x: D5) { type U = x.w.S }
  val program = (d: D4) => d.w
}
