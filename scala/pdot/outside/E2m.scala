import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-Y, illegal cyclic type reference (scalac E140)
// from: notes-pdot-frontend/scratch-d2/sc/M31_E2m.scala, d2 M31_E2m
object E2m {
  object z {
    object c { type A = z.B } // error
    type B = z.c.A
  }
  val program = z
}
