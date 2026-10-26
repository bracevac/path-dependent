import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, `this.C` where the inner refinement declares no C (rule 5)
// from: notes-scala-xv0/scalac-g3/NestRefThis.scala, refute-d3 NestRefThis
object NestRefThis {
  val program =
    (p: { type C = Any; val b: { type D = Any; val get: this.C } }) => // error
      p
}
