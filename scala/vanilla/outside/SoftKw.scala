import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-13, a soft keyword as a name (the parser)
// from: notes-scala-xv2/refute/hand/SoftKw.scala, refute-stage3 N7
object SoftKw {
  val program =
    (open: Any) =>
      open
}
