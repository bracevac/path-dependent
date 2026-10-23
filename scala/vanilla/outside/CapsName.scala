import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-13, `caps` as a name, which Scala reads as the package of `caps.any` (rule 7)
// from: notes-scala-xv2/refute/hand/CapsName.scala, refute-stage3 R2
object CapsName {
  val program =
    (caps: Any) =>
      caps
}
