import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-10 rule 1, a statement on the line of its `{`
// from: notes-scala-xv2/probe-hand/LayR.scala, a probe of the XV2 groups file
object LayR {
  val program = (y: Any) => { val x = y
    x
  }
}
