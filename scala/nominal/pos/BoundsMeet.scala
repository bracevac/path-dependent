import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-refute-d1/sc/BoundsMeet.scala, refute-d1 BoundsMeet
object BoundsMeet {
  trait A0
  trait B0
  trait L { type X <: A0 }
  trait R { type X <: B0 }
  class C extends L with R
  val program = (c: C) => (x: c.X) => (x: A0 & B0)
}
