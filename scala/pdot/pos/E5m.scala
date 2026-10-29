import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d2/sc/M23_E5m.scala, d2 M23_E5m
object E5m {
  object x {
    type C = { val incr: this.type } // warn
    type D = x.C & { val decr: this.type } // warn
    def d(u: Any): x.D = new Object { o =>
      val incr: o.type = o
      val decr: o.type = o
    }
  }
  val program = {
    val z = x.d(x)
    z.incr.decr
  }
}
