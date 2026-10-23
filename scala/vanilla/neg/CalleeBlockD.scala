import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.CalleeBlockSrcD
object CalleeBlockD {
  val program =
    (g: Any => Any) => {
      val h =
        x => { // error
          val z = g(x)
          z
        }
      h
    }
}
