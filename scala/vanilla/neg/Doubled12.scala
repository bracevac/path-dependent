import scala.reflect.Selectable.reflectiveSelectable

// ours: limit
// same as: Frontend.Doubled12src
object Doubled12 {
  val program =
    (x0: { type A }) =>
      (x1: { type A = x0.A } & { type A = x0.A }) =>
        (x2: { type A = x1.A } & { type A = x1.A }) =>
          (x3: { type A = x2.A } & { type A = x2.A }) =>
            (x4: { type A = x3.A } & { type A = x3.A }) =>
              (x5: { type A = x4.A } & { type A = x4.A }) =>
                (x6: { type A = x5.A } & { type A = x5.A }) =>
                  (x7: { type A = x6.A } & { type A = x6.A }) =>
                    (x8: { type A = x7.A } & { type A = x7.A }) =>
                      (x9: { type A = x8.A } & { type A = x8.A }) =>
                        (x10: { type A = x9.A } & { type A = x9.A }) =>
                          (x11: { type A = x10.A } & { type A = x10.A }) =>
                            (x12: { type A = x11.A } & { type A = x11.A }) =>
                              (y: x12.A) => {
                                val r: { val a: Any } = y // error
                                r
                              }
}
