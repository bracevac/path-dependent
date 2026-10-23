import Coercions.Frontend.Scala
import Coercions.Frontend.Examples

/-!
# Tests of the Scala translation

The checks of `Scala.lean`.  The translation is checked in the kernel, one
example per row of the mapping and one per refusal, on trees written by hand.
The comment above each example is the Scala text the tree stands for.  Every
position is `1:1` except at the node a refusal names.

`outcome` is checked by `#eval expect` on Scala texts.  Each text is a string
literal copied verbatim from a fixture under `notes-scala-xv1/`, and the
fixture's path is in its docstring.  The texts of `j/` are the judge's
programs J1, J2 and J4 written as Scala, and their outcomes are the judge's
verdicts, printed with names.  The texts of `refuse/` are refused by the
translation and not by the reader, and `LayB` by the reader.  For each text of
`j/`, the term and the table also meet the two side conditions under which
resolution is total (`STm.Scoped`, `STm.LabelsIn`).

The member check of S-17 is checked in the kernel on `dot%` programs with the
table `exampleTable`, by `#eval expect` on every example program of the front
end with its own table, and through `outcome` on the four texts of `j/` that
probe it.  scalac refuses three of them with E008 and compiles the fourth.

The printers are checked by round trips: in the kernel on seven terms and
three refusals, and by `#eval expect` on every example program, on the fill of
every example program that compiles, and on the reading of each text of `j/`.

No test reads a file.  The kernel checks on the bytes of the fixtures are
probes under `notes-scala-xv1/`.
-/

namespace Frontend.Scala.Tests

/-! ## Helpers -/

/-- The position of every node that no refusal names. -/
def q : ScalaSyntax.Pos := ⟨1, 1⟩

/-- A vanilla program with the written type `ty` and the right side `body`. -/
def prog (ty : Option ScalaSyntax.Ty) (body : ScalaSyntax.Tm) : ScalaSyntax.Program :=
  { imports := [(q, vanillaImportName)], name := "T", prelude := [], params := none, ty, body }

/-- Whether the translation refused with the message `m` at `p`. -/
def refuses (r : Except ScalaSyntax.Err STm) (p : ScalaSyntax.Pos) (m : String) : Bool :=
  match r with
  | .error e => decide (e = ⟨p, m⟩)
  | .ok _ => false

/-- The refinement `{ val a: Any }`. -/
def recA : ScalaSyntax.Ty := .refine q (.val q "a" (.any q) .nil)

/-- The refinement `{ type A }`. -/
def recTA : ScalaSyntax.Ty := .refine q (.typ q "A" none none .nil)

/-! ## The mapping, one example per row -/

-- `(x: Any) => x`
example : (ofScala (prog none (.lam q "x" (some (.any q)) (.var q "x")))).toOption =
    some (.lam "x" (some .top) (.var "x")) := by decide +kernel

-- `(x: Nothing) => x`
example : (ofScala (prog none (.lam q "x" (some (.nothing q)) (.var q "x")))).toOption =
    some (.lam "x" (some .bot) (.var "x")) := by decide +kernel

-- `(x: { type A }) => (y: x.A) => y`
example : (ofScala (prog none (.lam q "x" (some recTA)
      (.lam q "y" (some (.sel q (.var q "x") "A")) (.var q "y"))))).toOption =
    some (.lam "x" (some (.typ "A" .bot .top)) (.lam "y" (some (.sel "x" "A")) (.var "y"))) := by
  decide +kernel

-- `(x: { type A; val a: this.A }) => x`: `this` at the refinement's level gives a `μ`.
example : (ofScala (prog none (.lam q "x"
      (some (.refine q (.typ q "A" none none (.val q "a" (.sel q (.this q) "A") .nil))))
      (.var q "x")))).toOption =
    some (.lam "x" (some (.mu "this" (.and (.typ "A" .bot .top) (.fld "a" (.sel "this" "A")))))
      (.var "x")) := by decide +kernel

-- `(x: { type A; type B; val a: Any }) => x`: no `this`, no `μ`, a right-nested `∧`.
example : (ofScala (prog none (.lam q "x"
      (some (.refine q (.typ q "A" none none (.typ q "B" none none (.val q "a" (.any q) .nil)))))
      (.var q "x")))).toOption =
    some (.lam "x" (some (.and (.typ "A" .bot .top) (.and (.typ "B" .bot .top) (.fld "a" .top))))
      (.var "x")) := by decide +kernel

-- `(x: { type A >: { val a: Any } }) => x`
example : (ofScala (prog none (.lam q "x"
      (some (.refine q (.typ q "A" (some recA) none .nil))) (.var q "x")))).toOption =
    some (.lam "x" (some (.typ "A" (.fld "a" .top) .top)) (.var "x")) := by decide +kernel

-- `(x: { type A = Any }) => x`
example : (ofScala (prog none (.lam q "x"
      (some (.refine q (.alias q "A" (.any q) .nil))) (.var q "x")))).toOption =
    some (.lam "x" (some (.typ "A" .top .top)) (.var "x")) := by decide +kernel

-- `(x: { type A <: Any }) => x`
example : (ofScala (prog none (.lam q "x"
      (some (.refine q (.typ q "A" none (some (.any q)) .nil))) (.var q "x")))).toOption =
    some (.lam "x" (some (.typ "A" .bot .top)) (.var "x")) := by decide +kernel

-- `(x: { type A } & { type B } & { val a: Any }) => x`: the tree already nests left.
example : (ofScala (prog none (.lam q "x"
      (some (.and (.and recTA (.refine q (.typ q "B" none none .nil))) recA))
      (.var q "x")))).toOption =
    some (.lam "x" (some (.and (.and (.typ "A" .bot .top) (.typ "B" .bot .top)) (.fld "a" .top)))
      (.var "x")) := by decide +kernel

-- `(f: (x: { type A }) => x.A) => f`
example : (ofScala (prog none (.lam q "f"
      (some (.fn q (some "x") recTA .fat (.sel q (.var q "x") "A"))) (.var q "f")))).toOption =
    some (.lam "f" (some (.all "x" (.typ "A" .bot .top) (.sel "x" "A"))) (.var "f")) := by
  decide +kernel

-- `(f: Any => Nothing) => f`
example : (ofScala (prog none (.lam q "f"
      (some (.fn q none (.any q) .fat (.nothing q))) (.var q "f")))).toOption =
    some (.lam "f" (some (.all "_" .top .bot)) (.var "f")) := by decide +kernel

-- `(x: Any) => x`, a typed parameter
example : (ofScala (prog none (.lam q "x" (some (.any q)) (.var q "x")))).toOption =
    some (.lam "x" (some .top) (.var "x")) := by decide +kernel

-- `x => x`, an untyped parameter (`(x) => x` is the same tree)
example : (ofScala (prog none (.lam q "x" none (.var q "x")))).toOption =
    some (.lam "x" none (.var "x")) := by decide +kernel

-- `(f: Any) => (x: { val a: Any }) => f(x.a)`
example : (ofScala (prog none (.lam q "f" (some (.any q)) (.lam q "x" (some recA)
      (.app (.var q "f") (.sel (.var q "x") q "a")))))).toOption =
    some (.lam "f" (some .top) (.lam "x" (some (.fld "a" .top))
      (.app (.var "f") (.proj (.var "x") "a")))) := by decide +kernel

-- `(x: Any) => (x: Any)`
example : (ofScala (prog none (.lam q "x" (some (.any q)) (.asc q (.var q "x") (.any q))))).toOption =
    some (.lam "x" (some .top) (.asc (.var "x") .top)) := by decide +kernel

-- `(y: Any) => { val x = y; x }`
example : (ofScala (prog none (.lam q "y" (some (.any q))
      (.block q (.val q "x" none (.var q "y") (.last (.var q "x"))))))).toOption =
    some (.lam "y" (some .top) (.«let» "x" none (.var "y") (.var "x"))) := by decide +kernel

-- `(y: Any) => { y }`
example : (ofScala (prog none (.lam q "y" (some (.any q)) (.block q (.last (.var q "y")))))).toOption =
    some (.lam "y" (some .top) (.var "y")) := by decide +kernel

-- `(y: Any) => { val x: Any = y; y }`: the written type annotates `x` (S-11).
example : (ofScala (prog none (.lam q "y" (some (.any q))
      (.block q (.val q "x" (some (.any q)) (.var q "y") (.last (.var q "y"))))))).toOption =
    some (.lam "y" (some .top) (.«let» "x" none (.asc (.var "y") .top) (.var "y"))) := by
  decide +kernel

-- `(y: Any) => { val x: Any = y; x }`: a block that returns its last `val`.
example : (ofScala (prog none (.lam q "y" (some (.any q))
      (.block q (.val q "x" (some (.any q)) (.var q "y") (.last (.var q "x"))))))).toOption =
    some (.lam "y" (some .top) (.«let» "x" (some .top) (.var "y") (.var "x"))) := by
  decide +kernel

-- `(n: Any) => (new Object { z => val a = n }: { val a: Any })`
example : (ofScala (prog none (.lam q "n" (some (.any q))
      (.asc q (.lit q (some "z") (.val q "a" none (.var q "n") .nil)) recA)))).toOption =
    some (.lam "n" (some .top) (.«let» "ℓ" none (.obj "z" none (.trm "a" none (.var "n")))
      (.asc (.var "ℓ") (.fld "a" .top)))) := by decide +kernel

-- `(n: Any) => (new Object { type A = Any; val a: this.A = n; val b = n }: { val a: Any })`
example : (ofScala (prog none (.lam q "n" (some (.any q))
      (.asc q (.lit q none (.typ q "A" (.any q) (.val q "a" (some (.sel q (.this q) "A")) (.var q "n")
        (.val q "b" none (.var q "n") .nil)))) recA)))).toOption =
    some (.lam "n" (some .top) (.«let» "ℓ" none
      (.obj "this" none (.and (.typ "A" .top)
        (.and (.trm "a" (some (.sel "this" "A")) (.var "n")) (.trm "b" none (.var "n")))))
      (.asc (.var "ℓ") (.fld "a" .top)))) := by decide +kernel

-- `val program: Any => Any = x => x`
example : (ofScala (prog (some (.fn q none (.any q) .fat (.any q))) (.lam q "x" none (.var q "x")))).toOption =
    some (.asc (.lam "x" none (.var "x")) (.all "_" .top .top)) := by decide +kernel

-- `(n: Any) => { val o: { val a: Any } = new Object { val a = n }; o }`
example : (ofScala (prog none (.lam q "n" (some (.any q))
      (.block q (.val q "o" (some recA) (.lit q none (.val q "a" none (.var q "n") .nil))
        (.last (.var q "o"))))))).toOption =
    some (.lam "n" (some .top) (.«let» "o" (some (.fld "a" .top))
      (.«let» "ℓ" none (.obj "this" none (.trm "a" none (.var "n"))) (.asc (.var "ℓ") (.fld "a" .top)))
      (.var "o"))) := by decide +kernel

-- `val program: { val a: Any } = new Object { val a: Any = this.a }`
example : (ofScala (prog (some recA)
      (.lit q none (.val q "a" (some (.any q)) (.sel (.this q) q "a") .nil)))).toOption =
    some (.«let» "ℓ" none (.obj "this" none (.trm "a" (some .top) (.proj (.var "this") "a")))
      (.asc (.var "ℓ") (.fld "a" .top))) := by decide +kernel

/-! ## Refusals, at the node they name -/

-- `(f: Any -> Any) => f`, the arrow at 2:9
example : refuses (ofScala (prog none (.lam q "f"
      (some (.fn ⟨2, 9⟩ none (.any q) (.thin none) (.any q))) (.var q "f")))) ⟨2, 9⟩
    "`->` is capture syntax, outside the vanilla subset: write `=>`" = true := by decide +kernel

-- `(x: Any^) => x`, the `^` at 2:9
example : refuses (ofScala (prog none (.lam q "x" (some (.capt ⟨2, 9⟩ (.any q) none)) (.var q "x"))))
    ⟨2, 9⟩ "`^` is capture syntax, outside the vanilla subset" = true := by decide +kernel

-- `(x: { type C^ }) => x`, `C` at 2:9
example : refuses (ofScala (prog none (.lam q "x"
      (some (.refine q (.cap ⟨2, 9⟩ "C" none none .nil))) (.var q "x")))) ⟨2, 9⟩
    "the capture member `C^` is outside the vanilla subset" = true := by decide +kernel

-- `val program: { val a: Any } = new Object { type C^ = {}; val a = this.a }`, `C` at 2:9
example : refuses (ofScala (prog (some recA)
      (.lit q none (.cap ⟨2, 9⟩ "C" [] (.val q "a" none (.sel (.this q) q "a") .nil))))) ⟨2, 9⟩
    "the capture member `C^` is outside the vanilla subset" = true := by decide +kernel

-- a prelude line `class Cap extends caps.SharedCapability`, `Cap` at 2:9
example : refuses (ofScala { prog none (.lam q "x" (some (.any q)) (.var q "x")) with
      prelude := [.capClass ⟨2, 9⟩ "Cap"] }) ⟨2, 9⟩
    "a prelude is outside the vanilla subset" = true := by decide +kernel

-- `def program(k: Cap^) = …`, `k` at 2:5
example : refuses (ofScala { prog none (.lam q "x" (some (.any q)) (.var q "x")) with
      params := some [(⟨2, 5⟩, "k", "Cap")] }) ⟨2, 5⟩
    "`def program` is outside the vanilla subset: write `val program`" = true := by decide +kernel

-- no import, at 1:1
example : refuses (ofScala { prog none (.lam q "x" (some (.any q)) (.var q "x")) with
      imports := [] }) ⟨1, 1⟩
    "the vanilla header is the one line `import scala.reflect.Selectable.reflectiveSelectable`" =
    true := by decide +kernel

-- a second import, at 2:8
example : refuses (ofScala { prog none (.lam q "x" (some (.any q)) (.var q "x")) with
      imports := [(q, vanillaImportName), (⟨2, 8⟩, vanillaImportName)] }) ⟨2, 8⟩
    "the vanilla header is the one line `import scala.reflect.Selectable.reflectiveSelectable`" =
    true := by decide +kernel

-- another first import, at 1:8
example : refuses (ofScala { prog none (.lam q "x" (some (.any q)) (.var q "x")) with
      imports := [(⟨1, 8⟩, "language.experimental.captureChecking"), (q, vanillaImportName)] })
    ⟨1, 8⟩
    "the vanilla header is the one line `import scala.reflect.Selectable.reflectiveSelectable`" =
    true := by decide +kernel

-- `val program = this`, `this` at 2:9
example : refuses (ofScala (prog none (.this ⟨2, 9⟩))) ⟨2, 9⟩
    "`this` outside every refinement and object literal names the wrapper object in Scala" =
    true := by decide +kernel

-- `(x: this.A) => x`, `this` at 2:9
example : refuses (ofScala (prog none (.lam q "x" (some (.sel q (.this ⟨2, 9⟩) "A")) (.var q "x"))))
    ⟨2, 9⟩
    "`this` outside every refinement and object literal names the wrapper object in Scala" =
    true := by decide +kernel

-- `val program = new Object { val a = this.a }`, `new` at 2:9
example : refuses (ofScala (prog none (.lit ⟨2, 9⟩ none (.val q "a" none (.sel (.this q) q "a") .nil))))
    ⟨2, 9⟩ "an object literal needs a written type: scalac types it as Object" = true := by
  decide +kernel

-- `(x: {}) => x`, `{` at 2:9
example : refuses (ofScala (prog none (.lam q "x" (some (.refine ⟨2, 9⟩ .nil)) (.var q "x")))) ⟨2, 9⟩
    "an empty refinement is outside the subset" = true := by decide +kernel

-- `val program: Any = new Object {}`, `new` at 2:9
example : refuses (ofScala (prog (some (.any q)) (.lit ⟨2, 9⟩ none .nil))) ⟨2, 9⟩
    "an empty object literal is outside the subset" = true := by decide +kernel

-- The first refusal in the order of the text wins: `(x: Any^) -> Any` refuses the `^` at 2:5.
example : refuses (ofScala (prog none (.lam q "f"
      (some (.fn ⟨2, 9⟩ none (.capt ⟨2, 5⟩ (.any q) none) (.thin none) (.any q))) (.var q "f"))))
    ⟨2, 5⟩ "`^` is capture syntax, outside the vanilla subset" = true := by decide +kernel

/-! ## The label table -/

-- Each name within its sort, in the order given.
example : tableOf 0 0 [("A", true), ("a", false), ("B", true), ("b", false)] =
    [("A", .typ 0), ("a", .trm 0), ("B", .typ 1), ("b", .trm 1)] := by decide +kernel

/-! ## Outcomes of the fixtures -/

/-! ### The texts -/

/-- `notes-scala-xv1/j/J1ValSel.scala`. -/
def textJ1ValSel : String := "import scala.reflect.Selectable.reflectiveSelectable

object J1ValSel {
  val program = (x: { val a: Any }) => {
    val y: { val a: Any } = x
    y.a
  }
}
"

/-- `notes-scala-xv1/j/J1ValLast.scala`. -/
def textJ1ValLast : String := "import scala.reflect.Selectable.reflectiveSelectable

object J1ValLast {
  val program = (x: { val a: Any }) => {
    val y: { val a: Any } = x
    y
  }
}
"

/-- `notes-scala-xv1/j/J1Lit.scala`. -/
def textJ1Lit : String := "import scala.reflect.Selectable.reflectiveSelectable

object J1Lit {
  val program = (n: { val b: Any }) => (new Object {
    z =>
    val a = n
  }: { val a: { val b: Any } })
}
"

/-- `notes-scala-xv1/j/J1LitTyped.scala`. -/
def textJ1LitTyped : String := "import scala.reflect.Selectable.reflectiveSelectable

object J1LitTyped {
  val program = (n: { val b: Any }) => (new Object {
    z =>
    val a: { val b: Any } = n
  }: { val a: { val b: Any } })
}
"

/-- `notes-scala-xv1/j/J1X1.scala`. -/
def textJ1X1 : String := "import scala.reflect.Selectable.reflectiveSelectable

object J1X1 {
  val program = (x: Any) => (new Object {
    z =>
    type A = Any
    val a = x
  }: { val a: Any })
}
"

/-- `notes-scala-xv1/j/J1SA1.scala`. -/
def textJ1SA1 : String := "import scala.reflect.Selectable.reflectiveSelectable

object J1SA1 {
  val program = (x: Any) => (new Object {
    z =>
    val a = y => y
  }: { val a: Any => Any })
}
"

/-- `notes-scala-xv1/j/J1SelfSel.scala`. -/
def textJ1SelfSel : String := "import scala.reflect.Selectable.reflectiveSelectable

object J1SelfSel {
  val program = (x: Any) => (new Object {
    z =>
    type A = Any
    val a: z.A = x
  }: { type A; val a: this.A })
}
"

/-- `notes-scala-xv1/j/J2ValLit.scala`. -/
def textJ2ValLit : String := "import scala.reflect.Selectable.reflectiveSelectable

object J2ValLit {
  val program = (n: { val b: Any }) => {
    val o: { val a: { val b: Any } } = new Object {
      z =>
      val a = n
    }
    o.a
  }
}
"

/-- `notes-scala-xv1/j/J2RecUntyped.scala`. -/
def textJ2RecUntyped : String := "import scala.reflect.Selectable.reflectiveSelectable

object J2RecUntyped {
  val program: { val a: Any } = new Object {
    z =>
    val a = z.a
  }
}
"

/-- `notes-scala-xv1/j/J2RecTyped.scala`. -/
def textJ2RecTyped : String := "import scala.reflect.Selectable.reflectiveSelectable

object J2RecTyped {
  val program: { val a: Any } = new Object {
    z =>
    val a: Any = z.a
  }
}
"

/-- `notes-scala-xv1/j/J4E5.scala`. -/
def textJ4E5 : String := "import scala.reflect.Selectable.reflectiveSelectable

// E5: an object returned from a function and selected after a val.
object J4E5 {
  val program =
    (w: { type A = Any }) => {
      val f =
        (v: { type A = Any }) =>
          (new Object {
            val a = v
          }: { val a: v.A })
      val o = f(w)
      o.a
    }
}
"

/-- `notes-scala-xv1/j/J4E6Typed.scala`. -/
def textJ4E6Typed : String := "import scala.reflect.Selectable.reflectiveSelectable

object J4E6Typed {
  val program = (n: { val a: Any }) => (new Object {
    x =>
    type T = { val a: Any }
    val v: x.T = n
  }: { type T = { val a: Any }; val v: this.T })
}
"

/-- `notes-scala-xv1/j/J4E6Untyped.scala`. -/
def textJ4E6Untyped : String := "import scala.reflect.Selectable.reflectiveSelectable

object J4E6Untyped {
  val program = (n: { val a: Any }) => (new Object {
    x =>
    type T = { val a: Any }
    val v = n
  }: { type T = { val a: Any }; val v: this.T })
}
"

/-- `notes-scala-xv1/refuse/CapHat.scala`. -/
def textCapHat : String := "import scala.reflect.Selectable.reflectiveSelectable

object CapHat {
  val program = (x: Any^) => x
}
"

/-- `notes-scala-xv1/refuse/CapArrow.scala`. -/
def textCapArrow : String := "import scala.reflect.Selectable.reflectiveSelectable

object CapArrow {
  val program = (f: Any -> Any) => f
}
"

/-- `notes-scala-xv1/refuse/CapMember.scala`. -/
def textCapMember : String := "import scala.reflect.Selectable.reflectiveSelectable

object CapMember {
  val program = (x: { type C^ }) => x
}
"

/-- `notes-scala-xv1/refuse/CapImport.scala`. -/
def textCapImport : String := "import language.experimental.captureChecking
import scala.reflect.Selectable.reflectiveSelectable

object CapImport {
  val program = (x: Any) => x
}
"

/-- `notes-scala-xv1/refuse/Prelude.scala`. -/
def textPrelude : String := "import scala.reflect.Selectable.reflectiveSelectable

object Prelude {
  class Cap extends caps.SharedCapability
  val program = (x: Any) => x
}
"

/-- `notes-scala-xv1/refuse/NoImport.scala`. -/
def textNoImport : String := "object NoImport {
  val program = (x: Any) => x
}
"

/-- `notes-scala-xv1/refuse/TwoImports.scala`. -/
def textTwoImports : String := "import scala.reflect.Selectable.reflectiveSelectable
import scala.reflect.Selectable.reflectiveSelectable

object TwoImports {
  val program = (x: Any) => x
}
"

/-- `notes-scala-xv0/LayB.scala`. -/
def textLayB : String := "import scala.reflect.Selectable.reflectiveSelectable
// B: a more indented line that starts with '(' after a line that can end a statement.
object LayB {
  val program = (f: Any => { val a: Any }) => (w: Any) => {
    val r = f
      (w)
    r
  }
}
"

/-! ### The judge's programs -/

#eval expect ((outcome textJ1ValSel.toList).text == "ok : ∀(x : {a : ⊤}) ⊤")
  "outcome of j/J1ValSel.scala"

#eval expect ((outcome textJ1ValLast.toList).text == "ok : ∀(x : {a : ⊤}) {a : ⊤}")
  "outcome of j/J1ValLast.scala"

#eval expect ((outcome textJ1Lit.toList).text == "ok : ∀(x : {b : ⊤}) {a : {b : ⊤}}")
  "outcome of j/J1Lit.scala"

#eval expect ((outcome textJ1LitTyped.toList).text == "ok : ∀(x : {b : ⊤}) {a : {b : ⊤}}")
  "outcome of j/J1LitTyped.scala"

#eval expect ((outcome textJ1X1.toList).text == "ok : ∀(x : ⊤) {a : ⊤}")
  "outcome of j/J1X1.scala"

#eval expect ((outcome textJ1SA1.toList).text == "rejected: Missing parameter type")
  "outcome of j/J1SA1.scala"

#eval expect ((outcome textJ1SelfSel.toList).text == "ok : ∀(x : ⊤) μ(y. {A : ⊥ .. ⊤} ∧ {a : y.A})")
  "outcome of j/J1SelfSel.scala"

#eval expect ((outcome textJ2ValLit.toList).text == "ok : ∀(x : {b : ⊤}) {b : ⊤}")
  "outcome of j/J2ValLit.scala"

#eval expect ((outcome textJ2RecUntyped.toList).text == "rejected: Recursive value a needs type")
  "outcome of j/J2RecUntyped.scala"

#eval expect ((outcome textJ2RecTyped.toList).text == "ok : {a : ⊤}")
  "outcome of j/J2RecTyped.scala"

#eval expect ((outcome textJ4E5.toList).text == "ok : ∀(x : {A : ⊤ .. ⊤}) x.A")
  "outcome of j/J4E5.scala"

#eval expect ((outcome textJ4E6Typed.toList).text == "ok : ∀(x : {a : ⊤}) μ(y. {T : {a : ⊤} .. {a : ⊤}} ∧ {v : y.T})")
  "outcome of j/J4E6Typed.scala"

#eval expect ((outcome textJ4E6Untyped.toList).text == "ok : ∀(x : {a : ⊤}) μ(y. {T : {a : ⊤} .. {a : ⊤}} ∧ {v : y.T})")
  "outcome of j/J4E6Untyped.scala"

/-! ### Refusals of the translation, and one of the reader -/

#eval expect ((outcome textCapHat.toList).text ==
    "outside 4:24: `^` is capture syntax, outside the vanilla subset")
  "outcome of refuse/CapHat.scala"

#eval expect ((outcome textCapArrow.toList).text ==
    "outside 4:25: `->` is capture syntax, outside the vanilla subset: write `=>`")
  "outcome of refuse/CapArrow.scala"

#eval expect ((outcome textCapMember.toList).text ==
    "outside 4:28: the capture member `C^` is outside the vanilla subset")
  "outcome of refuse/CapMember.scala"

#eval expect ((outcome textCapImport.toList).text ==
    "outside 1:8: the vanilla header is the one line `import scala.reflect.Selectable.reflectiveSelectable`")
  "outcome of refuse/CapImport.scala"

#eval expect ((outcome textPrelude.toList).text ==
    "outside 4:9: a prelude is outside the vanilla subset")
  "outcome of refuse/Prelude.scala"

#eval expect ((outcome textNoImport.toList).text ==
    "outside 1:1: the vanilla header is the one line `import scala.reflect.Selectable.reflectiveSelectable`")
  "outcome of refuse/NoImport.scala"

#eval expect ((outcome textTwoImports.toList).text ==
    "outside 2:8: the vanilla header is the one line `import scala.reflect.Selectable.reflectiveSelectable`")
  "outcome of refuse/TwoImports.scala"

#eval expect ((outcome textLayB.toList).text ==
    "outside 6:7: a continuation line must follow one of = => -> ( { , : & <: >:")
  "outcome of notes-scala-xv0/LayB.scala"

/-! ### The side conditions of resolution

Every text of `j/` reads, and its term is closed and labelled by its own table,
so `resolveP` is total on it (D-2 of the groups file). -/

/-- Whether the characters read, and the term is scoped and labelled by the
table. -/
def covered (cs : List Char) : Bool :=
  match readProgram cs with
  | .ok (_, e, Λ) => STm.Scoped [] e && STm.LabelsIn Λ e
  | .error _ => false

#eval expect (covered textJ1ValSel.toList) "side conditions of j/J1ValSel.scala"
#eval expect (covered textJ1ValLast.toList) "side conditions of j/J1ValLast.scala"
#eval expect (covered textJ1Lit.toList) "side conditions of j/J1Lit.scala"
#eval expect (covered textJ1LitTyped.toList) "side conditions of j/J1LitTyped.scala"
#eval expect (covered textJ1X1.toList) "side conditions of j/J1X1.scala"
#eval expect (covered textJ1SA1.toList) "side conditions of j/J1SA1.scala"
#eval expect (covered textJ1SelfSel.toList) "side conditions of j/J1SelfSel.scala"
#eval expect (covered textJ2ValLit.toList) "side conditions of j/J2ValLit.scala"
#eval expect (covered textJ2RecUntyped.toList) "side conditions of j/J2RecUntyped.scala"
#eval expect (covered textJ2RecTyped.toList) "side conditions of j/J2RecTyped.scala"
#eval expect (covered textJ4E5.toList) "side conditions of j/J4E5.scala"
#eval expect (covered textJ4E6Typed.toList) "side conditions of j/J4E6Typed.scala"
#eval expect (covered textJ4E6Untyped.toList) "side conditions of j/J4E6Untyped.scala"

/-! ## The member check (S-17) -/

/-- The member check of `e` with the table `Λ`, when `e` compiles. -/
def checkMembers (Λ : LabelTable) (e : STm) : Option MemberCheck :=
  match compileE {} Λ e with
  | .ok ⟨a, _⟩ => some (members Λ e a)
  | .error _ => none

/-! ### In the kernel

`B` is `.typ 1` in `exampleTable`. -/

-- `(x: { type A }) => (y: x.B) => y`, the program of `j/Undecl.scala`.
example : checkMembers exampleTable (dot% λ(x : {A : ⊥ .. ⊤}). λ(y : x.B). y) =
    some (.undeclared (.typ 1)) := by decide +kernel

-- `(x: Any) => (y: x.B) => y`, the program of `j/UndeclAny.scala`.
example : checkMembers exampleTable (dot% λ(x : ⊤). λ(y : x.B). y) =
    some (.undeclared (.typ 1)) := by decide +kernel

-- The program of `j/UndeclVal.scala`: the `val` binds the type of its right side.
example : checkMembers exampleTable (dot% λ(x : {A : ⊥ .. ⊤}). let y = x in λ(z : y.B). z) =
    some (.undeclared (.typ 1)) := by decide +kernel

-- The program of `j/DeclVal.scala`.
example : checkMembers exampleTable (dot% λ(x : {A : ⊥ .. ⊤}). let y = x in λ(z : y.A). z) =
    some .ok := by decide +kernel

-- Selections on a function's argument, on a literal's self and on a field's type.
example : checkMembers exampleTable E5src = some .ok := by decide +kernel

example : checkMembers exampleTable E6src = some .ok := by decide +kernel

example : checkMembers exampleTable E8src = some .ok := by decide +kernel

-- A member three steps down a recursive type.
example : checkMembers exampleTable P1src = some .ok := by decide +kernel

example : checkMembers exampleTable P5src = some .ok := by decide +kernel

-- A member through an upper bound: `y : x.A` and `x.A <: {B : ⊥ .. ⊤}`.
example : checkMembers exampleTable
    (dot% λ(x : {A : ⊥ .. {B : ⊥ .. ⊤}}). λ(y : x.A). λ(z : y.B). z) = some .ok := by
  decide +kernel

-- P4's `s.B` names no member of its `μ`.
example : checkMembers exampleTable P4src = some (.undeclared (.typ 1)) := by decide +kernel

/-! ### Every example program

Each program with its own table, `labelsOfProgram`.  Those that compile are
96, and the member check refuses exactly one of them, P4. -/

/-- The example programs of the front end, every constant of type `STm` with
no argument, by module, then by name (`probe-examples`).  131 in all. -/
def examples : List (String × STm) :=
  -- `Resolve.lean`
  [("E10src", E10src), ("E1src", E1src), ("E2src", E2src), ("E2srcD", E2srcD), ("E2srcS", E2srcS),
   ("E3src", E3src), ("E4src", E4src), ("E5src", E5src), ("E5srcS", E5srcS), ("E6src", E6src),
   ("E6srcS", E6srcS), ("E7src", E7src), ("E7srcS", E7srcS), ("E8src", E8src), ("E8srcD", E8srcD),
   ("E9src", E9src), ("K1src", K1src), ("K1srcA", K1srcA)] ++
  -- `Typer.lean`
  [("A1src", A1src), ("B1src", B1src), ("E10tsrc", E10tsrc), ("E11src", E11src), ("E1ssrc", E1ssrc),
   ("E3ssrc", E3ssrc), ("Ginsrc", Ginsrc), ("Gsrc", Gsrc), ("LPsrc", LPsrc), ("P5src", P5src),
   ("R1src", R1src), ("R2src", R2src)] ++
  -- `Elab.lean`
  [("AliasRecSrcS", AliasRecSrcS), ("AliasSrc", AliasSrc), ("AliasSrcD", AliasSrcD),
   ("AmbSrcS", AmbSrcS), ("AndIncSrcD", AndIncSrcD), ("AndOneSrcD", AndOneSrcD),
   ("AndTopSrc", AndTopSrc), ("AndTopSrcD", AndTopSrcD), ("AndTwoSrc", AndTwoSrc),
   ("AndTwoSrcD", AndTwoSrcD), ("AscObjSrc", AscObjSrc), ("AscObjSrcS", AscObjSrcS),
   ("AscSrc", AscSrc), ("AscSrcD", AscSrcD), ("AscTopSrc", AscTopSrc), ("AscTopSrcS", AscTopSrcS),
   ("BareProjSrc", BareProjSrc), ("BareProjSrcS", BareProjSrcS), ("BareSrc", BareSrc),
   ("BareSrcS", BareSrcS), ("CalleeAndSrc", CalleeAndSrc), ("CalleeAndSrcD", CalleeAndSrcD),
   ("CalleeArgSrc", CalleeArgSrc), ("CalleeArgSrcD", CalleeArgSrcD),
   ("CalleeBlockSrcD", CalleeBlockSrcD), ("CalleeFunGoalSrc", CalleeFunGoalSrc),
   ("CalleeFunGoalSrcD", CalleeFunGoalSrcD), ("CalleeIncSrcD", CalleeIncSrcD),
   ("CalleeLetSrc", CalleeLetSrc), ("CalleeLetSrcD", CalleeLetSrcD),
   ("CalleeOtherSrcD", CalleeOtherSrcD), ("CalleeProjSrcD", CalleeProjSrcD),
   ("CalleeSelfSrcD", CalleeSelfSrcD), ("CalleeSrc", CalleeSrc), ("CalleeSrcD", CalleeSrcD),
   ("CalleeTopGoalSrc", CalleeTopGoalSrc), ("CalleeTopGoalSrcD", CalleeTopGoalSrcD),
   ("CalleeTopSrcD", CalleeTopSrcD), ("Cyc3SrcS", Cyc3SrcS), ("CycSrcS", CycSrcS),
   ("DomSrc", DomSrc), ("DomSrcD", DomSrcD), ("E11asrc", E11asrc), ("E11asrcA", E11asrcA),
   ("E11srcD", E11srcD), ("E2objSrc", E2objSrc), ("E2objSrcS", E2objSrcS), ("E5srcW", E5srcW),
   ("E6srcW", E6srcW), ("FwdSelfSrc", FwdSelfSrc), ("FwdSelfSrcS", FwdSelfSrcS), ("FwdSrc", FwdSrc),
   ("FwdSrcS", FwdSrcS), ("Id0SrcD", Id0SrcD), ("IdAscSrc", IdAscSrc), ("IdAscSrcD", IdAscSrcD),
   ("IdTopSrcD", IdTopSrcD), ("IncSrcD", IncSrcD), ("LetArgSrcD", LetArgSrcD),
   ("LowerSrcD", LowerSrcD), ("NoDomSrcS", NoDomSrcS), ("RecUSrcS", RecUSrcS), ("RecWSrc", RecWSrc),
   ("RecWSrcS", RecWSrcS), ("UpperSrcD", UpperSrcD), ("X1src", X1src), ("X1srcA", X1srcA),
   ("X2src", X2src), ("X2srcD", X2srcD), ("X3src", X3src), ("X3srcD", X3srcD), ("X5Src1", X5Src1),
   ("X5Src2", X5Src2), ("X5SrcS1", X5SrcS1), ("X5SrcS2", X5SrcS2)] ++
  -- `Examples.lean`
  [("AliasRecSrc", AliasRecSrc), ("AmbSrc", AmbSrc), ("AndIncSrc", AndIncSrc),
   ("AndOneSrc", AndOneSrc), ("AscMuSrc", AscMuSrc), ("AscMuSrcD", AscMuSrcD), ("BodySrc", BodySrc),
   ("BodySrcD", BodySrcD), ("Cyc3Src", Cyc3Src), ("CycSrc", CycSrc), ("Doubled12src", Doubled12src),
   ("Id0Src", Id0Src), ("IdTopSrc", IdTopSrc), ("IncSrc", IncSrc), ("LetArgSrc", LetArgSrc),
   ("LowerSrc", LowerSrc), ("MidSrc", MidSrc), ("MidSrcA", MidSrcA), ("NoDomSrc", NoDomSrc),
   ("P1src", P1src), ("P4src", P4src), ("PFsrc", PFsrc), ("StructSrc", StructSrc),
   ("StructSrcDS", StructSrcDS), ("UpperSrc", UpperSrc), ("X4src", X4src)]

/-- The names of the programs that compile, and of those the member check
refuses, from the member check of each program by name. -/
def sweepNames (r : List (String × Option MemberCheck)) : List String × List String :=
  (r.filterMap fun (n, m) => if m.isSome then some n else none,
   r.filterMap fun (n, m) => if m == some .ok || m == none then none else some n)

-- `labelsOfProgram` reads names by `String.toList`, so it stays in `#eval`.
#eval do
  let r := sweepNames (examples.map fun (n, e) => (n, checkMembers (labelsOfProgram e) e))
  expect (examples.length == 131) "131 example programs"
  expect (r.1.length == 96) "96 example programs compile"
  expect (r.2 == ["P4src"]) "the member check refuses P4src and no other example program"

/-! ### Through `outcome`

Each text is copied verbatim from its fixture.  scalac 3.8.4 refuses the first
three with E008, on lines 4, 4 and 6, and compiles the fourth (`j/*.out.txt`).
Our refusal sits at the selected member's name. -/

/-- `notes-scala-xv1/j/Undecl.scala`. -/
def textUndecl : String := "import scala.reflect.Selectable.reflectiveSelectable

object Undecl {
  val program = (x: { type A }) => (y: x.B) => y
}
"

/-- `notes-scala-xv1/j/UndeclAny.scala`. -/
def textUndeclAny : String := "import scala.reflect.Selectable.reflectiveSelectable

object UndeclAny {
  val program = (x: Any) => (y: x.B) => y
}
"

/-- `notes-scala-xv1/j/UndeclVal.scala`. -/
def textUndeclVal : String := "import scala.reflect.Selectable.reflectiveSelectable

object UndeclVal {
  val program = (x: { type A }) => {
    val y = x
    (z: y.B) => z
  }
}
"

/-- `notes-scala-xv1/j/DeclVal.scala`. -/
def textDeclVal : String := "import scala.reflect.Selectable.reflectiveSelectable

object DeclVal {
  val program = (x: { type A }) => {
    val y = x
    (z: y.A) => z
  }
}
"

#eval expect ((outcome textUndecl.toList).text ==
    "outside 4:42: type B is not a member of the type of x (scalac E008)")
  "outcome of j/Undecl.scala"

#eval expect ((outcome textUndeclAny.toList).text ==
    "outside 4:35: type B is not a member of the type of x (scalac E008)")
  "outcome of j/UndeclAny.scala"

#eval expect ((outcome textUndeclVal.toList).text ==
    "outside 6:11: type B is not a member of the type of y (scalac E008)")
  "outcome of j/UndeclVal.scala"

#eval expect ((outcome textDeclVal.toList).text == "ok : ∀(x : {A : ⊥ .. ⊤}) ∀(y : ⊥) ⊤")
  "outcome of j/DeclVal.scala"

/-! ## The printers (S-27)

`toScala` is checked in the kernel on seven round trips and three refusals.
Two of the round trips start from the readings of `j/J4E5.scala` and
`print/ThisLit.scala`, a literal form and `this` as a term, and `#eval expect`
checks that the reader gives those two terms.  Then `#eval expect` on every
example program with its own table, on the fill of every one that compiles,
and on the reading of each text of `j/` of the translation. -/

/-- The error of a result, if any. -/
def gapOf {α : Type} : Except String α → Option String
  | .error why => some why
  | .ok _ => none

/-- The reading of `j/J4E5.scala`: the literal under `{ val a: v.A }` in its
literal form (D-4 of the groups file). -/
def j4e5Reading : STm := dot% λ(w : {A : ⊤..⊤}).
  let f = λ(v : {A : ⊤..⊤}). (let ℓ = ν(this. {a = v}) in (ℓ : {a : v.A})) in let o = f w in o.a

/-- The reading of `print/ThisLit.scala`: `this.a` in a literal without a self
name reads as the variable `this`. -/
def thisLitReading : STm := dot% λ(x : ⊤).
  (let ℓ = ν(this. {a : ⊤ = x} ∧ {b : ⊤ = this.a}) in (ℓ : {b : ⊤}))

/-- A `μ` named from inside a nested refinement, where Scala's `this` names the
nested one. -/
def muOuter : STm := dot% λ(x : μ(s. {A : ⊥ .. ⊤} ∧ {b : {c : s.A}})). x

/-! ### In the kernel -/

-- `(x: { type A >: Any <: Nothing }) => { val y: { type B = { val a: Any } } = x; y }`
example : roundTrip exampleTable E1src = .same := by decide +kernel

-- `(x: { type A <: { val a: Any } }) => (y: x.A & { val a: Any }) => y.a`
example : roundTrip exampleTable E8src = .same := by decide +kernel

example : roundTrip exampleTable E9src = .same := by decide +kernel

-- `(f: Any) => (g: Any) => f(g(f))`
example : roundTrip exampleTable E10src = .same := by decide +kernel

-- `(k: ({ val a: Any } => Any) => Any) => k(y => y)`
example : roundTrip exampleTable K1srcA = .same := by decide +kernel

-- A literal form through the kernel.
example : roundTrip exampleTable j4e5Reading = .same := by decide +kernel

-- `this` as a term.
example : roundTrip exampleTable thisLitReading = .same := by decide +kernel

example : gapOf (toScala E5src) = some gapSelfType := by decide +kernel

example : gapOf (toScala E5srcS) = some gapUntypedLiteral := by decide +kernel

example : gapOf (toScala muOuter) = some gapMuOuter := by decide +kernel

/-! ### The two readings -/

/-- `notes-scala-xv1/print/ThisLit.scala`. -/
def textThisLit : String := "import scala.reflect.Selectable.reflectiveSelectable

// A literal without a self name whose member names another through `this` (refute-stage2 R2).
object ThisLit {
  val program = (x: Any) => (new Object {
    val a: Any = x
    val b: Any = this.a
  }: { val b: Any })
}
"

#eval expect ((readVanilla textJ4E5.toList).toOption.map Prod.fst == some j4e5Reading)
  "the reading of j/J4E5.scala"

#eval expect ((readVanilla textThisLit.toList).toOption.map Prod.fst == some thisLitReading)
  "the reading of print/ThisLit.scala"

/-! ### Every example program

Each with its own table.  A round trip may fail only for a reason, never by a
text that does not read back or by a term that reads back otherwise. -/

/-- The names whose round trip is `differs`, `unreadable` or `unresolved`. -/
def badTrips (r : List (String × Trip)) : List String :=
  r.filterMap fun (n, t) =>
    match t with
    | .same | .gap _ => none
    | _ => some n

-- `labelsOfProgram` reads names by `String.toList`, so it stays in `#eval`.
#eval do
  let r : List (String × Trip) := examples.map fun (n, e) => (n, roundTrip (labelsOfProgram e) e)
  expect (r.length == 131) "131 round trips"
  expect (badTrips r).isEmpty s!"round trips that differ, do not read back or do not resolve: {badTrips r}"

/-- The answer of a fill: `same` when its text reads back, `gap` with the
reason when it fails, `unreadable` when its text does not read back. -/
def fillTrip (Λ : LabelTable) (a : ATm []) : Trip :=
  match fillToScala Λ a with
  | .error why => .gap why
  | .ok P =>
    match readVanilla (ScalaSyntax.print P) with
    | .ok _ => .same
    | .error err => .unreadable err

-- A fill fails with a reason of D-9 or a refusal of the reader, or its text reads back.
#eval do
  let fs : List (String × Trip) := examples.filterMap fun (n, e) =>
    let Λ := labelsOfProgram e
    match compileE {} Λ e with
    | .ok ⟨a, _⟩ => some (n, fillTrip Λ a)
    | .error _ => none
  let bad := fs.filterMap fun (p : String × Trip) =>
    match p.2 with
    | .same => none
    | .gap why => if gapReasons.contains why || why.startsWith "reader: " then none else some p.1
    | _ => some p.1
  let reader := fs.filterMap fun (p : String × Trip) =>
    match p.2 with
    | .gap why => if why.startsWith "reader: " then some p.1 else none
    | _ => none
  expect (fs.length == 96) "96 fills"
  expect bad.isEmpty s!"fills that do not read back: {bad}"
  expect (reader.contains "E2src" && reader.contains "E7src") "the reader refuses the fills of E2src and E7src"

/-! ### The texts of `j/` -/

/-- The round trip of the reading of a text, with its own table. -/
def tripOfText (cs : List Char) : Option Trip :=
  match readVanilla cs with
  | .ok (e, Λ) => some (roundTrip Λ e)
  | .error _ => none

#eval do
  let texts : List (String × String) :=
    [("J1ValSel", textJ1ValSel), ("J1ValLast", textJ1ValLast), ("J1Lit", textJ1Lit),
     ("J1LitTyped", textJ1LitTyped), ("J1X1", textJ1X1), ("J1SA1", textJ1SA1), ("J1SelfSel", textJ1SelfSel),
     ("J2ValLit", textJ2ValLit), ("J2RecUntyped", textJ2RecUntyped), ("J2RecTyped", textJ2RecTyped),
     ("J4E5", textJ4E5), ("J4E6Typed", textJ4E6Typed), ("J4E6Untyped", textJ4E6Untyped)]
  let bad := texts.filterMap fun (p : String × String) =>
    if tripOfText p.2.toList == some Trip.same then none else some p.1
  expect (texts.length == 13) "13 texts"
  expect bad.isEmpty s!"readings of j/ that do not round trip: {bad}"

end Frontend.Scala.Tests
