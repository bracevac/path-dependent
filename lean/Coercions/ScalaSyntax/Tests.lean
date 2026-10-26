import Coercions.ScalaSyntax.Parse
import Coercions.ScalaSyntax.Scope
import Coercions.ScalaSyntax.Print

/-!
# Checks of the Scala reader

String checks by `#eval expect`, where a false check throws and fails the
build.  The texts are Lean string literals, never files, so a change to a text
rebuilds this module.  `String.toList` runs here in compiled code only, and no
theorem mentions it.

The layout texts are the judge's scalac probes `LayA` to `LayF` and `E5`,
copied from `notes-scala-xv0/`, and the probes of group g1 in
`notes-scala-xv0/scalac-g1/`.  Each was compiled by scalac 3.8.4 with and
without `-no-indent`.

The parser checks put each row of the plan's mapping tables into a minimal
file and compare the tree, with its positions erased.  The judge's `CapP` and
`ClsP` are copied from `notes-scala-frontends/scratch-judge/sc/`, and the
probes of group g2 are in `notes-scala-xv0/scalac-g2/`.

The checks of `check` give one accepted and one refused program per rule,
the refused one at its position.  Each text is a file of
`notes-scala-xv0/scalac-g3/` with scalac 3.8.4's output beside it: the probes
of the refuters and designers, rewritten to the subset's one program, and the
probes of group g3.

The checks of `print` compare the printed text of E5, `CapP`, `ClsP` and
`LayC` with their own text in the printer's layout, pin each rule of the
layout on a small program, and read back the printed text of every program
above that the reader accepts.  The probes of group g4, which scalac 3.8.4
read alike with and without `-no-indent`, are in `notes-scala-xv0/scalac-g4/`.
-/

namespace ScalaSyntax.Tests

open ScalaSyntax

/-- Fail the build, from `#eval`, when a check comes out false. -/
def expect (b : Bool) (msg : String) : IO Unit :=
  if b then pure () else throw (IO.userError msg)

/-- The tokens of a text. -/
def toks (s : String) : Except Err (List Token) := tokens s.toList

/-- The refusal of a text, or `none` when it is read. -/
def refusal (s : String) : Option Err :=
  match toks s with
  | .error e => some e
  | .ok _ => none

/-- The positions of the `sep`s of a text, or `none` when it is refused. -/
def seps (s : String) : Option (List Pos) :=
  (toks s).toOption.map fun ts => (ts.filter (·.tok == .sep)).map (·.pos)

/-- `layout` only inserts `sep`s: without them its tokens are the lexer's. -/
def onlySeps (s : String) : Bool :=
  (toks s).toOption.map (·.filter (·.tok != .sep)) == (lex s.toList).toOption

/-! ## Tokens and positions -/

/-- A token on line 1. -/
private def at1 (t : Tok) (c : Nat) (first : Bool := false) : Token := ⟨t, ⟨1, c⟩, first⟩

private def oneLine : String := "object X { val program = (x: Any) => x }"

#eval expect ((toks oneLine).toOption == some
    [at1 (.kw "object") 1 true, at1 (.ident "X" true) 8, at1 (.sym "{") 10, at1 (.kw "val") 12,
     at1 (.ident "program" false) 16, at1 (.sym "=") 24, at1 (.sym "(") 26,
     at1 (.ident "x" false) 27, at1 (.sym ":") 28, at1 (.ident "Any" true) 30,
     at1 (.sym ")") 33, at1 (.sym "=>") 35, at1 (.ident "x" false) 38, at1 (.sym "}") 40])
  "tokens: the kinds and positions of a one-line program"

/-! ## Comments -/

private def commented : String := "// a line comment
/* outer /* inner */ still outer */
object X { /* λ ⊤ */ val program = (x: Any) => x } // trailing
"

#eval expect ((toks commented).toOption.map (·.map (·.tok)) ==
    (toks oneLine).toOption.map (·.map (·.tok)))
  "comments: line and nested block comments disappear, a comment may hold λ ⊤"

#eval expect (((toks commented).toOption.bind (·.head?)).map (·.pos) == some ⟨3, 1⟩)
  "comments: the first token keeps its line"

#eval expect (refusal "/* /* */" == some ⟨⟨1, 1⟩, "unclosed comment"⟩)
  "comments: an unclosed nested comment is refused at its start"

/-! ## Refusals of the lexer -/

#eval expect (refusal "object X { val program = 1 }" ==
    some ⟨⟨1, 26⟩, "number literals are outside the subset"⟩)
  "refusal: a number literal at its column"

#eval expect (refusal "object X { val program = \"s\" }" ==
    some ⟨⟨1, 26⟩, "string and character literals are outside the subset"⟩)
  "refusal: a string literal"

#eval expect (refusal "object X { val program = (`x`: Any) => x }" ==
    some ⟨⟨1, 27⟩, "backquoted names are outside the subset"⟩)
  "refusal: a backquoted name"

#eval expect (refusal "object X { val program = (a$b: Any) => a$b }" ==
    some ⟨⟨1, 27⟩, "names with `$` are outside the subset"⟩)
  "refusal: a name with `$`"

#eval expect (refusal "object X { val program = (_: Any) => x }" ==
    some ⟨⟨1, 27⟩, "placeholders are outside the subset"⟩)
  "refusal: the placeholder `_`"

#eval expect (refusal "object X { val program = (x: Any) => x + x }" ==
    some ⟨⟨1, 40⟩, "operator `+` is outside the subset"⟩)
  "refusal: the operator `+`"

#eval expect (refusal "object X {\tval program = (x: Any) => x }" ==
    some ⟨⟨1, 11⟩, "tabs are outside the subset"⟩)
  "refusal: a tab"

#eval expect (refusal "object X { val program = (λ: Any) => λ }" ==
    some ⟨⟨1, 27⟩, "non-ASCII characters are outside the subset"⟩)
  "refusal: a non-ASCII character outside a comment"

-- scalac reads `x_:` as one name (probe `UnderOp`).
#eval expect (refusal "object X { val program = (x_: Any) => x_ }" ==
    some ⟨⟨1, 27⟩, "a name ending in `_` takes the operator after it in Scala: put a space between them"⟩)
  "refusal: a name ending in `_` before an operator"

-- `true`, `false` and `macro` are hard keywords of scalac 3.8.4 (probes
-- `KwTrue`, `KwFalse`, `KwMacro`), soft keywords are reserved too, and the
-- words of the subset are `kw`.
#eval expect ((lex "true false macro forSome open val this Val".toList).toOption.map (·.map (·.tok)) ==
    some [.reserved "true", .reserved "false", .reserved "macro", .reserved "forSome",
      .reserved "open", .kw "val", .kw "this", .ident "Val" true])
  "keywords: reserved words and the words of the subset"

/-! ## The column rule -/

private def layA : String := "import scala.reflect.Selectable.reflectiveSelectable
// A: the next statement starts at the column of the block's first statement.
object LayA {
  val program = (f: Any => { val a: Any }) => (w: Any) => {
    val r = f
    (w)
  }
}
"

private def layB : String := "import scala.reflect.Selectable.reflectiveSelectable
// B: a more indented line that starts with '(' after a line that can end a statement.
object LayB {
  val program = (f: Any => { val a: Any }) => (w: Any) => {
    val r = f
      (w)
    r
  }
}
"

private def layC : String := "import scala.reflect.Selectable.reflectiveSelectable
// C: the printer's layout: continuations after '=', '=>', '{', '(', ',', ':', '&'; statements at one column.
object LayC {
  val program =
    (x: {
      type A
      val a: this.A
    }) =>
      (y: { val b: Any } &
        { val c: Any }) => {
        val u =
          x.a
        val o: { val d: Any } =
          new Object {
            val d = u
          }
        o.d
      }
}
"

private def layD : String := "import scala.reflect.Selectable.reflectiveSelectable
// D: a statement less indented than the block's first statement.
object LayD {
  val program = (w: Any) => {
      val r = w
    r
  }
}
"

private def layE : String := "import scala.reflect.Selectable.reflectiveSelectable
// E: a more indented identifier after a line that can end a statement.
object LayE {
  val program = (f: Any) => (w: Any) => {
    val r = f
      w
    r
  }
}
"

private def layF : String := "import scala.reflect.Selectable.reflectiveSelectable
// F: a leading '.' on a more indented line.
object LayF {
  val program = (x: { val a: { val b: Any } }) => {
    val r = x
      .a
    r
  }
}
"

private def e5 : String := "import scala.reflect.Selectable.reflectiveSelectable

// E5: an object returned from a function and selected after a val.
object E5 {
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

/-- The message of the continuation rule. -/
private def contMsg : String := "a continuation line must follow one of = => -> ( { , : & <: >:"

-- The file's top level is a region at column 1, so `object` gets a `sep`
-- after the import.  In the block, `(w)` starts a statement.
#eval expect (seps layA == some [⟨3, 1⟩, ⟨6, 5⟩])
  "layout: LayA is read, with a sep before `object` and before `(w)`"

-- The block of line 10 starts at column 9, the column of that line's first
-- token, right of its 8 spaces of indentation.
#eval expect (seps layC == some [⟨3, 1⟩, ⟨7, 7⟩, ⟨13, 9⟩, ⟨17, 9⟩])
  "layout: LayC is read, with a sep before `object`, `val a`, `val o` and `o.d`"

#eval expect (refusal layB == some ⟨⟨6, 7⟩, contMsg⟩)
  "layout: LayB is refused at 6:7"

#eval expect (refusal layD == some ⟨⟨6, 5⟩, "line is indented too far to the left"⟩)
  "layout: LayD is refused at 6:5"

#eval expect (refusal layE == some ⟨⟨6, 7⟩, contMsg⟩)
  "layout: LayE is refused at 6:7"

#eval expect (refusal layF == some ⟨⟨6, 7⟩, contMsg⟩)
  "layout: LayF is refused at 6:7"

#eval expect ((toks "{ val a: Any; val b: Any }").toOption.map (·.map (·.tok)) ==
    some [.sym "{", .kw "val", .ident "a" false, .sym ":", .ident "Any" true, .sym ";",
      .kw "val", .ident "b" false, .sym ":", .ident "Any" true, .sym "}"])
  "layout: a one-line region keeps its `;` and gets no sep"

#eval expect ((toks "{\n  val a = x;\n  a\n}").toOption.map (·.map (·.tok)) ==
    some [.sym "{", .kw "val", .ident "a" false, .sym "=", .ident "x" false, .sym ";",
      .ident "a" false, .sym "}"])
  "layout: a `;` at the end of a line separates, and no sep follows it"

#eval expect (refusal "{ val a: Any\nval b: Any }" ==
    some ⟨⟨1, 3⟩, "the first statement after `{` goes on the next line, indented"⟩)
  "layout: a region that starts on the line of its `{` must end there"

#eval expect (seps e5 == some [⟨4, 1⟩, ⟨12, 7⟩, ⟨13, 7⟩])
  "layout: E5 is read, with a sep before `object`, `val o` and `o.a`"

#eval expect (onlySeps e5 && onlySeps layA && onlySeps layC)
  "layout: only sep tokens are inserted"

/-! ## The refinements of the column rule

Each from a probe of `notes-scala-xv0/scalac-g1/` that scalac 3.8.4 reads
differently with and without `-no-indent` (refused), or alike (read). -/

private def layG : String := "import scala.reflect.Selectable.reflectiveSelectable
// G: a comment before the first token of a line; the token sits at the block's column.
object LayG {
  val program = (w: Any) => {
      val r = w
 /*x*/r
  }
}
"

private def layI : String := "import scala.reflect.Selectable.reflectiveSelectable
// I: a continuation line less indented than the continuation line before it.
object LayI {
  val program = (w: Any) => {
    val f =
        (x: Any) =>
      x
    f
  }
}
"

private def layK : String := "import scala.reflect.Selectable.reflectiveSelectable
// K: a closing line left of the continuation line that opened it, then a deeper continuation.
object LayK {
  val program = (w: Any) => {
    val f =
        (x: {
          type A
      }) =>
          x
    f
  }
}
"

private def layM : String := "import scala.reflect.Selectable.reflectiveSelectable
// M: a continuation after '=>' at the column of the continuation line before it.
object LayM {
  val program = (w: Any) => {
    val f =
      (x: Any) =>
      x
    f
  }
}
"

private def layN : String := "import scala.reflect.Selectable.reflectiveSelectable
// N: a ';' on a continuation line after '='.
object LayN {
  val program = (w: Any) => {
    val a =
      w; val b = w
    a
  }
}
"

#eval expect (refusal layG ==
    some ⟨⟨6, 7⟩, "a comment before the first token of a line is outside the subset"⟩)
  "layout: LayG, a comment before a line's first token, is refused at 6:7"

#eval expect (refusal layI == some ⟨⟨7, 7⟩,
    "a continuation line must be indented at least as far as the continuation line before it"⟩)
  "layout: LayI, a continuation left of the one before, is refused at 7:7"

#eval expect (seps layK == some [⟨3, 1⟩, ⟨10, 5⟩])
  "layout: LayK is read, a closing line does not move the continuation column"

#eval expect (seps layM == some [⟨3, 1⟩, ⟨8, 5⟩])
  "layout: LayM is read, a continuation may stay at the column of the one before"

#eval expect (refusal layN == some ⟨⟨6, 8⟩,
    "`;` on a continuation line is outside the subset: start the next statement on its own line"⟩)
  "layout: LayN, a `;` on a continuation line, is refused at 6:8"

/-! ## The parser

One check per row of the plan's mapping tables (sixteen vanilla rows, eight
Captures rows, four Classifiers rows) and per program header: the text of the
row inside a minimal file, parsed and erased, is the expected tree.  Then the
refusals, each at its position, and E5 with every position written out. -/

/-- The parse of a text with its positions erased, or `none` when a stage
refuses it. -/
def parsed (s : String) : Option Program := (parseFile s.toList).toOption.map Program.erase

/-- The refusal of a text by the lexer, the column rule or the parser, or
`none` when it is read. -/
def parseRefusal (s : String) : Option Err :=
  match parseFile s.toList with
  | .error e => some e
  | .ok _ => none

/-- The position that `Program.erase` writes. -/
private abbrev o : Pos := Pos.zero

/-- The import of the vanilla header. -/
private def selectable : String := "scala.reflect.Selectable.reflectiveSelectable"

/-- A vanilla file whose program is `val program = e`, with `e` on line 3 from
column 17. -/
private def vanilla (e : String) : String :=
  "import " ++ selectable ++ "\nobject T {\n  val program = " ++ e ++ "\n}\n"

/-- A vanilla file whose program is `val program: T = e`. -/
private def vanillaTyped (T e : String) : String :=
  "import " ++ selectable ++ "\nobject T {\n  val program: " ++ T ++ " = " ++ e ++ "\n}\n"

/-- The tree of a vanilla file, positions erased. -/
private def vanillaProg (t : Tm) (T : Option Ty := none) : Program :=
  { imports := [(o, selectable)], name := "T", prelude := [], params := none, ty := T, body := t }

/-- The two imports of the capture front ends. -/
private def captureImports : String :=
  "import language.experimental.captureChecking\nimport " ++ selectable ++ "\n"

/-- A Captures file with the platform `k1`, `k2`, whose program's right side
`e` is on line 6 from column 5. -/
private def captures (e : String) : String :=
  captureImports ++ "object T {\n  class Cap extends caps.SharedCapability\n" ++
    "  def program(k1: Cap^, k2: Cap^) =\n    " ++ e ++ "\n}\n"

/-- The tree of a Captures file, positions erased. -/
private def capturesProg (t : Tm) : Program :=
  { imports := [(o, "language.experimental.captureChecking"), (o, selectable)], name := "T",
    prelude := [.capClass o "Cap"], params := some [(o, "k1", "Cap"), (o, "k2", "Cap")],
    ty := none, body := t }

/-- A Classifiers file with the prelude lines `pre`, the parameters `ps` and
the right side `e`. -/
private def classifiers (pre : List String) (ps e : String) : String :=
  captureImports ++ "object T {\n" ++ String.join (pre.map fun l => "  " ++ l ++ "\n") ++
    "  def program(" ++ ps ++ ") =\n    " ++ e ++ "\n}\n"

/-- The tree of a Classifiers file, positions erased. -/
private def classifiersProg (pre : List PreludeItem) (ps : List (String × String)) (t : Tm) :
    Program :=
  { imports := [(o, "language.experimental.captureChecking"), (o, selectable)], name := "T",
    prelude := pre, params := some (ps.map fun x => (o, x.1, x.2)), ty := none, body := t }

/-! Shorthands for the trees below, with their positions erased. -/

/-- A variable. -/
private abbrev vr (x : String) : Tm := .var o x
/-- A lambda. -/
private abbrev lm (x : String) (T : Option Ty) (t : Tm) : Tm := .lam o x T t
/-- `Any`. -/
private abbrev any : Ty := .any o
/-- `x.A`. -/
private abbrev selT (x A : String) : Ty := .sel o (.var o x) A
/-- A refinement. -/
private abbrev rf (ds : Decls) : Ty := .refine o ds
/-- A variable in a capture set. -/
private abbrev cv (x : String) : CapRef := .var o x

/-! ### The vanilla rows -/

#eval expect (parsed (vanilla "(x: Any) => (y: Nothing) => x") == some (vanillaProg
    (lm "x" (some any) (lm "y" (some (.nothing o)) (vr "x")))))
  "vanilla row: `Any`, `Nothing`"

#eval expect (parsed (vanilla "(x: { type A; val a: this.A }) => (y: x.A) => y") == some (vanillaProg
    (lm "x" (some (rf (.typ o "A" none none (.val o "a" (.sel o (.this o) "A") .nil))))
      (lm "y" (some (selT "x" "A")) (vr "y")))))
  "vanilla row: `x.A`, `this.A`"

#eval expect (parsed (vanilla "(x: {\n      type A\n      val a: this.A\n      val b: Any\n    }) => x") ==
    some (vanillaProg
      (lm "x" (some (rf (.typ o "A" none none (.val o "a" (.sel o (.this o) "A") (.val o "b" any .nil)))))
        (vr "x"))))
  "vanilla row: a refinement `{ d1; …; dn }` over several lines"

#eval expect (parsed (vanilla
      "(x: { type A >: Nothing <: Any; type B; type C = Any; type D <: Any; type E >: Nothing }) => x") ==
    some (vanillaProg
      (lm "x" (some (rf (.typ o "A" (some (.nothing o)) (some any) (.typ o "B" none none
        (.alias o "C" any (.typ o "D" none (some any) (.typ o "E" (some (.nothing o)) none .nil)))))))
        (vr "x"))))
  "vanilla row: `type A >: S <: T`, `type A`, `type A = T`"

#eval expect (parsed (vanilla "(x: { val a: { val b: Any } }) => x.a.b") == some (vanillaProg
    (lm "x" (some (rf (.val o "a" (rf (.val o "b" any .nil)) .nil)))
      (.sel (.sel (vr "x") o "a") o "b"))))
  "vanilla row: `val a: T` in a refinement"

#eval expect (parsed (vanilla "(x: { val a: Any } & { val b: Any } & { val c: Any }) => x") ==
    some (vanillaProg
      (lm "x" (some (.and (.and (rf (.val o "a" any .nil)) (rf (.val o "b" any .nil)))
        (rf (.val o "c" any .nil)))) (vr "x"))))
  "vanilla row: `S & T`, nested to the left"

#eval expect (parsed (vanilla "(f: (x: { type A }) => x.A) => (g: Any => Any => Any) => f") ==
    some (vanillaProg
      (lm "f" (some (.fn o (some "x") (rf (.typ o "A" none none .nil)) .fat (selT "x" "A")))
        (lm "g" (some (.fn o none any .fat (.fn o none any .fat any))) (vr "f")))))
  "vanilla row: `(x: S) => T` and `S => T`, nested to the right"

#eval expect (parsed (vanilla "(x: Any) => y => (z) => x") == some (vanillaProg
    (lm "x" (some any) (lm "y" none (lm "z" none (vr "x"))))))
  "vanilla row: `(x: T) => e`, `x => e`, `(x) => e`"

#eval expect (parsed (vanilla "(f: Any => { val a: Any }) => (x: Any) => f(x).a") == some (vanillaProg
    (lm "f" (some (.fn o none any .fat (rf (.val o "a" any .nil))))
      (lm "x" (some any) (.sel (.app (vr "f") (vr "x")) o "a")))))
  "vanilla row: `f(e)`, `e.a`"

#eval expect (parsed (vanilla "(x: Any) => (x: Any)") == some (vanillaProg
    (lm "x" (some any) (.asc o (vr "x") any))))
  "vanilla row: `(e: T)`, not followed by `=>`"

#eval expect (parsed (vanilla "(w: Any) => { val x = { w }; x }") == some (vanillaProg
    (lm "w" (some any) (.block o (.val o "x" none (.block o (.last (vr "w"))) (.last (vr "x")))))))
  "vanilla row: `{ val x = e; r }`, `{ e }`"

#eval expect (parsed (vanilla "(w: Any) => { val x: Any = w; w }") == some (vanillaProg
    (lm "w" (some any) (.block o (.val o "x" (some any) (vr "w") (.last (vr "w")))))))
  "vanilla row: `{ val x: T = e; r }`"

#eval expect (parsed (vanilla "(w: Any) => {\n    val y = w\n    val x: Any = y\n    x\n  }") ==
    some (vanillaProg
      (lm "w" (some any) (.block o (.val o "y" none (vr "w") (.val o "x" (some any) (vr "y")
        (.last (vr "x"))))))))
  "vanilla row: `{ …; val x: T = e; x }` over several lines"

#eval expect (parsed (vanillaTyped "{ val a: Any }" "new Object { s => val a = s }") ==
    some (vanillaProg (.lit o (some "s") (.val o "a" none (vr "s") .nil)) (some (rf (.val o "a" any .nil)))))
  "vanilla row: a literal under a written type, `new Object { s => ds }`"

#eval expect (parsed (vanilla
      "(w: Any) => (new Object { type A = Any; val a = w; val b: Any = w }: { type A = Any; val a: Any; val b: Any })") ==
    some (vanillaProg
      (lm "w" (some any) (.asc o
        (.lit o none (.typ o "A" any (.val o "a" none (vr "w") (.val o "b" (some any) (vr "w") .nil))))
        (rf (.alias o "A" any (.val o "a" any (.val o "b" any .nil))))))))
  "vanilla row: `type A = T`, `val a = e`, `val a: T = e` in a literal"

#eval expect (parsed (vanillaTyped "Any => Any" "(x: Any) => x") == some (vanillaProg
    (lm "x" (some any) (vr "x")) (some (.fn o none any .fat any))))
  "vanilla row: `val program: T = e`"

/-! ### The Captures rows -/

#eval expect (parsed (captures "(u: Any) => u") == some (capturesProg (lm "u" (some any) (vr "u"))))
  "Captures row: `def program(k1: Cap^, k2: Cap^)` and the prelude class"

#eval expect (parsed (captures "(f: Any -> Any) => f") == some (capturesProg
    (lm "f" (some (.fn o none any (.thin none) any)) (vr "f"))))
  "Captures row: `S -> T`"

#eval expect (parsed (captures "(f: Any ->{k1} Any) => f") == some (capturesProg
    (lm "f" (some (.fn o none any (.thin (some [cv "k1"])) any)) (vr "f"))))
  "Captures row: `S ->{k1} T`"

#eval expect (parsed (captures "(f: Any => Any) => f") == some (capturesProg
    (lm "f" (some (.fn o none any .fat any)) (vr "f"))))
  "Captures row: `S => T`"

#eval expect (parsed (captures "(x: { val a: Any }^{k1, k2}) => x") == some (capturesProg
    (lm "x" (some (.capt o (rf (.val o "a" any .nil)) (some [cv "k1", cv "k2"]))) (vr "x"))))
  "Captures row: `T^{k1, k2}`"

#eval expect (parsed (captures "(x: { val a: Any }^) => x") == some (capturesProg
    (lm "x" (some (.capt o (rf (.val o "a" any .nil)) none)) (vr "x"))))
  "Captures row: `T^`"

#eval expect (parsed (captures "(f: Any ->{caps.any} Any) => f") == some (capturesProg
    (lm "f" (some (.fn o none any (.thin (some [.any o])) any)) (vr "f"))))
  "Captures row: `caps.any`"

#eval expect (parsed (captures "(x: { type C^ >: {k1} <: {k1, k2} }) => x") == some (capturesProg
    (lm "x" (some (rf (.cap o "C" (some [cv "k1"]) (some [cv "k1", cv "k2"]) .nil))) (vr "x"))))
  "Captures row: `type C^ >: {k1} <: {k1, k2}`"

-- Two more Captures forms of the mapping table: a capture alias declared and
-- defined in a literal, and `->` before a `{` that opens a refinement.
#eval expect (parsed (captures "(new Object { type C^ = {k1} }: { type C^ = {k1} })") == some (capturesProg
    (.asc o (.lit o none (.cap o "C" [cv "k1"] .nil)) (rf (.capAlias o "C" [cv "k1"] .nil)))))
  "Captures: `type C^ = {k1}` in a literal and in a refinement"

#eval expect (parsed (captures "(f: Any -> { val a: Any }) => (g: Any ->{} Any) => f") ==
    some (capturesProg
      (lm "f" (some (.fn o none any (.thin none) (rf (.val o "a" any .nil))))
        (lm "g" (some (.fn o none any (.thin (some [])) any)) (vr "f")))))
  "Captures: after `->`, `{ val` opens the result and `{}` an empty capture set (probe ArrowRefine)"

/-! ### The Classifiers rows -/

#eval expect (parsed (classifiers ["trait IO extends caps.SharedCapability, caps.Classifier",
      "class Cap extends caps.SharedCapability"] "k: Cap^" "(u: Any) => u") ==
    some (classifiersProg [.classifier o "IO" none, .capClass o "Cap"] [("k", "Cap")]
      (lm "u" (some any) (vr "u"))))
  "Classifiers row: a root classifier trait"

#eval expect (parsed (classifiers ["trait ThreadLocal extends caps.SharedCapability, caps.Classifier",
      "trait Control extends ThreadLocal, caps.Classifier", "class Cap extends caps.SharedCapability"]
      "k: Cap^" "(u: Any) => u") ==
    some (classifiersProg [.classifier o "ThreadLocal" none,
      .classifier o "Control" (some "ThreadLocal"), .capClass o "Cap"] [("k", "Cap")]
      (lm "u" (some any) (vr "u"))))
  "Classifiers row: a child classifier trait"

#eval expect (parsed (classifiers ["trait Control extends caps.SharedCapability, caps.Classifier",
      "class CtlCap extends Control"] "ctl: CtlCap^" "(u: Any) => u") ==
    some (classifiersProg [.classifier o "Control" none, .platClass o "CtlCap" "Control"]
      [("ctl", "CtlCap")] (lm "u" (some any) (vr "u"))))
  "Classifiers row: a platform class"

#eval expect (parsed (classifiers ["trait Control extends caps.SharedCapability, caps.Classifier",
      "class CtlCap extends Control"] "ctl: CtlCap^"
      "(f: Any ->{ctl.only[Control]} Any) => (x: { type C^ <: {caps.any.only[Control]} }) => f") ==
    some (classifiersProg [.classifier o "Control" none, .platClass o "CtlCap" "Control"]
      [("ctl", "CtlCap")]
      (lm "f" (some (.fn o none any (.thin (some [.only o (some "ctl") "Control"])) any))
        (lm "x" (some (rf (.cap o "C" none (some [.only o none "Control"]) .nil))) (vr "f")))))
  "Classifiers row: `x.only[K]`, and `caps.any.only[K]` as a bound"

/-! ### The program headers -/

#eval expect ((parsed (vanilla "(x: Any) => x")).map (fun P => (P.params, P.ty)) == some (none, none))
  "header: `val program = e`"

#eval expect ((parsed (vanillaTyped "Any" "(x: Any)")).map (fun P => (P.params, P.ty)) ==
    some (none, some any))
  "header: `val program: T = e`"

#eval expect ((parsed (captureImports ++ "object T {\n  class Cap extends caps.SharedCapability\n" ++
      "  def program(k1: Cap^): Any = k1\n}\n")).map (fun P => (P.params, P.ty)) ==
    some (some [(o, "k1", "Cap")], some any))
  "header: `def program(k1: Cap^): T = e`"

-- An empty platform is `val program`, as in the judge's `CapV`.
#eval expect ((parsed (captureImports ++ "object T {\n  val program = (f: Any => Any) => f\n}\n")).map
    (fun P => (P.imports.length, P.params)) == some (2, none))
  "header: the capture imports with `val program`"

/-! ### Whole files -/

private def capP : String := "import language.experimental.captureChecking
import scala.reflect.Selectable.reflectiveSelectable
// Captures subset, printer layout: prelude class, platform as parameters, no box, no self name.
object CapP {
  class Cap extends caps.SharedCapability
  def program(k1: Cap^, k2: Cap^) =
    (f1: Any ->{k1} Any) =>
      (f2: Any ->{k2} Any) =>
        (u: Any) => {
          val o: { val e1: Any ->{k1} Any; val e2: Any ->{k2} Any }^{f1, f2} =
            new Object {
              val e1 = f1
              val e2 = f2
            }
          val m: { type C^ >: {k1} <: {k1, k2} } =
            new Object {
              type C^ = {k1}
            }
          val e = o.e1
          e(u)
        }
}
"

private def clsP : String := "import language.experimental.captureChecking
import scala.reflect.Selectable.reflectiveSelectable
// Classifiers prelude: user classifiers, one extending another, platform classes, x.only[K].
object ClsP {
  trait ThreadLocal extends caps.SharedCapability, caps.Classifier
  trait Control extends ThreadLocal, caps.Classifier
  trait IO extends caps.SharedCapability, caps.Classifier
  class CtlCap extends Control
  class IoCap extends IO
  def program(ctl: CtlCap^, io: IoCap^) =
    (f: Any ->{ctl} Any) =>
      (g: Any ->{io} Any) => {
        val h: Any ->{ctl.only[Control]} Any = f
        val k: Any ->{ctl.only[ThreadLocal]} Any = h
        k
      }
}
"

#eval expect ((parsed capP).isSome && (parsed clsP).isSome && (parsed layA).isSome && (parsed layC).isSome)
  "files: the judge's CapP and ClsP, and LayA and LayC, parse"

#eval expect ((parsed clsP).map (·.prelude) == some [.classifier o "ThreadLocal" none,
    .classifier o "Control" (some "ThreadLocal"), .classifier o "IO" none,
    .platClass o "CtlCap" "Control", .platClass o "IoCap" "IO"])
  "files: the prelude of ClsP, in order"

/-- E5 with every position written out. -/
private def e5Prog : Program :=
  { imports := [(⟨1, 8⟩, selectable)], name := "E5", prelude := [], params := none, ty := none,
    body :=
      .lam ⟨6, 6⟩ "w" (some (.refine ⟨6, 9⟩ (.alias ⟨6, 16⟩ "A" (.any ⟨6, 20⟩) .nil)))
        (.block ⟨6, 30⟩
          (.val ⟨7, 11⟩ "f" none
            (.lam ⟨8, 10⟩ "v" (some (.refine ⟨8, 13⟩ (.alias ⟨8, 20⟩ "A" (.any ⟨8, 24⟩) .nil)))
              (.asc ⟨11, 12⟩
                (.lit ⟨9, 12⟩ none (.val ⟨10, 17⟩ "a" none (.var ⟨10, 21⟩ "v") .nil))
                (.refine ⟨11, 14⟩ (.val ⟨11, 20⟩ "a" (.sel ⟨11, 25⟩ (.var ⟨11, 23⟩ "v") "A") .nil))))
            (.val ⟨12, 11⟩ "o" none (.app (.var ⟨12, 15⟩ "f") (.var ⟨12, 17⟩ "w"))
              (.last (.sel (.var ⟨13, 7⟩ "o") ⟨13, 9⟩ "a"))))) }

#eval expect ((parseFile e5.toList).toOption == some e5Prog)
  "files: E5 parses to its tree, every position included"

/-! ### Refusals

Each at its line and column.  On line 3 of `vanilla e` the text `e` starts at
column 17, and on line 6 of `captures e` at column 5. -/

#eval expect (parseRefusal (vanilla "((x: Any) => x: Any => Any)") ==
    some ⟨⟨3, 31⟩, "put the lambda in its own parentheses: ((x: S) => e): T"⟩)
  "refusal: an ascribed lambda, at its `:`"

#eval expect (parsed (vanilla "(((x: Any) => x): Any => Any)") == some (vanillaProg
    (.asc o (lm "x" (some any) (vr "x")) (.fn o none any .fat any))))
  "refusal: the lambda in its own parentheses is read"

#eval expect (parseRefusal (vanilla "(x: Any) => if (x) x else x") ==
    some ⟨⟨3, 29⟩, "`if` is outside the subset"⟩)
  "refusal: `if`"

#eval expect (parseRefusal (vanilla "(w: Any) => {\n    class A\n    w\n  }") ==
    some ⟨⟨4, 5⟩, "classes and traits are outside the subset, except the prelude's"⟩)
  "refusal: `class` in the body"

#eval expect (parseRefusal (vanilla "(w: Any) => (new Foo { val a = w }: { val a: Any })") ==
    some ⟨⟨3, 34⟩, "`new` takes only `Object` in the subset: write `new Object { … }`"⟩)
  "refusal: `new Foo {`"

#eval expect (parseRefusal (vanilla "(w: Any) => (new Object { s: Any => val a = w }: { val a: Any })") ==
    some ⟨⟨3, 44⟩, "a typed self is outside the subset"⟩)
  "refusal: a typed self"

#eval expect (parseRefusal ("import " ++ selectable ++ "\nobject T:\n  val program = (x: Any) => x\n") ==
    some ⟨⟨2, 9⟩, "expected `{`, found `:`"⟩)
  "refusal: `object T:` with an indented body"

#eval expect (parseRefusal (captures "(f: { val a: Any }^ & { val b: Any }) => f") ==
    some ⟨⟨6, 23⟩, "a bare `^` before `&` is an infix operator in Scala: write `(S^) & T`"⟩)
  "refusal: a bare `^` before `&` (probe HatAnd)"

#eval expect (parsed (captures "(f: ({ val a: Any }^) & { val b: Any }) => f") == some (capturesProg
    (lm "f" (some (.and (.capt o (rf (.val o "a" any .nil)) none) (rf (.val o "b" any .nil)))) (vr "f"))))
  "refusal: `(S^) & T` is read (probe HatAndParen)"

#eval expect (parseRefusal (captures "(f: Any ->{this} Any) => f") ==
    some ⟨⟨6, 16⟩, "`this` in a capture set is outside the subset"⟩)
  "refusal: `this` in a capture set"

#eval expect (parseRefusal (captures "(f: Any ->{caps.cap} Any) => f") ==
    some ⟨⟨6, 21⟩, "`caps.cap` is outside the subset: write `caps.any`"⟩)
  "refusal: `caps.cap`"

#eval expect (parseRefusal (captureImports ++ "object T {\n  class Cap extends caps.SharedCapability\n" ++
      "  def program() = (u: Any) => u\n}\n") ==
    some ⟨⟨5, 15⟩, "an empty platform is `val program`"⟩)
  "refusal: `def program()`"

#eval expect (parseRefusal (captureImports ++ "object T {\n  trait K extends caps.SharedCapability\n" ++
      "  val program = (u: Any) => u\n}\n") ==
    some ⟨⟨5, 3⟩, Parse.traitShape⟩)
  "refusal: a trait that is not a classifier"

#eval expect (parseRefusal (captureImports ++ "object T {\n  class Cap extends caps.SharedCapability with K\n" ++
      "  val program = (u: Any) => u\n}\n") ==
    some ⟨⟨4, 43⟩, Parse.classShape⟩)
  "refusal: a prelude class with a second parent"

#eval expect (parseRefusal (vanilla "(w: Any) => { val x = w; }") ==
    some ⟨⟨3, 42⟩, "a block ends with its result, not with a `val`"⟩)
  "refusal: a block that ends with a `val`"

#eval expect (parseRefusal (vanilla "(f: Any => Any) => f(f, f)") ==
    some ⟨⟨3, 39⟩, "several arguments are outside the subset"⟩)
  "refusal: several arguments"

#eval expect (parseRefusal (vanilla "(x: Int) => x") ==
    some ⟨⟨3, 21⟩, "the type `Int` is outside the subset"⟩)
  "refusal: a type outside the subset"

#eval expect (parseRefusal (vanilla "(x: { val a: { type B } }) => (y: x.a.B) => y") ==
    some ⟨⟨3, 54⟩, "paths of length two are outside the subset"⟩)
  "refusal: a type selection on a path of length two"

#eval expect (parseRefusal (vanilla "(f: (x: Any)) => f") ==
    some ⟨⟨3, 29⟩, "a named tuple `(x: S)` is outside the subset: write `(x: S) => T`"⟩)
  "refusal: `(x: S)` without an arrow, a named tuple in Scala"

#eval expect (parseRefusal ("import " ++ selectable ++ "\nobject T {\n  val main = (x: Any) => x\n}\n") ==
    some ⟨⟨3, 7⟩, "the wrapper object holds `program`, found `main`"⟩)
  "refusal: a member other than `program`"

#eval expect (parseRefusal (captureImports ++ "object T {\n  val program = (u: Any) => u\n" ++
      "  class Cap extends caps.SharedCapability\n}\n") ==
    some ⟨⟨5, 3⟩, "the prelude goes before the program"⟩)
  "refusal: a prelude line after the program"

#eval expect (parseRefusal (vanilla "(x: Any) => x\n}\nobject U {\n  val program = (x: Any) => x") ==
    some ⟨⟨5, 1⟩, "expected the end of the file, found `object`"⟩)
  "refusal: a second object"

/-! ## The checks

One accepted and one refused program per rule of `check`, the refused one at
its line and column, with the whole refusal compared.  Each probe text is the
file of the same name in `notes-scala-xv0/scalac-g3/`, and its `.out.txt`
there is scalac 3.8.4's output.  The whole files are the fixtures above.

The probes of the refuters and designers are rewritten to the subset's file,
with `val program` for `val main` or `val p5` and no other definition at the
top.  They are refute-d1 `M1`, `M2`, `D1`, `D3`, `N3` and `U1`, refute-d3
`DupBlock` to `NestRefThis`, d1 `ThisProbe` p5, d3 `DepUnused`, the scout's
`Probe`, and d2 `V08`, `V18` and `LPsrc`.  On line 3 of a vanilla probe the
program's right side starts at column 17. -/

/-- The refusal of a text by the reader or by `check`, or `none` when both
accept it. -/
def checkRefusal (s : String) : Option Err :=
  match parseFile s.toList >>= check with
  | .error e => some e
  | .ok _ => none

/-- Whether the reader and `check` accept a text. -/
def checked (s : String) : Bool := (checkRefusal s).isNone

/-- A vanilla probe: the object `name` whose program is `val program = e`. -/
private def probe (name e : String) : String :=
  "import " ++ selectable ++ "\nobject " ++ name ++ " {\n  val program = " ++ e ++ "\n}\n"

/-- A vanilla probe whose program is `val program: T = e`. -/
private def probeTyped (name T e : String) : String :=
  "import " ++ selectable ++ "\nobject " ++ name ++ " {\n  val program: " ++ T ++ " = " ++ e ++ "\n}\n"

/-- A Captures probe with the prelude class `Cap` whose program is
`def program(ps) = e`, on line 5. -/
private def probeCap (name ps e : String) : String :=
  captureImports ++ "object " ++ name ++ " {\n  class Cap extends caps.SharedCapability\n" ++
    "  def program(" ++ ps ++ ") = " ++ e ++ "\n}\n"

/-! ### Rule 1: a bare name is in scope -/

#eval expect (checked (probe "AccScope" "(x: { val a: Any }) => { val y = x.a; val z = y; z }"))
  "rule 1: lambda parameters and earlier block vals are in scope (AccScope)"

#eval expect (checkRefusal (probe "NotFound" "(x: Any) => y") ==
    some ⟨⟨3, 29⟩, "`y` is not in scope"⟩)
  "rule 1: a name bound nowhere, at the name (NotFound, scalac E006)"

#eval expect (checkRefusal (probeCap "CapNotFound" "k1: Cap^" "(f: Any ->{z} Any) => f") ==
    some ⟨⟨5, 38⟩, "`z` is not in scope"⟩)
  "rule 1: a capture set names only what is in scope (CapNotFound, scalac E006)"

#eval expect (checkRefusal (probeCap "NoClass" "k: Foo^" "(u: Any) => u") ==
    some ⟨⟨5, 15⟩, "`Foo` is not in scope: the prelude declares no class `Foo` (scalac E006)"⟩)
  "rule 1: the class of a platform parameter is declared in the prelude (NoClass, scalac E006)"

#eval expect (checkRefusal (captureImports ++ "object OnlyUndecl {\n" ++
      "  trait IO extends caps.SharedCapability, caps.Classifier\n  class IoCap extends IO\n" ++
      "  def program(io: IoCap^) = (f: Any ->{io.only[Control]} Any) => f\n}\n") ==
    some ⟨⟨6, 40⟩, "`Control` is not in scope: the prelude declares no classifier `Control`"⟩)
  "rule 1: `x.only[K]` names a classifier of the prelude (OnlyUndecl, scalac E006)"

/-! ### Rule 2: a member of an enclosing template hides a variable -/

#eval expect (checked (probe "AccM1"
    "(f: Any => Any) => (new Object { s => val a: Any = s; val b: Any => Any = f }: { val a: Any; val b: Any => Any })"))
  "rule 2: a variable that no member hides (AccM1, M1 renamed)"

#eval expect (checkRefusal (probe "M1"
    "(a: Any => Any) => (new Object { s => val a: Any = s; val b: Any => Any = a }: { val a: Any; val b: Any => Any })") ==
    some ⟨⟨3, 91⟩, "`a` names the member of the enclosing object here, as in Scala: rename the variable"⟩)
  "rule 2: refute-d1 M1, the parameter `a` read as the member `a` (scalac E007)"

#eval expect (checkRefusal (probe "RefMember" "(a: { type T }) => (y: { val a: Any; type B = a.T }) => y") ==
    some ⟨⟨3, 63⟩, "`a` names the member of the enclosing refinement here, as in Scala: rename the variable"⟩)
  "rule 2: a refinement's member hides a variable too (RefMember, scalac E008)"

/-! ### Rule 3: members are named through a path -/

#eval expect (checked (probe "AccM2"
    "(new Object { s => val a = (y: Any) => y; val b = s.a }: { val a: Any => Any; val b: Any => Any })"))
  "rule 3: a member named through the self name (AccM2, M2 with `s.a`)"

#eval expect (checkRefusal (probe "M2"
    "(new Object { s => val a = (y: Any) => y; val b = a }: { val a: Any => Any; val b: Any => Any })") ==
    some ⟨⟨3, 67⟩, "`a` is a member: members are named through a path, write `this.a`"⟩)
  "rule 3: refute-d1 M2, a bare member name (scalac reads it, exit 0)"

#eval expect (checkRefusal (probe "RefBare" "(y: { val a: { type T }; type B = a.T }) => y") ==
    some ⟨⟨3, 51⟩, "`a` is a member of the enclosing refinement: members are named through a path"⟩)
  "rule 3: a bare field of a refinement at the head of a path (RefBare, scalac exit 0)"

/-! ### Rule 4: `this` names a template, outside dependent function types -/

#eval expect (checked (probe "LPp" "(p: { type A <: Any => this.A }) => p"))
  "rule 4: `this` in a refinement under a plain arrow (LPp, LP's `p` alone; scalac warns, exit 0)"

#eval expect (checkRefusal (probe "ThisProbe" "(f: (y: Any) => { type A; val a: this.A }) => f") ==
    some ⟨⟨3, 50⟩, "inside `(x: S) => T` scalac reads `this` as the enclosing object"⟩)
  "rule 4: d1 ThisProbe p5, `this` inside a dependent function type (scalac E008)"

#eval expect (checkRefusal (probe "ThisTop" "(x: this.A) => x") ==
    some ⟨⟨3, 21⟩, "`this` outside every refinement and object literal names the wrapper object in Scala"⟩)
  "rule 4: `this` outside every template (ThisTop, scalac E008)"

/-! ### Rule 5: a selection on `this` or a self name names a declared member -/

#eval expect (checked (probe "AccThis" "(p: { type C = Any; val b: { type D = Any; val get: this.D } }) => p"))
  "rule 5: `this.D` in the refinement that declares `D` (AccThis)"

/-- A literal that reaches the outer literal by its self name. -/
private def nestSelf : String := "import scala.reflect.Selectable.reflectiveSelectable
object NestSelf {
  val program: { val b: Any => Any; val c: { val d: Any => Any } } =
    new Object {
      o =>
      val b = (n: Any) => n
      val c: { val d: Any => Any } = new Object { z => val d = o.b }
    }
}
"

#eval expect (checked nestSelf)
  "rule 5: a nested self-named literal reaches the outer literal by its self name (NestSelf)"

#eval expect (checkRefusal (probe "NestRefThis"
    "(p: { type C = Any; val b: { type D = Any; val get: this.C } }) => p") ==
    some ⟨⟨3, 74⟩, "type C is not a member of the refinement (scalac E008)"⟩)
  "rule 5: refute-d3 NestRefThis, `this` is the inner refinement (scalac E008)"

/-- refute-d3 `NestLitThis`, with the outer `val n` replaced by a lambda. -/
private def nestLitThis : String := "import scala.reflect.Selectable.reflectiveSelectable
object NestLitThis {
  val program: { val b: Any; val c: { val d: Any } } =
    new Object {
      val b = (n: Any) => n
      val c: { val d: Any } = new Object { z => val d = this.b }
    }
}
"

#eval expect (checkRefusal nestLitThis ==
    some ⟨⟨6, 62⟩, "value b is not a member of the object literal (scalac E008)"⟩)
  "rule 5: refute-d3 NestLitThis, `this` is the inner literal (scalac E008)"

/-! ### Rule 6: the binder of a dependent function type occurs in its result -/

#eval expect (checked (probe "AccDep" "(f: (x: { type A }) => x.A) => f"))
  "rule 6: a dependent function type whose result names its binder (AccDep)"

#eval expect (checkRefusal (probe "DepUnused"
    "(f: ((x: { val a: Any }) => Any) & ((x: Any) => Any)) => (y: Any) => f(y)") ==
    some ⟨⟨3, 42⟩, "the parameter `x` does not occur in the result: write `S => T`"⟩)
  "rule 6: d3 DepUnused, an unused binder at its arrow (scalac E051)"

/-! ### Rule 7: names that Scala reads as something else -/

#eval expect (checked (probe "AccNames" "(waits: { val equal: Any; type Clone }) => waits.equal"))
  "rule 7: names near the refused ones (AccNames)"

#eval expect (checkRefusal (probe "N3" "(x: { type Nothing; val a: Nothing }) => { val y: { val b: Any } = x.a; y }") ==
    some ⟨⟨3, 28⟩, "a member named `Nothing` hides the type `Nothing` in Scala: rename it"⟩)
  "rule 7: refute-d1 N3, a member named `Nothing` (scalac E007)"

#eval expect (checkRefusal (probe "U1" "(f: Any => Any) => { val g: Any => Any = f(_); g }") ==
    some ⟨⟨3, 60⟩, "placeholders are outside the subset"⟩)
  "rule 7: refute-d1 U1, `_` refused by the lexer (scalac reads a placeholder, exit 0)"

#eval expect (checkRefusal (probe "KwDo" "(do: Any) => do") ==
    some ⟨⟨3, 18⟩, "`do` is outside the subset"⟩)
  "rule 7: refute-d3 KwDo, refused by the parser (scalac E018)"

#eval expect (checkRefusal (probe "KwThen" "(then: Any) => then") ==
    some ⟨⟨3, 18⟩, "`then` is outside the subset"⟩)
  "rule 7: refute-d3 KwThen, refused by the parser (scalac E018)"

#eval expect (checkRefusal (probe "KwWith" "(with: Any) => with") ==
    some ⟨⟨3, 18⟩, "`with` is outside the subset"⟩)
  "rule 7: refute-d3 KwWith, refused by the parser (scalac E018)"

#eval expect (checkRefusal (probeTyped "ObjMember" "Any" "new Object { val toString = (n: Any) => n }") ==
    some ⟨⟨3, 39⟩, "`toString` is a member of every Scala object: rename it"⟩)
  "rule 7: refute-d3 ObjMember, a literal member `toString` (scalac E164)"

#eval expect (checkRefusal (probe "ObjMember3" "(x: { val getClass: Any }) => x.getClass") ==
    some ⟨⟨3, 27⟩, "`getClass` is a member of every Scala object: rename it"⟩)
  "rule 7: refute-d3 ObjMember3, a refinement member `getClass` (scalac E133)"

#eval expect (checkRefusal (probeTyped "WaitTop" "Any" "new Object { val wait = (n: Any) => n }") ==
    some ⟨⟨3, 39⟩, "`wait` is a member of every Scala object: rename it"⟩)
  "rule 7: refute-d3 WaitTop as a field (scalac E164)"

#eval expect (checkRefusal (probe "WaitParam" "(wait: Any) => (new Object { val a = wait }: { val a: Any })") ==
    some ⟨⟨3, 18⟩, "`wait` is a member of every Scala object: rename it"⟩)
  "rule 7: a parameter `wait`, which a literal inside hides (WaitParam, scalac E049)"

#eval expect (checkRefusal (probe "Wild2" "(_: { val a: Any }) => { val y = (_: { val a: Any }); y.a }") ==
    some ⟨⟨3, 18⟩, "placeholders are outside the subset"⟩)
  "rule 7: refute-d3 Wild2, `_` refused by the lexer (scalac E017)"

#eval expect (checkRefusal (probe "LowerType" "(x: { type a }) => x") ==
    some ⟨⟨3, 28⟩, "the type member `a` starts lower case: type members start upper case"⟩)
  "rule 7: a type member that starts lower case (LowerType, scalac exit 0)"

#eval expect (checkRefusal (probe "UpperField" "(x: { val A: Any }) => x") ==
    some ⟨⟨3, 27⟩, "the field `A` starts upper case: fields start lower case"⟩)
  "rule 7: a field that starts upper case (UpperField, scalac exit 0)"

#eval expect (checkRefusal (probe "UpperSel" "(x: { val a: Any }) => (y: x.a) => y") ==
    some ⟨⟨3, 46⟩, "the type member `a` starts lower case: type members start upper case"⟩)
  "rule 7: a type selection of a lower case name"

#eval expect (checkRefusal (probeCap "CapsVar" "k1: Cap^" "(caps: Any) => (f: Any ->{caps.any} Any) => f") ==
    some ⟨⟨5, 28⟩, "`caps` names the package of `caps.any` in Scala: rename it"⟩)
  "rule 7: a parameter `caps`, which turns `caps.any` into a selection (CapsVar, scalac E008)"

/-- The refusal of `check` on a program built by hand, whose body is `t`. -/
private def handRefusal (t : Tm) : Option Err :=
  match check { imports := [], name := "T", prelude := [], params := none, ty := none, body := t } with
  | .error e => some e
  | .ok _ => none

#eval expect (handRefusal (.lam ⟨1, 1⟩ "do" none (.var ⟨1, 2⟩ "do")) == some ⟨⟨1, 1⟩, "`do` is a keyword of Scala"⟩)
  "rule 7: `check` refuses a keyword in a tree built by hand"

#eval expect (handRefusal (.lam ⟨1, 1⟩ "a$b" none (.var ⟨1, 2⟩ "a$b")) ==
    some ⟨⟨1, 1⟩, "`a$b` is not a name of the subset: a letter, then letters, digits and `_`"⟩)
  "rule 7: `check` refuses `$` in a tree built by hand"

/-! ### Rule 8: one definition per name in a block, a template, the header -/

#eval expect (checked (probe "AccDup"
    "(y: { val a: Any }) => (z: { val a: { val b: Any } }) => { val w = z.a; { val w = y.a; w } }"))
  "rule 8: one name in two refinements and in two blocks (AccDup)"

#eval expect (checkRefusal (probe "D1" "(x: Any) => { val y = x; val y = (z: Any) => z; y }") ==
    some ⟨⟨3, 46⟩, "`y` is already defined in this block (scalac E161)"⟩)
  "rule 8: refute-d1 D1, at the second `y` (scalac E161 there)"

#eval expect (checkRefusal (probe "D3" "(y: { val a: Any; val a: { val b: Any } }) => y.a.b") ==
    some ⟨⟨3, 39⟩, "conflicting definitions of `a` in one refinement (scalac E120)"⟩)
  "rule 8: refute-d1 D3, at the second `a` (scalac E120 there)"

#eval expect (checkRefusal (probe "DupBlock" "(n: Any) => { val y = n; val y = n; y }") ==
    some ⟨⟨3, 46⟩, "`y` is already defined in this block (scalac E161)"⟩)
  "rule 8: refute-d3 DupBlock (scalac E161 at the same place)"

#eval expect (checkRefusal (probe "DupRef" "(y: { val a: Any; val a: { val b: Any } }) => { val z = y.a; z.b }") ==
    some ⟨⟨3, 39⟩, "conflicting definitions of `a` in one refinement (scalac E120)"⟩)
  "rule 8: refute-d3 DupRef (scalac E120 at the same place)"

#eval expect (checkRefusal (probe "DupRefType"
    "(y: { type A <: { val a: Any }; type A >: Any }) => (w: Any) => (w: y.A)") ==
    some ⟨⟨3, 54⟩, "`A` is already defined in this refinement (scalac E161)"⟩)
  "rule 8: refute-d3 DupRefType (scalac E161 at the same place)"

#eval expect (checkRefusal (probe "DupLit" "(n: Any) => (new Object { val a = n; val a = n }: { val a: Any })") ==
    some ⟨⟨3, 58⟩, "conflicting definitions of `a` in one object literal (scalac E120)"⟩)
  "rule 8: two members of one name in a literal (DupLit, scalac E120 at the same place)"

#eval expect (checkRefusal (probe "SelfMember" "(n: Any) => (new Object { a => val a = n }: { val a: Any })") ==
    some ⟨⟨3, 52⟩, "conflicting definitions of the self name and the member `a` (scalac E120)"⟩)
  "rule 8: a self name that is a member's name (SelfMember, scalac E120)"

#eval expect (checkRefusal (probeCap "DupParam" "k: Cap^, k: Cap^" "(u: Any) => u") ==
    some ⟨⟨5, 24⟩, "`k` is already defined as a parameter of `program` (scalac E161)"⟩)
  "rule 8: two parameters of one name (DupParam, scalac E161 at the same place)"

#eval expect (checkRefusal (captureImports ++ "object DupClass {\n  class Cap extends caps.SharedCapability\n" ++
      "  class Cap extends caps.SharedCapability\n  def program(k: Cap^) = (u: Any) => u\n}\n") ==
    some ⟨⟨5, 9⟩, "`Cap` is already defined in the prelude (scalac E161)"⟩)
  "rule 8: two prelude classes of one name (DupClass, scalac E161 at the same place)"

/-! ### Rule 9: a block `val` names neither itself nor a later `val` -/

#eval expect (checked (probe "AccShadow" "(x: Any) => { val x = (y: Any) => y; x }"))
  "rule 9: a block val may shadow a parameter that its right side does not name (AccShadow)"

#eval expect (checkRefusal (probe "V08" "(x: { val a: Any }) => { val x = x.a; x }") ==
    some ⟨⟨3, 50⟩, "recursive value `x` needs a type: its right side names it (scalac E045)"⟩)
  "rule 9: d2 V08, the right side names the val, not the parameter (scalac E045 at the same place)"

#eval expect (checkRefusal (probe "V18" "(c: Any) => { val a: Any = b; val b: Any = c; a }") ==
    some ⟨⟨3, 44⟩, "forward reference: `b` is defined later in this block (scalac E039)"⟩)
  "rule 9: d2 V18, a later val (scalac E039 at the same place)"

#eval expect (checkRefusal (probe "SelfTyped" "(x: Any) => { val y: Any = y; x }") ==
    some ⟨⟨3, 44⟩, "forward reference: the right side of `y` names it (scalac E039)"⟩)
  "rule 9: a typed val that names itself (SelfTyped, scalac E039 at the same place)"

/-! ### Rule 10: a literal stands under a written type -/

#eval expect (checked (probe "AccLit" "(w: Any) => { val o: { val get: Any } = new Object { val get = w }; o.get }"))
  "rule 10: a literal as the right side of a typed val (AccLit)"

#eval expect (checkRefusal (probe "TodayProbe" "(w: Any) => { val o = new Object { val get = w }; o.get }") ==
    some ⟨⟨3, 39⟩, "an object literal needs a written type: scalac types it as Object"⟩)
  "rule 10: the scout's Probe, a literal as an untyped val (scalac E008 at `o.get`)"

#eval expect (checkRefusal (probe "LitArg" "(f: { val a: Any } => Any) => f(new Object { val a = f })") ==
    some ⟨⟨3, 49⟩, "an object literal needs a written type: write `(new Object { … }: T)`"⟩)
  "rule 10: a literal as an argument (LitArg, scalac exit 0)"

#eval expect (checkRefusal (probe "LitRecv" "(w: Any) => (new Object { val get = w }).get") ==
    some ⟨⟨3, 30⟩, "an object literal needs a written type: write `(new Object { … }: T)`"⟩)
  "rule 10: a literal as the receiver of a selection"

#eval expect (checkRefusal (probe "LitBody" "(w: Any) => new Object { val get = w }") ==
    some ⟨⟨3, 29⟩, "an object literal needs a written type: write `(new Object { … }: T)`"⟩)
  "rule 10: a literal as a lambda body"

#eval expect (checkRefusal (probe "LitProg" "new Object { val get = (w: Any) => w }") ==
    some ⟨⟨3, 17⟩, "an object literal needs a written type: scalac types it as Object"⟩)
  "rule 10: a literal as an untyped `val program`"

/-! ### Rule 11: no cyclic alias or lower bound -/

#eval expect (checked (probe "AccChain" "(x: { type A = this.B; type B = Any }) => x"))
  "rule 11: an alias that reaches another member, no cycle (AccChain)"

#eval expect (checkRefusal (probe "LPsrc"
    "(p: { type A <: Any => this.A }) => (q: { type B >: Any => this.B }) => (x: p.A) => { val r: q.B = x; r }") ==
    some ⟨⟨3, 64⟩, "illegal cyclic type reference: the lower bound of `B` refers back to `B` (scalac E140)"⟩)
  "rule 11: d2 LPsrc, at `B`, the upper F-bound of `A` passes (scalac E140 at the same place)"

#eval expect (checkRefusal (probe "CycAlias" "(x: { type A = this.B; type B = this.A }) => x") ==
    some ⟨⟨3, 28⟩, "illegal cyclic type reference: the alias of `A` refers back to `A` (scalac E140)"⟩)
  "rule 11: two aliases in a cycle, at the first (CycAlias, scalac E140 at the same place)"

#eval expect (checked (probe "FSelfRef" "(x: { type A <: Any => this.A; type B = this.A }) => x"))
  "rule 11: an upper F-bound that another member selects (FSelfRef; scalac warns, exit 0)"

#eval expect (checkRefusal (probe "CycUpper" "(x: { type A <: this.B; type B <: this.A }) => x") ==
    some ⟨⟨3, 28⟩, "illegal cyclic type reference: the upper bound of `A` refers back to `A` (scalac E140)"⟩)
  "rule 11: upper bounds in a cycle outside function types (CycUpper, scalac E140 at the same place)"

#eval expect (checkRefusal (probe "UpFun2" "(x: { type A <: Any => this.B; type B <: Any => this.A }) => x") ==
    some ⟨⟨3, 28⟩,
      "illegal cyclic type reference: the upper bound of `A` refers back to `A` (scalac exceeds its recursion limit)"⟩)
  "rule 11: two upper F-bounds in a cycle (UpFun2, scalac: recursion limit exceeded)"

/-! ### Rule 12: platform names in capture sets, prelude names as classes -/

#eval expect (checked capP && checked clsP)
  "rule 12: the judge's CapP and ClsP, platform names in capture sets"

#eval expect (checkRefusal (probeCap "PlatTerm" "k1: Cap^" "(u: Any) => k1") ==
    some ⟨⟨5, 39⟩, "`k1` is a platform name: it stands only in capture sets"⟩)
  "rule 12: a platform name as a term (PlatTerm, scalac exit 0)"

#eval expect (checkRefusal (probeCap "PreludeVar" "k1: Cap^" "(Cap: Any) => Cap") ==
    some ⟨⟨5, 28⟩, "`Cap` is a class or trait of the prelude: rename it"⟩)
  "rule 12: a prelude class as a variable (PreludeVar, scalac exit 0)"

#eval expect (checkRefusal (probeCap "PreludeUse" "k1: Cap^" "(u: Any) => Cap") ==
    some ⟨⟨5, 39⟩, "`Cap` is a class or trait of the prelude, not a value"⟩)
  "rule 12: a prelude class as a term (PreludeUse, scalac E195)"

/-! ### Whole files -/

#eval expect (checked e5 && checked layA && checked layC)
  "files: E5, LayA and LayC pass the checks"

/-! ## The label table -/

/-- The label table of a text, or `none` when the reader refuses it. -/
def labelsOf (s : String) : Option (List (String × Bool)) := (parseFile s.toList).toOption.map labels

#eval expect (labelsOf e5 == some [("A", true), ("a", false)])
  "labels: E5"

#eval expect (labelsOf layC == some [("A", true), ("a", false), ("b", false), ("c", false), ("d", false)])
  "labels: LayC, in order of first appearance"

#eval expect (labelsOf capP == some [("e1", false), ("e2", false), ("C", true)])
  "labels: CapP, the capture member `C` is a type label"

#eval expect (labelsOf (probe "AccThis" "(p: { type C = Any; val b: { type D = Any; val get: this.D } }) => p") ==
    some [("C", true), ("b", false), ("D", true), ("get", false)])
  "labels: nested refinements, declared names in the order of the text"

/-! ## The printer

`print` of E5's tree is the text of `E5.scala` without its comment line.  The
judge's `CapP` and `ClsP` are written in the printer's layout and print back
to their own text, with the comment line left blank.  Then each rule of the
layout on a small program, and the round trip (R): every program above that
the reader accepts prints to a text that reads back to its tree, up to
positions.  The kernel checks the round trip of E5 in
`notes-scala-xv0/kernel-read.lean`. -/

/-- The printed text of a text that the reader reads, or `none`. -/
def printed (s : String) : Option String :=
  (parseFile s.toList).toOption.map fun P => String.ofList (print P)

/-- Whether a text reads to a tree whose printed text reads back to that
tree, up to positions. -/
def roundTrips (s : String) : Bool :=
  match parseFile s.toList with
  | .ok P => (parseFile (print P)).toOption.map Program.erase == some P.erase
  | .error _ => false

/-- A text without its comment lines, those that start with `//`. -/
def withoutComments (s : String) : String :=
  "\n".intercalate ((s.splitOn "\n").filter fun l => !l.startsWith "//")

/-- A text with its comment lines left blank. -/
def blankComments (s : String) : String :=
  "\n".intercalate ((s.splitOn "\n").map fun l => if l.startsWith "//" then "" else l)

#eval expect (String.ofList (print e5Prog) == withoutComments e5 && printed e5 == some (withoutComments e5))
  "print: E5's tree is the text of E5.scala without its comment line"

#eval expect (printed capP == some (blankComments capP))
  "print: the judge's CapP prints back to its text, the comment line blank"

#eval expect (printed clsP == some (blankComments clsP))
  "print: the judge's ClsP prints back to its text, the comment line blank"

private def layCPrinted : String := "import scala.reflect.Selectable.reflectiveSelectable

object LayC {
  val program =
    (x: { type A; val a: this.A }) =>
      (y: { val b: Any } & { val c: Any }) => {
        val u = x.a
        val o: { val d: Any } =
          new Object {
            val d = u
          }
        o.d
      }
}
"

#eval expect (printed layC == some layCPrinted)
  "print: LayC in the printer's layout, its short refinements on one line"

/-! ### The rules of the layout -/

/-- The printed text of a vanilla file whose program `e` stays on the line of
`val program =`. -/
private def vanillaP (e : String) : String :=
  "import " ++ selectable ++ "\n\nobject T {\n  val program = " ++ e ++ "\n}\n"

/-- The printed text of a Captures file whose program `e` stays on the line
of `def program(k1: Cap^, k2: Cap^) =`. -/
private def capturesP (e : String) : String :=
  captureImports ++ "\nobject T {\n  class Cap extends caps.SharedCapability\n" ++
    "  def program(k1: Cap^, k2: Cap^) = " ++ e ++ "\n}\n"

-- Parentheses where Scala would read the text otherwise, and none elsewhere.
#eval expect (printed (vanilla "(x: { val a: Any } & ({ val b: Any } & { val c: Any })) => x") ==
    some (vanillaP "(x: { val a: Any } & ({ val b: Any } & { val c: Any })) => x"))
  "print: a right-nested `&` gets parentheses, `A & (B & C)`"

#eval expect (printed (vanilla "(x: { val a: Any } & { val b: Any } & { val c: Any }) => x") ==
    some (vanillaP "(x: { val a: Any } & { val b: Any } & { val c: Any }) => x"))
  "print: a left-nested `&` gets none"

#eval expect (printed (vanilla "(f: (Any => Any) & (Any => Any)) => (g: (Any => Any) => Any) => f") ==
    some (vanillaP "(f: (Any => Any) & (Any => Any)) => (g: (Any => Any) => Any) => f"))
  "print: a function type as an operand of `&` or as a domain gets parentheses"

#eval expect (printed (vanilla "(f: ((x: { type A }) => x.A) => Any) => f") ==
    some (vanillaP "(f: ((x: { type A }) => x.A) => Any) => f"))
  "print: a dependent function type as a domain gets parentheses"

#eval expect (printed (captures "(x: ({ val a: Any } & { val b: Any })^{k1}) => (f: (Any => Any)^{k2}) => x") ==
    some (capturesP "(x: ({ val a: Any } & { val b: Any })^{k1}) => (f: (Any => Any)^{k2}) => x"))
  "print: an intersection or a function type under `^` gets parentheses"

#eval expect (printed (captures "(f: ({ val a: Any }^) & { val b: Any } & { val c: Any }^) => f") ==
    some (capturesP "(f: ({ val a: Any }^) & { val b: Any } & { val c: Any }^) => f"))
  "print: a bare `^` before `&` gets parentheses (probe HatAnd), at the end none"

#eval expect (printed (captures "(f: ({ val a: Any }^{k1})^{k2}) => f") ==
    some (capturesP "(f: ({ val a: Any }^{k1})^{k2}) => f"))
  "print: a capturing type under `^` gets parentheses"

#eval expect (printed (vanilla "(((x: Any) => x): Any => Any)") == some (vanillaP "(((x: Any) => x): Any => Any)"))
  "print: a lambda under an ascription gets its own parentheses"

#eval expect (printed (vanilla "(w: Any) => ((x: Any) => x)(w)") == some (vanillaP "(w: Any) => ((x: Any) => x)(w)"))
  "print: a lambda as a function gets parentheses"

#eval expect (printed (vanilla "(x: Any) => y => (z) => x") == some (vanillaP "(x: Any) => y => z => x"))
  "print: an untyped parameter prints without parentheses"

/-- A refinement of three fields whose names are 20, 20 and `n` long. -/
private def wide (n : Nat) : String :=
  "{ val " ++ String.ofList (List.replicate 20 'a') ++ ": Any; val " ++ String.ofList (List.replicate 20 'b') ++
    ": Any; val " ++ String.ofList (List.replicate n 'c') ++ ": Any }"

#eval expect ((wide 25).length == 100 && printed (vanilla ("(x: " ++ wide 25 ++ ") => x")) ==
    some (vanillaP ("(x: " ++ wide 25 ++ ") => x")))
  "print: a refinement of three members in 100 columns stays on one line"

#eval expect (printed (vanilla ("(x: " ++ wide 26 ++ ") => x")) == some ("import " ++ selectable ++
    "\n\nobject T {\n  val program =\n    (x: {\n      val " ++ String.ofList (List.replicate 20 'a') ++
    ": Any\n      val " ++ String.ofList (List.replicate 20 'b') ++ ": Any\n      val " ++
    String.ofList (List.replicate 26 'c') ++ ": Any\n    }) => x\n}\n"))
  "print: a refinement in 101 columns spans lines, and so does the program after `=`"

#eval expect (printed (vanilla
      "(x: { type A >: Nothing <: Any; type B; type C = Any; type D <: Any; type E >: Nothing }) => x") ==
    some ("import " ++ selectable ++ "\n\nobject T {\n  val program =\n    (x: {\n" ++
      "      type A >: Nothing <: Any\n      type B\n      type C = Any\n      type D <: Any\n" ++
      "      type E >: Nothing\n    }) => x\n}\n"))
  "print: a refinement of five members spans lines"

#eval expect (printed (vanilla "(x: { val a: { val b: Any; val c: Any; val d: Any; val e: Any } }) => x") ==
    some ("import " ++ selectable ++ "\n\nobject T {\n  val program =\n    (x: {\n      val a: {\n" ++
      "        val b: Any\n        val c: Any\n        val d: Any\n        val e: Any\n      }\n    }) => x\n}\n"))
  "print: a refinement that holds a long one spans lines too"

#eval expect (printed (vanillaTyped "{ val a: Any }" "new Object { s => val a = s }") ==
    some ("import " ++ selectable ++ "\n\nobject T {\n  val program: { val a: Any } =\n    new Object {\n" ++
      "      s =>\n      val a = s\n    }\n}\n"))
  "print: a literal spans lines, its self name on a line of its own (probe SelfLines of scalac-g2)"

#eval expect (printed (vanilla "(w: Any) => { val x = { w }; x }") ==
    some ("import " ++ selectable ++ "\n\nobject T {\n  val program =\n    (w: Any) => {\n" ++
      "      val x = {\n        w\n      }\n      x\n    }\n}\n"))
  "print: a block spans lines, and its `{` stays on the line of `=` or `=>`"

#eval expect (printed (probe "AccDup"
      "(y: { val a: Any }) => (z: { val a: { val b: Any } }) => { val w = z.a; { val w = y.a; w } }") ==
    some ("import " ++ selectable ++ "\n\nobject AccDup {\n  val program =\n    (y: { val a: Any }) =>\n" ++
      "      (z: { val a: { val b: Any } }) => {\n        val w = z.a\n        {\n          val w = y.a\n" ++
      "          w\n        }\n      }\n}\n"))
  "print: a block as the result of a block starts its own line (probe BlkRes of scalac-g4)"

/-! ### The round trip -/

/-- The programs of the checks above that the reader reads, those of the
checks of `check` that it accepts, the whole files, and the programs of the
layout rules, by name.  Each prints to a text that reads back to its tree. -/
def accepted : List (String × String) :=
  [("vanilla row Any, Nothing", vanilla "(x: Any) => (y: Nothing) => x"),
   ("vanilla row x.A, this.A", vanilla "(x: { type A; val a: this.A }) => (y: x.A) => y"),
   ("vanilla row a refinement over several lines",
     vanilla "(x: {\n      type A\n      val a: this.A\n      val b: Any\n    }) => x"),
   ("vanilla row type A >: S <: T, type A, type A = T",
     vanilla "(x: { type A >: Nothing <: Any; type B; type C = Any; type D <: Any; type E >: Nothing }) => x"),
   ("vanilla row val a: T in a refinement", vanilla "(x: { val a: { val b: Any } }) => x.a.b"),
   ("vanilla row S & T", vanilla "(x: { val a: Any } & { val b: Any } & { val c: Any }) => x"),
   ("vanilla row (x: S) => T, S => T", vanilla "(f: (x: { type A }) => x.A) => (g: Any => Any => Any) => f"),
   ("vanilla row (x: T) => e, x => e, (x) => e", vanilla "(x: Any) => y => (z) => x"),
   ("vanilla row f(e), e.a", vanilla "(f: Any => { val a: Any }) => (x: Any) => f(x).a"),
   ("vanilla row (e: T)", vanilla "(x: Any) => (x: Any)"),
   ("vanilla row { val x = e; r }, { e }", vanilla "(w: Any) => { val x = { w }; x }"),
   ("vanilla row { val x: T = e; r }", vanilla "(w: Any) => { val x: Any = w; w }"),
   ("vanilla row { …; val x: T = e; x }", vanilla "(w: Any) => {\n    val y = w\n    val x: Any = y\n    x\n  }"),
   ("vanilla row a self-named literal", vanillaTyped "{ val a: Any }" "new Object { s => val a = s }"),
   ("vanilla row the members of a literal", vanilla
     "(w: Any) => (new Object { type A = Any; val a = w; val b: Any = w }: { type A = Any; val a: Any; val b: Any })"),
   ("vanilla row val program: T = e", vanillaTyped "Any => Any" "(x: Any) => x"),
   ("Captures row def program", captures "(u: Any) => u"),
   ("Captures row S -> T", captures "(f: Any -> Any) => f"),
   ("Captures row S ->{k1} T", captures "(f: Any ->{k1} Any) => f"),
   ("Captures row S => T", captures "(f: Any => Any) => f"),
   ("Captures row T^{k1, k2}", captures "(x: { val a: Any }^{k1, k2}) => x"),
   ("Captures row T^", captures "(x: { val a: Any }^) => x"),
   ("Captures row caps.any", captures "(f: Any ->{caps.any} Any) => f"),
   ("Captures row type C^ >: {k1} <: {k1, k2}", captures "(x: { type C^ >: {k1} <: {k1, k2} }) => x"),
   ("Captures type C^ = {k1}", captures "(new Object { type C^ = {k1} }: { type C^ = {k1} })"),
   ("Captures -> before a refinement, ->{}", captures "(f: Any -> { val a: Any }) => (g: Any ->{} Any) => f"),
   ("Classifiers row a root classifier", classifiers ["trait IO extends caps.SharedCapability, caps.Classifier",
     "class Cap extends caps.SharedCapability"] "k: Cap^" "(u: Any) => u"),
   ("Classifiers row a child classifier", classifiers
     ["trait ThreadLocal extends caps.SharedCapability, caps.Classifier",
      "trait Control extends ThreadLocal, caps.Classifier", "class Cap extends caps.SharedCapability"]
     "k: Cap^" "(u: Any) => u"),
   ("Classifiers row a platform class", classifiers ["trait Control extends caps.SharedCapability, caps.Classifier",
     "class CtlCap extends Control"] "ctl: CtlCap^" "(u: Any) => u"),
   ("Classifiers row x.only[K]", classifiers ["trait Control extends caps.SharedCapability, caps.Classifier",
     "class CtlCap extends Control"] "ctl: CtlCap^"
     "(f: Any ->{ctl.only[Control]} Any) => (x: { type C^ <: {caps.any.only[Control]} }) => f"),
   ("header val program: T = e", vanillaTyped "Any" "(x: Any)"),
   ("header def program(k1: Cap^): T = e",
     captureImports ++ "object T {\n  class Cap extends caps.SharedCapability\n  def program(k1: Cap^): Any = k1\n}\n"),
   ("header the capture imports with val program",
     captureImports ++ "object T {\n  val program = (f: Any => Any) => f\n}\n"),
   ("the lambda in its own parentheses", vanilla "(((x: Any) => x): Any => Any)"),
   ("(S^) & T", captures "(f: ({ val a: Any }^) & { val b: Any }) => f"),
   ("E5", e5), ("LayA", layA), ("LayC", layC), ("CapP", capP), ("ClsP", clsP),
   ("AccScope", probe "AccScope" "(x: { val a: Any }) => { val y = x.a; val z = y; z }"),
   ("AccM1", probe "AccM1"
     "(f: Any => Any) => (new Object { s => val a: Any = s; val b: Any => Any = f }: { val a: Any; val b: Any => Any })"),
   ("AccM2", probe "AccM2"
     "(new Object { s => val a = (y: Any) => y; val b = s.a }: { val a: Any => Any; val b: Any => Any })"),
   ("LPp", probe "LPp" "(p: { type A <: Any => this.A }) => p"),
   ("AccThis", probe "AccThis" "(p: { type C = Any; val b: { type D = Any; val get: this.D } }) => p"),
   ("NestSelf", nestSelf),
   ("AccDep", probe "AccDep" "(f: (x: { type A }) => x.A) => f"),
   ("AccNames", probe "AccNames" "(waits: { val equal: Any; type Clone }) => waits.equal"),
   ("AccDup", probe "AccDup"
     "(y: { val a: Any }) => (z: { val a: { val b: Any } }) => { val w = z.a; { val w = y.a; w } }"),
   ("AccShadow", probe "AccShadow" "(x: Any) => { val x = (y: Any) => y; x }"),
   ("AccLit", probe "AccLit" "(w: Any) => { val o: { val get: Any } = new Object { val get = w }; o.get }"),
   ("AccChain", probe "AccChain" "(x: { type A = this.B; type B = Any }) => x"),
   ("FSelfRef", probe "FSelfRef" "(x: { type A <: Any => this.A; type B = this.A }) => x"),
   ("layout A & (B & C)", vanilla "(x: { val a: Any } & ({ val b: Any } & { val c: Any })) => x"),
   ("layout function types under & and as domains",
     vanilla "(f: (Any => Any) & (Any => Any)) => (g: (Any => Any) => Any) => f"),
   ("layout a dependent domain", vanilla "(f: ((x: { type A }) => x.A) => Any) => f"),
   ("layout & and => under ^", captures "(x: ({ val a: Any } & { val b: Any })^{k1}) => (f: (Any => Any)^{k2}) => x"),
   ("layout bare ^ around &", captures "(f: ({ val a: Any }^) & { val b: Any } & { val c: Any }^) => f"),
   ("layout ^ under ^", captures "(f: ({ val a: Any }^{k1})^{k2}) => f"),
   ("layout a lambda as a function", vanilla "(w: Any) => ((x: Any) => x)(w)"),
   ("layout 100 columns", vanilla ("(x: " ++ wide 25 ++ ") => x")),
   ("layout 101 columns", vanilla ("(x: " ++ wide 26 ++ ") => x")),
   ("layout a long refinement inside a short one",
     vanilla "(x: { val a: { val b: Any; val c: Any; val d: Any; val e: Any } }) => x"),
   ("header val program = e", vanilla "(x: Any) => x")]

#eval accepted.forM fun (n, s) => expect (roundTrips s) ("round trip: " ++ n)

#eval expect (accepted.length == 64) "round trip: sixty-four programs"

#eval expect (accepted.all fun (_, s) => printed s == (printed s).bind printed)
  "round trip: a printed text prints to itself"

end ScalaSyntax.Tests
