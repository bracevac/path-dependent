import Coercions.Nominal.Frontend.ScalaRead.Parse
import Coercions.Nominal.Frontend.ScalaRead.Scope
import Coercions.Nominal.Frontend.ScalaRead.Print
import Coercions.Nominal.Frontend.Surface

/-!
# Checks of the pDOT Scala reader

String checks by `#eval expect`, where a false check throws and fails the
build.  The texts are Lean string literals, never files, so a change to a text
rebuilds this module.  `String.toList` runs here in compiled code only, and no
theorem mentions it.

The parser checks put each row of the grammar (plan XI, "XS: the Scala
subset") into a minimal file and compare the tree, with its positions erased.
The refusal checks give each refusal of the parser at its line and column with
its message, as the planner's `notes-pdot-xs1a/plan/PTable.lean` found them.

The kind checks give the word of a path's kind at the innermost body of
`program`, one row of the kind table each, as `notes-pdot-xs1a/plan/P7Kinds.lean`
found them.  Then the shortest unstable prefix of R08, and the module chains of
three XS0 files.

The rule checks give the verdict of `check` on one text per rule, taken or
refused at its line and column with its message, the planner's
`notes-pdot-xs1a/plan/table.planner.out.txt` with the two endings of R-Y.  The
label checks give the table of Fig1, a name at both sorts, and `ℓself` last.

The printer checks give the printed text of three XS0 files, as the planner's
`notes-pdot-xs1a/plan/P5Corpus.lean` printed them.  Then the round trip: every
text of this file that `check` takes reads back from its printed text to the
same tree up to positions.

The class checks (plan XII, stage N5) give each new row of the grammar with its tree, each refusal of
the parser and of the walk at its line and column with its message, the planner's
`notes-nominal-n5/plan/T4Rules.out.txt`, the rows of the refutation's repairs (`notes-nominal-n5/revise/`), the
kinds of class instances, the label table of a class file, and the printed text of a class file.  Their texts
join the round trip.
-/

namespace NominalFrontend.ScalaRead.Tests

open NominalFrontend.ScalaRead
open NominalFrontend.ScalaRead.Parse (msgRA msgRP msgRO msgProgram msgDefTerm msgAfter msgExtends msgRI
  msgHeader msgRLC msgRCC msgROE msgRAN msgRSU msgRW msgRTP msgRMO)
open ScalaSyntax (Pos Err)

/-- The tree of a text with its positions erased, or `none` when it is refused. -/
def parsed (s : String) : Option File := (parseFile s.toList).toOption.map File.erase

/-- The refusal of a text, or `none` when it is read. -/
def refusal (s : String) : Option Err :=
  match parseFile s.toList with
  | .error e => some e
  | .ok _ => none

/-- A test file: the header, a blank line, `object A {` on line 3, the lines
indented by two, `}`. -/
def file (ls : List String) : String :=
  "import scala.reflect.Selectable.reflectiveSelectable\n\nobject A {\n" ++
    String.join (ls.map fun l => "  " ++ l ++ "\n") ++ "}\n"

/-- The erased position. -/
def z : Pos := ScalaSyntax.Pos.zero

/-! ## The grammar, one row each -/

-- Program typed
#eval expect (parsed (file ["val program: Any = A"]) ==
  some ⟨z, "A", .nil, some (.any z), .path (.var z "A")⟩) "program typed"

-- Member object, with self
#eval expect (parsed (file ["object o { s => type T = Any }", "val program = o"]) ==
  some ⟨z, "A", .obj z "o" (some "s") (.typ z "T" (.any z) .nil) .nil, none, .path (.var z "o")⟩)
  "member object with self"

-- Member type alias
#eval expect (parsed (file ["object o { type T = Any }", "val program = o"]) ==
  some ⟨z, "A", .obj z "o" none (.typ z "T" (.any z) .nil) .nil, none, .path (.var z "o")⟩)
  "member type alias"

-- Member val untyped, typed
#eval expect (parsed (file ["object o { val f = (u: Any) => u; val g: Any => Any = (u: Any) => u }",
    "val program = o"]) ==
  some ⟨z, "A",
    .obj z "o" none
      (.val z "f" none (.lam z "u" (some (.any z)) (.path (.var z "u")))
        (.val z "g" (some (.fn z none (.any z) (.any z))) (.lam z "u" (some (.any z)) (.path (.var z "u"))) .nil))
      .nil,
    none, .path (.var z "o")⟩)
  "member val untyped and typed"

-- Member def, one list and two, result written or not
#eval expect (parsed (file ["def f(x: Any)(y: x.type): x.type = y", "def g(x: Any) = x", "val program = A"]) ==
  some ⟨z, "A",
    .defn z "f" [⟨z, "x", .any z⟩, ⟨z, "y", .sngl z (.var z "x")⟩] (some (.sngl z (.var z "x")))
      (.path (.var z "y"))
      (.defn z "g" [⟨z, "x", .any z⟩] none (.path (.var z "x")) .nil),
    none, .path (.var z "A")⟩)
  "member def"

-- Type: dependent function
#eval expect (parsed (file ["val program = (f: (x: { type B }) => x.B) => f"]) ==
  some ⟨z, "A", .nil, none,
    .lam z "f" (some (.fn z (some "x") (.refine z (.typ z "B" .absent .absent .nil)) (.sel z (.var z "x") "B")))
      (.path (.var z "f"))⟩)
  "dependent function type"

-- Type: function, `&` nested left
#eval expect (parsed (file ["val program = (f: Any => Any & Nothing & Any) => f"]) ==
  some ⟨z, "A", .nil, none,
    .lam z "f" (some (.fn z none (.any z) (.and (.and (.any z) (.nothing z)) (.any z)))) (.path (.var z "f"))⟩)
  "function type, & nested left"

-- Type: path then member, of length three
#eval expect (parsed (file ["object o { object p { object q { type T = Any } } }",
    "val program = (x: o.p.q.T) => x"]) ==
  some ⟨z, "A",
    .obj z "o" none (.obj z "p" none (.obj z "q" none (.typ z "T" (.any z) .nil) .nil) .nil) .nil,
    none,
    .lam z "x" (some (.sel z (.sel (.sel (.var z "o") z "p") z "q") "T")) (.path (.var z "x"))⟩)
  "path of length three then member"

-- Type: `this.a.type`, `this.A`
#eval expect (parsed (file ["val program = (q: { type A; val a: this.A; val b: this.a.type }) => q"]) ==
  some ⟨z, "A", .nil, none,
    .lam z "q"
      (some (.refine z (.typ z "A" .absent .absent
        (.val z "a" (.sel z (.this z) "A") (.val z "b" (.sngl z (.sel (.this z) z "a")) .nil)))))
      (.path (.var z "q"))⟩)
  "this.A and this.a.type"

-- Type: bare member
#eval expect (parsed (file ["val program = (t: { type A; val x: { val y: A } }) => t"]) ==
  some ⟨z, "A", .nil, none,
    .lam z "t"
      (some (.refine z (.typ z "A" .absent .absent (.val z "x" (.refine z (.val z "y" (.name z "A") .nil)) .nil))))
      (.path (.var z "t"))⟩)
  "bare member"

-- Decl bounds: none, lower, upper, both
#eval expect (parsed (file
    ["val program = (q: { type A; type B >: Any; type C <: Any; type D >: Nothing <: Any }) => q"]) ==
  some ⟨z, "A", .nil, none,
    .lam z "q"
      (some (.refine z (.typ z "A" .absent .absent (.typ z "B" (.given (.any z)) .absent
        (.typ z "C" .absent (.given (.any z)) (.typ z "D" (.given (.nothing z)) (.given (.any z)) .nil))))))
      (.path (.var z "q"))⟩)
  "declaration bounds"

-- Expr: the three lambda forms
#eval expect (parsed (file ["val program = (f: Any) => ((x) => x)"]) ==
  some ⟨z, "A", .nil, none, .lam z "f" (some (.any z)) (.lam z "x" none (.path (.var z "x")))⟩)
  "lambda forms (x: T) and (x)"
#eval expect (parsed (file ["val program = x => x"]) ==
  some ⟨z, "A", .nil, none, .lam z "x" none (.path (.var z "x"))⟩)
  "lambda form x"

-- Postfix: a path folded, a selection on an application
#eval expect (parsed (file ["object o { def f(x: Any): o.type = o }", "val program = o.f(o).f(o)"]) ==
  some ⟨z, "A",
    .obj z "o" none (.defn z "f" [⟨z, "x", .any z⟩] (some (.sngl z (.var z "o"))) (.path (.var z "o")) .nil) .nil,
    none,
    .app (.sel (.app (.path (.sel (.var z "o") z "f")) (.path (.var z "o"))) z "f") (.path (.var z "o"))⟩)
  "postfix folds a path"

-- Atom: ascription, of a literal
#eval expect (parsed (file ["val program = (new Object { type T = Any }: { type T })"]) ==
  some ⟨z, "A", .nil, none,
    .asc z (.lit z none (.typ z "T" (.any z) .nil)) (.refine z (.typ z "T" .absent .absent .nil))⟩)
  "ascription of a literal"

-- Block with typed and untyped vals
#eval expect (parsed (file ["val program = {", "  val a = A", "  val b: a.type = a", "  b", "}"]) ==
  some ⟨z, "A", .nil, none,
    .block z (.val z "a" none (.path (.var z "A"))
      (.val z "b" (some (.sngl z (.var z "a"))) (.path (.var z "a")) (.last (.path (.var z "b")))))⟩)
  "block"

-- Literal with a self name on its `{` line (E5m's shape)
#eval expect (parsed (file ["val program: { val a: Any } = new Object { s =>", "  val a: s.type = s", "}"]) ==
  some ⟨z, "A", .nil, some (.refine z (.val z "a" (.any z) .nil)),
    .lit z (some "s") (.val z "a" (some (.sngl z (.var z "s"))) (.path (.var z "s")) .nil)⟩)
  "literal with a self name on its brace line"

-- Sep by `;`
#eval expect (parsed (file ["object o { type T = Any; type U = Any }", "val program = o"]) ==
  some ⟨z, "A", .obj z "o" none (.typ z "T" (.any z) (.typ z "U" (.any z) .nil)) .nil, none, .path (.var z "o")⟩)
  "separated by ;"

-- Simple: a type in parentheses
#eval expect (parsed (file ["val program = (f: (Any => Any) => Any) => f"]) ==
  some ⟨z, "A", .nil, none,
    .lam z "f" (some (.fn z none (.fn z none (.any z) (.any z)) (.any z))) (.path (.var z "f"))⟩)
  "type in parentheses"

-- Decl: a refinement's alias
#eval expect (parsed (file ["val program = (q: { type A = Any; type B = this.A }) => q"]) ==
  some ⟨z, "A", .nil, none,
    .lam z "q" (some (.refine z (.alias z "A" (.any z) (.alias z "B" (.sel z (.this z) "A") .nil))))
      (.path (.var z "q"))⟩)
  "refinement alias"

-- Atom: `this`
#eval expect (parsed (file ["val program = this"]) == some ⟨z, "A", .nil, none, .path (.this z)⟩) "this"

-- Atom: ascription of a path
#eval expect (parsed (file ["object o { type T = Any }", "val program = (o: o.type)"]) ==
  some ⟨z, "A", .obj z "o" none (.typ z "T" (.any z) .nil) .nil, none,
    .asc z (.path (.var z "o")) (.sngl z (.var z "o"))⟩)
  "ascription of a path"

/-! ## The parser's refusals, at their positions -/

/-- The refusal `msg` at `line:col`. -/
def at? (s : String) (line col : Nat) (msg : String) : Bool := refusal s == some ⟨⟨line, col⟩, msg⟩

#eval expect (at? (file ["object o {", "  type T", "}", "val program = o"]) 5 10 msgRA) "RA-obj"
#eval expect (at? (file ["val program: { type T } = new Object {", "  type T <: Any", "}"]) 5 10 msgRA) "RA-lit"
#eval expect (at? (file ["object o {", "  def b: Any = o", "}", "val program = o"]) 5 9 msgRP) "RP-none"
#eval expect (at? (file ["def f(): Any = A", "val program = A"]) 4 8 msgRP) "RP-empty"
#eval expect (at? (file ["def f(x: Any, y: Any): Any = x", "val program = A"]) 4 15 msgRP) "RP-two"
#eval expect (at? (file ["val program = (r: { def a(x: Any): Any }) => r"]) 4 23 msgRP) "RP-ref"
#eval expect (at? (file ["val program = {", "  object o { type T = Any }", "  o", "}"]) 5 5 msgRO) "RO-block"
#eval expect (at? (file ["object o {", "  val program = o", "}", "val program = o"]) 5 9 msgProgram) "RO-program"
#eval expect (at? (file ["def program(x: Any): Any = x"]) 4 7 msgProgram) "RO-defprogram"
#eval expect (at? (file ["object o { s: Any => type T = Any }", "val program = o"]) 4 15
  "a typed self is outside the subset") "RO-typedself"
#eval expect (at? (file ["val program = {", "  def f(x: Any): Any = x", "  f", "}"]) 5 5 msgDefTerm) "RO-defblock"
#eval expect (at? (file ["val program = A", "object o { type T = Any }"]) 5 3 msgAfter) "RO-after"
#eval expect (at? (file ["val program = {", "  import scala.language.experimental", "  A", "}"]) 5 5 msgRI) "RI-term"
#eval expect (parsed (file ["class C", "val program = A"]) ==
  some ⟨z, "A", .cls z .concrete "C" [] .nil .nil .nil, none, .path (.var z "A")⟩) "class C, read (N5)"
#eval expect (parsed (file ["trait C", "val program = A"]) ==
  some ⟨z, "A", .cls z .trait "C" [] .nil .nil .nil, none, .path (.var z "A")⟩) "trait C, read (N5)"
#eval expect (at? (file ["object o { type T = Any }"]) 5 1 msgAfter) "RO-noprogram"
#eval expect (at? (file ["object o extends Any { type T = Any }", "val program = o"]) 4 12 msgROE) "R-OE"

-- A second import after the header
#eval expect (at? ("import scala.reflect.Selectable.reflectiveSelectable\n\nimport scala.language.experimental\n" ++
    "object A {\n  val program = A\n}\n") 3 8 msgRI) "RI-two"

-- A file whose one import is not the header
#eval expect (at? ("import scala.language.experimental\n\nobject A {\n  val program = A\n}\n") 1 8 msgHeader)
  "header wrong"

-- A block `{ x =>` is no template: the column rule refuses its next line
#eval expect (at? (file ["val program = ((f: Any => Any) => f)({ x =>", "  x", "})"]) 4 42
  "the first statement after `{` goes on the next line, indented") "block self name"

/-! ## The kind table, one row each -/

/-- The context at the innermost body of `program`: through lambdas, ascriptions and blocks, into a
literal. -/
def envAlong (env : List Scope.Entry) : Tm → List Scope.Entry
  | .lam _ x T b => envAlong (.param x T false :: env) b
  | .asc _ e _ => envAlong env e
  | .block _ ss => statsEnv env ss
  | .lit p s ms => .tmpl (.lit p s ms) :: env
  | _ => env
where statsEnv (env : List Scope.Entry) : Stats → List Scope.Entry
  | .last t => envAlong env t
  | .val _ x T e r => statsEnv (.val x T e :: env) r

/-- The word of the kind of `q` at the innermost body of `program`, or `none` when the text is refused. -/
def kindAt (s : String) (q : Path) : Option Scope.KindWord :=
  (parseFile s.toList).toOption.map fun F =>
    (Scope.kindPath (F.size + 1) (envAlong (Scope.stemEnv F) F.body) none q).word

/-- `P7Kinds.lean`'s text with `type T = Any` as the first member of `o`. -/
def k1 : String := "import scala.reflect.Selectable.reflectiveSelectable

object W {
  object o {
    type T = Any
    object a { type A = Any }
    val m: o.a.type = o.a
    val n = o.a
    val f = (u: Any) => u
    def g(u: Any)(v: Any): Any = v
  }
  val program = (x: o.type) => (y: { val b: x.type; val c: { type A } }) => (z: o.T) => {
    val v = o
    val w: o.a.type = o.a
    val u = y.c
    (new Object { s => val d: s.type = s }: { val d: Any })
  }
}
"

#eval expect (kindAt k1 (.var z "o") == some .obj) "kind o: a bare member object"
#eval expect (kindAt k1 (.var z "W") == some .obj) "kind W: the wrapper's name"
#eval expect (kindAt k1 (.this z) == some .lit) "kind this: inside the literal"
#eval expect (kindAt k1 (.sel (.var z "o") z "a") == some .obj) "kind o.a: o declares object a"
#eval expect (kindAt k1 (.sel (.var z "o") z "m") == some .obj) "kind o.m: val m: o.a.type = o.a"
#eval expect (kindAt k1 (.sel (.var z "o") z "n") == some .obj) "kind o.n: val n = o.a, a module path"
#eval expect (kindAt k1 (.sel (.var z "o") z "f") == some .fun) "kind o.f: a val holding a lambda"
#eval expect (kindAt k1 (.sel (.var z "o") z "g") == some (.meth 2)) "kind o.g: a def of two lists"
#eval expect (kindAt k1 (.var z "x") == some .obj) "kind x: a parameter at o.type"
#eval expect (kindAt k1 (.var z "y") == some .str) "kind y: a parameter at a refinement"
#eval expect (kindAt k1 (.sel (.var z "y") z "b") == some .obj) "kind y.b: val b: x.type"
#eval expect (kindAt k1 (.sel (.var z "y") z "c") == some .unstable) "kind y.c: val c: { type A } under str"
#eval expect (kindAt k1 (.var z "z") == some .str) "kind z: a parameter at o.T"
#eval expect (kindAt k1 (.var z "v") == some .obj) "kind v: a block alias"
#eval expect (kindAt k1 (.var z "w") == some .obj) "kind w: a block val at o.a.type"
#eval expect (kindAt k1 (.var z "u") == some .val) "kind u: a block val, no written type, no module path"
#eval expect (kindAt k1 (.sel (.var z "u") z "A") == some .unstable) "kind u.A: a selection on val"
#eval expect (kindAt k1 (.var z "s") == some .lit) "kind s: the literal's self name"
#eval expect (kindAt k1 (.sel (.var z "s") z "d") == some .lit) "kind s.d: val d: s.type = s"
#eval expect (kindAt k1 (.sel (.var z "o") z "zz") == some .unstable) "kind o.zz: no member zz"

#eval expect (kindAt
  (file ["val program = (q: { type A }) => (p: { val a: q.type & { type A } }) => (y: p.a.A) => y"])
  (.sel (.var z "p") z "a") == some .unstable) "kind p.a: a refinement val at an intersection"
#eval expect (kindAt (file ["val program = (q: { val a: { type A }; val b: this.a.type }) => (v: Any) => v"])
  (.sel (.var z "q") z "b") == some .unstable) "kind q.b: val b: this.a.type"
#eval expect (kindAt (file ["val program = (q: { val a: { type A }; val b: this.a.type }) => (v: Any) => v"])
  (.sel (.var z "q") z "a") == some .unstable) "kind q.a: val a: { type A } under str"
#eval expect (kindAt (file ["val program = (q: { type B }) => (x: { val a: q.type }) => (z: Any) => z"])
  (.sel (.var z "x") z "a") == some .str) "kind x.a: val a: q.type, q at a refinement"
#eval expect (kindAt
  (file ["val program = (x: Any) => (new Object { val x = (u: Any) => u }: { val x: Any => Any })"])
  (.var z "x") == some .fun) "kind x: the literal's member hides the parameter (D-11)"
#eval expect (kindAt
  (file ["val program = (x: Any) => (new Object { s => val y = (u: Any) => u }: { val y: Any => Any })"])
  (.sel (.var z "s") z "y") == some .fun) "kind s.y: a literal's val holding a lambda"
#eval expect (kindAt (file ["val program = x => x"]) (.var z "x") == some .val) "kind x: an untyped lambda parameter"
#eval expect (kindAt (file ["val program = x => x"]) (.sel (.var z "x") z "a") == some .unstable)
  "kind x.a: a selection on an untyped lambda parameter"

-- `this.a` in a refinement with `val a: { type A }`
#eval expect ((Scope.kindPath 4 [.tmpl (.ref z (.val z "a" (.refine z (.typ z "A" .absent .absent .nil)) .nil))]
  none (.sel (.this z) z "a")).word == .refval) "kind this.a: refval"

/-! ## The shortest unstable prefix -/

/-- `scratch-refute-d3/sc/R08RefValAndSngl.scala` of the main checkout, verbatim. -/
def r08 : String := "import scala.reflect.Selectable.reflectiveSelectable\n\nobject R08RefValAndSngl {\n" ++
  "  // design risk R3: a refinement val at an intersection with a singleton, as a prefix\n" ++
  "  val program = (q: { type A }) => (p: { val a: q.type & { type A } }) => (y: p.a.A) => y\n}\n"

/-- The shortest unstable prefix of `q` at the innermost body of `program`, positions erased, or `none`
when the text is refused. -/
def prefixAt (s : String) (q : Path) : Option (Option Path) :=
  (parseFile s.toList).toOption.map fun F =>
    (Scope.unstablePrefix? (F.size + 1) (envAlong (Scope.stemEnv F) F.body) q).map Path.erase

#eval expect (prefixAt r08 (.sel (.var z "p") z "a") == some (some (.sel (.var z "p") z "a")))
  "R08: the prefix p.a of p.a.A is unstable"
#eval expect (prefixAt r08 (.sel (.sel (.var z "p") z "a") z "A") == some (some (.sel (.var z "p") z "a")))
  "R08: the shortest unstable prefix of the path p.a.A is p.a"
#eval expect (prefixAt k1 (.sel (.sel (.var z "y") z "b") z "a") == some none) "k1: y.b.a has no unstable prefix"

/-! ## Modules -/

/-- `scala/pdot/pos/Fig1.scala`, verbatim. -/
def fig1 : String := "import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/sc/C01Fig1.scala, d3 C01Fig1
object Fig1 {
  object dotty {
    object core {
      object types {
        type Type = Any
        type TypeRef = core.types.Type & { val symb: core.symbols.Symbol }
      }
      object symbols {
        type Symbol = { val tpe: core.types.Type }
      }
    }
  }
  val program = (r: dotty.core.types.TypeRef) => (r.symb.tpe: dotty.core.types.Type)
}
"

/-- `scala/pdot/pos/ObjInLit.scala`, verbatim. -/
def objInLit : String := "import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-judge/sc/J04ObjInLit.scala, judge J04ObjInLit
object ObjInLit {
  val program = (new Object {
    object a {
      type A = Any
    }
  }: { val a: { type A } })
}
"

/-- `scala/pdot/pos/E7Obj.scala`, verbatim. -/
def e7Obj : String := "import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/sc/C04E7Obj.scala, d3 C04E7Obj
object E7Obj {
  object core {
    object types {
      type A = Any
      val f: Any => Any = (u: Any) => u
    }
    val m: core.types.type = core.types
  }
  val program = core.m.f(core)
}
"

#eval expect ((parseFile fig1.toList).toOption.map modules ==
  some [["dotty"], ["dotty", "core"], ["dotty", "core", "types"], ["dotty", "core", "symbols"]]) "modules of Fig1"
#eval expect ((parseFile objInLit.toList).toOption.map modules == some []) "modules of ObjInLit"
#eval expect ((parseFile e7Obj.toList).toOption.map modules == some [["core"], ["core", "types"]])
  "modules of E7Obj"

/-! ## The refusals of the walk, at their positions -/

/-- The verdict of `check` on a text: `taken`, or the refusal at `line:col` with its message. -/
def verdict (s : String) : String :=
  match parseFile s.toList >>= check with
  | .ok _ => "taken"
  | .error e => toString e.pos.line ++ ":" ++ toString e.pos.col ++ ": " ++ e.msg

/-- The verdict `line:col: msg`. -/
def at! (line col : Nat) (msg : String) : String := toString line ++ ":" ++ toString col ++ ": " ++ msg

/-- Rule 4's message. -/
def msgR4 : String := "inside `(x: S) => T` scalac reads `this` as the enclosing object"

#eval expect (verdict (file ["object o {", "  type T = Any", "}", "val program = o"]) == "taken") "RA-ok"
#eval expect (verdict (file ["object o {", "  val a: { type A } = new Object { type A = Any }", "}",
  "val program = o"]) == at! 5 9 Scope.msgRL) "RL"
#eval expect (verdict (file ["object o {", "  object a { type A = Any }", "}", "val program = o"]) == "taken")
  "RL-ok"
#eval expect (verdict (file ["object p { type A = Any }", "object o {", "  val c: { type A } = p", "}",
  "val program = o"]) == at! 6 9 Scope.msgRV) "RV-typed"
#eval expect (verdict (file ["object o {", "  val f = (x: Any) => x", "  val g = o.f", "}", "val program = o"]) ==
  at! 6 9 Scope.msgRV) "RV-untyped"
#eval expect (verdict (file ["object p { type A = Any }", "object o {", "  val c: p.type = p", "  val d = p", "}",
  "val program = o"]) == "taken") "RV-ok"
#eval expect (verdict (file ["object core { def f(u: Any): Any = u }", "val r = core.f(core)", "val program = r"]) ==
  at! 5 7 Scope.msgRR) "RR"
#eval expect (verdict (file ["val f = (u: Any) => u", "val program = f"]) == "taken") "RR-ok"
#eval expect (verdict (file ["object o { def f(u: Any): Any = u }",
  "val program = (x: { val f: Any => Any }) => x"]) == at! 5 27 Scope.msgRD) "RD-val"
#eval expect (verdict (file ["object o { def f(u: Any): Any = u }", "object p { def f(u: Any)(v: Any): Any = v }",
  "val program = o"]) == at! 5 18 Scope.msgRD) "RD-lists"
#eval expect (verdict (file ["object o { def f(u: Any): Any = u }", "object p { def f(v: Any): Any = v }",
  "val program = o"]) == "taken") "RD-ok"
#eval expect (verdict (file ["def f(x: Any)(y: Any): Any = y", "val program = f(A)"]) == at! 5 17 Scope.msgRU)
  "RU-partial"
#eval expect (verdict (file ["object o {", "  def f(x: Any): o.type = o", "}", "val program = o.f.f"]) ==
  at! 7 19 Scope.msgRU) "RU-prefix"
#eval expect (verdict (file ["object o {", "  def f(x: Any): o.type = o", "}", "val program = (y: o.f.type) => y"]) ==
  at! 7 23 Scope.msgRU) "RU-type"
#eval expect (verdict (file ["def f(x: Any): Any => Any = (y: Any) => y", "val program = f(A)(A)"]) == "taken")
  "RU-ok"
#eval expect (verdict (file ["val program = (p: { val a: { type A } }) => (y: p.a.A) => y"]) ==
  at! 4 53 (Scope.msgRS (.sel (.var z "p") z "a"))) "RS-refval"
#eval expect (verdict (file
  ["val program = (q: { type A }) => (p: { val a: q.type & { type A } }) => (y: p.a.A) => y"]) ==
  at! 4 81 (Scope.msgRS (.sel (.var z "p") z "a"))) "RS-r08"
#eval expect (verdict (file ["object o { type T = { val a: { type A } } }",
  "val program = (x: o.T) => (y: x.a.A) => y"]) == at! 5 35 (Scope.msgRS (.sel (.var z "x") z "a"))) "RS-alias"
#eval expect (verdict (file ["val program = (q: { val a: { val b: { type A } }; val c: this.a.b.A }) => q"]) ==
  at! 4 67 (Scope.msgRS (.sel (.sel (.this z) z "a") z "b"))) "RS-thisdeep"
#eval expect (verdict (file
  ["val program = (q: { type B }) => (x: { val a: q.type }) => (z: x.a.B) => (z: q.B)"]) == "taken") "RS-ok"
#eval expect (verdict (file ["val program = (q: { val a: { type A }; val g: this.a.type => Any }) => q"]) == "taken")
  "RS-thisok"
#eval expect (verdict (file ["object a {", "  type T = b.U", "}", "object b {", "  type U = a.T", "}",
  "val program = a"]) == at! 5 10 (Scope.msgRY true "alias" "T")) "RY-obj"
#eval expect (verdict (file ["val program = (x: { type C = this.D; type D = this.C }) => x"]) ==
  at! 4 28 (Scope.msgRY true "alias" "C")) "RY-ref"
#eval expect (verdict (file ["val program = (x: { type C <: Any => this.C }) => x"]) == "taken") "RY-ok"
#eval expect (verdict (file ["object a {", "  type T = Any => b.U", "}", "object b {", "  type U = Any => a.T", "}",
  "val program = a"]) == at! 5 10 (Scope.msgRY false "alias" "T")) "RY-fnres"
#eval expect (verdict (file ["object a {", "  type T = b.U => Any", "}", "object b {", "  type U = Any => a.T", "}",
  "val program = a"]) == at! 5 10 (Scope.msgRY true "alias" "T")) "RY-fnparam"
#eval expect (verdict (file ["object o {", "  val a: o.b.type = o.b", "  val b: o.a.type = o.a", "}",
  "val program = o"]) == at! 5 9 (Scope.msgRC "a")) "RC"
#eval expect (verdict (file ["val program: Any = new Object { x =>", "  val a: x.a.type = x.a", "}"]) ==
  at! 5 9 (Scope.msgRC "a")) "RC-self"
#eval expect (verdict (file ["object o {", "  object b { type T = Any }", "  val a: o.b.type = o.b", "}",
  "val program = o"]) == "taken") "RC-ok"
#eval expect (verdict (file ["object core {", "  object types { type T = Any }", "}",
  "val program = (x: core.type) => (y: x.types.T) => y"]) == at! 7 41 Scope.msgRK) "RK"
#eval expect (verdict (file ["object core {", "  object types { type T = Any }", "}",
  "val program = (f: (x: core.type) => x.types.T) => f"]) == at! 7 41 Scope.msgRK) "RK-fn"
#eval expect (verdict (file ["object core {", "  type T = Any", "}", "val program = (x: core.type) => (y: x.T) => y"]) ==
  "taken") "RK-ok"
#eval expect (verdict (file ["object core {", "  object types { type T = Any }", "}",
  "def h(x: core.type)(t: x.types.T): Any = t", "val program = core"]) == "taken") "RK-def"
#eval expect (verdict (file ["val program = (x: Any) => y"]) == at! 4 29 "`y` is not in scope") "R1"
#eval expect (verdict (file ["val program = (q: { type B; val f: (x: Any) => this.B }) => q"]) == at! 4 50 msgR4)
  "R4"
#eval expect (verdict (file ["val program = this"]) == "taken") "R4-ok"
#eval expect (verdict (file ["object o {", "  val a: this.b.type = this.b", "}", "val program = o"]) ==
  at! 5 17 "value b is not a member of the object (scalac E008)") "R5"
#eval expect (verdict (file ["val program = (f: (x: Any) => Any) => f"]) ==
  at! 4 30 "the parameter `x` does not occur in the result: write `S => T`") "R6"
#eval expect (verdict (file ["object Core { type T = Any }", "val program = Core"]) ==
  at! 4 10 "the field `Core` starts upper case: fields start lower case") "R7"
#eval expect (verdict (file ["object o {", "  type T = Any", "  type T = Any", "}", "val program = o"]) ==
  at! 6 10 "conflicting definitions of `T` in one object (scalac E120)") "R8-obj"
#eval expect (verdict (file ["def f(x: Any)(x: Any): Any = x", "val program = A"]) ==
  at! 4 17 "`x` is already a parameter of `f`") "R8-param"
#eval expect (verdict (file ["val program = {", "  val a = b", "  val b = (x: Any) => x", "  a", "}"]) ==
  at! 5 13 "forward reference: `b` is defined later in this block (scalac E039)") "R9"
#eval expect (verdict (file ["val program = ((x: Any) => x)(new Object { type T = Any })"]) ==
  at! 4 33 "an object literal needs a written type: write `(new Object { … }: T)`") "R10-arg"
#eval expect (verdict (file ["def f(x: Any) = new Object { type T = Any }", "val program = f(A)"]) ==
  at! 4 19 "an object literal needs a written type: scalac types it as Object") "R10-def"
#eval expect (verdict (file ["def f(x: Any): { type T } = new Object { type T = Any }", "val program = f(A)"]) ==
  "taken") "R10-ok"
#eval expect (verdict (file ["val program = (x: Int) => x"]) == at! 4 21 "the type `Int` is outside the subset")
  "bare-type"
#eval expect (verdict (file ["val program = (t: { type A; val x: { val y: A } }) => (t.x.y: t.A)"]) == "taken")
  "bare-ok"

-- The parser's rows through `check`: their verdicts are their parser refusals
#eval expect (verdict (file ["object o {", "  type T", "}", "val program = o"]) == at! 5 10 msgRA) "RA-obj, check"
#eval expect (verdict (file ["val program: { type T } = new Object {", "  type T <: Any", "}"]) == at! 5 10 msgRA)
  "RA-lit, check"
#eval expect (verdict (file ["object o {", "  def b: Any = o", "}", "val program = o"]) == at! 5 9 msgRP)
  "RP-none, check"
#eval expect (verdict (file ["def f(): Any = A", "val program = A"]) == at! 4 8 msgRP) "RP-empty, check"
#eval expect (verdict (file ["def f(x: Any, y: Any): Any = x", "val program = A"]) == at! 4 15 msgRP)
  "RP-two, check"
#eval expect (verdict (file ["val program = (r: { def a(x: Any): Any }) => r"]) == at! 4 23 msgRP) "RP-ref, check"
#eval expect (verdict (file ["val program = {", "  object o { type T = Any }", "  o", "}"]) == at! 5 5 msgRO)
  "RO-block, check"
#eval expect (verdict (file ["object o {", "  val program = o", "}", "val program = o"]) == at! 5 9 msgProgram)
  "RO-program, check"
#eval expect (verdict (file ["def program(x: Any): Any = x"]) == at! 4 7 msgProgram) "RO-defprogram, check"
#eval expect (verdict (file ["object o { s: Any => type T = Any }", "val program = o"]) ==
  at! 4 15 "a typed self is outside the subset") "RO-typedself, check"
#eval expect (verdict (file ["val program = {", "  def f(x: Any): Any = x", "  f", "}"]) == at! 5 5 msgDefTerm)
  "RO-defblock, check"
#eval expect (verdict (file ["val program = A", "object o { type T = Any }"]) == at! 5 3 msgAfter) "RO-after, check"
#eval expect (verdict (file ["val program = {", "  import scala.language.experimental", "  A", "}"]) ==
  at! 5 5 msgRI) "RI-term, check"
#eval expect (verdict (file ["class C", "val program = A"]) == "taken") "class C, check (N5)"

/-! ## Labels -/

#eval expect ((parseFile fig1.toList).toOption.map labels ==
  some [("dotty", .trm 0), ("core", .trm 1), ("types", .trm 2), ("Type", .typ 0), ("TypeRef", .typ 1),
    ("symb", .trm 3), ("symbols", .trm 4), ("Symbol", .typ 2), ("tpe", .trm 5), ("ℓself", .trm 6)])
  "labels of Fig1"

/-- A name at both sorts.  `check` refuses it by rule 7, and `labels` does not care. -/
def bothSorts : String := file ["val program = (y: { type A; val A: Any }) => y"]

#eval expect (match (parseFile bothSorts.toList).toOption.map labels with
  | some Λ => Λ.contains ("A", .typ 0) && Λ.contains ("A", .trm 0)
  | none => false) "labels: A at both sorts"

/-- Whether `ℓself` is the last entry of the table of a text, and the only one of its name. -/
def selfLast (s : String) : Bool :=
  match (parseFile s.toList).toOption.map labels with
  | some Λ => Λ.getLast?.map Prod.fst == some selfLabelName && (Λ.filter (·.1 == selfLabelName)).length == 1
  | none => false

#eval expect (selfLast fig1 && selfLast objInLit && selfLast e7Obj && selfLast k1 && selfLast r08 &&
  selfLast bothSorts) "labels: ℓself last"


/-! ## The printer -/

/-- `scala/pdot/pos/E5m.scala`, verbatim. -/
def e5m : String := "import scala.reflect.Selectable.reflectiveSelectable

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
"

/-- `scala/pdot/disagree/SnglInFn.scala`, verbatim. -/
def snglInFn : String := "import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: pDOT subtyping widens no singleton, so Any => q.type is no subtype of Any => { type B }
// from: notes-pdot-frontend/scratch-d2/sc/M49_SnglInFn.scala, d2 M49_SnglInFn
object SnglInFn {
  object q { type B = Any; val me: this.type = this }
  val g: Any => q.type = (x: Any) => q.me
  def k(u: Any): Any => { type B } = g
  val program = k(q)
}
"

/-- `scala/pdot/pos/E3m.scala`, verbatim. -/
def e3m : String := "import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d2/sc/M24_E3m.scala, d2 M24_E3m
object E3m {
  object dotty {
    object core {
      object types {
        type Tpe = Any
        type TypeRef = types.Tpe & { val symb: core.symbols.Symbol }
        def typeRef(s: core.symbols.Symbol): types.TypeRef = new Object {
          val symb: s.type = s
        }
      }
      object symbols {
        type Symbol = { val tpe: core.types.Tpe }
        def symbol(u: core.types.Tpe): symbols.Symbol = new Object {
          val tpe: u.type = u
        }
      }
    }
  }
  val program = {
    val s = dotty.core.symbols.symbol(dotty)
    dotty.core.types.typeRef(s)
  }
}
"

/-- The printed text of a text's tree, or `none` when the text is refused. -/
def printed (s : String) : Option String := (parseFile s.toList).toOption.map fun F => String.ofList (print F)

-- A literal's self name on its own line, a literal on the line after a def's `=`
#eval expect (printed e5m == some "import scala.reflect.Selectable.reflectiveSelectable

object E5m {
  object x {
    type C = { val incr: this.type }
    type D = x.C & { val decr: this.type }
    def d(u: Any): x.D =
      new Object {
        o =>
        val incr: o.type = o
        val decr: o.type = o
      }
  }
  val program = {
    val z = x.d(x)
    z.incr.decr
  }
}
") "print of E5m"

-- A one-line object with `;` spans lines
#eval expect (printed snglInFn == some "import scala.reflect.Selectable.reflectiveSelectable

object SnglInFn {
  object q {
    type B = Any
    val me: this.type = this
  }
  val g: Any => q.type = (x: Any) => q.me
  def k(u: Any): Any => { type B } = g
  val program = k(q)
}
") "print of SnglInFn"

-- Objects three deep, each `new Object {` on the line after its def's `=`
#eval expect (printed e3m == some "import scala.reflect.Selectable.reflectiveSelectable

object E3m {
  object dotty {
    object core {
      object types {
        type Tpe = Any
        type TypeRef = types.Tpe & { val symb: core.symbols.Symbol }
        def typeRef(s: core.symbols.Symbol): types.TypeRef =
          new Object {
            val symb: s.type = s
          }
      }
      object symbols {
        type Symbol = { val tpe: core.types.Tpe }
        def symbol(u: core.types.Tpe): symbols.Symbol =
          new Object {
            val tpe: u.type = u
          }
      }
    }
  }
  val program = {
    val s = dotty.core.symbols.symbol(dotty)
    dotty.core.types.typeRef(s)
  }
}
") "print of E3m"

/-- Whether the printed text of a text's tree reads back to the same tree up to positions. -/
def roundTrips (s : String) : Bool :=
  match parseFile s.toList with
  | .ok F => (parseFile (print F)).toOption.map File.erase == some F.erase
  | .error _ => false

/-- Every text of this file: the grammar rows, the parser's refusals, the kind rows, the rule rows, the
named texts. -/
def texts : List String :=
  [k1, r08, fig1, objInLit, e7Obj, bothSorts, e5m, snglInFn, e3m,
    "import scala.reflect.Selectable.reflectiveSelectable\n\nimport scala.language.experimental\n" ++
      "object A {\n  val program = A\n}\n",
    "import scala.language.experimental\n\nobject A {\n  val program = A\n}\n",
    file ["val program: Any = A"],
    file ["object o { s => type T = Any }", "val program = o"],
    file ["object o { type T = Any }", "val program = o"],
    file ["object o { val f = (u: Any) => u; val g: Any => Any = (u: Any) => u }", "val program = o"],
    file ["def f(x: Any)(y: x.type): x.type = y", "def g(x: Any) = x", "val program = A"],
    file ["val program = (f: (x: { type B }) => x.B) => f"],
    file ["val program = (f: Any => Any & Nothing & Any) => f"],
    file ["object o { object p { object q { type T = Any } } }", "val program = (x: o.p.q.T) => x"],
    file ["val program = (q: { type A; val a: this.A; val b: this.a.type }) => q"],
    file ["val program = (t: { type A; val x: { val y: A } }) => t"],
    file ["val program = (q: { type A; type B >: Any; type C <: Any; type D >: Nothing <: Any }) => q"],
    file ["val program = (f: Any) => ((x) => x)"],
    file ["val program = x => x"],
    file ["object o { def f(x: Any): o.type = o }", "val program = o.f(o).f(o)"],
    file ["val program = (new Object { type T = Any }: { type T })"],
    file ["val program = {", "  val a = A", "  val b: a.type = a", "  b", "}"],
    file ["val program: { val a: Any } = new Object { s =>", "  val a: s.type = s", "}"],
    file ["object o { type T = Any; type U = Any }", "val program = o"],
    file ["val program = (f: (Any => Any) => Any) => f"],
    file ["val program = (q: { type A = Any; type B = this.A }) => q"],
    file ["val program = this"],
    file ["object o { type T = Any }", "val program = (o: o.type)"],
    file ["object o {", "  type T", "}", "val program = o"],
    file ["val program: { type T } = new Object {", "  type T <: Any", "}"],
    file ["object o {", "  def b: Any = o", "}", "val program = o"],
    file ["def f(): Any = A", "val program = A"],
    file ["def f(x: Any, y: Any): Any = x", "val program = A"],
    file ["val program = (r: { def a(x: Any): Any }) => r"],
    file ["val program = {", "  object o { type T = Any }", "  o", "}"],
    file ["object o {", "  val program = o", "}", "val program = o"],
    file ["def program(x: Any): Any = x"],
    file ["object o { s: Any => type T = Any }", "val program = o"],
    file ["val program = {", "  def f(x: Any): Any = x", "  f", "}"],
    file ["val program = A", "object o { type T = Any }"],
    file ["val program = {", "  import scala.language.experimental", "  A", "}"],
    file ["class C", "val program = A"],
    file ["trait C", "val program = A"],
    file ["object o { type T = Any }"],
    file ["object o extends Any { type T = Any }", "val program = o"],
    file ["val program = ((f: Any => Any) => f)({ x =>", "  x", "})"],
    file ["val program = (q: { type A }) => (p: { val a: q.type & { type A } }) => (y: p.a.A) => y"],
    file ["val program = (q: { val a: { type A }; val b: this.a.type }) => (v: Any) => v"],
    file ["val program = (q: { type B }) => (x: { val a: q.type }) => (z: Any) => z"],
    file ["val program = (x: Any) => (new Object { val x = (u: Any) => u }: { val x: Any => Any })"],
    file ["val program = (x: Any) => (new Object { s => val y = (u: Any) => u }: { val y: Any => Any })"],
    file ["object o {", "  type T = Any", "}", "val program = o"],
    file ["object o {", "  val a: { type A } = new Object { type A = Any }", "}", "val program = o"],
    file ["object o {", "  object a { type A = Any }", "}", "val program = o"],
    file ["object p { type A = Any }", "object o {", "  val c: { type A } = p", "}", "val program = o"],
    file ["object o {", "  val f = (x: Any) => x", "  val g = o.f", "}", "val program = o"],
    file ["object p { type A = Any }", "object o {", "  val c: p.type = p", "  val d = p", "}", "val program = o"],
    file ["object core { def f(u: Any): Any = u }", "val r = core.f(core)", "val program = r"],
    file ["val f = (u: Any) => u", "val program = f"],
    file ["object o { def f(u: Any): Any = u }", "val program = (x: { val f: Any => Any }) => x"],
    file ["object o { def f(u: Any): Any = u }", "object p { def f(u: Any)(v: Any): Any = v }", "val program = o"],
    file ["object o { def f(u: Any): Any = u }", "object p { def f(v: Any): Any = v }", "val program = o"],
    file ["def f(x: Any)(y: Any): Any = y", "val program = f(A)"],
    file ["object o {", "  def f(x: Any): o.type = o", "}", "val program = o.f.f"],
    file ["object o {", "  def f(x: Any): o.type = o", "}", "val program = (y: o.f.type) => y"],
    file ["def f(x: Any): Any => Any = (y: Any) => y", "val program = f(A)(A)"],
    file ["val program = (p: { val a: { type A } }) => (y: p.a.A) => y"],
    file ["object o { type T = { val a: { type A } } }", "val program = (x: o.T) => (y: x.a.A) => y"],
    file ["val program = (q: { val a: { val b: { type A } }; val c: this.a.b.A }) => q"],
    file ["val program = (q: { type B }) => (x: { val a: q.type }) => (z: x.a.B) => (z: q.B)"],
    file ["val program = (q: { val a: { type A }; val g: this.a.type => Any }) => q"],
    file ["object a {", "  type T = b.U", "}", "object b {", "  type U = a.T", "}", "val program = a"],
    file ["val program = (x: { type C = this.D; type D = this.C }) => x"],
    file ["val program = (x: { type C <: Any => this.C }) => x"],
    file ["object a {", "  type T = Any => b.U", "}", "object b {", "  type U = Any => a.T", "}", "val program = a"],
    file ["object a {", "  type T = b.U => Any", "}", "object b {", "  type U = Any => a.T", "}", "val program = a"],
    file ["object o {", "  val a: o.b.type = o.b", "  val b: o.a.type = o.a", "}", "val program = o"],
    file ["val program: Any = new Object { x =>", "  val a: x.a.type = x.a", "}"],
    file ["object o {", "  object b { type T = Any }", "  val a: o.b.type = o.b", "}", "val program = o"],
    file ["object core {", "  object types { type T = Any }", "}",
      "val program = (x: core.type) => (y: x.types.T) => y"],
    file ["object core {", "  object types { type T = Any }", "}",
      "val program = (f: (x: core.type) => x.types.T) => f"],
    file ["object core {", "  type T = Any", "}", "val program = (x: core.type) => (y: x.T) => y"],
    file ["object core {", "  object types { type T = Any }", "}", "def h(x: core.type)(t: x.types.T): Any = t",
      "val program = core"],
    file ["val program = (x: Any) => y"],
    file ["val program = (q: { type B; val f: (x: Any) => this.B }) => q"],
    file ["object o {", "  val a: this.b.type = this.b", "}", "val program = o"],
    file ["val program = (f: (x: Any) => Any) => f"],
    file ["object Core { type T = Any }", "val program = Core"],
    file ["object o {", "  type T = Any", "  type T = Any", "}", "val program = o"],
    file ["def f(x: Any)(x: Any): Any = x", "val program = A"],
    file ["val program = {", "  val a = b", "  val b = (x: Any) => x", "  a", "}"],
    file ["val program = ((x: Any) => x)(new Object { type T = Any })"],
    file ["def f(x: Any) = new Object { type T = Any }", "val program = f(A)"],
    file ["def f(x: Any): { type T } = new Object { type T = Any }", "val program = f(A)"],
    file ["val program = (x: Int) => x"],
    file ["val program = (t: { type A; val x: { val y: A } }) => (t.x.y: t.A)"]]

/-- The texts of this file that `check` takes. -/
def takenTexts : List String := texts.filter fun s => verdict s == "taken"

#eval expect (takenTexts.length == 49) "49 texts of this file that check takes"
#eval expect (takenTexts.all roundTrips) "round trip of every text that check takes"

/-! ## Classes and traits (N5): the grammar, one row each -/

-- ClassDef: parameters with and without `val`, a first parent with arguments, `with`
#eval expect (parsed (file ["trait T", "class K(val v: Any, w: Any) extends T",
    "class L(val u: Any) extends K(u, A) with T",
    "val program = A"]) ==
  some ⟨z, "A",
    .cls z .trait "T" [] .nil .nil
      (.cls z .concrete "K" [⟨z, true, "v", .any z⟩, ⟨z, false, "w", .any z⟩] (.cons ⟨z, none, "T"⟩ .nil .nil) .nil
        (.cls z .concrete "L" [⟨z, true, "u", .any z⟩]
          (.cons ⟨z, none, "K"⟩ (.cons (.path (.var z "u")) (.cons (.path (.var z "A")) .nil)) (.cons ⟨z, none,
    "T"⟩ .nil .nil))
          .nil .nil)),
    none, .path (.var z "A")⟩) "class definitions"

-- `abstract class`, TraitDef with `extends … with`, ClassRef `q.C`
#eval expect (parsed (file ["object m { trait T }", "trait U", "abstract class K extends m.T with U",
    "trait V extends m.T with U", "val program = A"]) ==
  some ⟨z, "A",
    .obj z "m" none (.cls z .trait "T" [] .nil .nil .nil)
      (.cls z .trait "U" [] .nil .nil
        (.cls z .abstract "K" [] (.cons ⟨z, some (.var z "m"), "T"⟩ .nil (.cons ⟨z, none, "U"⟩ .nil .nil)) .nil
          (.cls z .trait "V" [] (.cons ⟨z, some (.var z "m"), "T"⟩ .nil (.cons ⟨z, none, "U"⟩ .nil .nil)) .nil .nil))),
    none, .path (.var z "A")⟩) "abstract class, trait, a parent through an object"

-- ClassMem and ClassDecl: bounds, an alias, `val` and `def` abstract and defined, `override`
#eval expect (parsed (file ["trait T {", "  type B >: Nothing <: Any", "  type C = Any", "  val a: Any",
    "  val b: Any = A",
    "  def f(x: Any): Any", "  override def g(x: Any)(y: Any): Any = y", "}", "val program = A"]) ==
  some ⟨z, "A",
    .cls z .trait "T" [] .nil
      (.typ z false "B" (.given (.nothing z)) (.given (.any z))
        (.alias z false "C" (.any z)
          (.valDecl z false "a" (.any z)
            (.val z false "b" (.any z) (.path (.var z "A"))
              (.defDecl z false "f" [⟨z, "x", .any z⟩] (.any z)
                (.defn z true "g" [⟨z, "x", .any z⟩, ⟨z, "y", .any z⟩] (.any z) (.path (.var z "y")) .nil))))))
      .nil,
    none, .path (.var z "A")⟩) "class members"

-- Expr: `new C()` reads as `new C`, `new q.C(e1, e2)`
#eval expect (parsed (file ["object m { class K(val v: Any, val w: Any) }", "class L",
    "val program = { val l = new L(); new m.K(l, A) }"]) ==
  some ⟨z, "A",
    .obj z "m" none (.cls z .concrete "K" [⟨z, true, "v", .any z⟩, ⟨z, true, "w", .any z⟩] .nil .nil .nil)
      (.cls z .concrete "L" [] .nil .nil .nil),
    none,
    .block z (.val z "l" none (.new z ⟨z, none, "L"⟩ .nil)
      (.last (.new z ⟨z, some (.var z "m"), "K"⟩ (.cons (.path (.var z "l")) (.cons (.path (.var z "A")) .nil)))))⟩)
  "new"

-- An empty body `{}` reads as no body
#eval expect (parsed (file ["class K {}", "val program = new K"]) == parsed (file ["class K", "val program = new K"]))
  "empty class body"

/-! ## Classes and traits (N5): the parser's refusals, at their positions -/

#eval expect (at? (file ["val program = {", "  class L(val v: Any)", "  A", "}"]) 5 5 msgRLC) "LC-block"
#eval expect (at? (file ["val program: { type T } = new Object {", "  class L", "  type T = Any",
    "}"]) 5 5 msgRLC) "LC-lit"
#eval expect (at? (file ["val program: { type T } = new Object {", "  abstract class L", "  type T = Any",
    "}"]) 5 14 msgRLC) "LC-abstract-lit"
#eval expect (at? (file ["class O {", "  class I", "}", "val program = A"]) 5 5 msgRCC) "CC-class"
#eval expect (at? (file ["trait O { object o { type T = Any } }", "val program = A"]) 4 13 msgRCC) "CC-object"
#eval expect (at? (file ["trait O { abstract class I }", "val program = A"]) 4 22 msgRCC) "CC-abstract"
#eval expect (at? (file ["trait T", "object o extends T { type U = Any }", "val program = o"]) 5 12 msgROE) "OE"
#eval expect (at? (file ["trait T", "val program = new T { type U = Any }"]) 5 23 msgRAN) "AN-trait"
#eval expect (at? (file ["class K(val v: Any)", "val program = new K(A) { type U = Any }"]) 5 26 msgRAN) "AN-class"
#eval expect (at? (file ["class B { def m(u: Any): Any = u }",
    "class K extends B { override def m(u: Any): Any = super.m(u) }", "val program = A"]) 5 53 msgRSU) "SU"
#eval expect (at? (file ["class K { val v = A }", "val program = A"]) 4 17 msgRW) "W-val"
#eval expect (at? (file ["class K { def m(u: Any) = u }", "val program = A"]) 4 17 msgRW) "W-def"
#eval expect (at? (file ["class K[X]", "val program = A"]) 4 10 msgRTP) "TP-class"
#eval expect (at? (file ["trait T[X]", "val program = A"]) 4 10 msgRTP) "TP-trait"
#eval expect (at? (file ["class K", "val program = new K[Any]"]) 5 22 "type arguments are outside the subset") "TP-new"
#eval expect (at? (file ["final class K", "val program = A"]) 4 3 (msgRMO "final")) "MO-final"
#eval expect (at? (file ["class K { private val v: Any = A }", "val program = A"]) 4 13 (msgRMO "private")) "MO-private"
#eval expect (at? (file ["object o { override def m(u: Any): Any = u }",
    "val program = o"]) 4 14 (msgRMO "override")) "MO-override-obj"
#eval expect (at? (file ["lazy val x = A", "val program = A"]) 4 3 (msgRMO "lazy")) "MO-lazy"
#eval expect (at? (file ["abstract trait T", "val program = A"]) 4 3 (msgRMO "abstract")) "MO-abstract-trait"
#eval expect (at? (file ["case class K(v: Any)", "val program = A"]) 4 3 (msgRMO "case")) "MO-case"
#eval expect (at? (file ["class K { def m: Any }", "val program = A"]) 4 17 msgRP) "RP-class"
#eval expect (at? (file ["object o { type T }", "val program = o"]) 4 19 msgRA) "RA-obj-stays"
#eval expect (at? (file ["def f(x: Any): Any = x",
    "val program = f(A, A)"]) 5 20 "several arguments are outside the subset") "several-args-app"
#eval expect (at? (file ["trait T(x: Any)",
    "val program = A"]) 4 10 "expected a line break or `;`, found `(`") "trait-param"

/-! ## Classes and traits (N5): the refusals of the walk, at their positions -/

#eval expect (verdict (file ["class K(val v: Any, val w: Any)", "class L(val u: Any) extends K(u, A)",
    "val program = new L(A)"]) == "taken") "args-ok"
#eval expect (verdict (file ["class K", "class L extends K()", "val program = new L()"]) == "taken") "args-empty"
#eval expect (verdict (file ["val program = new Q"]) == at! 4 21 (Scope.msgNoCls "Q")) "new-unknown"
#eval expect (verdict (file ["object m { class K(val v: Any) }", "val program = new m.K(m)"]) == "taken") "new-path"
#eval expect (verdict (file ["object m { class K }", "object k {", "  val a: m.type = m", "  class D extends a.K",
    "}", "val program = A"]) == at! 7 23 Scope.msgRPP) "PP-alias"
#eval expect (verdict (file ["class D extends Q", "val program = A"]) == at! 4 19 Scope.msgRPP) "PP-unknown"
#eval expect (verdict (file ["object m { type T = Any }", "class D extends m.T", "val program = A"])
    == at! 5 21 Scope.msgRPP) "PP-typealias"
#eval expect (verdict (file ["object m { object n { trait T } }", "class D extends m.n.T", "val program = A"])
    == "taken") "PP-ok"
#eval expect (verdict (file ["class K", "object o { type K = Any }", "val program = o"])
    == at! 5 19 Scope.msgRCN) "CN-obj"
#eval expect (verdict (file ["class K", "val program = (x: { type K }) => x"]) == at! 5 28 Scope.msgRCN) "CN-ref"
#eval expect (verdict (file ["class K", "trait T { type K }", "val program = A"]) == at! 5 18 Scope.msgRCN) "CN-cls"
#eval expect (verdict (file ["object a { class K }", "object b { class K }", "val program = A"])
    == at! 5 20 Scope.msgRCN2) "CN-dup"
#eval expect (verdict (file ["class K { val me: Any = this }", "val program = A"]) == at! 4 17 Scope.msgRVT) "VT"
#eval expect (verdict (file ["class K(val w: Any) { val v: Any = this.w }", "val program = A"])
    == at! 4 29 Scope.msgRVT) "VT-sel"
#eval expect (verdict (file ["class K { val v: Any = { A } }", "val program = A"]) == at! 4 17 Scope.msgRR) "R-cls"
#eval expect (verdict (file ["class K { val f: Any => Any = (x: Any) => x }", "val program = A"])
    == "taken") "cls-val-lambda"
#eval expect (verdict (file ["class K(x: Any)", "val program = (c: K) => c.x"])
    == at! 5 29 (Scope.msgRPA "x")) "PA-path"
#eval expect (verdict (file ["class K(x: Any)", "val program = new K(A).x"]) == at! 5 26 (Scope.msgRPA "x")) "PA-new"
#eval expect (verdict (file ["class K(x: Any) {", "  def get(u: Any): Any = x", "  def me(u: Any): Any = this.x", "}",
    "val program = A"]) == "taken") "PA-inside"
#eval expect (verdict (file ["trait T { val v: Any }", "object o {", "  val v: o.type = o",
    "  class K(val v2: Any) extends T { def get(u: Any): Any = v }", "}", "val program = o"])
    == at! 7 61 (Scope.msgRBN "v")) "BN"
#eval expect (verdict (file ["trait T { val v: Any }", "object o {", "  val v: o.type = o",
    "  class K(val w: Any) extends T { val v: Any = w; def get(u: Any): Any = v }", "}", "val program = o"])
    == "taken") "BN-own"
#eval expect (verdict (file ["trait P extends Q", "trait Q extends P", "val program = A"])
    == at! 4 19 (Scope.msgRCI "trait" "P")) "CI"
#eval expect (verdict (file ["trait P extends P", "val program = A"]) == at! 4 19 (Scope.msgRCI "trait" "P")) "CI-self"
#eval expect (verdict (file ["trait X extends P", "trait P extends Q", "trait Q extends P", "val program = A"])
    == at! 5 19 (Scope.msgRCI "trait" "P")) "CI-below"
#eval expect (verdict (file ["object a { type T = Any }", "object b { type T = Any }", "trait L { type X >: a.type }",
    "trait R { type X >: b.type }", "class K extends L with R", "val program = A"]) == at! 8 9 (Scope.msgRLB "X")) "LB"
#eval expect (verdict (file ["object a { type T = Any }", "object b { type T = Any }", "trait L { type X >: a.type }",
    "trait R { type X >: b.type }", "class K extends L with R { type X = a.type }", "val program = A"])
    == "taken") "LB-alias"
#eval expect (verdict (file ["object a { type T = Any }", "object b { type T = Any }", "trait L { type X >: a.type }",
    "trait R { type X >: b.type }", "trait K extends L with R", "val program = A"]) == "taken") "LB-trait"
#eval expect (verdict (file ["object a { type T = Any }", "trait L { type X >: a.type }",
    "trait R { type X >: a.type }", "class K extends L with R", "val program = A"]) == "taken") "LB-same"
#eval expect (verdict (file ["class P { def m(y: Any): Any = y }", "class K extends P { def m(y: P): Any = y }",
    "val program = A"]) == at! 5 27 (Scope.msgROL "m")) "OL"
#eval expect (verdict (file ["trait P { def m(y: Any): Any }", "class K extends P { def m(y: K): Any = y }",
    "val program = A"]) == "taken") "OL-abstract"
#eval expect (verdict (file ["class P { def m(y: Any): Any = y }", "class K extends P { def m(y: Any): Any = y }",
    "val program = A"]) == "taken") "OL-same"
#eval expect (verdict (file ["class K { def v(u: Any): Any = u }", "trait T { val v: Any }", "val program = A"])
    == at! 5 17 Scope.msgRD) "RD-cls"
#eval expect (verdict (file ["class K { def m(u: Any): Any = this.z }", "val program = A"])
    == at! 4 39 "value z is not a member of the class (scalac E008)") "R5-cls"
#eval expect (verdict (file ["trait T { val v: Any }",
    "class K(val w: Any) extends T { val v: Any = w; def m(u: Any): Any = this.v }", "val program = A"])
    == "taken") "this-inherited"
#eval expect (verdict (file ["object o { type T = Any }", "class K(val p: o.type)",
    "val program = (k: K) => (y: k.p.T) => y"]) == "taken") "inst-prefix"
#eval expect (verdict (file ["object o { type T = Any }", "class K(val p: o.type)", "val program = {",
    "  val k = new K(o)", "  (y: k.p.T) => y", "}"]) == "taken") "inst-prefix-new"
#eval expect (verdict (file ["object o { type T = Any }", "class K { def p(u: Any): o.type = o }",
    "val program = (k: K) => (y: k.p.T) => y"])
    == at! 6 33 "a method is called with all its parameter lists") "inst-prefix-def"
#eval expect (verdict (file ["class k", "val program = A"])
    == at! 4 9 "the type member `k` starts lower case: type members start upper case") "R7-cls"
#eval expect (verdict (file ["class K(val v: Any) { val v: Any = A }", "val program = A"])
    == at! 4 29 "conflicting definitions of `v` in one class (scalac E120)") "R8-cls"
#eval expect (verdict (file ["class K(v: Any, v: Any)", "val program = A"])
    == at! 4 19 "`v` is already a parameter of `K`") "R8-param"
#eval expect (verdict (file ["class K {}", "val program = new K"]) == "taken") "empty-body"

/-! ## Classes and traits (N5): the repairs of the refutation, at their positions -/

#eval expect (verdict (file ["class D(val w: Any)", "class K(val x: Any) extends D(y) { val y: Any = x }", "val program = new K(A)"])
    == at! 5 33 "`y` is not in scope") "head-parent-arg-member"
#eval expect (verdict (file ["trait T { val y: Any = A }", "class D(val w: Any)", "class K extends D(y) with T", "val program = new K"])
    == at! 6 21 "`y` is not in scope") "head-parent-arg-inherited"
#eval expect (verdict (file ["class D(val w: Any)", "class K(z: Any) extends D(z)", "val program = new K(A)"])
    == "taken") "head-parent-arg-param"
#eval expect (verdict (file ["class C(val v: L) { type L = Any }", "val program = new C(A)"])
    == at! 4 18 "the type `L` is outside the subset") "head-param-type-member"
#eval expect (verdict (file ["trait M { type T }", "class C(val v: o.T, val o: M)", "val program = A"])
    == at! 5 18 "forward reference: `o` is defined later in this block (scalac E039)") "head-param-forward"
#eval expect (verdict (file ["trait M { type T }", "class C(val o: M, val v: o.T)", "val program = A"])
    == "taken") "head-param-earlier"
#eval expect (verdict (file ["type L = Any", "class C(val v: this.L) { type L = Nothing }", "val program = new C(A)"])
    == "taken") "head-this-outer"
#eval expect (verdict (file ["trait T { type L = Any }", "object o {", "  type L = A.type", "  class C extends T { def f(y: L): Any = y }", "}", "val program = A"])
    == at! 7 34 (Scope.msgRBN "L")) "BN-type"
#eval expect (verdict (file ["trait T { type L = Any }", "object o {", "  type L = A.type", "  class C extends T { type L = Any; def f(y: L): Any = y }", "}", "val program = A"])
    == "taken") "BN-type-own"
#eval expect (verdict (file ["class D(x: Any) { def get(y: Any): Any = x }", "class K(z: Any) extends D(z) { def h(y: Any): Any = x }", "val program = new K(A)"])
    == at! 5 55 "`x` is not in scope") "plain-inherited"
#eval expect (verdict (file ["class D(x: Any) { def get(y: Any): Any = x }", "class K(z: Any) extends D(z) { def h(y: Any): Any = this.x }", "val program = new K(A)"])
    == at! 5 60 "value x is not a member of the class (scalac E008)") "plain-inherited-this"
#eval expect (verdict (file ["object o {", "  object x { type T = Any }", "  class D(x: Any) { def get(y: Any): Any = x }", "  class K(z: Any) extends D(z) { def h(y: Any): Any = x }", "}", "val program = new o.K(A)"])
    == "taken") "plain-inherited-outer"
#eval expect (verdict (file ["trait P { def m(y: Any): Any }", "trait K extends P { def m(y: K): Any = y }", "val program = A"])
    == at! 5 27 (Scope.msgROL "m")) "OL-trait-abstract"
#eval expect (verdict (file ["trait P { def m(y: Any): Any = y }", "trait Q { def m(y: P): Any = y }", "class K extends P with Q", "val program = new K"])
    == at! 6 9 (Scope.msgROL2 "m")) "OL-two-parents"
#eval expect (verdict (file ["trait P { def m(y: Any): Any }", "trait Q { def m(y: P): Any }", "trait K extends P with Q", "val program = A"])
    == at! 6 9 (Scope.msgROL2 "m")) "OL-two-parents-abstract"
#eval expect (verdict (file ["trait P { def m(y: Any): Any = y }", "trait R { def m(y: P): Any }", "class K extends P with R { override def m(y: P): Any = y }", "val program = new K"])
    == at! 6 43 (Scope.msgROL "m")) "OL-override-overload"
#eval expect (verdict (file ["class D", "class P { def m(y: D): Any = y }", "class K extends P { override def m(y: Any): Any = y }", "val program = A"])
    == "taken") "OL-override-widen"
#eval expect (verdict (file ["class C {", "  type A = B", "  type B = A", "}", "val program = new C"])
    == at! 5 10 (Scope.msgRY true "alias" "A")) "RY-cls"
#eval expect (verdict (file ["class C {", "  type A = this.B", "  type B = this.A", "}", "val program = new C"])
    == at! 5 10 (Scope.msgRY true "alias" "A")) "RY-cls-this"
#eval expect (verdict (file ["trait T { type A = B; type B }", "class K extends T { type B = A }", "val program = new K"])
    == at! 5 28 (Scope.msgRY true "alias" "B")) "RY-cls-inherited"
#eval expect (verdict (file ["trait T { type A = B; type B }", "trait U { type B = A; type A }", "class K extends T with U", "val program = new K"])
    == at! 6 9 (Scope.msgRY false "inherited alias or bound" "B")) "RY-cls-two-parents"
#eval expect (verdict (file ["class C {", "  val x: y.type = y", "  val y: x.type = x", "}", "val program = new C"])
    == at! 5 9 (Scope.msgRC "x")) "RC-cls"
#eval expect (verdict (file ["trait T { val x: y.type = y; val y: Any }", "class K extends T { val y: x.type = x }", "val program = new K"])
    == at! 5 27 (Scope.msgRC "y")) "RC-cls-inherited"
#eval expect (verdict (file ["class K { val v: Any = A }", "val program = (new K).v"])
    == "taken") "sel-new-nil"
#eval expect (verdict (file ["class K", "val program = (new K)(A)"])
    == "taken") "app-new-nil"
#eval expect (verdict (file ["object m { class K { val v: Any = A } }", "val program = (new m.K).v"])
    == "taken") "sel-new-path-nil"

-- G-1: a parameter's type is read outside the body, so `this.w` is the wrapper's object `w`
#eval expect (kindAt (file ["object w { type T = Any }", "class C(val v: this.w.type) { val w: Any = A }",
  "val program = (k: C) => k"]) (.sel (.var z "k") z "v") == some .obj) "kind k.v: a parameter type read in the head"
-- G-4: `new` with no arguments under a selection or an application prints in parentheses
#eval expect (printed (file ["class K { val v: Any = A }", "val program = (new K).v"]) ==
  some (file ["class K {", "  val v: Any = A", "}", "val program = (new K).v"])) "print of (new K).v"

/-! ## Classes and traits (N5): kinds, linearization, labels -/

#eval expect (kindAt (file ["class K(val p: Any)", "val program = (k: K) => k"]) (.var z "k") == some .inst)
  "kind k: a parameter at a class"
#eval expect (kindAt (file ["object o { type T = Any }", "class K(val p: o.type)", "val program = (k: K) => k"])
  (.sel (.var z "k") z "p") == some .obj) "kind k.p: a val parameter at a module singleton"
#eval expect (kindAt (file ["class K { def get(u: Any): Any = u }", "val program = (k: K) => k"])
  (.sel (.var z "k") z "get") == some (.meth 1)) "kind k.get: a def of a class"
#eval expect (kindAt (file ["trait T { val v: Any }", "class K(val w: Any) extends T { val v: Any = w }",
  "val program = (k: K) => k"]) (.sel (.var z "k") z "v") == some .str) "kind k.v: an own val at Any"
#eval expect (kindAt (file ["trait T { val v: Any }", "class K extends T", "val program = (k: K) => k"])
  (.sel (.var z "k") z "v") == some .str) "kind k.v: an inherited val"
#eval expect (kindAt (file ["class K", "val program = { val k = new K; k }"]) (.var z "k") == some .inst)
  "kind k: a block val bound to new"

/-- The names of `L(C)` for the class `C` of a text, in order, or `none`. -/
def linNames (s : String) (C : String) : Option (List String) :=
  (parseFile s.toList).toOption.bind fun F =>
    match (F.mems.clsEnvs (Scope.stemEnv F)).find? fun e => ((Scope.clsOf? e).map (·.name)) == some C with
    | some e => (Scope.linOf e).map fun L => L.filterMap fun e' => (Scope.clsOf? e').map (·.name)
    | none => none

-- facts 6.7, scout S07: L(E) = E, D, B, C, A
#eval expect (linNames (file ["trait A", "trait B extends A", "trait C extends A", "trait D extends B with C",
  "class E extends C with B with D", "val program = A"]) "E" == some ["E", "D", "B", "C", "A"]) "L(E), S07"
-- the diamond of S06: L(K) = K, R, L, Base
#eval expect (linNames (file ["class Base", "trait L extends Base", "trait R extends Base",
  "class K extends Base with L with R", "val program = A"]) "K" == some ["K", "R", "L", "Base"]) "L(K), a diamond"
-- a cycle answers none
#eval expect (linNames (file ["trait P extends Q", "trait Q extends P", "val program = A"]) "P" == none) "L(P), a cycle"

#eval expect ((parseFile (file ["class C(x: Any) { def get(u: Any): Any = x }",
    "val program = new C(A)"]).toList).toOption.map labels ==
  some [("C", .typ 0), ("get", .trm 0), ("new$C", .trm 1), ("get$C", .trm 2), ("ℓx$C", .trm 3), ("ℓself", .trm 4)])
  "labels: new$C, get$C, ℓx$C"
#eval expect ((parseFile (file ["trait T { def m(u: Any): Any }", "class K extends T { def m(u: Any): Any = u }",
    "val program = new K"]).toList).toOption.map labels ==
  some [("T", .typ 0), ("m", .trm 0), ("K", .typ 1), ("new$K", .trm 1), ("m$K", .trm 2), ("ov$K$m$K", .trm 3),
    ("ovp$K$m$K", .trm 4), ("ov$K$m$T", .trm 5), ("ovp$K$m$T", .trm 6), ("ℓself", .trm 7)])
  "labels: the override witnesses"
#eval expect ((parseFile (file ["trait T { type L <: Any }", "class K extends T { type L = Any }",
    "val program = new K"]).toList).toOption.map labels ==
  some [("T", .typ 0), ("L", .typ 1), ("K", .typ 2), ("new$K", .trm 0), ("ovl$K$L$T", .trm 1), ("ovu$K$L$T", .trm 2),
    ("ℓself", .trm 3)])
  "labels: the type member witnesses"

/-! ## Classes and traits (N5): the printer -/

/-- `scala/nominal/pos/Running.scala`, verbatim. -/
def running : String := "import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d1/sc/Running.scala, d1 Running
object Running {
  trait Shape {
    type Unit
    def area(u: Any): Any
    def me(u: Any): Shape = this
    def self2(u: Any): this.type = this
  }
  class Square(val side: Any) extends Shape {
    type Unit = Any
    def area(u: Any): Any = side
  }
  object geo {
    class Point(val x: Any) { def move(d: Any): Point = new Point(d) }
  }
  val program = {
    val s: Shape = new Square(geo)
    val p: geo.Point = new geo.Point(s)
    val q = s.me(p)
    val w: q.type = q.self2(p)
    val a = p.move(w)
    a.x
  }
}
"

-- Members one per line, a class body two spaces further in, `new` in place
#eval expect (printed running == some "import scala.reflect.Selectable.reflectiveSelectable

object Running {
  trait Shape {
    type Unit
    def area(u: Any): Any
    def me(u: Any): Shape = this
    def self2(u: Any): this.type = this
  }
  class Square(val side: Any) extends Shape {
    type Unit = Any
    def area(u: Any): Any = side
  }
  object geo {
    class Point(val x: Any) {
      def move(d: Any): Point = new Point(d)
    }
  }
  val program = {
    val s: Shape = new Square(geo)
    val p: geo.Point = new geo.Point(s)
    val q = s.me(p)
    val w: q.type = q.self2(p)
    val a = p.move(w)
    a.x
  }
}
") "print of Running"

/-- The texts of the rows of the refutation's repairs. -/
def repairTexts : List String :=
  [file ["class D(val w: Any)", "class K(val x: Any) extends D(y) { val y: Any = x }", "val program = new K(A)"],
    file ["trait T { val y: Any = A }", "class D(val w: Any)", "class K extends D(y) with T", "val program = new K"],
    file ["class D(val w: Any)", "class K(z: Any) extends D(z)", "val program = new K(A)"],
    file ["class C(val v: L) { type L = Any }", "val program = new C(A)"],
    file ["trait M { type T }", "class C(val v: o.T, val o: M)", "val program = A"],
    file ["trait M { type T }", "class C(val o: M, val v: o.T)", "val program = A"],
    file ["type L = Any", "class C(val v: this.L) { type L = Nothing }", "val program = new C(A)"],
    file ["trait T { type L = Any }", "object o {", "  type L = A.type", "  class C extends T { def f(y: L): Any = y }", "}", "val program = A"],
    file ["trait T { type L = Any }", "object o {", "  type L = A.type", "  class C extends T { type L = Any; def f(y: L): Any = y }", "}", "val program = A"],
    file ["class D(x: Any) { def get(y: Any): Any = x }", "class K(z: Any) extends D(z) { def h(y: Any): Any = x }", "val program = new K(A)"],
    file ["class D(x: Any) { def get(y: Any): Any = x }", "class K(z: Any) extends D(z) { def h(y: Any): Any = this.x }", "val program = new K(A)"],
    file ["object o {", "  object x { type T = Any }", "  class D(x: Any) { def get(y: Any): Any = x }", "  class K(z: Any) extends D(z) { def h(y: Any): Any = x }", "}", "val program = new o.K(A)"],
    file ["trait P { def m(y: Any): Any }", "trait K extends P { def m(y: K): Any = y }", "val program = A"],
    file ["trait P { def m(y: Any): Any = y }", "trait Q { def m(y: P): Any = y }", "class K extends P with Q", "val program = new K"],
    file ["trait P { def m(y: Any): Any }", "trait Q { def m(y: P): Any }", "trait K extends P with Q", "val program = A"],
    file ["trait P { def m(y: Any): Any = y }", "trait R { def m(y: P): Any }", "class K extends P with R { override def m(y: P): Any = y }", "val program = new K"],
    file ["class D", "class P { def m(y: D): Any = y }", "class K extends P { override def m(y: Any): Any = y }", "val program = A"],
    file ["class C {", "  type A = B", "  type B = A", "}", "val program = new C"],
    file ["class C {", "  type A = this.B", "  type B = this.A", "}", "val program = new C"],
    file ["trait T { type A = B; type B }", "class K extends T { type B = A }", "val program = new K"],
    file ["trait T { type A = B; type B }", "trait U { type B = A; type A }", "class K extends T with U", "val program = new K"],
    file ["class C {", "  val x: y.type = y", "  val y: x.type = x", "}", "val program = new C"],
    file ["trait T { val x: y.type = y; val y: Any }", "class K extends T { val y: x.type = x }", "val program = new K"],
    file ["class K { val v: Any = A }", "val program = (new K).v"],
    file ["class K", "val program = (new K)(A)"],
    file ["object m { class K { val v: Any = A } }", "val program = (new m.K).v"]]

/-- The texts of the class checks. -/
def classTexts : List String :=
  [running,
    file ["val program = {", "  class L(val v: Any)", "  A", "}"],
    file ["val program: { type T } = new Object {", "  class L", "  type T = Any", "}"],
    file ["val program: { type T } = new Object {", "  abstract class L", "  type T = Any", "}"],
    file ["class O {", "  class I", "}", "val program = A"],
    file ["trait O { object o { type T = Any } }", "val program = A"],
    file ["trait O { abstract class I }", "val program = A"],
    file ["trait T", "object o extends T { type U = Any }", "val program = o"],
    file ["trait T", "val program = new T { type U = Any }"],
    file ["class K(val v: Any)", "val program = new K(A) { type U = Any }"],
    file ["class B { def m(u: Any): Any = u }", "class K extends B { override def m(u: Any): Any = super.m(u) }",
    "val program = A"],
    file ["class K { val v = A }", "val program = A"],
    file ["class K { def m(u: Any) = u }", "val program = A"],
    file ["class K[X]", "val program = A"],
    file ["trait T[X]", "val program = A"],
    file ["class K", "val program = new K[Any]"],
    file ["final class K", "val program = A"],
    file ["class K { private val v: Any = A }", "val program = A"],
    file ["object o { override def m(u: Any): Any = u }", "val program = o"],
    file ["lazy val x = A", "val program = A"],
    file ["abstract trait T", "val program = A"],
    file ["case class K(v: Any)", "val program = A"],
    file ["class K { def m: Any }", "val program = A"],
    file ["object o { type T }", "val program = o"],
    file ["class K(val v: Any, val w: Any)", "class L(val u: Any) extends K(u, A)", "val program = new L(A)"],
    file ["class K", "class L extends K()", "val program = new L()"],
    file ["def f(x: Any): Any = x", "val program = f(A, A)"],
    file ["val program = new Q"],
    file ["object m { class K(val v: Any) }", "val program = new m.K(m)"],
    file ["object m { class K }", "object k {", "  val a: m.type = m", "  class D extends a.K", "}", "val program = A"],
    file ["class D extends Q", "val program = A"],
    file ["object m { type T = Any }", "class D extends m.T", "val program = A"],
    file ["object m { object n { trait T } }", "class D extends m.n.T", "val program = A"],
    file ["class K", "object o { type K = Any }", "val program = o"],
    file ["class K", "val program = (x: { type K }) => x"],
    file ["class K", "trait T { type K }", "val program = A"],
    file ["object a { class K }", "object b { class K }", "val program = A"],
    file ["class K { val me: Any = this }", "val program = A"],
    file ["class K(val w: Any) { val v: Any = this.w }", "val program = A"],
    file ["class K { val v: Any = { A } }", "val program = A"],
    file ["class K { val f: Any => Any = (x: Any) => x }", "val program = A"],
    file ["class K(x: Any)", "val program = (c: K) => c.x"],
    file ["class K(x: Any)", "val program = new K(A).x"],
    file ["class K(x: Any) {", "  def get(u: Any): Any = x", "  def me(u: Any): Any = this.x", "}", "val program = A"],
    file ["trait T { val v: Any }", "object o {", "  val v: o.type = o",
    "  class K(val v2: Any) extends T { def get(u: Any): Any = v }", "}", "val program = o"],
    file ["trait T { val v: Any }", "object o {", "  val v: o.type = o",
    "  class K(val w: Any) extends T { val v: Any = w; def get(u: Any): Any = v }", "}", "val program = o"],
    file ["trait P extends Q", "trait Q extends P", "val program = A"],
    file ["trait P extends P", "val program = A"],
    file ["trait X extends P", "trait P extends Q", "trait Q extends P", "val program = A"],
    file ["object a { type T = Any }", "object b { type T = Any }", "trait L { type X >: a.type }",
    "trait R { type X >: b.type }", "class K extends L with R", "val program = A"],
    file ["object a { type T = Any }", "object b { type T = Any }", "trait L { type X >: a.type }",
    "trait R { type X >: b.type }", "class K extends L with R { type X = a.type }", "val program = A"],
    file ["object a { type T = Any }", "object b { type T = Any }", "trait L { type X >: a.type }",
    "trait R { type X >: b.type }", "trait K extends L with R", "val program = A"],
    file ["object a { type T = Any }", "trait L { type X >: a.type }", "trait R { type X >: a.type }",
    "class K extends L with R", "val program = A"],
    file ["class P { def m(y: Any): Any = y }", "class K extends P { def m(y: P): Any = y }", "val program = A"],
    file ["trait P { def m(y: Any): Any }", "class K extends P { def m(y: K): Any = y }", "val program = A"],
    file ["class P { def m(y: Any): Any = y }", "class K extends P { def m(y: Any): Any = y }", "val program = A"],
    file ["class K { def v(u: Any): Any = u }", "trait T { val v: Any }", "val program = A"],
    file ["class K { def m(u: Any): Any = this.z }", "val program = A"],
    file ["trait T { val v: Any }", "class K(val w: Any) extends T { val v: Any = w; def m(u: Any): Any = this.v }",
    "val program = A"],
    file ["object o { type T = Any }", "class K(val p: o.type)", "val program = (k: K) => (y: k.p.T) => y"],
    file ["object o { type T = Any }", "class K(val p: o.type)", "val program = {", "  val k = new K(o)",
    "  (y: k.p.T) => y", "}"],
    file ["object o { type T = Any }", "class K { def p(u: Any): o.type = o }",
    "val program = (k: K) => (y: k.p.T) => y"],
    file ["class k", "val program = A"],
    file ["class K(val v: Any) { val v: Any = A }", "val program = A"],
    file ["class K(v: Any, v: Any)", "val program = A"],
    file ["trait T(x: Any)", "val program = A"],
    file ["class K {}", "val program = new K"]] ++
  repairTexts

/-- The class texts that `check` takes. -/
def takenClassTexts : List String := classTexts.filter fun s => verdict s == "taken"
#eval expect (takenClassTexts.length == 26) "26 class texts that check takes"
#eval expect (takenClassTexts.all roundTrips) "round trip of every class text that check takes"
#eval expect (takenClassTexts.all selfLast) "labels: ℓself last in every class text that check takes"

end NominalFrontend.ScalaRead.Tests
