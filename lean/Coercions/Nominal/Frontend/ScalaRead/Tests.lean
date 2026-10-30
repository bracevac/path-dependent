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
-/

namespace NominalFrontend.ScalaRead.Tests

open NominalFrontend.ScalaRead
open NominalFrontend.ScalaRead.Parse (msgRA msgRP msgRO msgProgram msgDefTerm msgAfter msgRT msgExtends msgRI
  msgHeader)
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
#eval expect (at? (file ["class C", "val program = A"]) 4 3 msgRT) "RT-class"
#eval expect (at? (file ["trait C", "val program = A"]) 4 3 msgRT) "RT-trait"
#eval expect (at? (file ["object o { type T = Any }"]) 5 1 msgAfter) "RO-noprogram"
#eval expect (at? (file ["object o extends Any { type T = Any }", "val program = o"]) 4 12 msgExtends) "RT-extends"

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
#eval expect (verdict (file ["class C", "val program = A"]) == at! 4 3 msgRT) "RT-class, check"

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

#eval expect (takenTexts.length == 47) "47 texts of this file that check takes"
#eval expect (takenTexts.all roundTrips) "round trip of every text that check takes"

end NominalFrontend.ScalaRead.Tests
