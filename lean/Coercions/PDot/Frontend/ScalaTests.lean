import Coercions.PDot.Frontend.Scala

/-!
# Checks of the pDOT Scala mapping

One check per row of the mapping (plan XI, "The Scala mapping, one case per construct"), on a text
read by `readPDot`, with the surface term it gives.  Then the label table and the module chains, the
outcome of each row, the member check R-M, the printers on every row, the risk program ProtoSelf,
and the refusals of the printers.  Every check is `#eval expect`.  The texts are string literals, never
files.  `String.toList` runs here in compiled code only, and no theorem mentions it.
-/

namespace PDotFrontend.Scala.Tests

open PDotFrontend PDotFrontend.Scala

/-- A test file: the header, a blank line, `object A {` on line 3, the lines indented by two, `}`. -/
def file (ls : List String) : String :=
  "import scala.reflect.Selectable.reflectiveSelectable\n\nobject A {\n" ++
    String.join (ls.map fun l => "  " ++ l ++ "\n") ++ "}\n"

/-- The surface term of a text, or `none` when it is refused. -/
def term (ls : List String) : Option STm := (readPDot (file ls).toList).toOption.map (·.1)

/-- The binder of a template one level below the stem. -/
def n1 : String := "ν'"

/-- `ℓself = z`, the first definition of a template. -/
def sd (z : String) : SDefs := .trm .nil "ℓself" none (.var z)

/-- `let σ = ν(σ) {d} in b`. -/
def stem (d : SDefs) (b : STm) : STm := .«let» "σ" none (.obj "σ" none d) b

/-- A path `r.a₁.….aₙ` in a type. -/
def sp : String → List String → SPath
  | r, as => as.foldl SPath.sel (.var r)

/-- A path `r.a₁.….aₙ` in a term. -/
def tp : String → List String → STm
  | r, as => as.foldl STm.proj (.var r)

/-- `p.ℓself`. -/
def ts (r : String) (as : List String) : STm := .proj (tp r as) "ℓself"

/-- `object o { type T = Any }` in the stem. -/
def oT : SDefs := .trm (sd "σ") "o" none (.obj n1 none (.typ (sd n1) "T" .top))

/-! ## The program and templates -/

-- `object A { object o { type T = Any }; val program = o }`
#eval expect (term ["object o { type T = Any }", "val program = o"] == some (stem oT (ts "σ" ["o"])))
  "stem"
-- `val program: o.type = o`
#eval expect (term ["object o { type T = Any }", "val program: o.type = o"] ==
  some (stem oT (.asc (ts "σ" ["o"]) (.sngl (sp "σ" ["o"]))))) "stem typed"
-- no member: no stem
#eval expect (term ["val program = (x: Any) => x"] == some (.lam "x" (some .top) (.var "x"))) "no member"
#eval expect (term ["val program: Any => Any = (x: Any) => x"] ==
  some (.asc (.lam "x" (some .top) (.var "x")) (.all "_" .top .top))) "no member typed"
-- no member, the wrapper named: the stem is made
#eval expect (term ["val program = A"] == some (stem (sd "σ") (ts "σ" []))) "wrapper named"
-- `object o { s => val me: s.type = s }`: `s` names the binder
#eval expect (term ["object o { s => val me: s.type = s }", "val program = o"] ==
  some (stem (.trm (sd "σ") "o" none (.obj n1 none (.trm (sd n1) "me" (some (.sngl (.var n1))) (.var n1))))
    (ts "σ" ["o"]))) "object self name"
-- `val a: o.type = o` and `val a = o`, `o` a module path
#eval expect (term ["object o { type T = Any }", "object p { val a: o.type = o }", "val program = p"] ==
  some (stem (.trm oT "p" none (.obj n1 none (.trm (sd n1) "a" (some (.sngl (sp "σ" ["o"]))) (tp "σ" ["o"]))))
    (ts "σ" ["p"]))) "val singleton field"
#eval expect (term ["object o { type T = Any }", "object p { val a = o }", "val program = p"] ==
  some (stem (.trm oT "p" none (.obj n1 none (.trm (sd n1) "a" none (tp "σ" ["o"])))) (ts "σ" ["p"])))
  "val module field"
-- `val f: Any => Any = (u: Any) => u` and `val f = (u: Any) => u`
#eval expect (term ["object o { val f: Any => Any = (u: Any) => u }", "val program = o"] ==
  some (stem (.trm (sd "σ") "o" none (.obj n1 none (.trm (sd n1) "f" (some (.all "_" .top .top))
    (.lam "u" (some .top) (.var "u"))))) (ts "σ" ["o"]))) "val typed lambda"
#eval expect (term ["object o { val f = (u: Any) => u }", "val program = o"] ==
  some (stem (.trm (sd "σ") "o" none (.obj n1 none (.trm (sd n1) "f" none
    (.lam "u" (some .top) (.var "u"))))) (ts "σ" ["o"]))) "val untyped lambda"
-- `def f(x: Any)(y: x.type): x.type = y`
#eval expect (term ["def f(x: Any)(y: x.type): x.type = y", "val program = A"] ==
  some (stem (.trm (sd "σ") "f" (some (.all "x" .top (.all "y" (.sngl (.var "x")) (.sngl (.var "x")))))
    (.lam "x" (some .top) (.lam "y" (some (.sngl (.var "x"))) (.var "y")))) (ts "σ" []))) "def typed curried"
-- `def g(x: Any) = x`
#eval expect (term ["def g(x: Any) = x", "val program = A"] ==
  some (stem (.trm (sd "σ") "g" none (.lam "x" (some .top) (.var "x"))) (ts "σ" []))) "def inferred"
-- `def mk(u: Any): { val a: Any } = new Object { val a: u.type = u }`: the literal under the result
#eval expect (term ["def mk(u: Any): { val a: Any } = new Object { val a: u.type = u }", "val program = A"] ==
  some (stem (.trm (sd "σ") "mk" (some (.all "u" .top (.fld "a" .top)))
    (.lam "u" (some .top) (.«let» "ℓ" none (.obj n1 none (.trm (sd n1) "a" (some (.sngl (.var "u"))) (.var "u")))
      (.asc (.var "ℓ") (.fld "a" .top))))) (ts "σ" []))) "def literal"

/-! ## Types -/

#eval expect (term ["val program = (x: Any) => (y: Nothing) => y"] ==
  some (.lam "x" (some .top) (.lam "y" (some .bot) (.var "y")))) "Any, Nothing"
#eval expect (term ["object o { type T = Any }", "val program = (x: o.T) => (y: o.type) => y"] ==
  some (stem oT (.lam "x" (some (.sel (sp "σ" ["o"]) "T")) (.lam "y" (some (.sngl (sp "σ" ["o"]))) (ts "y" [])))))
  "p.A, p.type"
#eval expect (term ["type T = Any", "val program = (x: T) => x"] ==
  some (stem (.typ (sd "σ") "T" .top) (.lam "x" (some (.sel (.var "σ") "T")) (.var "x")))) "bare A"
#eval expect (term ["val program = (x: { type A; val a: this.A }) => x"] ==
  some (.lam "x" (some (.mu n1 (.and (.typ "A" .bot .top) (.fld "a" (.sel (.var n1) "A"))))) (.var "x")))
  "refinement under μ"
#eval expect (term ["val program = (x: { type A >: Nothing <: Any; type B = Any; val b: Any }) => x"] ==
  some (.lam "x" (some (.and (.typ "A" .bot .top) (.and (.typ "B" .top .top) (.fld "b" .top)))) (.var "x")))
  "refinement, bounds, alias, val"
#eval expect (term ["val program = (x: { type A } & { val b: Any }) => x"] ==
  some (.lam "x" (some (.and (.typ "A" .bot .top) (.fld "b" .top))) (.var "x"))) "S & T"
#eval expect (term ["val program = (f: (x: { type A }) => x.A) => f"] ==
  some (.lam "f" (some (.all "x" (.typ "A" .bot .top) (.sel (.var "x") "A"))) (.var "f"))) "(x: S) => T"
#eval expect (term ["val program = (f: Any => Any) => f"] ==
  some (.lam "f" (some (.all "_" .top .top)) (.var "f"))) "S => T"

/-! ## Paths -/

-- `this` in an object, `o` inside its own body
#eval expect (term ["object o { val me: this.type = this }", "val program = o"] ==
  some (stem (.trm (sd "σ") "o" none (.obj n1 none (.trm (sd n1) "me" (some (.sngl (.var n1))) (.var n1))))
    (ts "σ" ["o"]))) "this of an object"
#eval expect (term ["object o { def me(u: Any): o.type = o }", "val program = o"] ==
  some (stem (.trm (sd "σ") "o" none (.obj n1 none (.trm (sd n1) "me" (some (.all "u" .top (.sngl (.var n1))))
    (.lam "u" (some .top) (ts n1 []))))) (ts "σ" ["o"]))) "o inside its own body"
-- a bare member of an object, of a refinement
#eval expect (term ["object o { type T = Any; def id(u: T): T = u }", "val program = o"] ==
  some (stem (.trm (sd "σ") "o" none (.obj n1 none (.trm (.typ (sd n1) "T" .top) "id"
    (some (.all "u" (.sel (.var n1) "T") (.sel (.var n1) "T"))) (.lam "u" (some (.sel (.var n1) "T")) (.var "u")))))
    (ts "σ" ["o"]))) "bare member of an object"
#eval expect (term ["val program = (t: { type A; val x: { val y: A } }) => t"] ==
  some (.lam "t" (some (.mu n1 (.and (.typ "A" .bot .top) (.fld "x" (.fld "y" (.sel (.var n1) "A")))))) (.var "t")))
  "bare member of an outer refinement"

/-! ## Terms -/

#eval expect (term ["val program = (q: { type B }) => (x: { val a: q.type }) => x.a"] ==
  some (.lam "q" (some (.typ "B" .bot .top)) (.lam "x" (some (.fld "a" (.sngl (.var "q")))) (tp "x" ["a"]))))
  "stable path"
#eval expect (term ["val program = (o: { val a: { type A } }) => o.a"] ==
  some (.lam "o" (some (.fld "a" (.typ "A" .bot .top))) (.bind .unstable "·u" (tp "o" ["a"]) (.var "·u"))))
  "unstable path, bound whole"
#eval expect (term ["val program = (o: { val a: { val b: Any } }) => o.a.b"] ==
  some (.lam "o" (some (.fld "a" (.fld "b" .top))) (.bind .unstable "·u" (tp "o" ["a"]) (tp "·u" ["b"]))))
  "unstable prefix"
#eval expect (term ["val program = (f: Any => { val a: Any }) => f(f).a"] ==
  some (.lam "f" (some (.all "_" .top (.fld "a" .top))) (.proj (.app (.var "f") (.var "f")) "a"))) "e.a"
#eval expect (term ["def f(x: Any)(y: Any): Any = y", "val program = f(A)(A)"] ==
  some (stem (.trm (sd "σ") "f" (some (.all "x" .top (.all "y" .top .top)))
      (.lam "x" (some .top) (.lam "y" (some .top) (.var "y"))))
    (.bind .widen "·v" (.app (.app (tp "σ" ["f"]) (ts "σ" [])) (ts "σ" [])) (.var "·v"))))
  "a def of two lists, as the program's result"
#eval expect (term ["val program = (f: (Any => Any) => Any) => f(x => x)"] ==
  some (.lam "f" (some (.all "_" (.all "_" .top .top) .top))
    (.bind .widen "·v" (.app (.var "f") (.lam "x" none (.var "x"))) (.var "·v")))) "x => e"
#eval expect (term ["val program = (x: Any) => (x: Any)"] ==
  some (.lam "x" (some .top) (.asc (.var "x") .top))) "(e: T)"
#eval expect (term ["val program = (new Object { val a: Any => Any = (u: Any) => u }: { val a: Any => Any })"] ==
  some (.«let» "ℓ" none (.obj n1 none (.trm (sd n1) "a" (some (.all "_" .top .top)) (.lam "u" (some .top) (.var "u"))))
    (.asc (.var "ℓ") (.fld "a" (.all "_" .top .top))))) "a literal under its type"
#eval expect (term ["object o { type T = Any }", "val program = { val c = o; c }"] ==
  some (stem oT (.alias "c" (sp "σ" ["o"]) (ts "c" [])))) "block alias of a module path"
#eval expect (term ["val program = (x: Any) => { val y: x.type = x; y }"] ==
  some (.lam "x" (some .top) (.alias "y" (.var "x") (.var "y")))) "block alias at the singleton"
#eval expect (term ["val program = (x: { val a: Any }) => { val y = x; y }"] ==
  some (.lam "x" (some (.fld "a" .top)) (.«let» "y" none (.var "x") (.var "y")))) "block val of another path"
#eval expect (term ["val program = (f: Any => Any) => { val y = f(f); y }"] ==
  some (.lam "f" (some (.all "_" .top .top))
    (.bind .widen "·v" (.app (.var "f") (.var "f")) (.«let» "y" none (.var "·v") (.var "y"))))) "block val of a term"
#eval expect (term ["val program = (f: Any => Any) => { val y: Any = f(f); f }"] ==
  some (.lam "f" (some (.all "_" .top .top)) (.«let» "y" none (.asc (.app (.var "f") (.var "f")) .top) (.var "f"))))
  "typed block val"
#eval expect (term ["val program = (f: Any => Any) => { val y: Any = f(f); y }"] ==
  some (.lam "f" (some (.all "_" .top .top)) (.«let» "y" (some .top) (.app (.var "f") (.var "f")) (.var "y"))))
  "typed block val, returned"
#eval expect (term ["val program = (f: Any => Any) => { f }"] ==
  some (.lam "f" (some (.all "_" .top .top)) (.var "f"))) "{ e }"
#eval expect (term ["val program = (f: Any => Any) => (x: Any) => f(x)"] ==
  some (.lam "f" (some (.all "_" .top .top))
    (.lam "x" (some .top) (.bind .widen "·v" (.app (.var "f") (.var "x")) (.var "·v"))))) "a lambda body f(u)"

/-! ## Labels and modules -/

#eval expect ((readPDot (file ["object o { object p { type T = Any } }", "val program = o.p"]).toList).toOption.map
    (fun r => (r.2.1, r.2.2)) ==
  some ([("o", .trm 0), ("p", .trm 1), ("T", .typ 0), ("ℓself", .trm 2)], [[], [.trm 0], [.trm 0, .trm 1]]))
  "labels and modules"
#eval expect ((readPDot (file ["val program = (x: Any) => x"]).toList).toOption.map (fun r => r.2.2) == some [])
  "no stem, no module"

/-! ## Outcomes -/

/-- The kind of the outcome of a text. -/
def kindOf (ls : List String) : Kind := (outcome (file ls).toList).kind

/-- The reason of a rejected text. -/
def reasonOf (ls : List String) : Option PReason :=
  match outcome (file ls).toList with
  | .rejected _ r => some r
  | _ => none

/-- The refusal of a text outside. -/
def errOf (ls : List String) : Option ScalaSyntax.Err :=
  match outcome (file ls).toList with
  | .outside e => some e
  | _ => none

#eval expect (kindOf ["object o { type T = Any }", "val program: o.type = o"] == .ok) "ok"
#eval expect (reasonOf ["val program = (x: { type B }) => { val y = x; (z: y.B) => (z: x.B) }"] == some .mismatch)
  "rejected, widened (AliasWiden)"
#eval expect (reasonOf ["val program = { val f = x => x; f }"] == some (.missingParamType none)) "rejected, a slot"
#eval expect (reasonOf ["object loop { def go(u: Any) = loop.go(u) }", "val program = loop"] ==
  some (.cyclicRef (.trm 1))) "rejected, cyclic"
#eval expect (kindOf ["class C", "val program = A"] == .outside) "outside, by the reader"
#eval expect ((outcome "".toList).kind == .outside) "outside, an empty file"

/-! ## The member check R-M -/

-- ObjUndeclared, the text of `scala/pdot/outside/ObjUndeclared.scala` without its comments
#eval expect (errOf ["object o {", "  object a {", "    type A = Any", "  }", "}", "val program = (y: o.a.B) => y"] ==
  some ⟨⟨9, 25⟩, "type B is not a member of the type of o.a (scalac E008)"⟩) "R-M, a type member"
#eval expect (errOf ["object o { type T = Any }", "val program = (y: o.b.type) => y"] ==
  some ⟨⟨5, 23⟩, "`o.b` is not a valid type prefix, since it is not an immutable path (scalac E083)"⟩)
  "an undeclared field step is refused by R-S before R-M"
#eval expect (kindOf ["object o { type T = Any }", "val program = (y: o.T) => y"] == .ok) "R-M, a declared member"
-- R-M walks into a refinement, as scalac (E008) and the vanilla check
#eval expect (kindOf ["object o { type T = Any }", "val program = (y: { val c: o.B }) => y"] == .outside)
  "R-M, inside a refinement"
#eval expect (kindOf ["object o { type T = Any }", "val program = (y: { type C >: o.B }) => y"] == .outside)
  "R-M, inside a refinement's bound"
#eval expect (kindOf ["object o { type T = Any }", "val program = (y: { val c: o.T }) => y"] == .ok)
  "R-M, a declared member inside a refinement"

/-! ## The printers -/

/-- The text of the outcome of a text. -/
def textOf (ls : List String) : String := (outcome (file ls).toList).text

/-- Whether a text reads back from its printed term to the same resolution. -/
def trips (ls : List String) : Bool :=
  match readPDot (file ls).toList with
  | .ok (e, Λ, _) => match roundTrip Λ e with
    | .same => true
    | _ => false
  | .error _ => false

/-- Whether a text is ASCII.  The printers write a name byte by byte (`ScalaRead/Print.lean:33-35`), so
`ℓself` prints as three bytes and `contains 'ℓ'` cannot see it. -/
def ascii (t : String) : Bool := t.toList.all (·.toNat < 128)

/-- Whether the fill of a text prints, is ASCII, and reads back. -/
def fillReads (ls : List String) : Bool :=
  match outcome (file ls).toList with
  | .ok Λ r => match fillToScala Λ r.1 with
    | .ok F => ascii (String.ofList (ScalaRead.print F)) && (readPDot (ScalaRead.print F)).toOption.isSome
    | .error _ => false
  | _ => false


#eval expect (textOf ["object o { type T = Any }", "val program: o.type = o"] == "ok : Any") "text, ok"
#eval expect (textOf ["object o { type T = Any }", "val program = (y: o.T) => y"] == "ok : Any => Any") "text, a type"
#eval expect (textOf ["val program = (x: { type B }) => { val y = x; (z: y.B) => (z: x.B) }"] ==
  "rejected: Type mismatch") "text, rejected"
#eval expect (textOf ["val program = { val f = x => x; f }"] == "rejected: missing parameter type (scalac E081)")
  "text, a slot"
#eval expect (textOf ["object loop { def go(u: Any) = loop.go(u) }", "val program = loop"] ==
  "rejected: recursive value go needs type (scalac E044)") "text, cyclic"
#eval expect (textOf ["object o {", "  object a {", "    type A = Any", "  }", "}", "val program = (y: o.a.B) => y"] ==
  "outside 9:25: type B is not a member of the type of o.a (scalac E008)") "text, outside"

-- every text of the mapping section reads back to the same resolution
#eval expect ([["object o { type T = Any }", "val program = o"],
    ["object o { type T = Any }", "val program: o.type = o"],
    ["val program = (x: Any) => x"], ["val program: Any => Any = (x: Any) => x"], ["val program = A"],
    ["object o { s => val me: s.type = s }", "val program = o"],
    ["object o { type T = Any }", "object p { val a: o.type = o }", "val program = p"],
    ["object o { type T = Any }", "object p { val a = o }", "val program = p"],
    ["object o { val f: Any => Any = (u: Any) => u }", "val program = o"],
    ["object o { val f = (u: Any) => u }", "val program = o"],
    ["def f(x: Any)(y: x.type): x.type = y", "val program = A"], ["def g(x: Any) = x", "val program = A"],
    ["def mk(u: Any): { val a: Any } = new Object { val a: u.type = u }", "val program = A"],
    ["val program = (x: Any) => (y: Nothing) => y"],
    ["object o { type T = Any }", "val program = (x: o.T) => (y: o.type) => y"],
    ["type T = Any", "val program = (x: T) => x"], ["val program = (x: { type A; val a: this.A }) => x"],
    ["val program = (x: { type A >: Nothing <: Any; type B = Any; val b: Any }) => x"],
    ["val program = (x: { type A } & { val b: Any }) => x"], ["val program = (f: (x: { type A }) => x.A) => f"],
    ["val program = (f: Any => Any) => f"], ["object o { val me: this.type = this }", "val program = o"],
    ["object o { def me(u: Any): o.type = o }", "val program = o"],
    ["object o { type T = Any; def id(u: T): T = u }", "val program = o"],
    ["val program = (t: { type A; val x: { val y: A } }) => t"],
    ["val program = (q: { type B }) => (x: { val a: q.type }) => x.a"],
    ["val program = (o: { val a: { type A } }) => o.a"], ["val program = (o: { val a: { val b: Any } }) => o.a.b"],
    ["val program = (f: Any => { val a: Any }) => f(f).a"],
    ["def f(x: Any)(y: Any): Any = y", "val program = f(A)(A)"],
    ["val program = (f: (Any => Any) => Any) => f(x => x)"], ["val program = (x: Any) => (x: Any)"],
    ["val program = (new Object { val a: Any => Any = (u: Any) => u }: { val a: Any => Any })"],
    ["object o { type T = Any }", "val program = { val c = o; c }"],
    ["val program = (x: Any) => { val y: x.type = x; y }"], ["val program = (x: { val a: Any }) => { val y = x; y }"],
    ["val program = (f: Any => Any) => { val y = f(f); y }"],
    ["val program = (f: Any => Any) => { val y: Any = f(f); f }"],
    ["val program = (f: Any => Any) => { val y: Any = f(f); y }"], ["val program = (f: Any => Any) => { f }"],
    ["val program = (f: Any => Any) => (x: Any) => f(x)"]].all trips) "round trips of the rows"
#eval expect (fillReads ["object o { type T = Any }", "val program: o.type = o"] &&
  fillReads ["def f(x: Any)(y: x.type): x.type = y", "val program = A"] &&
  fillReads ["val program = (new Object { val a: Any => Any = (u: Any) => u }: { val a: Any => Any })"]) "fills"

-- The risk of the stage: d3's ProtoSelf, whose term names `σ.core.types.ℓself` and whose printed fill does not
/-- The text of d3's ProtoSelf, whose term holds `σ.core.types.ℓself` as the argument of `g`. -/
def protoSelf : List String := ["object core {", "  object types {", "    type A = { val v: Any }",
  "    val f: Any => Any = (u: Any) => u", "  }", "  val m: core.types.type = core.types", "}",
  "val program = {", "  val g = (x: core.types.type) => (y: x.A) => (y: core.m.A)", "  val h = g(core.types)",
  "  core.m.f(h)", "}"]
mutual
/-- Whether `s` occurs in a surface term. -/
def occurs (s : STm) (e : STm) : Bool :=
  decide (e = s) || match e with
  | .var _ => false
  | .lam _ _ t => occurs s t
  | .obj _ _ d => occursD s d
  | .app t u => occurs s t || occurs s u
  | .proj t _ => occurs s t
  | .«let» _ _ t u => occurs s t || occurs s u
  | .asc t _ => occurs s t
  | .alias _ _ u => occurs s u
  | .bind _ _ t u => occurs s t || occurs s u
termination_by structural e
/-- Whether `s` occurs in the definitions of a template. -/
def occursD (s : STm) (d : SDefs) : Bool :=
  match d with
  | .nil => false
  | .typ ds _ _ => occursD s ds
  | .trm ds _ _ t => occursD s ds || occurs s t
termination_by structural d
end
#eval expect ((term protoSelf).map (occurs (ts "σ" ["core", "types"])) == some true &&
  ascii (textOf protoSelf) && textOf protoSelf == "ok : Any" && fillReads protoSelf && trips protoSelf) "ProtoSelf"
-- an inferred `this` result widens to the object's self type, whose `ℓself` declaration the text drops
#eval expect (textOf ["object core { type T = Any; def me(u: Any) = this }", "val program = core.me(core)"] ==
  "ok : { type T = Any }") "a widened self type prints without ℓself"
#eval expect (tyText [("ℓself", .trm 0)] (.all .top (.sngl (.sel (.var .here) (.trm 0)))) == "(x0: Any) => x0.type")
  "a path ending in ℓself prints without it"

-- The printers' refusals
/-- The reason a term has no Scala form, or `none`. -/
def gapOf (e : STm) : Option String :=
  match toScala e with
  | .error w => some w
  | .ok _ => none
#eval expect (gapOf (.obj "x" none (sd "x")) == some gapUntypedLiteral) "a bare literal"
#eval expect (gapOf (.«let» "ℓ" none (.obj "z" (some .top) (sd "z")) (.asc (.var "ℓ") .top)) == some gapSelfType)
  "a written self type"
#eval expect (gapOf (.lam "x" (some .top) (.«let» "y" (some .top) (.var "x") (.var "x"))) == some gapLetType)
  "a typed let with another body"
#eval expect (gapOf (.«let» "ℓ" none (.obj "z" none .nil) (.asc (.var "ℓ") .top)) == some gapSelfField)
  "a literal without ℓself"

/-! ## A program for the `// same as:` link of the fixture -/

/-- `λ(x : ⊤). x`, the program of the fixture file `pos/SameId.scala`. -/
def idSrc : STm := pdt% λ(x : ⊤). x

#eval expect (term ["val program = (x: Any) => x"] == some idSrc) "idSrc"

end PDotFrontend.Scala.Tests
