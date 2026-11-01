import Coercions.Nominal.Frontend.Scala

/-!
# Checks of the pDOT Scala mapping

One check per row of the mapping (plan XI, "The Scala mapping, one case per construct"), on a text
read by `readNominal`, with the surface term it gives.  Then the label table and the module chains, the
outcome of each row, the member check R-M, the printers on every row, the risk program ProtoSelf,
and the refusals of the printers.  Every check is `#eval expect`.  The texts are string literals, never
files.  `String.toList` runs here in compiled code only, and no theorem mentions it.
-/

namespace NominalFrontend.Scala.Tests

open NominalFrontend NominalFrontend.Scala

/-- A test file: the header, a blank line, `object A {` on line 3, the lines indented by two, `}`. -/
def file (ls : List String) : String :=
  "import scala.reflect.Selectable.reflectiveSelectable\n\nobject A {\n" ++
    String.join (ls.map fun l => "  " ++ l ++ "\n") ++ "}\n"

/-- The surface term of a text, or `none` when it is refused. -/
def term (ls : List String) : Option STm := (readNominal (file ls).toList).toOption.map (·.1)

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

#eval expect ((readNominal (file ["object o { object p { type T = Any } }", "val program = o.p"]).toList).toOption.map
    (fun r => (r.2.1, r.2.2)) ==
  some ([("o", .trm 0), ("p", .trm 1), ("T", .typ 0), ("ℓself", .trm 2)], [[], [.trm 0], [.trm 0, .trm 1]]))
  "labels and modules"
#eval expect ((readNominal (file ["val program = (x: Any) => x"]).toList).toOption.map (fun r => r.2.2) == some [])
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
#eval expect (kindOf ["trait T { class C }", "val program = A"] == .outside) "outside, by the reader"
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
  match readNominal (file ls).toList with
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
    | .ok F => ascii (String.ofList (ScalaRead.print F)) && (readNominal (ScalaRead.print F)).toOption.isSome
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
  | .inst _ _ _ d => occursD s d
termination_by structural e
/-- Whether `s` occurs in the definitions of a template. -/
def occursD (s : STm) (d : SDefs) : Bool :=
  match d with
  | .nil => false
  | .typ ds _ _ => occursD s ds
  | .trm ds _ _ t => occursD s ds || occurs s t
  | .cls ds _ _ => occursD s ds
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

/-! ## Classes and traits (plan XII, stage N6)

One check per equation of "The mapping, one equation per construct", on a text read by `readNominal`.
Then the five class-shape checks and the five OV checks, each rejected with scalac's text beside an
accepted neighbour, the worked example against `Run_src`, the member check R-M in a class, the tags,
and the printers on a class file. -/

/-- The binder of a class body or an instance in the stem. -/
def b1 : String := "ν'"
/-- The binder of a class body in an object of the stem. -/
def b2 : String := "ν''"

/-- The labels of definitions, in order. -/
def labelsOfDefs : SDefs → List String
  | .nil => []
  | .typ ds A _ | .cls ds A _ => labelsOfDefs ds ++ [A]
  | .trm ds a _ _ => labelsOfDefs ds ++ [a]

/-- The definitions of the stem of a term. -/
def stemOf : STm → Option SDefs
  | .«let» "σ" none (.obj "σ" none d) _ => some d
  | _ => none

/-- The definition `a` of a list of definitions, its written type and its right side. -/
def defOf (a : String) : SDefs → Option (Option SType × STm)
  | .nil => none
  | .typ ds _ _ | .cls ds _ _ => defOf a ds
  | .trm ds b T t => if decide (a = b) then some (T, t) else defOf a ds

/-- The body of the class `C` of a list of definitions. -/
def clsOf (C : String) : SDefs → Option SType
  | .nil => none
  | .typ ds _ _ | .trm ds _ _ _ => clsOf C ds
  | .cls ds D T => if decide (C = D) then some T else clsOf C ds

/-- The tagged literal at the end of a chain of lambdas. -/
def instIn : STm → Option STm
  | .lam _ _ t => instIn t
  | .inst x p C d => some (.inst x p C d)
  | _ => none

/-- The stem of a text. -/
def stemT (ls : List String) : Option SDefs := (term ls).bind stemOf

/-- The definition `a` of the stem of a text. -/
def defT (ls : List String) (a : String) : Option (Option SType × STm) := (stemT ls).bind (defOf a)

/-- The instance of the constructor `new$K` of the stem of a text. -/
def instT (ls : List String) (K : String) : Option STm := (defT ls ("new$" ++ K)).bind fun (_, t) => instIn t

/-- The refusal of a check of the classes. -/
def checkedOf (ls : List String) : Option ScalaSyntax.Err :=
  match outcome (file ls).toList with
  | .checked _ e => some e
  | _ => none

/-- `{ℓself : z.type}`. -/
def selfDec (z : String) : SType := .fld "ℓself" (.sngl (.var z))

/-! ### The equations of the mapping -/

-- ⟦trait K { ms }⟧ᶻ = class K = Body(K), modfuns(K): own declarations, `⋀ᴸ`, `⋀ᴿ [] = ⊤`, `modfun`
#eval expect (stemT ["trait T { type L; val v: L; def get(y: Any): L = v }", "val program = A"] ==
  some (.trm (.cls (sd "σ") "T" (.and (.mu b1 (.and (.and (.and (selfDec b1) (.typ "L" .bot .top))
      (.fld "v" (.sel (.var b1) "L"))) (.fld "get" (.all "y" .top (.sel (.var b1) "L"))))) .top))
    "get$T" (some (.all b1 (.sel (.var "σ") "T") (.all "y" .top (.sel (.var b1) "L"))))
    (.lam b1 (some (.sel (.var "σ") "T")) (.lam "y" (some .top) (tp b1 ["v"]))))) "trait, Body, own, modfun"
-- ⟦class K⟧ᶻ with no parameter: Ctor-Nil, `Inst(K)` with `ℓself` only, `⟦new K⟧ = let ·n = σ.new$K σ in ·n`
#eval expect (term ["class C", "val program = new C"] ==
  some (stem (.trm (.cls (sd "σ") "C" (.and (.mu b1 (selfDec b1)) .top)) "new$C"
      (some (.all "·c" .top (.sel (.var "σ") "C"))) (.lam "·c" (some .top) (.inst b1 (.var "σ") "C" (sd b1))))
    (.«let» "·n" none (.app (tp "σ" ["new$C"]) (.var "σ")) (.var "·n")))) "class, Ctor-Nil, new"
-- ⟦abstract class K(ps) extends P⟧ᶻ: `vdec`, parents, no constructor (Ctor-Abs)
#eval expect (stemT ["trait T", "abstract class B(val v: Any) extends T", "val program = A"] ==
  some (.cls (.cls (sd "σ") "T" (.and (.mu b1 (selfDec b1)) .top)) "B"
    (.and (.mu b1 (.and (selfDec b1) (.fld "v" .top))) (.and (.sel (.var "σ") "T") .top)))) "abstract class, vdec"
-- `witness(K, val a : T = q)`, `inst(x)`, `inst(a)` with the parameter replaced by its argument
#eval expect (defT ["class C(val w: Any) { val v: Any = w }", "val program = A"] "v$C" ==
  some (some (.all b1 (.sel (.var "σ") "C") .top), .lam b1 (some (.sel (.var "σ") "C")) (tp b1 ["w"]))) "val witness"
#eval expect (instT ["class C(val w: Any) { val v: Any = w }", "val program = A"] "C" ==
  some (.inst b1 (.var "σ") "C" (.trm (.trm (sd b1) "w" none (.var "w")) "v" none (.var "w")))) "inst(x), inst(a)"
-- `hid(x : S)`, `⟦x⟧ = this.ℓx$K`, `inst(ℓx)`, the forwarder `inst(f)` (D-9, D-11)
#eval expect (stemT ["class C(x: Any) { def get(u: Any): Any = x }", "val program = A"] ==
  some (.trm (.trm (.cls (sd "σ") "C" (.and (.mu b1 (.and (.and (selfDec b1) (.fld "ℓx$C" .top))
      (.fld "get" (.all "u" .top .top)))) .top))
    "get$C" (some (.all b1 (.sel (.var "σ") "C") (.all "u" .top .top)))
      (.lam b1 (some (.sel (.var "σ") "C")) (.lam "u" (some .top) (tp b1 ["ℓx$C"]))))
    "new$C" (some (.all "x" .top (.sel (.var "σ") "C")))
      (.lam "x" (some .top) (.inst b1 (.var "σ") "C" (.trm (.trm (sd b1) "ℓx$C" none (.var "x")) "get"
        (some (.all "u" .top .top)) (.lam "u" (some .top)
          (.«let» "·g" none (.app (tp "σ" ["get$C"]) (.var b1)) (.app (.var "·g") (.var "u"))))))))) "hid, plain parameter"
-- `arg(K, D, y)`: an inherited `val` parameter at the argument of the parent
#eval expect (instT ["class C(val v: Any)", "class D(val w: Any) extends C(w)", "val program = A"] "D" ==
  some (.inst b1 (.var "σ") "D" (.trm (.trm (sd b1) "w" none (.var "w")) "v" none (.var "w")))) "arg through a parent"
#eval expect (instT ["class C1(val v1: Any)", "class C2(val v2: Any) extends C1(v2)", "class C3(val v3: Any) extends C2(v3)",
    "val program = A"] "C3" ==
  some (.inst b1 (.var "σ") "C3" (.trm (.trm (.trm (sd b1) "v3" none (.var "v3")) "v2" none (.var "v3")) "v1" none
    (.var "v3")))) "arg through two parents"
-- `inst(f)` from an ancestor: the forwarder calls the ancestor's module function at the instance
#eval expect ((instT ["trait T { def get(y: Any): Any = y }", "class C extends T", "val program = A"] "C") ==
  some (.inst b1 (.var "σ") "C" (.trm (sd b1) "get" (some (.all "y" .top .top)) (.lam "y" (some .top)
    (.«let» "·g" none (.app (tp "σ" ["get$T"]) (.var b1)) (.app (.var "·g") (.var "y"))))))) "inherited forwarder"
-- `inst(A)`: the first alias in `L(K)`, else the meet of the upper bounds
#eval expect ((instT ["trait L { type T = Any }", "trait R { type T }", "class C extends L with R", "val program = A"] "C") ==
  some (.inst b1 (.var "σ") "C" (.typ (sd b1) "T" .top))) "inst(A), alias"
#eval expect ((instT ["trait A0", "trait B0", "trait L { type X <: A0 }", "trait R { type X <: B0 }", "class C extends L with R",
    "val program = A"] "C") ==
  some (.inst b1 (.var "σ") "C" (.typ (sd b1) "X" (.and (.sel (.var "σ") "B0") (.sel (.var "σ") "A0"))))) "inst(A), meet"
-- `⟦this⟧ = this.ℓself` in a body
#eval expect (defT ["class C { def me(u: Any): C = this }", "val program = A"] "me$C" ==
  some (some (.all b1 (.sel (.var "σ") "C") (.all "u" .top (.sel (.var "σ") "C"))),
    .lam b1 (some (.sel (.var "σ") "C")) (.lam "u" (some .top) (ts b1 [])))) "this"
-- `⟦C⟧ = z'.C`, `⟦new p.K(ē)⟧ = let ·n = ⟦p⟧.new$K ē in ·n`
#eval expect ((term ["object m { class C(val v: Any) }", "val program = (c: m.C) => new m.C(c)"]).map (fun e =>
    (match e with
    | .«let» _ _ _ b => b
    | e => e)) ==
  some (.lam "c" (some (.sel (sp "σ" ["m"]) "C")) (.«let» "·n" none (.app (tp "σ" ["m", "new$C"]) (.var "c")) (.var "·n"))))
  "class type, new with a prefix"
-- a class in an object: its module functions in the object, its forwarders by the object's binder
#eval expect (((term ["object m { trait T { def f(u: Any): Any = u }; class C extends T }", "val program = A"]).bind (fun e =>
    (stemOf e).bind (defOf "m"))).map (fun (_, t) => (match t with
      | .obj _ _ d => (labelsOfDefs d, (defOf "new$C" d).bind fun (_, t) => instIn t)
      | _ => ([], none))) ==
  some (["ℓself", "T", "f$T", "C", "new$C"], some (.inst b2 (.var b1) "C" (.trm (sd b2) "f" (some (.all "u" .top .top))
    (.lam "u" (some .top) (.«let» "·g" none (.app (tp b1 ["f$T"]) (.var b2)) (.app (.var "·g") (.var "u")))))))) "class in an object"
-- an ancestor in another object: its module function by its path from the stem
#eval expect (((term ["object a { trait T { def f(u: Any): Any = u } }", "object b { class C extends a.T }", "val program = A"]).bind
    (fun e => (stemOf e).bind (defOf "b"))).bind (fun (_, t) => (match t with
      | .obj _ _ d => (defOf "new$C" d).bind fun (_, t) => instIn t
      | _ => none)) ==
  some (.inst b2 (.var b1) "C" (.trm (sd b2) "f" (some (.all "u" .top .top))
    (.lam "u" (some .top) (.«let» "·g" none (.app (tp "σ" ["a", "f$T"]) (.var b2)) (.app (.var "·g") (.var "u"))))))) "ancestor in another object"
-- `ovm` and `ovp` written for different types, left out for equal ones (D-13)
#eval expect ((stemT ["class K", "trait L { def m(u: Any): K = new K }", "trait R { def m(u: Any): Any }", "class C extends L with R",
    "val program = A"]).map labelsOfDefs ==
  some ["ℓself", "K", "new$K", "L", "m$L", "R", "C", "ov$C$m$R", "new$C"]) "ovm written, ovp left out"
#eval expect ((stemT ["trait B { def m(u: Any): Any }", "trait L extends B { override def m(u: Any): Any = u }",
    "trait R extends B { override def m(u: Any): Any = u }", "class C extends L with R", "val program = A"]).map labelsOfDefs ==
  some ["ℓself", "B", "L", "m$L", "R", "m$R", "C", "new$C"]) "witnesses of equal types left out"
#eval expect (defT ["trait T { type L <: Any }", "trait U extends T { type L <: { type V } }", "val program = A"] "ovu$U$L$T" ==
  none) "ovu left out at an upper bound ⊤"
#eval expect ((defT ["trait T { type L <: { type V } }", "class D extends T { type L = Any }", "val program = A"] "ovu$D$L$T").map
    (·.1) == some (some (.all b1 (.sel (.var "σ") "D") (.all "·w" .top (.typ "V" .bot .top))))) "ovu written"
#eval expect ((defT ["trait T { val a: Any }", "class C(val a: T) extends T", "val program = A"] "ovv$C$a$T") == none &&
  (defT ["trait T { val a: T }", "class C(val a: Any) extends T", "val program = A"] "ovv$C$a$T").isSome) "ovv"
-- ovc(K, A, D, E): the inherited bounds of `A` in `D` and `E`, pairwise (refutation G-1, probes Q26, V1)
/-- Two traits that bound the type member `X` of the trait `K` from below by `u.type` and from above by `Nothing`. -/
def inhText (hi : String) : List String :=
  ["object u { type V = Any }", "trait L { type X >: u.type }", "trait R { type X" ++ hi ++ " }", "trait K extends L with R",
    "val program: Any = u"]
#eval expect ((defT (inhText " <: Nothing") "ovc$K$X$L$R").map (·.1) == some (some (.all b1 (.sel (.var "σ") "K")
    (.all "·w" (.sngl (.sel (.var "σ") "u")) .bot))) && defT (inhText " <: Nothing") "ovc$K$X$R$L" == none) "ovc"
#eval expect (kindOf (inhText " <: Nothing") == .rejected && kindOf (inhText "") == .ok) "ovc, rejected and its neighbour"
-- the tags of the term sit on constructors only (`ofScala_tags`)
#eval expect ((term ["trait T { def get(y: Any): Any = y }", "class C(val w: Any) extends T", "val program = new C(A)"]).map tmTags ==
  some true) "tags"
#eval expect (tmTags (.inst "i" (.var "σ") "C" .nil) == false && tmTags (stem (.trm (sd "σ") "mk" none
  (.lam "u" none (.inst "i" (.var "σ") "C" .nil))) (.var "σ")) == false) "tags, refused shapes"

/-! ### The checks -/

-- S30, the arity of `new` (scalac E171), and an argument to a class without parameters
#eval expect (checkedOf ["class C(val x: Any)", "val program: Any = new C"] ==
  some ⟨⟨5, 22⟩, "missing argument for parameter x of constructor C in class C (scalac E171)"⟩) "S30"
#eval expect (kindOf ["class C(val x: Any)", "val program: Any = new C(A)"] == .ok) "S30, neighbour"
#eval expect (checkedOf ["class C", "val program: Any = new C(A)"] ==
  some ⟨⟨5, 28⟩, "too many arguments for constructor C in class C"⟩) "S30, no parameter"
#eval expect (errOf ["class C(val x: Any)", "val program: Any = new C(A, A)"] == some ⟨⟨5, 26⟩, msgTupled⟩) "tupled arguments"
#eval expect (checkedOf ["class C(val x: Any, val y: Any)", "val program: Any = new C(A, A, A)"] ==
  some ⟨⟨5, 34⟩, "too many arguments for constructor C in class C"⟩) "S30, two parameters"
-- S31, the arity of the first parent (scalac E171)
#eval expect (checkedOf ["class D(val x: Any)", "class K extends D", "val program: Any = new K"] ==
  some ⟨⟨5, 19⟩, "missing argument for parameter x of constructor D in class D (scalac E171)"⟩) "S31"
#eval expect (kindOf ["class D(val x: Any)", "class K extends D(A)", "val program: Any = new K"] == .ok) "S31, neighbour"
#eval expect (checkedOf ["class D(val x: Any, val y: Any)", "class K extends D(A, A, A)", "val program: Any = new K"] ==
  some ⟨⟨5, 27⟩, "too many arguments for constructor D in class D"⟩) "S31, two parameters"
#eval expect (checkedOf ["class B(val x: Any)", "trait T extends B", "class K extends T", "val program: Any = new K"] ==
  some ⟨⟨6, 9⟩, "missing argument for parameter x of constructor B in class B (scalac E171)"⟩) "S31, through a trait"
#eval expect (kindOf ["class D(val x: Any)", "trait T extends D", "class K(val y: Any) extends D(y) with T",
  "val program: Any = new K(A)"] == .ok) "S31, not at a trait"
#eval expect (errOf ["class D(val x: Any)", "class K extends D((u: Any) => u)", "val program: Any = new K"] ==
  some ⟨⟨5, 19⟩, msgParentArg⟩) "a parent argument that is no path"
-- S32, arguments to a trait parent
#eval expect (checkedOf ["trait T", "class K extends T(A)", "val program: Any = new K"] ==
  some ⟨⟨5, 21⟩, "too many arguments for constructor T in trait T"⟩) "S32"
#eval expect (kindOf ["trait T", "class K extends T", "val program: Any = new K"] == .ok) "S32, neighbour"
-- S33, a class after `with` (scalac E104)
#eval expect (checkedOf ["class A0", "class B0", "class K extends A0 with B0", "val program: Any = new K"] ==
  some ⟨⟨6, 27⟩, "class B0 is not a trait (scalac E104)"⟩) "S33"
#eval expect (kindOf ["class A0", "trait B0", "class K extends A0 with B0", "val program: Any = new K"] == .ok) "S33, neighbour"
-- S34, a trait after `with` whose superclass the class's superclass does not derive from
#eval expect (checkedOf ["class A0", "class B0", "trait T extends B0", "class K extends A0 with T", "val program: Any = new K"] ==
  some ⟨⟨7, 27⟩, "illegal trait inheritance: superclass A0 does not derive from trait T's superclass B0"⟩) "S34"
#eval expect (kindOf ["class B0", "class A0 extends B0", "trait T extends B0", "class K extends A0 with T",
  "val program: Any = new K"] == .ok) "S34, neighbour"
#eval expect (kindOf ["class A0", "class B0 extends A0", "trait T1 extends B0", "trait T2 extends A0", "class K extends T2 with T1",
  "val program: Any = new K"] == .ok) "S34, the superclass through the parents"
-- OV-Need (scalac E164)
#eval expect (checkedOf ["class P { def m(u: Any): Any = u }", "class Q extends P { def m(u: Any): Any = u }", "val program = new Q"] ==
  some ⟨⟨5, 27⟩, "error overriding method m in class P: method m needs `override` modifier (scalac E164)"⟩) "OV-Need"
#eval expect (kindOf ["class P { def m(u: Any): Any = u }", "class Q extends P { override def m(u: Any): Any = u }",
  "val program = new Q"] == .ok) "OV-Need, neighbour"
#eval expect (kindOf ["class P { def m(u: Any): Any = u }", "abstract class Q extends P { def m(u: Any): Any }",
  "val program = A"] == .ok) "OV-Need, not at an abstract member"
-- OV-Nothing (scalac E037)
#eval expect (checkedOf ["class P { override def m(u: Any): Any = u }", "val program = new P"] ==
  some ⟨⟨4, 26⟩, "method m overrides nothing (scalac E037)"⟩) "OV-Nothing"
#eval expect (kindOf ["class P { def m(u: Any): Any = u }", "val program = new P"] == .ok) "OV-Nothing, neighbour"
-- OV-Accidental (Martres p.75, scalac E164)
#eval expect (checkedOf ["trait L { def m(u: Any): Any = u }", "trait R { def m(u: Any): Any = u }", "class C extends L with R",
  "val program = new C"] ==
  some ⟨⟨6, 9⟩, "class C inherits conflicting members: m in trait L and m in trait R (scalac E164)"⟩) "OV-Accidental"
#eval expect (checkedOf ["trait Base { def foo(u: Any): Any }", "trait Sub1 extends Base { def foo(u: Any): Any = u }",
  "trait Unrelated { def foo(u: Any): Any }", "trait Sub2 extends Unrelated { override def foo(u: Any): Any = A }",
  "class C extends Sub1 with Sub2", "val program = new C"] ==
  some ⟨⟨8, 9⟩, "error overriding method foo in trait Sub1: method foo in trait Sub2 cannot override a concrete member " ++
    "without a third member that's overridden by both (scalac E164)"⟩) "OV-Accidental, thesis"
#eval expect (kindOf ["trait B { def m(u: Any): Any }", "trait L extends B { override def m(u: Any): Any = u }",
  "trait R extends B { override def m(u: Any): Any = u }", "class C extends L with R", "val program = new C"] == .ok)
  "OV-Accidental, neighbour"
-- OV-Abstract
#eval expect (checkedOf ["trait T { def m(u: Any): Any }", "class C extends T", "val program = new C"] ==
  some ⟨⟨5, 9⟩, "class C needs to be abstract, since m in trait T is not defined"⟩) "OV-Abstract"
#eval expect (kindOf ["trait T { def m(u: Any): Any }", "abstract class C extends T", "val program = A"] == .ok)
  "OV-Abstract, neighbour"
-- OV-New (scalac E042)
#eval expect (checkedOf ["trait T { def m(u: Any): Any }", "val program = new T"] ==
  some ⟨⟨5, 21⟩, "T is a trait; it cannot be instantiated (scalac E042)"⟩) "OV-New, trait"
#eval expect (checkedOf ["abstract class C", "val program = new C"] ==
  some ⟨⟨5, 21⟩, "C is abstract; it cannot be instantiated (scalac E042)"⟩) "OV-New, abstract class"
#eval expect (kindOf ["trait T { def m(u: Any): Any }", "class C extends T { def m(u: Any): Any = u }", "val program = new C"] ==
  .ok) "OV-New, neighbour"

/-! ### The worked example, the member check, the printers -/

/-- The worked example of plan XII ("A worked example"). -/
def workedText : List String := ["object u { type A = Any }", "trait T {", "  type L", "  val v: L",
  "  def get(y: Any): L = v", "}", "class C(val w: Any) extends T {", "  type L = Any", "  val v: L = w", "}",
  "val program: T = new C(u)"]

-- It compiles at `Body(T)`, as `Run_src` (`Examples.lean:407`), whose type prints the same
#eval expect (textOf workedText == "ok : { type L; val v: this.L; val get: Any => this.L } & Any") "worked example"
-- the stem holds `Run_src`'s definitions in `Run_src`'s order, and the instance `Run_src`'s fields
#eval expect ((stemT workedText).map labelsOfDefs == some ["ℓself", "u", "T", "get$T", "C", "v$C", "new$C"] &&
  (instT workedText "C").map (fun t => match t with
    | .inst _ _ _ d => labelsOfDefs d
    | _ => []) == some ["ℓself", "w", "L", "v", "get"]) "worked example, the definitions of Run_src"
-- R-M in a class body (scalac E008)
#eval expect (errOf ["object o { type T = Any }", "class C(val p: o.type) { def get(u: p.B): Any = u }", "val program = new C(o)"] ==
  some ⟨⟨5, 41⟩, "type B is not a member of the type of p (scalac E008)"⟩) "R-M in a class"
#eval expect (kindOf ["object o { type T = Any }", "class C(val p: o.type) { def get(u: p.T): Any = u }", "val program = new C(o)"] ==
  .ok) "R-M in a class, neighbour"
-- the printers: a class program has no Scala form, its fill neither, and its round trip is the gap
#eval expect ((term workedText).map (fun e => match toScala e with
    | .error w => decide (w = gapClass)
    | .ok _ => false) == some true) "toScala of a class program"
#eval expect (match outcome (file workedText).toList with
  | .ok Λ r => match fillToScala Λ r.1 with
    | .error w => decide (w = gapClass)
    | .ok _ => false
  | _ => false) "fillToScala of a class program"
#eval expect (match readNominal (file workedText).toList with
  | .ok (e, Λ, _) => match roundTrip Λ e with
    | .gap w => decide (w = gapClass)
    | _ => false
  | .error _ => false) "roundTrip of a class program"
#eval expect (gapReasons.length == 11 && gapReasons.contains gapClass) "gap reasons"

/-! ## A program for the `// same as:` link of the fixture -/

/-- `λ(x : ⊤). x`, the program of the fixture file `pos/SameId.scala`. -/
def idSrc : STm := pdc% λ(x : ⊤). x

#eval expect (term ["val program = (x: Any) => x"] == some idSrc) "idSrc"

end NominalFrontend.Scala.Tests
