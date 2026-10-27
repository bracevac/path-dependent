import Coercions.PDot.Frontend.Notation
import Coercions.PDot.Frontend.Resolve
import Coercions.PDot.Source

/-!
# The programs of `PDot.Source` in the notation

Each program of `PDot/Source/Programs.lean` and `PDot/Source/Examples.lean` is
written here in `pdt%`, with every self type and every domain written.  Each
comes with a fixed label table, equal to the `abbrev`s of its source file.

Two theorems follow each program, both by `decide +kernel`.  `Ek_side` says the
program meets the four side conditions of `Surface.lean` under its table.
`Ek_resolves` says resolution gives back the hand term of the source, once the
tags and the `let` types are erased.

The binder names are those of the comments of the sources.  Self types nest to
the left as the hand terms do, so an intersection of three declarations is
written `(D₁ ∧ D₂) ∧ D₃`.  The label `Type` is written `«Type»`.

The last section resolves the contexts of the path examples E9 to E11 and one
path of E9.  They match `e9_G`, `e10_G` and `e11_G` of `PDot/Source/Examples.lean`.

Nothing here is part of the metatheory.
-/

namespace PDotFrontend.Sources

open PDotFrontend

/-! ## E1: pDOT's Fig. 1 (`Programs.lean:77-91`) -/

/-- The labels of E1 (`Programs.lean:94-108`). -/
def Λ1 : LabelTable := [("core", .trm 0), ("types", .trm 1), ("symbols", .trm 2), ("symb", .trm 3),
  ("tpe", .trm 4), ("Type", .typ 0), ("TypeRef", .typ 1), ("Symbol", .typ 2)]

/-- E1 in the notation. -/
def E1_src : STm := pdt%
  let dotty = ν(d : {core : μ(c. {types : μ(t. {«Type» : ⊤..⊤}
                    ∧ {TypeRef : t.«Type» ∧ {symb : c.symbols.Symbol} .. t.«Type» ∧ {symb : c.symbols.Symbol}})}
              ∧ {symbols : μ(s. {Symbol : {tpe : c.types.«Type»} .. {tpe : c.types.«Type»}})})}) {
    core = ν(c : {types : μ(t. {«Type» : ⊤..⊤}
                    ∧ {TypeRef : t.«Type» ∧ {symb : c.symbols.Symbol} .. t.«Type» ∧ {symb : c.symbols.Symbol}})}
              ∧ {symbols : μ(s. {Symbol : {tpe : c.types.«Type»} .. {tpe : c.types.«Type»}})}) {
      types = ν(t : {«Type» : ⊤..⊤}
                    ∧ {TypeRef : t.«Type» ∧ {symb : c.symbols.Symbol} .. t.«Type» ∧ {symb : c.symbols.Symbol}}) {
        type «Type» = ⊤, type TypeRef = t.«Type» ∧ {symb : c.symbols.Symbol}},
      symbols = ν(s : {Symbol : {tpe : c.types.«Type»} .. {tpe : c.types.«Type»}}) {
        type Symbol = {tpe : c.types.«Type»}}}} in dotty

theorem E1_side : E1_src.Scoped [] = true ∧ E1_src.LabelsIn Λ1 = true ∧
    E1_src.FieldsOk = true ∧ E1_src.PathOperands = true := by decide +kernel

theorem E1_resolves : (resolve Λ1 E1_src).map ATm.erase = some PDot.Source.E1_prog := by
  decide +kernel

/-! ## E2: the length-two path (`Programs.lean:153-160`) -/

/-- The labels of E2 (`Programs.lean:166-170`). -/
def Λ2 : LabelTable := [("c", .trm 0), ("A", .typ 0), ("B", .typ 1)]

/-- E2 in the notation. -/
def E2_src : STm := pdt%
  let x = ν(z : {c : μ(w. {A : z.B..z.B})} ∧ {B : z.c.A..z.c.A}) {
    c = ν(w : {A : z.B..z.B}) {type A = z.B}, type B = z.c.A} in x

theorem E2_side : E2_src.Scoped [] = true ∧ E2_src.LabelsIn Λ2 = true ∧
    E2_src.FieldsOk = true ∧ E2_src.PathOperands = true := by decide +kernel

theorem E2_resolves : (resolve Λ2 E2_src).map ATm.erase = some PDot.Source.E2_prog := by
  decide +kernel

/-! ## E3: `CompilerExample.v` (`Programs.lean:195-212`) -/

/-- The labels of E3 (`Programs.lean:223-245`). -/
def Λ3 : LabelTable := [("DottyCore", .typ 0), ("Tpe", .typ 1), ("Symbol", .typ 2), ("dottyCore", .trm 0),
  ("types", .trm 1), ("typeRef", .trm 2), ("symbols", .trm 3), ("symbol", .trm 4), ("symb", .trm 5),
  ("tpe", .trm 6), ("denotation", .trm 7), ("srcPos", .trm 8)]

/-- E3 in the notation. -/
def E3_src : STm := pdt%
  ν(r : {DottyCore : μ(c. {types : μ(t. {Tpe : ⊥..⊤} ∧ {typeRef : ∀(s : c.symbols.Symbol) t.Tpe ∧ {symb : c.symbols.Symbol}})}
                         ∧ {symbols : μ(y. {Symbol : ⊥..⊤} ∧ {symbol : ∀(u : c.types.Tpe) y.Symbol ∧ {tpe : c.types.Tpe}})})
                 .. μ(c. {types : μ(t. {Tpe : ⊥..⊤} ∧ {typeRef : ∀(s : c.symbols.Symbol) t.Tpe ∧ {symb : c.symbols.Symbol}})}
                         ∧ {symbols : μ(y. {Symbol : ⊥..⊤} ∧ {symbol : ∀(u : c.types.Tpe) y.Symbol ∧ {tpe : c.types.Tpe}})})}
        ∧ {dottyCore : ∀(e : ⊤) r.DottyCore}) {
    type DottyCore = μ(c. {types : μ(t. {Tpe : ⊥..⊤} ∧ {typeRef : ∀(s : c.symbols.Symbol) t.Tpe ∧ {symb : c.symbols.Symbol}})}
                         ∧ {symbols : μ(y. {Symbol : ⊥..⊤} ∧ {symbol : ∀(u : c.types.Tpe) y.Symbol ∧ {tpe : c.types.Tpe}})}),
    dottyCore = λ(e : ⊤). let k = ν(c :
        {types : μ(t. {Tpe : μ(o. {denotation : ∀(z : ⊤) ⊤})..μ(o. {denotation : ∀(z : ⊤) ⊤})}
                      ∧ {typeRef : ∀(s : c.symbols.Symbol) t.Tpe ∧ {symb : c.symbols.Symbol}})}
        ∧ {symbols : μ(y. {Symbol : μ(o. {srcPos : ∀(z : ⊤) ⊤})..μ(o. {srcPos : ∀(z : ⊤) ⊤})}
                      ∧ {symbol : ∀(u : c.types.Tpe) y.Symbol ∧ {tpe : c.types.Tpe}})}) {
      types = ν(t : {Tpe : μ(o. {denotation : ∀(z : ⊤) ⊤})..μ(o. {denotation : ∀(z : ⊤) ⊤})}
                      ∧ {typeRef : ∀(s : c.symbols.Symbol) t.Tpe ∧ {symb : c.symbols.Symbol}}) {
        type Tpe = μ(o. {denotation : ∀(z : ⊤) ⊤}),
        typeRef = λ(s : c.symbols.Symbol).
          let o = ν(o : {symb : s.type} ∧ {denotation : ∀(z : ⊤) ⊤}) {symb = s, denotation = λ(z : ⊤). z} in o},
      symbols = ν(y : {Symbol : μ(o. {srcPos : ∀(z : ⊤) ⊤})..μ(o. {srcPos : ∀(z : ⊤) ⊤})}
                      ∧ {symbol : ∀(u : c.types.Tpe) y.Symbol ∧ {tpe : c.types.Tpe}}) {
        type Symbol = μ(o. {srcPos : ∀(z : ⊤) ⊤}),
        symbol = λ(u : c.types.Tpe).
          let o = ν(o : {tpe : u.type} ∧ {srcPos : ∀(z : ⊤) ⊤}) {tpe = u, srcPos = λ(z : ⊤). z} in o}} in k}

theorem E3_side : E3_src.Scoped [] = true ∧ E3_src.LabelsIn Λ3 = true ∧
    E3_src.FieldsOk = true ∧ E3_src.PathOperands = true := by decide +kernel

theorem E3_resolves : (resolve Λ3 E3_src).map ATm.erase = some PDot.Source.compiler_t := by
  decide +kernel

/-! ## E4: `ListExample.v` (`Programs.lean:448-462`) -/

/-- The labels of E4 (`Programs.lean:471-481`). -/
def Λ4 : LabelTable := [("A", .typ 0), ("List", .typ 1), ("Nil", .trm 0), ("Cons", .trm 1),
  ("head", .trm 2), ("tail", .trm 3)]

/-- E4 in the notation. -/
def E4_src : STm := pdt%
  ν(sci : ({List : μ(l. ({A : ⊥..⊤} ∧ {head : ∀(u : ⊤) l.A}) ∧ {tail : ∀(u : ⊤) sci.List ∧ {A : ⊥..l.A}})
                 .. μ(l. ({A : ⊥..⊤} ∧ {head : ∀(u : ⊤) l.A}) ∧ {tail : ∀(u : ⊤) sci.List ∧ {A : ⊥..l.A}})}
           ∧ {Nil : ∀(x : {A : ⊥..⊤}) sci.List ∧ {A : ⊥..⊥}})
          ∧ {Cons : ∀(x : {A : ⊥..⊤}) ∀(y : x.A) ∀(ys : sci.List ∧ {A : ⊥..x.A}) sci.List ∧ {A : ⊥..x.A}}) {
    type List = μ(l. ({A : ⊥..⊤} ∧ {head : ∀(u : ⊤) l.A}) ∧ {tail : ∀(u : ⊤) sci.List ∧ {A : ⊥..l.A}}),
    Nil = λ(x : {A : ⊥..⊤}).
      let r = ν(r : ({A : ⊥..⊥} ∧ {head : ∀(u : ⊤) r.A}) ∧ {tail : ∀(u : ⊤) sci.List ∧ {A : ⊥..r.A}}) {
        type A = ⊥, head = λ(u : ⊤). r.head u, tail = λ(u : ⊤). r.tail u} in r,
    Cons = λ(x : {A : ⊥..⊤}). λ(y : x.A). λ(ys : sci.List ∧ {A : ⊥..x.A}).
      let r = ν(r : ({A : x.A..x.A} ∧ {head : ∀(u : ⊤) r.A}) ∧ {tail : ∀(u : ⊤) sci.List ∧ {A : ⊥..x.A}}) {
        type A = x.A, head = λ(u : ⊤). y, tail = λ(u : ⊤). ys} in r}

theorem E4_side : E4_src.Scoped [] = true ∧ E4_src.LabelsIn Λ4 = true ∧
    E4_src.FieldsOk = true ∧ E4_src.PathOperands = true := by decide +kernel

theorem E4_resolves : (resolve Λ4 E4_src).map ATm.erase = some PDot.Source.list_t := by
  decide +kernel

/-! ## E5: `SingletonTypeExample.v` (`Programs.lean:669-679`) -/

/-- The labels of E5 (`Programs.lean:688-696`). -/
def Λ5 : LabelTable := [("C", .typ 0), ("D", .typ 1), ("d", .trm 0), ("incr", .trm 1), ("decr", .trm 2)]

/-- E5 in the notation. -/
def E5_src : STm := pdt%
  let x = ν(x : ({C : μ(c. {incr : c.type})..μ(c. {incr : c.type})}
                 ∧ {D : μ(d. x.C ∧ {decr : d.type})..μ(d. x.C ∧ {decr : d.type})})
                ∧ {d : ∀(u : ⊤) x.D}) {
    type C = μ(c. {incr : c.type}), type D = μ(d. x.C ∧ {decr : d.type}),
    d = λ(u : ⊤). let o = ν(o : {incr : o.type} ∧ {decr : o.type}) {incr = o, decr = o} in o} in
  let z = x.d x in z.incr.decr

theorem E5_side : E5_src.Scoped [] = true ∧ E5_src.LabelsIn Λ5 = true ∧
    E5_src.FieldsOk = true ∧ E5_src.PathOperands = true := by decide +kernel

theorem E5_resolves : (resolve Λ5 E5_src).map ATm.erase = some PDot.Source.sngl_t := by
  decide +kernel

/-! ## E6: gDOT's Fig. 2 in pDOT form (`Programs.lean:809-827`) -/

/-- The labels of E6 (`Programs.lean:839-867`). -/
def Λ6 : LabelTable := [("Option", .typ 0), ("Type", .typ 1), ("TypeTop", .typ 2), ("TypeRef", .typ 3),
  ("Symbol", .typ 4), ("A", .typ 5), ("types", .trm 0), ("symbols", .trm 1), ("newTypeTop", .trm 2),
  ("newTypeRef", .trm 3), ("symb", .trm 4), ("newSymbol", .trm 5), ("tpe", .trm 6), ("id", .trm 7),
  ("n", .trm 8)]

/-- E6 in the notation. -/
def E6_src : STm := pdt%
  let options = ν(o : {Option : ⊤..⊤}) {type Option = ⊤} in
  let pcore = ν(p :
      {types : μ(t. ((({«Type» : ⊤..⊤} ∧ {TypeTop : t.«Type»..t.«Type»}) ∧ {newTypeTop : ∀(u : ⊤) t.TypeTop})
                     ∧ {TypeRef : t.«Type» ∧ {symb : p.symbols.Symbol} .. t.«Type» ∧ {symb : p.symbols.Symbol}})
                    ∧ {newTypeRef : ∀(s : p.symbols.Symbol) t.TypeRef})}
      ∧ {symbols : μ(y. {Symbol : {tpe : options.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}}
                           .. {tpe : options.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}}}
                       ∧ {newSymbol : ∀(u : options.Option ∧ {A : ⊥..p.types.«Type»}) ∀(i : {n : ⊤}) y.Symbol})}) {
    types = ν(t : ((({«Type» : ⊤..⊤} ∧ {TypeTop : t.«Type»..t.«Type»}) ∧ {newTypeTop : ∀(u : ⊤) t.TypeTop})
                     ∧ {TypeRef : t.«Type» ∧ {symb : p.symbols.Symbol} .. t.«Type» ∧ {symb : p.symbols.Symbol}})
                    ∧ {newTypeRef : ∀(s : p.symbols.Symbol) t.TypeRef}) {
      type «Type» = ⊤, type TypeTop = t.«Type», newTypeTop = λ(u : ⊤). u,
      type TypeRef = t.«Type» ∧ {symb : p.symbols.Symbol},
      newTypeRef = λ(s : p.symbols.Symbol). let r = ν(r : {symb : s.type}) {symb = s} in r},
    symbols = ν(y : {Symbol : {tpe : options.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}}
                           .. {tpe : options.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}}}
                       ∧ {newSymbol : ∀(u : options.Option ∧ {A : ⊥..p.types.«Type»}) ∀(i : {n : ⊤}) y.Symbol}) {
      type Symbol = {tpe : options.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}},
      newSymbol = λ(u : options.Option ∧ {A : ⊥..p.types.«Type»}). λ(i : {n : ⊤}).
        let r = ν(r : {tpe : u.type} ∧ {id : i.type}) {tpe = u, id = i} in r}} in
  let pc = pcore in pc

theorem E6_side : E6_src.Scoped [] = true ∧ E6_src.LabelsIn Λ6 = true ∧
    E6_src.FieldsOk = true ∧ E6_src.PathOperands = true := by decide +kernel

theorem E6_resolves : (resolve Λ6 E6_src).map ATm.erase = some PDot.Source.E6_prog := by
  decide +kernel

/-! ## E7: a module alias used as a prefix (`Programs.lean:1102-1109`) -/

/-- The labels of E7 (`Programs.lean:1116-1122`). -/
def Λ7 : LabelTable := [("types", .trm 0), ("f", .trm 1), ("m", .trm 2), ("A", .typ 0)]

/-- E7 in the notation. -/
def E7_src : STm := pdt%
  let core = ν(c : {types : μ(t. {A : ⊤..⊤} ∧ {f : ∀(u : ⊤) ⊤})} ∧ {m : c.types.type}) {
    types = ν(t : {A : ⊤..⊤} ∧ {f : ∀(u : ⊤) ⊤}) {type A = ⊤, f = λ(u : ⊤). u}, m = c.types} in
  core.m.f core

theorem E7_side : E7_src.Scoped [] = true ∧ E7_src.LabelsIn Λ7 = true ∧
    E7_src.FieldsOk = true ∧ E7_src.PathOperands = true := by decide +kernel

theorem E7_resolves : (resolve Λ7 E7_src).map ATm.erase = some PDot.Source.E7_prog := by
  decide +kernel

/-! ## E8: replacement at an abstract member (`Programs.lean:1176-1182`) -/

/-- The labels of E8 (`Programs.lean:1193-1197`). -/
def Λ8 : LabelTable := [("A", .typ 0), ("f", .trm 0), ("me", .trm 1)]

/-- E8 in the notation. -/
def E8_src : STm := pdt%
  let g = λ(x : {A : ⊥..⊤} ∧ {f : ∀(u : ⊤) ⊤}). λ(y : x.type). λ(v : y.A). let w = y.f v in v in
  let o = ν(o : ({A : ⊤..⊤} ∧ {f : ∀(u : ⊤) ⊤}) ∧ {me : o.type}) {type A = ⊤, f = λ(u : ⊤). u, me = o} in
  let h = g o in let k = h o.me in k o

theorem E8_side : E8_src.Scoped [] = true ∧ E8_src.LabelsIn Λ8 = true ∧
    E8_src.FieldsOk = true ∧ E8_src.PathOperands = true := by decide +kernel

theorem E8_resolves : (resolve Λ8 E8_src).map ATm.erase = some PDot.Source.E8_prog := by
  decide +kernel

/-! ## E13: the cyclic object (`Examples.lean:175-187`) -/

/-- The labels of E13 (`Examples.lean:182`). -/
def Λ13 : LabelTable := [("a", .trm 0)]

/-- E13 in the notation. -/
def E13_src : STm := pdt% ν(x : {a : x.a.type}) {a = x.a}

theorem E13_side : E13_src.Scoped [] = true ∧ E13_src.LabelsIn Λ13 = true ∧
    E13_src.FieldsOk = true ∧ E13_src.PathOperands = true := by decide +kernel

theorem E13_resolves : (resolve Λ13 E13_src).map ATm.erase = some (.val PDot.Source.e13_lit) := by
  decide +kernel

/-! ## N1: bad bounds (`Examples.lean:212-229`) -/

/-- The labels of N1 (`Examples.lean:219-225`). -/
def ΛN1 : LabelTable := [("a", .trm 0), ("b", .trm 1), ("c", .trm 2), ("C", .typ 0)]

/-- N1 in the notation. -/
def N1_src : STm := pdt% ν(x : {a : {C : ∀(y : ⊤) ⊤ .. {c : ⊤}}} ∧ {b : {c : ⊤}}) {a = x.a, b = λ(y : ⊤). y}

theorem N1_side : N1_src.Scoped [] = true ∧ N1_src.LabelsIn ΛN1 = true ∧
    N1_src.FieldsOk = true ∧ N1_src.PathOperands = true := by decide +kernel

theorem N1_resolves : (resolve ΛN1 N1_src).map ATm.erase = some (.val PDot.Source.badBoundsLit) := by
  decide +kernel

/-! ## N2: Fact 2 (`Examples.lean:244-256`) -/

/-- The labels of N2 (`Examples.lean:251-253`). -/
def ΛN2 : LabelTable := [("a", .trm 0), ("A", .typ 0)]

/-- N2 in the notation. -/
def N2_src : STm := pdt% ν(x : {a : {A : ⊤..⊥}}) {a = x.a}

theorem N2_side : N2_src.Scoped [] = true ∧ N2_src.LabelsIn ΛN2 = true ∧
    N2_src.FieldsOk = true ∧ N2_src.PathOperands = true := by decide +kernel

theorem N2_resolves : (resolve ΛN2 N2_src).map ATm.erase = some (.val PDot.Source.fact2Lit) := by
  decide +kernel

/-! ## N3: the dangling literal (`Examples.lean:267-297`) -/

/-- The labels of N3 (`Examples.lean:280-282`). -/
def ΛN3 : LabelTable := [("h", .trm 0), ("zz", .trm 1)]

/-- N3 in the notation. -/
def N3_src : STm := pdt% ν(x : {h : x.zz.type}) {h = x.zz}

theorem N3_side : N3_src.Scoped [] = true ∧ N3_src.LabelsIn ΛN3 = true ∧
    N3_src.FieldsOk = true ∧ N3_src.PathOperands = true := by decide +kernel

theorem N3_resolves : (resolve ΛN3 N3_src).map ATm.erase = some (.val PDot.Source.danglingLit) := by
  decide +kernel

/-! ## The contexts of the path examples E9 to E11

The entries match `e9_G`, `e10_G` and `e11_G` (`Examples.lean:50,90,149`). -/

open PDot.Source

/-- The labels of E9. -/
def Λ9 : LabelTable := [("a", .trm 0), ("b", .trm 1)]
/-- The labels of E10. -/
def Λ10 : LabelTable := [("a", .trm 0), ("b", .trm 1)]
/-- The labels of E11. -/
def Λ11 : LabelTable := [("a", .trm 0)]

theorem E9_ctx : resolveTy Λ9 .nil (pdtTy% μ(z. {a : z.type} ∧ {b : ⊤})) =
    some (.mu (.and (.rcd (.trm e9_a (.sngl (.var .here)))) (.rcd (.trm e9_b .top)))) := by
  decide +kernel

theorem E9_path : resolvePath Λ9 (NameEnv.nil.cons "x") (.sel (.sel (.var "x") "a") "b") =
    some ((e9_x.sel e9_a).sel e9_b) := by
  decide +kernel

theorem E10_ctx : resolveTy Λ10 ((NameEnv.nil.cons "q").cons "p") (pdtTy% {a : p.type} ∧ {b : p.type}) =
    some (.and (.rcd (.trm e10_a (.sngl (.var .here)))) (.rcd (.trm e10_b (.sngl (.var .here))))) := by
  decide +kernel

theorem E11_ctx : resolveTy Λ11 (NameEnv.nil.cons "q") (pdtTy% μ(z. {a : q.type})) =
    some (.mu (.rcd (.trm e11_a (.sngl (.var (.there .here)))))) := by
  decide +kernel

end PDotFrontend.Sources
