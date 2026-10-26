import Coercions.PDot.Source.Derived

/-!
# The programs E1 to E8

Eight pDOT programs, each a closed term `Tm []`, a derivation `def` of its typing in the empty
context, and a `Nonempty` theorem.  Three of them replay the example lemmas of the Coq
formalization under their Coq names: `compiler_typecheck` (`CompilerExample.v:71`),
`list_typing` (`ListExample.v:49`) and `typecheck` (`SingletonTypeExample.v:32`).

* `E1_typed`: pDOT's Fig. 1, the Dotty fragment in precise form (`design-d3.md:960-975`).
* `E2_typed`: the length-two path (`design-d3.md:977-987`).
* `compiler_typecheck`: `CompilerExample.v:21-71`.
* `list_typing`: `ListExample.v:16-49`.
* `typecheck`: `SingletonTypeExample.v:14-32`.
* `E6_typed`: gDOT's Fig. 2 in pDOT form (`design-d3.md:1048-1076`).
* `E7_typed`: a module alias used as a prefix (`design-d3.md:1078-1090`).
* `E8_typed`: `λ(y : x.type)` with replacement at an abstract member (`design-d3.md:1092-1108`).

The terms are written in the de Bruijn form of the Coq files.  Coq's `this`, `super`, `ssuper`, …
(`ExampleTactics.v:6-13`) are the bound variables `0`, `1`, `2`, …, which are `ref0`, `ref1`,
`ref2`, … here.  Each Coq binder is one binder here, so an index means the same variable on both
sides.  Coq's notations of `ExampleTactics.v` and of each example are `abbrev`s with the same
parameters.  The texts of `design-d3.md` are written in the same form, with each named binder
resolved to its index.

Each annotation is a left-nested intersection in the order of its definitions,
`({D₁} ∧ {D₂}) ∧ {D₃}`, since `ty_defs_cons` puts the last definition on the right
(`Definitions.v:802-806`) and `ty_new_intro` takes the annotation as it is.

The derivations state the type of each step.  A type that the step reads at a path is written by a
template over paths (the functions named `…At`), which is the annotation opened at those paths.  The
template agrees with the annotation by computation, which the elaborator checks at each use.

Each label is a declared constant with a name unique in `PDot.Source`, a term label `.trm n` or a
type label `.typ n`.  The label hypotheses of the Coq files are theorems here, by `decide`.
-/

namespace PDot.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## The notations of `ExampleTactics.v` -/

/-- `path_ref 0`, Coq's `this` (`ExampleTactics.v:8`): the newest bound variable. -/
abbrev ref0 {s : Sig} : Path (s,x) := .var .here
/-- `path_ref 1`, Coq's `super` (`ExampleTactics.v:9`). -/
abbrev ref1 {s : Sig} : Path ((s,x),x) := .var (.there .here)
/-- `path_ref 2`, Coq's `ssuper` (`ExampleTactics.v:10`). -/
abbrev ref2 {s : Sig} : Path (((s,x),x),x) := .var (.there (.there .here))
/-- `path_ref 3`, Coq's `sssuper` (`ExampleTactics.v:11`). -/
abbrev ref3 {s : Sig} : Path ((((s,x),x),x),x) := .var (.there (.there (.there .here)))
/-- `path_ref 4`, Coq's `ssssuper` (`ExampleTactics.v:12`). -/
abbrev ref4 {s : Sig} : Path (((((s,x),x),x),x),x) := .var (.there (.there (.there (.there .here))))
/-- `path_ref 5`, Coq's `sssssuper` (`ExampleTactics.v:13`). -/
abbrev ref5 {s : Sig} : Path ((((((s,x),x),x),x),x),x) :=
  .var (.there (.there (.there (.there (.there .here)))))
/-- `path_ref 6`, one binder further out than Coq's notations go.  Only derivations use it. -/
abbrev ref6 {s : Sig} : Path (((((((s,x),x),x),x),x),x),x) :=
  .var (.there (.there (.there (.there (.there (.there .here))))))

/-- `typ_rcd {A >: S <: U}`, the record type of one type member. -/
abbrev tdec {s : Sig} (A : Label) (S U : Ty s) : Ty s := .rcd (.typ A S U)
/-- `typ_rcd {a ⦂ T}`, the record type of one field. -/
abbrev fdec {s : Sig} (a : Label) (T : Ty s) : Ty s := .rcd (.trm a T)
/-- `Lazy T = ∀(⊤) T` (`ExampleTactics.v:16`). -/
abbrev lazyTy {s : Sig} (T : Ty (s,x)) : Ty s := .all .top T
/-- `Id = Lazy ⊤` (`ExampleTactics.v:18`). -/
abbrev idTy {s : Sig} : Ty s := .all .top .top
/-- `id = λ(⊤) this` (`ExampleTactics.v:17`). -/
abbrev idVal {s : Sig} : Val s := .lam .top (.path ref0)
/-- `lazy t = defv (λ(⊤) t)` (`ExampleTactics.v:15`). -/
abbrev lazyRhs {s : Sig} (t : Tm (s,x)) : Rhs s := .defv (.lam .top t)
/-- `let_trm t = let z = t in z` (`ExampleTactics.v:19`). -/
abbrev letTrm {s : Sig} (t : Tm s) : Tm s := .lett t (.path ref0)

/-! ## E1: pDOT's Fig. 1 (`design-d3.md:960-975`)

```text
let dotty = ν(d : {core : μ(c : Tc)}) {
  core = ν(c : Tc) {
    types   = ν(t : Tt) { Type = ⊤, TypeRef = t.Type ∧ {symb : c.symbols.Symbol} },
    symbols = ν(s : Ts) { Symbol = {tpe : c.types.Type} } } }
in dotty
Tt = {Type : ⊤..⊤} ∧ {TypeRef : t.Type ∧ {symb : c.symbols.Symbol} .. t.Type ∧ {symb : c.symbols.Symbol}}
Ts = {Symbol : {tpe : c.types.Type} .. {tpe : c.types.Type}}
Tc = {types : μ(t : Tt)} ∧ {symbols : μ(s : Ts)}
```

The three literals are typed by `ty_def_new` at `d.core`, `d.core.types` and `d.core.symbols`.
`c.symbols.Symbol` in `types` names the sibling `symbols` through the enclosing self `c`. -/

/-- The field `core`. -/
abbrev e1_core : Label := .trm 0
/-- The field `types`. -/
abbrev e1_types : Label := .trm 1
/-- The field `symbols`. -/
abbrev e1_symbols : Label := .trm 2
/-- The field `symb`. -/
abbrev e1_symb : Label := .trm 3
/-- The field `tpe`. -/
abbrev e1_tpe : Label := .trm 4
/-- The type member `Type`. -/
abbrev e1_Type : Label := .typ 0
/-- The type member `TypeRef`. -/
abbrev e1_TypeRef : Label := .typ 1
/-- The type member `Symbol`. -/
abbrev e1_Symbol : Label := .typ 2

/-- `t.Type ∧ {symb : c.symbols.Symbol}`, under `c` then `t`. -/
abbrev e1_Ref {s : Sig} : Ty ((s,x),x) :=
  .and (.sel ref0 e1_Type) (fdec e1_symb (.sel (ref1.sel e1_symbols) e1_Symbol))
/-- `Tt`, under `c` then `t`. -/
abbrev e1_Tt {s : Sig} : Ty ((s,x),x) := .and (tdec e1_Type .top .top) (tdec e1_TypeRef e1_Ref e1_Ref)
/-- `{tpe : c.types.Type}`, under `c` then `s`. -/
abbrev e1_Sym {s : Sig} : Ty ((s,x),x) := fdec e1_tpe (.sel (ref1.sel e1_types) e1_Type)
/-- `Ts`, under `c` then `s`. -/
abbrev e1_Ts {s : Sig} : Ty ((s,x),x) := tdec e1_Symbol e1_Sym e1_Sym
/-- `Tc`, under `c`. -/
abbrev e1_Tc {s : Sig} : Ty (s,x) := .and (fdec e1_types (.mu e1_Tt)) (fdec e1_symbols (.mu e1_Ts))
/-- `{core : μ(c : Tc)}`, under `d`. -/
abbrev e1_Td {s : Sig} : Ty (s,x) := fdec e1_core (.mu e1_Tc)

/-- `{Type = ⊤} ▹ {TypeRef = t.Type ∧ {symb : c.symbols.Symbol}}`, under `c` then `t`. -/
abbrev e1_typesDefs {s : Sig} : Defs ((s,x),x) :=
  .cons (.cons .nil (.typ e1_Type .top)) (.typ e1_TypeRef e1_Ref)
/-- `{Symbol = {tpe : c.types.Type}}`, under `c` then `s`. -/
abbrev e1_symbolsDefs {s : Sig} : Defs ((s,x),x) := .cons .nil (.typ e1_Symbol e1_Sym)
/-- `{types = ν(t : Tt) …} ▹ {symbols = ν(s : Ts) …}`, under `c`. -/
abbrev e1_coreDefs {s : Sig} : Defs (s,x) :=
  .cons (.cons .nil (.trm e1_types (.defv (.new e1_Tt e1_typesDefs))))
    (.trm e1_symbols (.defv (.new e1_Ts e1_symbolsDefs)))
/-- `{core = ν(c : Tc) …}`, under `d`. -/
abbrev e1_dottyDefs {s : Sig} : Defs (s,x) := .cons .nil (.trm e1_core (.defv (.new e1_Tc e1_coreDefs)))

/-- The program E1. -/
abbrev E1_prog : Tm [] := letTrm (.val (.new e1_Td e1_dottyDefs))

-- ⊢ ν(d : {core : μ(c : Tc)}) {core = …} : μ(d. {core : μ(c : Tc)})
--   ty_new_intro, ty_defs_one, then ty_def_new at d.core, whose definitions are
--   ty_def_new at d.core.types (ty_defs_cons of two ty_def_typ) and at d.core.symbols (ty_def_typ)
def E1_lit : HasTy .nil (.val (.new e1_Td e1_dottyDefs)) (.mu e1_Td) :=
  .ty_new_intro (.ty_defs_one (.ty_def_new rfl
    (.ty_defs_cons
      (.ty_defs_one (.ty_def_new rfl (.ty_defs_cons (.ty_defs_one .ty_def_typ) .ty_def_typ rfl)))
      (.ty_def_new rfl (.ty_defs_one .ty_def_typ)) rfl)))

-- ⊢ let dotty = ν(…) … in dotty : μ(d. {core : μ(c : Tc)})          ty_let, ty_var
def E1_d : HasTy .nil E1_prog (.mu e1_Td) := .ty_let E1_lit (.ty_var rfl)

theorem E1_typed : Nonempty (HasTy .nil E1_prog (.mu e1_Td)) := ⟨E1_d⟩

/-! ## E2: the length-two path (`design-d3.md:977-987`)

```text
let x = ν(z : {c : μ(w : {A : z.B..z.B})} ∧ {B : z.c.A..z.c.A}) {
  c = ν(w : {A : z.B..z.B}) { A = z.B },
  B = z.c.A }
in x
```

`B = z.c.A` selects through the path `z.c` of length two, and `A = z.B` refers back.  The two type
definitions form a cycle, which no rule asks to end. -/

/-- The field `c`. -/
abbrev e2_c : Label := .trm 0
/-- The type member `A`. -/
abbrev e2_A : Label := .typ 0
/-- The type member `B`. -/
abbrev e2_B : Label := .typ 1

/-- `{A : z.B..z.B}`, under `z` then `w`. -/
abbrev e2_Tw {s : Sig} : Ty ((s,x),x) := tdec e2_A (.sel ref1 e2_B) (.sel ref1 e2_B)
/-- `{c : μ(w : {A : z.B..z.B})} ∧ {B : z.c.A..z.c.A}`, under `z`. -/
abbrev e2_Tz {s : Sig} : Ty (s,x) :=
  .and (fdec e2_c (.mu e2_Tw)) (tdec e2_B (.sel (ref0.sel e2_c) e2_A) (.sel (ref0.sel e2_c) e2_A))
/-- `{c = ν(w : {A : z.B..z.B}) {A = z.B}} ▹ {B = z.c.A}`, under `z`. -/
abbrev e2_defs {s : Sig} : Defs (s,x) :=
  .cons (.cons .nil (.trm e2_c (.defv (.new e2_Tw (.cons .nil (.typ e2_A (.sel ref1 e2_B)))))))
    (.typ e2_B (.sel (ref0.sel e2_c) e2_A))

/-- The program E2. -/
abbrev E2_prog : Tm [] := letTrm (.val (.new e2_Tz e2_defs))

-- ⊢ ν(z : …) {c = …} ▹ {B = z.c.A} : μ(z. …)
--   ty_new_intro, ty_defs_cons of ty_def_new at z.c (one ty_def_typ) and ty_def_typ
def E2_lit : HasTy .nil (.val (.new e2_Tz e2_defs)) (.mu e2_Tz) :=
  .ty_new_intro (.ty_defs_cons (.ty_defs_one (.ty_def_new rfl (.ty_defs_one .ty_def_typ))) .ty_def_typ rfl)

-- ⊢ let x = ν(…) … in x : μ(z. …)                                   ty_let, ty_var
def E2_d : HasTy .nil E2_prog (.mu e2_Tz) := .ty_let E2_lit (.ty_var rfl)

theorem E2_typed : Nonempty (HasTy .nil E2_prog (.mu e2_Tz)) := ⟨E2_d⟩

/-! ## E3: `CompilerExample.v` (`:21-71`)

```text
ν(r : {DottyCore : μ(c : DCA)..μ(c : DCA)} ∧ {dottyCore : Lazy r.DottyCore}) {
  DottyCore = μ(c : DCA),
  dottyCore = λ(e : ⊤). let k = ν(c : DCT) {
      types = ν(t : TT) { Tpe = μ(o : {denotation : Id}),
                          typeRef = λ(s : c.symbols.Symbol).
                            let o = ν(o : {symb : s.type} ∧ {denotation : Id}) {symb = s, denotation = id} in o },
      symbols = ν(y : SS) { Symbol = μ(o : {srcPos : Id}),
                            symbol = λ(u : c.types.Tpe).
                              let o = ν(o : {tpe : u.type} ∧ {srcPos : Id}) {tpe = u, srcPos = id} in o } }
    in k }
TT(L, U) = {Tpe : L..U} ∧ {typeRef : ∀(s : c.symbols.Symbol) (t.Tpe ∧ {symb : c.symbols.Symbol})}
SS(L, U) = {Symbol : L..U} ∧ {symbol : ∀(u : c.types.Tpe) (y.Symbol ∧ {tpe : c.types.Tpe})}
DCA = {types : μ(t : TT(⊥, ⊤))} ∧ {symbols : μ(y : SS(⊥, ⊤))}
DCT = {types : μ(t : TT(TpeImpl, TpeImpl))} ∧ {symbols : μ(y : SS(SymbolImpl, SymbolImpl))}
```

typed at `μ(r. …)`, the Coq lemma `compiler_typecheck`.  The text is `design-d3.md:989-1012`.  Each
constructor returns `o` at `t.Tpe ∧ {symb : c.symbols.Symbol}`: `o.symb : s.type`, then `ty_sngl`
gives `o.symb : c.symbols.Symbol`, then `ty_rcd_intro`.  The package `k` is returned at
`r.DottyCore` through its abstract view: `ty_rec_elim`, `ty_new_elim` and `ty_rec_elim` at each
module, the bounds widened to `⊥..⊤`, `ty_rec_intro` and `ty_rcd_intro` back, then `subtyp_sel2`.
The hypotheses `types <> symbols`, `symb <> denotation` and `tpe <> srcPos` (`:17-19`) are
`cp_labels`. -/

/-- `DottyCore`. -/
abbrev cp_DottyCore : Label := .typ 0
/-- `Tpe`. -/
abbrev cp_Tpe : Label := .typ 1
/-- `Symbol`. -/
abbrev cp_Symbol : Label := .typ 2
/-- `dottyCore`. -/
abbrev cp_dottyCore : Label := .trm 0
/-- `types`. -/
abbrev cp_types : Label := .trm 1
/-- `typeRef`. -/
abbrev cp_typeRef : Label := .trm 2
/-- `symbols`. -/
abbrev cp_symbols : Label := .trm 3
/-- `symbol`. -/
abbrev cp_symbol : Label := .trm 4
/-- `symb`. -/
abbrev cp_symb : Label := .trm 5
/-- `tpe`. -/
abbrev cp_tpe : Label := .trm 6
/-- `denotation`. -/
abbrev cp_denotation : Label := .trm 7
/-- `srcPos`. -/
abbrev cp_srcPos : Label := .trm 8

/-- `Hypothesis TS`, `ST` and `TS'` (`CompilerExample.v:17-19`). -/
theorem cp_labels : cp_types ≠ cp_symbols ∧ cp_symb ≠ cp_denotation ∧ cp_tpe ≠ cp_srcPos := by decide

/-- `TpeImpl = μ(typ_rcd {denotation ⦂ Id})` (`CompilerExample.v:14`). -/
abbrev cp_TpeImpl {s : Sig} : Ty s := .mu (fdec cp_denotation idTy)
/-- `SymbolImpl = μ(typ_rcd {srcPos ⦂ Id})` (`CompilerExample.v:15`). -/
abbrev cp_SymbolImpl {s : Sig} : Ty s := .mu (fdec cp_srcPos idTy)
/-- `typesType L U` (`CompilerExample.v:21-24`), under `c` then `t`. -/
abbrev cp_typesType {s : Sig} (L U : Ty ((s,x),x)) : Ty ((s,x),x) :=
  .and (tdec cp_Tpe L U)
    (fdec cp_typeRef (.all (.sel (ref1.sel cp_symbols) cp_Symbol)
                       (.and (.sel ref1 cp_Tpe) (fdec cp_symb (.sel (ref2.sel cp_symbols) cp_Symbol)))))
/-- `symbolsType L U` (`CompilerExample.v:25-28`), under `c` then `y`. -/
abbrev cp_symbolsType {s : Sig} (L U : Ty ((s,x),x)) : Ty ((s,x),x) :=
  .and (tdec cp_Symbol L U)
    (fdec cp_symbol (.all (.sel (ref1.sel cp_types) cp_Tpe)
                      (.and (.sel ref1 cp_Symbol) (fdec cp_tpe (.sel (ref2.sel cp_types) cp_Tpe)))))
/-- `DottyCorePackage tl tu sl su` (`CompilerExample.v:29-31`), under `c`. -/
abbrev cp_DottyCorePackage {s : Sig} (tl tu sl su : Ty ((s,x),x)) : Ty (s,x) :=
  .and (fdec cp_types (.mu (cp_typesType tl tu))) (fdec cp_symbols (.mu (cp_symbolsType sl su)))
/-- `DottyCoreAbstract` (`CompilerExample.v:33`). -/
abbrev cp_DottyCoreAbstract {s : Sig} : Ty (s,x) := cp_DottyCorePackage .bot .top .bot .top
/-- `DottyCoreTight` (`CompilerExample.v:34`). -/
abbrev cp_DottyCoreTight {s : Sig} : Ty (s,x) :=
  cp_DottyCorePackage cp_TpeImpl cp_TpeImpl cp_SymbolImpl cp_SymbolImpl

/-- `ν(typ_rcd {symb ⦂ {{ super }}} ∧ typ_rcd {denotation ⦂ Id}) {symb := defp super} Λ
{denotation := defv id}` (`CompilerExample.v:50-54`), under the parameter `s` of `typeRef`. -/
abbrev cp_typeRefLit {s : Sig} : Val (s,x) :=
  .new (.and (fdec cp_symb (.sngl ref1)) (fdec cp_denotation idTy))
    (.cons (.cons .nil (.trm cp_symb (.defp ref1))) (.trm cp_denotation (.defv idVal)))
/-- `ν(typ_rcd {tpe ⦂ {{ super }}} ∧ typ_rcd {srcPos ⦂ Id}) {tpe := defp super} Λ
{srcPos := defv id}` (`CompilerExample.v:61-65`), under the parameter `u` of `symbol`. -/
abbrev cp_symbolLit {s : Sig} : Val (s,x) :=
  .new (.and (fdec cp_tpe (.sngl ref1)) (fdec cp_srcPos idTy))
    (.cons (.cons .nil (.trm cp_tpe (.defp ref1))) (.trm cp_srcPos (.defv idVal)))
/-- The definitions of `types` (`CompilerExample.v:46-54`), under `c` then `t`. -/
abbrev cp_typesDefs {s : Sig} : Defs ((s,x),x) :=
  .cons (.cons .nil (.typ cp_Tpe cp_TpeImpl))
    (.trm cp_typeRef (.defv (.lam (.sel (ref1.sel cp_symbols) cp_Symbol) (letTrm (.val cp_typeRefLit)))))
/-- The definitions of `symbols` (`CompilerExample.v:57-65`), under `c` then `y`. -/
abbrev cp_symbolsDefs {s : Sig} : Defs ((s,x),x) :=
  .cons (.cons .nil (.typ cp_Symbol cp_SymbolImpl))
    (.trm cp_symbol (.defv (.lam (.sel (ref1.sel cp_types) cp_Tpe) (letTrm (.val cp_symbolLit)))))
/-- The definitions of the package (`CompilerExample.v:43-65`), under `c`. -/
abbrev cp_coreDefs {s : Sig} : Defs (s,x) :=
  .cons (.cons .nil (.trm cp_types (.defv (.new (cp_typesType cp_TpeImpl cp_TpeImpl) cp_typesDefs))))
    (.trm cp_symbols (.defv (.new (cp_symbolsType cp_SymbolImpl cp_SymbolImpl) cp_symbolsDefs)))
/-- The annotation of the outer literal (`CompilerExample.v:37-38`), under `r`. -/
abbrev cp_rT {s : Sig} : Ty (s,x) :=
  .and (tdec cp_DottyCore (.mu cp_DottyCoreAbstract) (.mu cp_DottyCoreAbstract))
    (fdec cp_dottyCore (lazyTy (.sel ref1 cp_DottyCore)))
/-- The definitions of the outer literal (`CompilerExample.v:39-65`), under `r`. -/
abbrev cp_rDefs {s : Sig} : Defs (s,x) :=
  .cons (.cons .nil (.typ cp_DottyCore (.mu cp_DottyCoreAbstract)))
    (.trm cp_dottyCore (lazyRhs (letTrm (.val (.new cp_DottyCoreTight cp_coreDefs)))))

/-- Coq's `t` (`CompilerExample.v:36-65`). -/
abbrev compiler_t : Tm [] := .val (.new cp_rT cp_rDefs)
/-- Coq's `T` (`CompilerExample.v:67-69`). -/
abbrev compiler_T : Ty [] := .mu cp_rT

/-! ### Templates of the opened types -/

/-- `typesType L U` with `c` and `t` paths. -/
abbrev cp_typesAt {s : Sig} (c t : Path s) (L U : Ty s) : Ty s :=
  .and (tdec cp_Tpe L U)
    (fdec cp_typeRef (.all (.sel (c.sel cp_symbols) cp_Symbol)
       (.and (.sel t.weaken cp_Tpe) (fdec cp_symb (.sel (c.weaken.sel cp_symbols) cp_Symbol)))))
/-- `symbolsType L U` with `c` and `y` paths. -/
abbrev cp_symbolsAt {s : Sig} (c y : Path s) (L U : Ty s) : Ty s :=
  .and (tdec cp_Symbol L U)
    (fdec cp_symbol (.all (.sel (c.sel cp_types) cp_Tpe)
       (.and (.sel y.weaken cp_Symbol) (fdec cp_tpe (.sel (c.weaken.sel cp_types) cp_Tpe)))))
/-- `DottyCorePackage tl tu sl su` with `c` a path. -/
abbrev cp_packageAt {s : Sig} (c : Path s) (tl tu sl su : Ty (s,x)) : Ty s :=
  .and (fdec cp_types (.mu (cp_typesAt c.weaken ref0 tl tu))) (fdec cp_symbols (.mu (cp_symbolsAt c.weaken ref0 sl su)))

/-! ### The constructors `typeRef` and `symbol` -/

/-- `[r :ˢ rT]`. -/
abbrev cp_Gr : Ctx ([],x) := Ctx.nil.consSelf cp_rT
/-- `[r :ˢ rT, e : ⊤]`. -/
abbrev cp_Ge : Ctx (([],x),x) := cp_Gr.cons .top
/-- `[r :ˢ rT, e : ⊤, c :ˢ DCT]`. -/
abbrev cp_Gc : Ctx ((([],x),x),x) := cp_Ge.consSelf cp_DottyCoreTight
/-- `[…, c :ˢ DCT, s : c.symbols.Symbol]`. -/
abbrev cp_Gs : Ctx (((([],x),x),x),x) := cp_Gc.cons (.sel (ref0.sel cp_symbols) cp_Symbol)
/-- `[…, c :ˢ DCT, s : c.symbols.Symbol, o : μ(o. {symb : s.type} ∧ {denotation : Id})]`. -/
abbrev cp_Gso : Ctx ((((([],x),x),x),x),x) :=
  cp_Gs.cons (.mu (.and (fdec cp_symb (.sngl ref1)) (fdec cp_denotation idTy)))
/-- `[…, c :ˢ DCT, u : c.types.Tpe]`. -/
abbrev cp_Gu : Ctx (((([],x),x),x),x) := cp_Gc.cons (.sel (ref0.sel cp_types) cp_Tpe)
/-- `[…, c :ˢ DCT, u : c.types.Tpe, o : μ(o. {tpe : u.type} ∧ {srcPos : Id})]`. -/
abbrev cp_Guo : Ctx ((((([],x),x),x),x),x) :=
  cp_Gu.cons (.mu (.and (fdec cp_tpe (.sngl ref1)) (fdec cp_srcPos idTy)))

-- Gs ⊢ ν(o : {symb : s.type} ∧ {denotation : Id}) … : μ(o. …)     ty_def_path at s, ty_def_all at id
def CP_typeRefLit : HasTy cp_Gs (.val cp_typeRefLit) (.mu (.and (fdec cp_symb (.sngl ref1)) (fdec cp_denotation idTy))) :=
  .ty_new_intro (.ty_defs_cons (.ty_defs_one (.ty_def_path (.ty_var rfl))) (.ty_def_all (.ty_all_intro (.ty_var rfl))) rfl)
-- Gso ⊢ c : DCT⟨c⟩                                     ty_var
def CP_c_so : HasTy cp_Gso (.path ref2) (cp_packageAt ref2 cp_TpeImpl cp_TpeImpl cp_SymbolImpl cp_SymbolImpl) :=
  .ty_var rfl
-- Gso ⊢ c.types : TT(TpeImpl, TpeImpl)⟨c.types⟩        ty_sub by subtyp_and11, ty_new_elim, ty_rec_elim
def CP_ctypes_so : HasTy cp_Gso (.path (ref2.sel cp_types)) (cp_typesAt ref2 (ref2.sel cp_types) cp_TpeImpl cp_TpeImpl) :=
  .ty_rec_elim (T := cp_typesAt ref3 ref0 cp_TpeImpl cp_TpeImpl) (.ty_new_elim (.ty_sub CP_c_so .subtyp_and11))
-- Gso ⊢ o : {symb : s.type} ∧ {denotation : Id}         ty_var, ty_rec_elim
def CP_o_so : HasTy cp_Gso (.path ref0) (.and (fdec cp_symb (.sngl ref1)) (fdec cp_denotation idTy)) :=
  .ty_rec_elim (T := .and (fdec cp_symb (.sngl ref2)) (fdec cp_denotation idTy)) (.ty_var rfl)
-- Gso ⊢ o : c.types.Tpe     ty_sub by subtyp_and12, ty_rec_intro at TpeImpl, subtyp_sel2 at c.types : {Tpe : TpeImpl..TpeImpl}
def CP_o_Tpe : HasTy cp_Gso (.path ref0) (.sel (ref2.sel cp_types) cp_Tpe) :=
  .ty_sub (.ty_rec_intro (T := fdec cp_denotation idTy) (.ty_sub CP_o_so .subtyp_and12))
    (.subtyp_sel2 (.ty_sub CP_ctypes_so .subtyp_and11))
-- Gso ⊢ o : {symb : c.symbols.Symbol}                 ty_new_elim, ty_sngl at s : c.symbols.Symbol, ty_rcd_intro
def CP_o_symb : HasTy cp_Gso (.path ref0) (fdec cp_symb (.sel (ref2.sel cp_symbols) cp_Symbol)) :=
  .ty_rcd_intro (.ty_sngl (.ty_new_elim (.ty_sub CP_o_so .subtyp_and11)) (.ty_var rfl))
-- Gc ⊢ λ(s : c.symbols.Symbol). let o = … in o : ∀(s : c.symbols.Symbol) (c.types.Tpe ∧ {symb : c.symbols.Symbol})
--   ty_all_intro, ty_let, ty_and_intro
def CP_typeRef : HasTy cp_Gc (.val (.lam (.sel (ref0.sel cp_symbols) cp_Symbol) (letTrm (.val cp_typeRefLit))))
    (.all (.sel (ref0.sel cp_symbols) cp_Symbol)
      (.and (.sel (ref1.sel cp_types) cp_Tpe) (fdec cp_symb (.sel (ref1.sel cp_symbols) cp_Symbol)))) :=
  .ty_all_intro (.ty_let CP_typeRefLit (.ty_and_intro CP_o_Tpe CP_o_symb))

-- Gu ⊢ ν(o : {tpe : u.type} ∧ {srcPos : Id}) … : μ(o. …)          ty_def_path at u, ty_def_all at id
def CP_symbolLit : HasTy cp_Gu (.val cp_symbolLit) (.mu (.and (fdec cp_tpe (.sngl ref1)) (fdec cp_srcPos idTy))) :=
  .ty_new_intro (.ty_defs_cons (.ty_defs_one (.ty_def_path (.ty_var rfl))) (.ty_def_all (.ty_all_intro (.ty_var rfl))) rfl)
-- Guo ⊢ c : DCT⟨c⟩                                     ty_var
def CP_c_uo : HasTy cp_Guo (.path ref2) (cp_packageAt ref2 cp_TpeImpl cp_TpeImpl cp_SymbolImpl cp_SymbolImpl) :=
  .ty_var rfl
-- Guo ⊢ c.symbols : SS(SymbolImpl, SymbolImpl)⟨c.symbols⟩   ty_sub by subtyp_and12, ty_new_elim, ty_rec_elim
def CP_csym_uo : HasTy cp_Guo (.path (ref2.sel cp_symbols))
    (cp_symbolsAt ref2 (ref2.sel cp_symbols) cp_SymbolImpl cp_SymbolImpl) :=
  .ty_rec_elim (T := cp_symbolsAt ref3 ref0 cp_SymbolImpl cp_SymbolImpl) (.ty_new_elim (.ty_sub CP_c_uo .subtyp_and12))
-- Guo ⊢ o : {tpe : u.type} ∧ {srcPos : Id}              ty_var, ty_rec_elim
def CP_o_uo : HasTy cp_Guo (.path ref0) (.and (fdec cp_tpe (.sngl ref1)) (fdec cp_srcPos idTy)) :=
  .ty_rec_elim (T := .and (fdec cp_tpe (.sngl ref2)) (fdec cp_srcPos idTy)) (.ty_var rfl)
-- Guo ⊢ o : c.symbols.Symbol  ty_sub by subtyp_and12, ty_rec_intro at SymbolImpl, subtyp_sel2 at c.symbols
def CP_o_Symbol : HasTy cp_Guo (.path ref0) (.sel (ref2.sel cp_symbols) cp_Symbol) :=
  .ty_sub (.ty_rec_intro (T := fdec cp_srcPos idTy) (.ty_sub CP_o_uo .subtyp_and12))
    (.subtyp_sel2 (.ty_sub CP_csym_uo .subtyp_and11))
-- Guo ⊢ o : {tpe : c.types.Tpe}                       ty_new_elim, ty_sngl at u : c.types.Tpe, ty_rcd_intro
def CP_o_tpe : HasTy cp_Guo (.path ref0) (fdec cp_tpe (.sel (ref2.sel cp_types) cp_Tpe)) :=
  .ty_rcd_intro (.ty_sngl (.ty_new_elim (.ty_sub CP_o_uo .subtyp_and11)) (.ty_var rfl))
-- Gc ⊢ λ(u : c.types.Tpe). let o = … in o : ∀(u : c.types.Tpe) (c.symbols.Symbol ∧ {tpe : c.types.Tpe})
--   ty_all_intro, ty_let, ty_and_intro
def CP_symbol : HasTy cp_Gc (.val (.lam (.sel (ref0.sel cp_types) cp_Tpe) (letTrm (.val cp_symbolLit))))
    (.all (.sel (ref0.sel cp_types) cp_Tpe)
      (.and (.sel (ref1.sel cp_symbols) cp_Symbol) (fdec cp_tpe (.sel (ref1.sel cp_types) cp_Tpe)))) :=
  .ty_all_intro (.ty_let CP_symbolLit (.ty_and_intro CP_o_Symbol CP_o_tpe))

-- Ge ⊢ ν(c : DCT) {types = …} ▹ {symbols = …} : μ(c. DCT)
--   ty_def_new at c.types and at c.symbols, each ty_def_typ then ty_def_all
def CP_coreLit : HasTy cp_Ge (.val (.new cp_DottyCoreTight cp_coreDefs)) (.mu cp_DottyCoreTight) :=
  .ty_new_intro (.ty_defs_cons
    (.ty_defs_one (.ty_def_new rfl (.ty_defs_cons (.ty_defs_one .ty_def_typ) (.ty_def_all CP_typeRef) rfl)))
    (.ty_def_new rfl (.ty_defs_cons (.ty_defs_one .ty_def_typ) (.ty_def_all CP_symbol) rfl)) rfl)

/-! ### The package returned at `r.DottyCore` -/

/-- `[r :ˢ rT, e : ⊤, k : μ(c. DCT)]`. -/
abbrev cp_Gk : Ctx ((([],x),x),x) := cp_Ge.cons (.mu cp_DottyCoreTight)

-- Gk ⊢ k : DCT⟨k⟩                                      ty_var, ty_rec_elim
def CP_k_open : HasTy cp_Gk (.path ref0) (cp_packageAt ref0 cp_TpeImpl cp_TpeImpl cp_SymbolImpl cp_SymbolImpl) :=
  .ty_rec_elim (T := cp_DottyCoreTight) (.ty_var rfl)
-- Gk ⊢ k.types : TT(TpeImpl, TpeImpl)⟨k.types⟩         ty_sub by subtyp_and11, ty_new_elim, ty_rec_elim
def CP_ktypes : HasTy cp_Gk (.path (ref0.sel cp_types)) (cp_typesAt ref0 (ref0.sel cp_types) cp_TpeImpl cp_TpeImpl) :=
  .ty_rec_elim (T := cp_typesAt ref1 ref0 cp_TpeImpl cp_TpeImpl) (.ty_new_elim (.ty_sub CP_k_open .subtyp_and11))
-- Gk ⊢ k.symbols : SS(SymbolImpl, SymbolImpl)⟨k.symbols⟩  ty_sub by subtyp_and12, ty_new_elim, ty_rec_elim
def CP_ksymbols : HasTy cp_Gk (.path (ref0.sel cp_symbols))
    (cp_symbolsAt ref0 (ref0.sel cp_symbols) cp_SymbolImpl cp_SymbolImpl) :=
  .ty_rec_elim (T := cp_symbolsAt ref1 ref0 cp_SymbolImpl cp_SymbolImpl) (.ty_new_elim (.ty_sub CP_k_open .subtyp_and12))
-- Gk ⊢ k : {types : μ(t. TT(⊥, ⊤))}     subtyp_typ by subtyp_bot and subtyp_top, ty_and_intro, ty_rec_intro, ty_rcd_intro
def CP_k_types_abs : HasTy cp_Gk (.path ref0) (fdec cp_types (.mu (cp_typesAt ref1 ref0 .bot .top))) :=
  .ty_rcd_intro (.ty_rec_intro (T := cp_typesAt ref1 ref0 .bot .top)
    (.ty_and_intro (.ty_sub (.ty_sub CP_ktypes .subtyp_and11) (.subtyp_typ .subtyp_bot .subtyp_top))
      (.ty_sub CP_ktypes .subtyp_and12)))
-- Gk ⊢ k : {symbols : μ(y. SS(⊥, ⊤))}   the same at symbols
def CP_k_symbols_abs : HasTy cp_Gk (.path ref0) (fdec cp_symbols (.mu (cp_symbolsAt ref1 ref0 .bot .top))) :=
  .ty_rcd_intro (.ty_rec_intro (T := cp_symbolsAt ref1 ref0 .bot .top)
    (.ty_and_intro (.ty_sub (.ty_sub CP_ksymbols .subtyp_and11) (.subtyp_typ .subtyp_bot .subtyp_top))
      (.ty_sub CP_ksymbols .subtyp_and12)))
-- Gk ⊢ k : μ(c. DCA)                                   ty_and_intro, ty_rec_intro
def CP_k_abs : HasTy cp_Gk (.path ref0) (.mu cp_DottyCoreAbstract) :=
  .ty_rec_intro (T := cp_DottyCoreAbstract) (.ty_and_intro CP_k_types_abs CP_k_symbols_abs)
-- Gk ⊢ k : r.DottyCore                     ty_sub by subtyp_sel2 at r : {DottyCore : μ(c. DCA)..μ(c. DCA)}
def CP_k_ret : HasTy cp_Gk (.path ref0) (.sel ref2 cp_DottyCore) :=
  .ty_sub CP_k_abs (.subtyp_sel2 (.ty_sub (.ty_var rfl) .subtyp_and11))

-- Gr ⊢ λ(e : ⊤). let k = ν(c : DCT) … in k : Lazy r.DottyCore        ty_all_intro, ty_let
def CP_dottyCore : HasTy cp_Gr (.val (.lam .top (letTrm (.val (.new cp_DottyCoreTight cp_coreDefs)))))
    (lazyTy (.sel ref1 cp_DottyCore)) :=
  .ty_all_intro (.ty_let CP_coreLit CP_k_ret)

-- ⊢ t : T                                              ty_new_intro, ty_def_typ, ty_def_all
def CP_d : HasTy .nil compiler_t compiler_T :=
  .ty_new_intro (.ty_defs_cons (.ty_defs_one .ty_def_typ) (.ty_def_all CP_dottyCore) rfl)

/-- `Lemma compiler_typecheck : empty ⊢ t : T` (`CompilerExample.v:71`). -/
theorem compiler_typecheck : Nonempty (HasTy .nil compiler_t compiler_T) := ⟨CP_d⟩

/-! ## E4: `ListExample.v` (`:16-49`)

```text
ν(sci : {List : μ(l : LT(l))..μ(l : LT(l))}
      ∧ {Nil : ∀(x : {A : ⊥..⊤}) (sci.List ∧ {A : ⊥..⊥})}
      ∧ {Cons : ∀(x : {A : ⊥..⊤}) ∀(y : x.A) ∀(ys : sci.List ∧ {A : ⊥..x.A}) (sci.List ∧ {A : ⊥..x.A})}) {
  List = μ(l : LT(l)),
  Nil  = λ(x : {A : ⊥..⊤}).
           let r = ν(r : {A : ⊥..⊥} ∧ {head : Lazy r.A} ∧ {tail : Lazy (sci.List ∧ {A : ⊥..r.A})}) {
                     A = ⊥, head = λ(u : ⊤). r.head u, tail = λ(u : ⊤). r.tail u } in r,
  Cons = λ(x : {A : ⊥..⊤}). λ(y : x.A). λ(ys : sci.List ∧ {A : ⊥..x.A}).
           let r = ν(r : {A : x.A..x.A} ∧ {head : Lazy r.A} ∧ {tail : Lazy (sci.List ∧ {A : ⊥..x.A})}) {
                     A = x.A, head = λ(u : ⊤). y, tail = λ(u : ⊤). ys } in r }
LT(l) = {A : ⊥..⊤} ∧ {head : Lazy l.A} ∧ {tail : Lazy (sci.List ∧ {A : ⊥..l.A})}
```

typed at `μ(sci. …)`, the Coq lemma `list_typing`.  The text is `design-d3.md:1014-1030`.  In `Cons`
the literal's `tail` is declared at `Lazy (sci.List ∧ {A : ⊥..x.A})` (`ListExample.v:43`), and the
returned `r` reaches `LT(r)` through `subtyp_fld`, `subtyp_all` and `subtyp_sel2` at
`x.A <: r.A`, as the Coq proof does (`:159-163`).  The hypotheses `Nil <> Cons` and `head <> tail`
(`:13-14`) are `ls_labels`. -/

/-- `A`. -/
abbrev ls_A : Label := .typ 0
/-- `List`. -/
abbrev ls_List : Label := .typ 1
/-- `Nil`. -/
abbrev ls_Nil : Label := .trm 0
/-- `Cons`. -/
abbrev ls_Cons : Label := .trm 1
/-- `head`. -/
abbrev ls_head : Label := .trm 2
/-- `tail`. -/
abbrev ls_tail : Label := .trm 3

/-- `Hypothesis NC : Nil <> Cons` and `Hypothesis HT : head <> tail` (`ListExample.v:13-14`). -/
theorem ls_labels : ls_Nil ≠ ls_Cons ∧ ls_head ≠ ls_tail := by decide

/-- `ListTypeA list_level A_lower A_upper A_level` (`ListExample.v:16-19`), under the list's self.
`list_level` and `A_level` are paths under the binder of `Lazy`, as Coq writes them. -/
abbrev ls_ListTypeA {s : Sig} (ll : Path ((s,x),x)) (lo hi : Ty (s,x)) (al : Path ((s,x),x)) : Ty (s,x) :=
  .and (.and (tdec ls_A lo hi) (fdec ls_head (lazyTy (.sel ref1 ls_A))))
    (fdec ls_tail (lazyTy (.and (.sel ll ls_List) (tdec ls_A .bot (.sel al ls_A)))))
/-- `ListType list_level = ListTypeA list_level ⊥ ⊤ super` (`ListExample.v:20`). -/
abbrev ls_ListType {s : Sig} (ll : Path ((s,x),x)) : Ty (s,x) := ls_ListTypeA ll .bot .top ref1
/-- `ListObjType` (`ListExample.v:22-28`), under `sci`. -/
abbrev ls_ListObjType {s : Sig} : Ty (s,x) :=
  .and (.and (tdec ls_List (.mu (ls_ListType ref2)) (.mu (ls_ListType ref2)))
             (fdec ls_Nil (.all (tdec ls_A .bot .top) (.and (.sel ref1 ls_List) (tdec ls_A .bot .bot)))))
    (fdec ls_Cons (.all (tdec ls_A .bot .top)
                    (.all (.sel ref0 ls_A)
                      (.all (.and (.sel ref2 ls_List) (tdec ls_A .bot (.sel ref1 ls_A)))
                        (.and (.sel ref3 ls_List) (tdec ls_A .bot (.sel ref2 ls_A)))))))
/-- The literal of `Nil` (`ListExample.v:35-39`), under `sci` then `x`. -/
abbrev ls_NilLit {s : Sig} : Val ((s,x),x) :=
  .new (ls_ListTypeA ref3 .bot .bot ref1)
    (.cons (.cons (.cons .nil (.typ ls_A .bot))
        (.trm ls_head (.defv (.lam .top (.app (ref1.sel ls_head) ref0)))))
      (.trm ls_tail (.defv (.lam .top (.app (ref1.sel ls_tail) ref0)))))
/-- The literal of `Cons` (`ListExample.v:43-47`), under `sci`, `x`, `y`, `ys`. -/
abbrev ls_ConsLit {s : Sig} : Val ((((s,x),x),x),x) :=
  .new (ls_ListTypeA ref5 (.sel ref3 ls_A) (.sel ref3 ls_A) ref4)
    (.cons (.cons (.cons .nil (.typ ls_A (.sel ref3 ls_A))) (.trm ls_head (lazyRhs (.path ref3))))
      (.trm ls_tail (lazyRhs (.path ref2))))
/-- The definitions of the library (`ListExample.v:32-47`), under `sci`. -/
abbrev ls_defs {s : Sig} : Defs (s,x) :=
  .cons (.cons (.cons .nil (.typ ls_List (.mu (ls_ListType ref2))))
      (.trm ls_Nil (.defv (.lam (tdec ls_A .bot .top) (letTrm (.val ls_NilLit))))))
    (.trm ls_Cons (.defv (.lam (tdec ls_A .bot .top)
      (.val (.lam (.sel ref0 ls_A)
        (.val (.lam (.and (.sel ref2 ls_List) (tdec ls_A .bot (.sel ref1 ls_A))) (letTrm (.val ls_ConsLit)))))))))

/-- Coq's `t` (`ListExample.v:30-47`). -/
abbrev list_t : Tm [] := .val (.new ls_ListObjType ls_defs)
/-- Coq's type `μ ListObjType` (`ListExample.v:50`). -/
abbrev list_T : Ty [] := .mu ls_ListObjType

/-! ### The template of the opened list type -/

/-- `ListTypeA` opened: `sci` the library, `self` the list, `al` the path whose `A` bounds the
tail's `A`. -/
abbrev ls_listAt {s : Sig} (sci : Path s) (lo hi : Ty s) (self al : Path s) : Ty s :=
  .and (.and (tdec ls_A lo hi) (fdec ls_head (lazyTy (.sel self.weaken ls_A))))
    (fdec ls_tail (lazyTy (.and (.sel sci.weaken ls_List) (tdec ls_A .bot (.sel al.weaken ls_A)))))

/-! ### `Nil` -/

/-- `[sci :ˢ ListObjType]`. -/
abbrev ls_Gsci : Ctx ([],x) := Ctx.nil.consSelf ls_ListObjType
/-- `[sci :ˢ …, x : {A : ⊥..⊤}]`. -/
abbrev ls_Gx : Ctx (([],x),x) := ls_Gsci.cons (tdec ls_A .bot .top)
/-- The annotation of `Nil`'s literal, under `sci`, `x`, `r`. -/
abbrev ls_NilT : Ty ((([],x),x),x) := ls_ListTypeA ref3 .bot .bot ref1
/-- `[sci :ˢ …, x : {A : ⊥..⊤}, r :ˢ NilT]`. -/
abbrev ls_Gnr : Ctx ((([],x),x),x) := ls_Gx.consSelf ls_NilT
/-- `[sci :ˢ …, x : {A : ⊥..⊤}, r :ˢ NilT, u : ⊤]`. -/
abbrev ls_Gnu : Ctx (((([],x),x),x),x) := ls_Gnr.cons .top
/-- `[sci :ˢ …, x : {A : ⊥..⊤}, r : μ(r. NilT)]`. -/
abbrev ls_Gnr2 : Ctx ((([],x),x),x) := ls_Gx.cons (.mu ls_NilT)

-- Gnu ⊢ r : NilT⟨r⟩                                    ty_var
def LS_n_r_u : HasTy ls_Gnu (.path ref1) (ls_listAt ref3 .bot .bot ref1 ref1) := .ty_var rfl
-- Gnr ⊢ λ(u : ⊤). r.head u : Lazy r.A                  ty_all_intro, ty_all_elim at r.head (ty_sub, ty_new_elim)
def LS_n_head : HasTy ls_Gnr (.val (.lam .top (.app (ref1.sel ls_head) ref0))) (lazyTy (.sel ref1 ls_A)) :=
  .ty_all_intro (.ty_all_elim (T := .sel ref2 ls_A)
    (.ty_new_elim (.ty_sub LS_n_r_u (.subtyp_trans .subtyp_and11 .subtyp_and12))) (.ty_var rfl))
-- Gnr ⊢ λ(u : ⊤). r.tail u : Lazy (sci.List ∧ {A : ⊥..r.A})          ty_all_intro, ty_all_elim at r.tail
def LS_n_tail : HasTy ls_Gnr (.val (.lam .top (.app (ref1.sel ls_tail) ref0)))
    (lazyTy (.and (.sel ref3 ls_List) (tdec ls_A .bot (.sel ref1 ls_A)))) :=
  .ty_all_intro (.ty_all_elim (T := .and (.sel ref4 ls_List) (tdec ls_A .bot (.sel ref2 ls_A)))
    (.ty_new_elim (.ty_sub LS_n_r_u .subtyp_and12)) (.ty_var rfl))
-- Gx ⊢ ν(r : NilT) {A = ⊥} ▹ {head = …} ▹ {tail = …} : μ(r. NilT)   ty_def_typ, ty_def_all twice
def LS_nilLit : HasTy ls_Gx (.val ls_NilLit) (.mu ls_NilT) :=
  .ty_new_intro (.ty_defs_cons (.ty_defs_cons (.ty_defs_one .ty_def_typ) (.ty_def_all LS_n_head) rfl)
    (.ty_def_all LS_n_tail) rfl)

-- Gnr2 ⊢ r : NilT⟨r⟩                                   ty_var, ty_rec_elim
def LS_n_open : HasTy ls_Gnr2 (.path ref0) (ls_listAt ref2 .bot .bot ref0 ref0) :=
  .ty_rec_elim (T := ls_listAt ref3 .bot .bot ref0 ref0) (.ty_var rfl)
-- Gnr2 ⊢ r : {A : ⊥..⊥}                                ty_sub by subtyp_and11 twice
def LS_n_A : HasTy ls_Gnr2 (.path ref0) (tdec ls_A .bot .bot) :=
  .ty_sub LS_n_open (.subtyp_trans .subtyp_and11 .subtyp_and11)
-- Gnr2 ⊢ sci : {List : μ(l. LT(l))..μ(l. LT(l))}       ty_var, ty_sub by subtyp_and11 twice
def LS_n_sciList : HasTy ls_Gnr2 (.path ref2)
    (tdec ls_List (.mu (ls_listAt ref3 .bot .top ref0 ref0)) (.mu (ls_listAt ref3 .bot .top ref0 ref0))) :=
  .ty_sub (.ty_var rfl) (.subtyp_trans .subtyp_and11 .subtyp_and11)
-- Gnr2 ⊢ r : μ(l. LT(l))         ty_and_intro of the three components, {A : ⊥..⊥} <: {A : ⊥..⊤}, ty_rec_intro
def LS_n_LT : HasTy ls_Gnr2 (.path ref0) (.mu (ls_listAt ref3 .bot .top ref0 ref0)) :=
  .ty_rec_intro (T := ls_listAt ref3 .bot .top ref0 ref0)
    (.ty_and_intro
      (.ty_and_intro (.ty_sub LS_n_A (.subtyp_typ .subtyp_refl .subtyp_top))
        (.ty_sub LS_n_open (.subtyp_trans .subtyp_and11 .subtyp_and12)))
      (.ty_sub LS_n_open .subtyp_and12))
-- Gnr2 ⊢ r : sci.List ∧ {A : ⊥..⊥}                     ty_sub by subtyp_sel2, ty_and_intro
def LS_n_ret : HasTy ls_Gnr2 (.path ref0) (.and (.sel ref2 ls_List) (tdec ls_A .bot .bot)) :=
  .ty_and_intro (.ty_sub LS_n_LT (.subtyp_sel2 LS_n_sciList)) LS_n_A
-- Gsci ⊢ Nil's lambda : ∀(x : {A : ⊥..⊤}) (sci.List ∧ {A : ⊥..⊥})    ty_all_intro, ty_let
def LS_nil : HasTy ls_Gsci (.val (.lam (tdec ls_A .bot .top) (letTrm (.val ls_NilLit))))
    (.all (tdec ls_A .bot .top) (.and (.sel ref1 ls_List) (tdec ls_A .bot .bot))) :=
  .ty_all_intro (.ty_let LS_nilLit LS_n_ret)

/-! ### `Cons` -/

/-- `[sci :ˢ …, x : {A : ⊥..⊤}, y : x.A]`. -/
abbrev ls_Gy : Ctx ((([],x),x),x) := ls_Gx.cons (.sel ref0 ls_A)
/-- `[sci :ˢ …, x, y, ys : sci.List ∧ {A : ⊥..x.A}]`. -/
abbrev ls_Gys : Ctx (((([],x),x),x),x) := ls_Gy.cons (.and (.sel ref2 ls_List) (tdec ls_A .bot (.sel ref1 ls_A)))
/-- The annotation of `Cons`'s literal, under `sci`, `x`, `y`, `ys`, `r`. -/
abbrev ls_ConsT : Ty ((((([],x),x),x),x),x) := ls_ListTypeA ref5 (.sel ref3 ls_A) (.sel ref3 ls_A) ref4
/-- `[…, ys, r :ˢ ConsT]`. -/
abbrev ls_Gcr : Ctx ((((([],x),x),x),x),x) := ls_Gys.consSelf ls_ConsT
/-- `[…, ys, r :ˢ ConsT, u : ⊤]`. -/
abbrev ls_Gcu : Ctx (((((([],x),x),x),x),x),x) := ls_Gcr.cons .top
/-- `[…, ys, r : μ(r. ConsT)]`. -/
abbrev ls_Gcr2 : Ctx ((((([],x),x),x),x),x) := ls_Gys.cons (.mu ls_ConsT)
/-- `[…, ys, r : μ(r. ConsT), u : ⊤]`. -/
abbrev ls_Gcu2 : Ctx (((((([],x),x),x),x),x),x) := ls_Gcr2.cons .top

-- Gcu ⊢ r : ConsT⟨r⟩                                   ty_var
def LS_c_r_u : HasTy ls_Gcu (.path ref1) (ls_listAt ref5 (.sel ref4 ls_A) (.sel ref4 ls_A) ref1 ref4) := .ty_var rfl
-- Gcr ⊢ λ(u : ⊤). y : Lazy r.A                         ty_all_intro, ty_sub by subtyp_sel2 at r : {A : x.A..x.A}
def LS_c_head : HasTy ls_Gcr (.val (.lam .top (.path ref3))) (lazyTy (.sel ref1 ls_A)) :=
  .ty_all_intro (.ty_sub (.ty_var rfl) (.subtyp_sel2 (.ty_sub LS_c_r_u (.subtyp_trans .subtyp_and11 .subtyp_and11))))
-- Gcr ⊢ λ(u : ⊤). ys : Lazy (sci.List ∧ {A : ⊥..x.A})  ty_all_intro, ty_var
def LS_c_tail : HasTy ls_Gcr (.val (.lam .top (.path ref2)))
    (lazyTy (.and (.sel ref5 ls_List) (tdec ls_A .bot (.sel ref4 ls_A)))) :=
  .ty_all_intro (.ty_var rfl)
-- Gys ⊢ ν(r : ConsT) {A = x.A} ▹ {head = …} ▹ {tail = …} : μ(r. ConsT)   ty_def_typ, ty_def_all twice
def LS_consLit : HasTy ls_Gys (.val ls_ConsLit) (.mu ls_ConsT) :=
  .ty_new_intro (.ty_defs_cons (.ty_defs_cons (.ty_defs_one .ty_def_typ) (.ty_def_all LS_c_head) rfl)
    (.ty_def_all LS_c_tail) rfl)

-- Gcr2 ⊢ r : ConsT⟨r⟩                                  ty_var, ty_rec_elim
def LS_c_open : HasTy ls_Gcr2 (.path ref0) (ls_listAt ref4 (.sel ref3 ls_A) (.sel ref3 ls_A) ref0 ref3) :=
  .ty_rec_elim (T := ls_listAt ref5 (.sel ref4 ls_A) (.sel ref4 ls_A) ref0 ref4) (.ty_var rfl)
-- Gcr2 ⊢ r : {A : x.A..x.A}                            ty_sub by subtyp_and11 twice
def LS_c_A : HasTy ls_Gcr2 (.path ref0) (tdec ls_A (.sel ref3 ls_A) (.sel ref3 ls_A)) :=
  .ty_sub LS_c_open (.subtyp_trans .subtyp_and11 .subtyp_and11)
-- Gcu2 ⊢ r : {A : x.A..x.A}                            ty_var, ty_rec_elim, ty_sub by subtyp_and11 twice
def LS_c_A_u : HasTy ls_Gcu2 (.path ref1) (tdec ls_A (.sel ref4 ls_A) (.sel ref4 ls_A)) :=
  .ty_sub (.ty_rec_elim (T := ls_listAt ref6 (.sel ref5 ls_A) (.sel ref5 ls_A) ref0 ref5) (.ty_var rfl))
    (.subtyp_trans .subtyp_and11 .subtyp_and11)
-- Gcr2 ⊢ {tail : Lazy (sci.List ∧ {A : ⊥..x.A})} <: {tail : Lazy (sci.List ∧ {A : ⊥..r.A})}
--   subtyp_fld, subtyp_all, subtyp_and2, subtyp_typ, subtyp_sel2 at x.A <: r.A
def LS_c_tailSub : Sub ls_Gcr2
    (fdec ls_tail (lazyTy (.and (.sel ref5 ls_List) (tdec ls_A .bot (.sel ref4 ls_A)))))
    (fdec ls_tail (lazyTy (.and (.sel ref5 ls_List) (tdec ls_A .bot (.sel ref1 ls_A))))) :=
  .subtyp_fld (.subtyp_all .subtyp_refl
    (.subtyp_and2 .subtyp_and11 (.subtyp_trans .subtyp_and12 (.subtyp_typ .subtyp_refl (.subtyp_sel2 LS_c_A_u)))))
-- Gcr2 ⊢ r : μ(l. LT(l))         ty_and_intro of the three components, ty_rec_intro
def LS_c_LT : HasTy ls_Gcr2 (.path ref0) (.mu (ls_listAt ref5 .bot .top ref0 ref0)) :=
  .ty_rec_intro (T := ls_listAt ref5 .bot .top ref0 ref0)
    (.ty_and_intro
      (.ty_and_intro (.ty_sub LS_c_A (.subtyp_typ .subtyp_bot .subtyp_top))
        (.ty_sub LS_c_open (.subtyp_trans .subtyp_and11 .subtyp_and12)))
      (.ty_sub (.ty_sub LS_c_open .subtyp_and12) LS_c_tailSub))
-- Gcr2 ⊢ sci : {List : μ(l. LT(l))..μ(l. LT(l))}       ty_var, ty_sub by subtyp_and11 twice
def LS_c_sciList : HasTy ls_Gcr2 (.path ref4)
    (tdec ls_List (.mu (ls_listAt ref5 .bot .top ref0 ref0)) (.mu (ls_listAt ref5 .bot .top ref0 ref0))) :=
  .ty_sub (.ty_var rfl) (.subtyp_trans .subtyp_and11 .subtyp_and11)
-- Gcr2 ⊢ r : sci.List ∧ {A : ⊥..x.A}                   subtyp_sel2, subtyp_typ, ty_and_intro
def LS_c_ret : HasTy ls_Gcr2 (.path ref0) (.and (.sel ref4 ls_List) (tdec ls_A .bot (.sel ref3 ls_A))) :=
  .ty_and_intro (.ty_sub LS_c_LT (.subtyp_sel2 LS_c_sciList)) (.ty_sub LS_c_A (.subtyp_typ .subtyp_bot .subtyp_refl))
-- Gsci ⊢ Cons's lambda : ∀(x : {A : ⊥..⊤}) ∀(y : x.A) ∀(ys : sci.List ∧ {A : ⊥..x.A}) (sci.List ∧ {A : ⊥..x.A})
--   ty_all_intro three times, ty_let
def LS_cons : HasTy ls_Gsci
    (.val (.lam (tdec ls_A .bot .top) (.val (.lam (.sel ref0 ls_A)
      (.val (.lam (.and (.sel ref2 ls_List) (tdec ls_A .bot (.sel ref1 ls_A))) (letTrm (.val ls_ConsLit))))))))
    (.all (tdec ls_A .bot .top) (.all (.sel ref0 ls_A)
      (.all (.and (.sel ref2 ls_List) (tdec ls_A .bot (.sel ref1 ls_A)))
        (.and (.sel ref3 ls_List) (tdec ls_A .bot (.sel ref2 ls_A)))))) :=
  .ty_all_intro (.ty_all_intro (.ty_all_intro (.ty_let LS_consLit LS_c_ret)))

-- ⊢ t : μ ListObjType                                 ty_new_intro, ty_def_typ, ty_def_all twice
def LS_d : HasTy .nil list_t list_T :=
  .ty_new_intro (.ty_defs_cons (.ty_defs_cons (.ty_defs_one .ty_def_typ) (.ty_def_all LS_nil) rfl)
    (.ty_def_all LS_cons) rfl)

/-- `Lemma list_typing : empty ⊢ t : μ ListObjType` (`ListExample.v:49-50`). -/
theorem list_typing : Nonempty (HasTy .nil list_t list_T) := ⟨LS_d⟩

/-! ## E5: `SingletonTypeExample.v` (`:14-32`)

```text
let x = ν(x : {C : μ(c : {incr : c.type})..μ(c : {incr : c.type})}
            ∧ {D : μ(d : x.C ∧ {decr : d.type})..μ(d : x.C ∧ {decr : d.type})}
            ∧ {d : Lazy x.D}) {
  C = μ(c : {incr : c.type}),
  D = μ(d : x.C ∧ {decr : d.type}),
  d = λ(u : ⊤). let o = ν(o : {incr : o.type} ∧ {decr : o.type}) {incr = o, decr = o} in o }
in let z = x.d x in z.incr.decr
```

typed at `μ(o : {incr : o.type} ∧ {decr : o.type})`, the Coq lemma `typecheck`.  The derivation
follows the Coq proof (`SingletonTypeExample.v:33-106`).  The body of `d` returns `o` at `x.D` by
`subtyp_sel2` from `μ(x.C ∧ {decr : o.type})`, built by `ty_rec_intro`.  The result `z.incr.decr` is
typed at `z.type` by `ty_sngl` and `ty_new_elim`, and then at the answer type by `ty_sngl` again.
The hypotheses `C <> D` and `incr <> decr` (`:11-12`) are `sg_labels`. -/

/-- `C`. -/
abbrev sg_C : Label := .typ 0
/-- `D`. -/
abbrev sg_D : Label := .typ 1
/-- `d`. -/
abbrev sg_d : Label := .trm 0
/-- `incr`. -/
abbrev sg_incr : Label := .trm 1
/-- `decr`. -/
abbrev sg_decr : Label := .trm 2

/-- `Hypothesis CD : C <> D` and `Hypothesis di : incr <> decr` (`SingletonTypeExample.v:11-12`). -/
theorem sg_labels : sg_C ≠ sg_D ∧ sg_incr ≠ sg_decr := by decide

/-- `μ(typ_rcd {incr ⦂ {{ this }} })`. -/
abbrev sg_CT {s : Sig} : Ty s := .mu (fdec sg_incr (.sngl ref0))
/-- `μ(super↓C ∧ typ_rcd {decr ⦂ {{ this }} })`, under the self `x` of the literal. -/
abbrev sg_DT {s : Sig} : Ty (s,x) := .mu (.and (.sel ref1 sg_C) (fdec sg_decr (.sngl ref0)))
/-- The annotation of `x`, under `x`: `typ_rcd {C >: … <: …} ∧ typ_rcd {D >: … <: …} ∧
typ_rcd {d ⦂ Lazy (super↓D)}` (`SingletonTypeExample.v:16-20`). -/
abbrev sg_Tx {s : Sig} : Ty (s,x) :=
  .and (.and (tdec sg_C sg_CT sg_CT) (tdec sg_D sg_DT sg_DT)) (fdec sg_d (lazyTy (.sel ref1 sg_D)))
/-- `typ_rcd {incr ⦂ {{ this }} } ∧ typ_rcd {decr ⦂ {{ this }} }`, under its self. -/
abbrev sg_To {s : Sig} : Ty (s,x) := .and (fdec sg_incr (.sngl ref0)) (fdec sg_decr (.sngl ref0))
/-- `defs_nil Λ {incr :=p this} Λ {decr :=p this}`, under its self. -/
abbrev sg_oDefs {s : Sig} : Defs (s,x) :=
  .cons (.cons .nil (.trm sg_incr (.defp ref0))) (.trm sg_decr (.defp ref0))
/-- The definitions of `x` (`SingletonTypeExample.v:21-26`), under `x`. -/
abbrev sg_xDefs {s : Sig} : Defs (s,x) :=
  .cons (.cons (.cons .nil (.typ sg_C sg_CT)) (.typ sg_D sg_DT))
    (.trm sg_d (lazyRhs (letTrm (.val (.new sg_To sg_oDefs)))))

/-- Coq's `t` (`SingletonTypeExample.v:14-28`). -/
abbrev sngl_t : Tm [] :=
  .lett (.val (.new sg_Tx sg_xDefs)) (.lett (.app (ref0.sel sg_d) ref0) (.path ((ref0.sel sg_incr).sel sg_decr)))
/-- Coq's `T` (`SingletonTypeExample.v:30`). -/
abbrev sngl_T : Ty [] := .mu sg_To

/-! ### The literal `x` -/

/-- `[x :ˢ Tx]`. -/
abbrev sg_Gx : Ctx ([],x) := Ctx.nil.consSelf sg_Tx
/-- `[x :ˢ Tx, u : ⊤]`. -/
abbrev sg_Gu : Ctx (([],x),x) := sg_Gx.cons .top
/-- `[x :ˢ Tx, u : ⊤, o : μ(o. To)]`. -/
abbrev sg_Go : Ctx ((([],x),x),x) := sg_Gu.cons (.mu sg_To)

-- Gu ⊢ ν(o : To) {incr = o} ▹ {decr = o} : μ(o. To)     ty_def_path twice at o : To
def SG_oLit : HasTy sg_Gu (.val (.new sg_To sg_oDefs)) (.mu sg_To) :=
  .ty_new_intro (.ty_defs_cons (.ty_defs_one (.ty_def_path (.ty_var rfl))) (.ty_def_path (.ty_var rfl)) rfl)

-- Go ⊢ x : Tx⟨x⟩                                       ty_var
def SG_x_o : HasTy sg_Go (.path ref2) (sg_Tx.substPath ref2) := .ty_var rfl
-- Go ⊢ o : To⟨o⟩                                       ty_var, ty_rec_elim
def SG_o_open : HasTy sg_Go (.path ref0) (sg_To.substPath ref0) := .ty_rec_elim (T := sg_To) (.ty_var rfl)
-- Go ⊢ o : μ(c. {incr : c.type})                       ty_sub by subtyp_and11, ty_rec_intro
def SG_o_CT : HasTy sg_Go (.path ref0) sg_CT :=
  .ty_rec_intro (T := fdec sg_incr (.sngl ref0)) (.ty_sub SG_o_open .subtyp_and11)
-- Go ⊢ o : x.C                                         ty_sub by subtyp_sel2 at x : {C : CT..CT}
def SG_o_xC : HasTy sg_Go (.path ref0) (.sel ref2 sg_C) :=
  .ty_sub SG_o_CT (.subtyp_sel2 (.ty_sub SG_x_o (.subtyp_trans .subtyp_and11 .subtyp_and11)))
-- Go ⊢ o : μ(d. x.C ∧ {decr : d.type})                 ty_and_intro, ty_rec_intro
def SG_o_DT : HasTy sg_Go (.path ref0) (sg_DT.substPath ref2) :=
  .ty_rec_intro (T := .and (.sel ref3 sg_C) (fdec sg_decr (.sngl ref0)))
    (.ty_and_intro SG_o_xC (.ty_sub SG_o_open .subtyp_and12))
-- Go ⊢ o : x.D                                         ty_sub by subtyp_sel2 at x : {D : DT..DT}
def SG_o_xD : HasTy sg_Go (.path ref0) (.sel ref2 sg_D) :=
  .ty_sub SG_o_DT (.subtyp_sel2 (.ty_sub SG_x_o (.subtyp_trans .subtyp_and11 .subtyp_and12)))

-- Gx ⊢ λ(u : ⊤). let o = ν(o : To) … in o : Lazy x.D   ty_all_intro, ty_let
def SG_dDef : HasTy sg_Gx (.val (.lam .top (letTrm (.val (.new sg_To sg_oDefs))))) (lazyTy (.sel ref1 sg_D)) :=
  .ty_all_intro (.ty_let SG_oLit SG_o_xD)

-- ⊢ ν(x : Tx) {C = …} ▹ {D = …} ▹ {d = …} : μ(x. Tx)   ty_def_typ twice, ty_def_all
def SG_xLit : HasTy .nil (.val (.new sg_Tx sg_xDefs)) (.mu sg_Tx) :=
  .ty_new_intro (.ty_defs_cons (.ty_defs_cons (.ty_defs_one .ty_def_typ) .ty_def_typ rfl) (.ty_def_all SG_dDef) rfl)

/-! ### The body `let z = x.d x in z.incr.decr` -/

/-- `[x : μ(x. Tx)]`. -/
abbrev sg_G1 : Ctx ([],x) := Ctx.nil.cons (.mu sg_Tx)
/-- `[x : μ(x. Tx), z : x.D]`. -/
abbrev sg_G2 : Ctx (([],x),x) := sg_G1.cons (.sel ref0 sg_D)

-- G1 ⊢ x.d : Lazy x.D                                  ty_var, ty_rec_elim, ty_sub by subtyp_and12, ty_new_elim
def SG_xd : HasTy sg_G1 (.path (ref0.sel sg_d)) (lazyTy (.sel ref1 sg_D)) :=
  .ty_new_elim (.ty_sub (.ty_rec_elim (T := sg_Tx) (.ty_var rfl)) .subtyp_and12)
-- G1 ⊢ x.d x : x.D                                     ty_all_elim, with x : ⊤ by ty_sub by subtyp_top
def SG_app : HasTy sg_G1 (.app (ref0.sel sg_d) ref0) (.sel ref0 sg_D) :=
  .ty_all_elim (T := .sel ref1 sg_D) SG_xd (.ty_sub (.ty_var rfl) .subtyp_top)

-- G2 ⊢ x : Tx⟨x⟩                                       ty_var, ty_rec_elim
def SG_x_z : HasTy sg_G2 (.path ref1) (sg_Tx.substPath ref1) := .ty_rec_elim (T := sg_Tx) (.ty_var rfl)
-- G2 ⊢ z : μ(d. x.C ∧ {decr : d.type})                 ty_var, ty_sub by subtyp_sel1 at x : {D : DT..DT}
def SG_z_DT : HasTy sg_G2 (.path ref0) (sg_DT.substPath ref1) :=
  .ty_sub (.ty_var rfl) (.subtyp_sel1 (.ty_sub SG_x_z (.subtyp_trans .subtyp_and11 .subtyp_and12)))
-- G2 ⊢ z : x.C ∧ {decr : z.type}                       ty_rec_elim
def SG_z_open : HasTy sg_G2 (.path ref0) (.and (.sel ref1 sg_C) (fdec sg_decr (.sngl ref0))) :=
  .ty_rec_elim (T := .and (.sel ref2 sg_C) (fdec sg_decr (.sngl ref0))) SG_z_DT
-- G2 ⊢ z : {incr : z.type}                             ty_sub by subtyp_and11, subtyp_sel1 at x : {C : CT..CT}, ty_rec_elim
def SG_z_incr : HasTy sg_G2 (.path ref0) (fdec sg_incr (.sngl ref0)) :=
  .ty_rec_elim (T := fdec sg_incr (.sngl ref0))
    (.ty_sub (.ty_sub SG_z_open .subtyp_and11)
      (.subtyp_sel1 (.ty_sub SG_x_z (.subtyp_trans .subtyp_and11 .subtyp_and11))))
-- G2 ⊢ z : {decr : z.type}                             ty_sub by subtyp_and12
def SG_z_decr : HasTy sg_G2 (.path ref0) (fdec sg_decr (.sngl ref0)) := .ty_sub SG_z_open .subtyp_and12
-- G2 ⊢ z.incr : {decr : z.type}                        ty_new_elim, ty_sngl
def SG_zi : HasTy sg_G2 (.path (ref0.sel sg_incr)) (fdec sg_decr (.sngl ref0)) :=
  .ty_sngl (.ty_new_elim SG_z_incr) SG_z_decr
-- G2 ⊢ z.incr.decr : z.type                            ty_new_elim
def SG_zid : HasTy sg_G2 (.path ((ref0.sel sg_incr).sel sg_decr)) (.sngl ref0) := .ty_new_elim SG_zi
-- G2 ⊢ z : μ(o. {incr : o.type} ∧ {decr : o.type})      ty_and_intro, ty_rec_intro
def SG_z_T : HasTy sg_G2 (.path ref0) (.mu sg_To) := .ty_rec_intro (T := sg_To) (.ty_and_intro SG_z_incr SG_z_decr)
-- G2 ⊢ z.incr.decr : μ(o. {incr : o.type} ∧ {decr : o.type})            ty_sngl
def SG_ret : HasTy sg_G2 (.path ((ref0.sel sg_incr).sel sg_decr)) (.mu sg_To) := .ty_sngl SG_zid SG_z_T

-- ⊢ t : T                                              ty_let twice
def SG_d : HasTy .nil sngl_t sngl_T := .ty_let SG_xLit (.ty_let SG_app SG_ret)

/-- `Lemma typecheck : empty ⊢ t : T` (`SingletonTypeExample.v:32`). -/
theorem typecheck : Nonempty (HasTy .nil sngl_t sngl_T) := ⟨SG_d⟩

/-! ## E6: gDOT's Fig. 2 in pDOT form (`design-d3.md:1048-1076`)

```text
let options = ν(o : {Option : ⊤..⊤}) { Option = ⊤ } in
let pcore = ν(p : {types : μ(t : Tt)} ∧ {symbols : μ(y : Ty)}) {
  types = ν(t : Tt) {
    Type = ⊤, TypeTop = t.Type, newTypeTop = λ(u : ⊤). u,
    TypeRef = t.Type ∧ {symb : p.symbols.Symbol},
    newTypeRef = λ(s : p.symbols.Symbol). let r = ν(r : {symb : s.type}) { symb = s } in r },
  symbols = ν(y : Ty) {
    Symbol = {tpe : Opt} ∧ {id : Nat},
    newSymbol = λ(u : Opt). λ(i : Nat). let r = ν(r : {tpe : u.type} ∧ {id : i.type}) { tpe = u, id = i } in r } }
in let pc = pcore in pc
Opt = options.Option ∧ {A : ⊥..p.types.Type}, Nat = {n : ⊤}
Tt  = {Type : ⊤..⊤} ∧ {TypeTop : t.Type..t.Type} ∧ {newTypeTop : ∀(u : ⊤) t.TypeTop}
    ∧ {TypeRef : t.Type ∧ {symb : p.symbols.Symbol} .. t.Type ∧ {symb : p.symbols.Symbol}}
    ∧ {newTypeRef : ∀(s : p.symbols.Symbol) t.TypeRef}
Ty  = {Symbol : {tpe : Opt} ∧ {id : Nat} .. {tpe : Opt} ∧ {id : Nat}} ∧ {newSymbol : ∀(u : Opt) ∀(i : Nat) y.Symbol}
```

The constructors return their record at the declared type by `ty_rcd_intro` after `ty_sngl`, then
`subtyp_sel2`.  `pc` is bound at the abstract type `μ(p. {types : μ(t : TtAbs)} ∧ {symbols : μ(y :
TyAbs)})`, where `TtAbs` and `TyAbs` lower every type member's bound to `⊥` (`TypeRef >: ⊥ <: …`).  The
view is taken at the let-bound path `pcore`: `ty_rec_elim`, `ty_new_elim`, `ty_rec_elim` at
`pcore.types`, subsumption on the opened record, `ty_rec_intro`, `ty_rcd_intro`, the same at
`pcore.symbols`, `ty_and_intro` and `ty_rec_intro`, all on paths.  The abstract type mentions the
let-bound `options` through `Opt`, and `ty_let` asks a type free of it, so the program has type `⊤`.
`E6_typed` states both: the view in `[options, pcore]` and the program in the empty context. -/

/-- `Option`. -/
abbrev f2_Option : Label := .typ 0
/-- `Type`. -/
abbrev f2_Type : Label := .typ 1
/-- `TypeTop`. -/
abbrev f2_TypeTop : Label := .typ 2
/-- `TypeRef`. -/
abbrev f2_TypeRef : Label := .typ 3
/-- `Symbol`. -/
abbrev f2_Symbol : Label := .typ 4
/-- `A`. -/
abbrev f2_A : Label := .typ 5
/-- `types`. -/
abbrev f2_types : Label := .trm 0
/-- `symbols`. -/
abbrev f2_symbols : Label := .trm 1
/-- `newTypeTop`. -/
abbrev f2_newTypeTop : Label := .trm 2
/-- `newTypeRef`. -/
abbrev f2_newTypeRef : Label := .trm 3
/-- `symb`. -/
abbrev f2_symb : Label := .trm 4
/-- `newSymbol`. -/
abbrev f2_newSymbol : Label := .trm 5
/-- `tpe`. -/
abbrev f2_tpe : Label := .trm 6
/-- `id`. -/
abbrev f2_id : Label := .trm 7
/-- `n`. -/
abbrev f2_n : Label := .trm 8

/-- `{Option : ⊤..⊤}`. -/
abbrev f2_To {s : Sig} : Ty s := tdec f2_Option .top .top
/-- `Nat = {n : ⊤}`. -/
abbrev f2_Nat {s : Sig} : Ty s := fdec f2_n .top
/-- `Opt = options.Option ∧ {A : ⊥..p.types.Type}`, under `options`, `p`, `y`. -/
abbrev f2_Opt {s : Sig} : Ty (((s,x),x),x) :=
  .and (.sel ref2 f2_Option) (tdec f2_A .bot (.sel (ref1.sel f2_types) f2_Type))
/-- `t.Type ∧ {symb : p.symbols.Symbol}`, under `p` then `t`. -/
abbrev f2_Ref {s : Sig} : Ty ((s,x),x) :=
  .and (.sel ref0 f2_Type) (fdec f2_symb (.sel (ref1.sel f2_symbols) f2_Symbol))
/-- `Tt`, under `p` then `t`. -/
abbrev f2_Tt {s : Sig} : Ty ((s,x),x) :=
  .and (.and (.and (.and (tdec f2_Type .top .top) (tdec f2_TypeTop (.sel ref0 f2_Type) (.sel ref0 f2_Type)))
                   (fdec f2_newTypeTop (.all .top (.sel ref1 f2_TypeTop))))
             (tdec f2_TypeRef f2_Ref f2_Ref))
    (fdec f2_newTypeRef (.all (.sel (ref1.sel f2_symbols) f2_Symbol) (.sel ref1 f2_TypeRef)))
/-- `{tpe : Opt} ∧ {id : Nat}`, under `options`, `p`, `y`. -/
abbrev f2_SymT {s : Sig} : Ty (((s,x),x),x) := .and (fdec f2_tpe f2_Opt) (fdec f2_id f2_Nat)
/-- `Ty`, under `options`, `p`, `y`. -/
abbrev f2_Ty {s : Sig} : Ty (((s,x),x),x) :=
  .and (tdec f2_Symbol f2_SymT f2_SymT) (fdec f2_newSymbol (.all f2_Opt (.all f2_Nat (.sel ref2 f2_Symbol))))
/-- `{types : μ(t : Tt)} ∧ {symbols : μ(y : Ty)}`, under `options` then `p`. -/
abbrev f2_Tp {s : Sig} : Ty ((s,x),x) := .and (fdec f2_types (.mu f2_Tt)) (fdec f2_symbols (.mu f2_Ty))

/-- `ν(r : {symb : s.type}) {symb = s}`, under the parameter `s` of `newTypeRef`. -/
abbrev f2_refLit {s : Sig} : Val (s,x) := .new (fdec f2_symb (.sngl ref1)) (.cons .nil (.trm f2_symb (.defp ref1)))
/-- `ν(r : {tpe : u.type} ∧ {id : i.type}) {tpe = u, id = i}`, under the parameters `u`, `i` of
`newSymbol`. -/
abbrev f2_symLit {s : Sig} : Val ((s,x),x) :=
  .new (.and (fdec f2_tpe (.sngl ref2)) (fdec f2_id (.sngl ref1)))
    (.cons (.cons .nil (.trm f2_tpe (.defp ref2))) (.trm f2_id (.defp ref1)))
/-- The definitions of `types`, under `p` then `t`. -/
abbrev f2_typesDefs {s : Sig} : Defs ((s,x),x) :=
  .cons (.cons (.cons (.cons (.cons .nil (.typ f2_Type .top)) (.typ f2_TypeTop (.sel ref0 f2_Type)))
          (.trm f2_newTypeTop (.defv (.lam .top (.path ref0)))))
        (.typ f2_TypeRef f2_Ref))
    (.trm f2_newTypeRef (.defv (.lam (.sel (ref1.sel f2_symbols) f2_Symbol) (letTrm (.val f2_refLit)))))
/-- The definitions of `symbols`, under `options`, `p`, `y`. -/
abbrev f2_symbolsDefs {s : Sig} : Defs (((s,x),x),x) :=
  .cons (.cons .nil (.typ f2_Symbol f2_SymT))
    (.trm f2_newSymbol (.defv (.lam f2_Opt (.val (.lam f2_Nat (letTrm (.val f2_symLit)))))))
/-- The definitions of `pcore`, under `options` then `p`. -/
abbrev f2_pDefs {s : Sig} : Defs ((s,x),x) :=
  .cons (.cons .nil (.trm f2_types (.defv (.new f2_Tt f2_typesDefs))))
    (.trm f2_symbols (.defv (.new f2_Ty f2_symbolsDefs)))

/-- The program E6. -/
abbrev E6_prog : Tm [] :=
  .lett (.val (.new f2_To (.cons .nil (.typ f2_Option .top))))
    (.lett (.val (.new f2_Tp f2_pDefs)) (.lett (.path ref0) (.path ref0)))

/-! ### Templates of the opened types -/

/-- `t.Type ∧ {symb : p.symbols.Symbol}` with `p` and `t` paths. -/
abbrev f2_RefAt {s : Sig} (p t : Path s) : Ty s :=
  .and (.sel t f2_Type) (fdec f2_symb (.sel (p.sel f2_symbols) f2_Symbol))
/-- `Tt` with `p` and `t` paths. -/
abbrev f2_TtAt {s : Sig} (p t : Path s) : Ty s :=
  .and (.and (.and (.and (tdec f2_Type .top .top) (tdec f2_TypeTop (.sel t f2_Type) (.sel t f2_Type)))
                   (fdec f2_newTypeTop (.all .top (.sel t.weaken f2_TypeTop))))
             (tdec f2_TypeRef (f2_RefAt p t) (f2_RefAt p t)))
    (fdec f2_newTypeRef (.all (.sel (p.sel f2_symbols) f2_Symbol) (.sel t.weaken f2_TypeRef)))
/-- `Opt` with `options` and `p` paths. -/
abbrev f2_OptAt {s : Sig} (o p : Path s) : Ty s :=
  .and (.sel o f2_Option) (tdec f2_A .bot (.sel (p.sel f2_types) f2_Type))
/-- `{tpe : Opt} ∧ {id : Nat}` with `options` and `p` paths. -/
abbrev f2_SymTAt {s : Sig} (o p : Path s) : Ty s := .and (fdec f2_tpe (f2_OptAt o p)) (fdec f2_id f2_Nat)
/-- `Ty` with `options`, `p` and `y` paths. -/
abbrev f2_TyAt {s : Sig} (o p y : Path s) : Ty s :=
  .and (tdec f2_Symbol (f2_SymTAt o p) (f2_SymTAt o p))
    (fdec f2_newSymbol (.all (f2_OptAt o p) (.all f2_Nat (.sel y.weaken.weaken f2_Symbol))))
/-- The body of `pcore`'s type with `options` and `p` paths. -/
abbrev f2_TpAt {s : Sig} (o p : Path s) : Ty s :=
  .and (fdec f2_types (.mu (f2_TtAt p.weaken ref0))) (fdec f2_symbols (.mu (f2_TyAt o.weaken p.weaken ref0)))
/-- `TtAbs`: `Tt` with every type member's lower bound `⊥`. -/
abbrev f2_TtAbsAt {s : Sig} (p t : Path s) : Ty s :=
  .and (.and (.and (.and (tdec f2_Type .bot .top) (tdec f2_TypeTop .bot (.sel t f2_Type)))
                   (fdec f2_newTypeTop (.all .top (.sel t.weaken f2_TypeTop))))
             (tdec f2_TypeRef .bot (f2_RefAt p t)))
    (fdec f2_newTypeRef (.all (.sel (p.sel f2_symbols) f2_Symbol) (.sel t.weaken f2_TypeRef)))
/-- `TyAbs`: `Ty` with `Symbol >: ⊥`. -/
abbrev f2_TyAbsAt {s : Sig} (o p y : Path s) : Ty s :=
  .and (tdec f2_Symbol .bot (f2_SymTAt o p))
    (fdec f2_newSymbol (.all (f2_OptAt o p) (.all f2_Nat (.sel y.weaken.weaken f2_Symbol))))
/-- The abstract body `{types : μ(t : TtAbs)} ∧ {symbols : μ(y : TyAbs)}`. -/
abbrev f2_AbsAt {s : Sig} (o p : Path s) : Ty s :=
  .and (fdec f2_types (.mu (f2_TtAbsAt p.weaken ref0))) (fdec f2_symbols (.mu (f2_TyAbsAt o.weaken p.weaken ref0)))

/-! ### The module `types` -/

/-- `[options : μ(o. {Option : ⊤..⊤})]`. -/
abbrev f2_Gopt : Ctx ([],x) := Ctx.nil.cons (.mu f2_To)
/-- `[options, p :ˢ Tp]`. -/
abbrev f2_Gp : Ctx (([],x),x) := f2_Gopt.consSelf f2_Tp
/-- `[options, p :ˢ Tp, u : ⊤]`. -/
abbrev f2_Gtu : Ctx ((([],x),x),x) := f2_Gp.cons .top
/-- `[options, p :ˢ Tp, s : p.symbols.Symbol]`. -/
abbrev f2_Gs : Ctx ((([],x),x),x) := f2_Gp.cons (.sel (ref0.sel f2_symbols) f2_Symbol)
/-- `[options, p :ˢ Tp, s : p.symbols.Symbol, r : μ(r. {symb : s.type})]`. -/
abbrev f2_Gsr : Ctx (((([],x),x),x),x) := f2_Gs.cons (.mu (fdec f2_symb (.sngl ref1)))

-- Gtu ⊢ p.types : Tt⟨p.types⟩                          ty_var, ty_sub by subtyp_and11, ty_new_elim, ty_rec_elim
def F2_ptypes_tu : HasTy f2_Gtu (.path (ref1.sel f2_types)) (f2_TtAt ref1 (ref1.sel f2_types)) :=
  .ty_rec_elim (T := f2_TtAt ref2 ref0) (.ty_new_elim (.ty_sub (.ty_var rfl) .subtyp_and11))
-- Gp ⊢ λ(u : ⊤). u : ∀(u : ⊤) p.types.TypeTop
--   ty_all_intro, ty_sub by ⊤ <: p.types.Type <: p.types.TypeTop (subtyp_sel2 twice)
def F2_newTypeTop : HasTy f2_Gp (.val (.lam .top (.path ref0))) (.all .top (.sel (ref1.sel f2_types) f2_TypeTop)) :=
  .ty_all_intro (.ty_sub (.ty_var rfl)
    (.subtyp_trans (.subtyp_sel2 (.ty_sub F2_ptypes_tu (Sub.andProj _ 4)))
      (.subtyp_sel2 (.ty_sub F2_ptypes_tu (Sub.andProj _ 3)))))

-- Gs ⊢ ν(r : {symb : s.type}) {symb = s} : μ(r. {symb : s.type})   ty_def_path at s
def F2_refLit : HasTy f2_Gs (.val f2_refLit) (.mu (fdec f2_symb (.sngl ref1))) :=
  .ty_new_intro (.ty_defs_one (.ty_def_path (.ty_var rfl)))
-- Gsr ⊢ p.types : Tt⟨p.types⟩                          ty_var, ty_sub by subtyp_and11, ty_new_elim, ty_rec_elim
def F2_ptypes_sr : HasTy f2_Gsr (.path (ref2.sel f2_types)) (f2_TtAt ref2 (ref2.sel f2_types)) :=
  .ty_rec_elim (T := f2_TtAt ref3 ref0) (.ty_new_elim (.ty_sub (.ty_var rfl) .subtyp_and11))
-- Gsr ⊢ r : p.types.Type                               ty_sub by ⊤ <: p.types.Type (subtyp_top, subtyp_sel2)
def F2_r_Type : HasTy f2_Gsr (.path ref0) (.sel (ref2.sel f2_types) f2_Type) :=
  .ty_sub (.ty_var rfl) (.subtyp_trans .subtyp_top (.subtyp_sel2 (.ty_sub F2_ptypes_sr (Sub.andProj _ 4))))
-- Gsr ⊢ r : {symb : p.symbols.Symbol}                  ty_rec_elim, ty_new_elim, ty_sngl at s, ty_rcd_intro
def F2_r_symb : HasTy f2_Gsr (.path ref0) (fdec f2_symb (.sel (ref2.sel f2_symbols) f2_Symbol)) :=
  .ty_rcd_intro (.ty_sngl (.ty_new_elim (.ty_rec_elim (T := fdec f2_symb (.sngl ref2)) (.ty_var rfl))) (.ty_var rfl))
-- Gsr ⊢ r : p.types.TypeRef                            ty_and_intro, ty_sub by subtyp_sel2 at {TypeRef : …}
def F2_r_ret : HasTy f2_Gsr (.path ref0) (.sel (ref2.sel f2_types) f2_TypeRef) :=
  .ty_sub (.ty_and_intro F2_r_Type F2_r_symb) (.subtyp_sel2 (.ty_sub F2_ptypes_sr (Sub.andProj _ 1)))
-- Gp ⊢ λ(s : p.symbols.Symbol). let r = … in r : ∀(s : p.symbols.Symbol) p.types.TypeRef   ty_all_intro, ty_let
def F2_newTypeRef : HasTy f2_Gp (.val (.lam (.sel (ref0.sel f2_symbols) f2_Symbol) (letTrm (.val f2_refLit))))
    (.all (.sel (ref0.sel f2_symbols) f2_Symbol) (.sel (ref1.sel f2_types) f2_TypeRef)) :=
  .ty_all_intro (.ty_let F2_refLit F2_r_ret)

/-! ### The module `symbols` -/

/-- `[options, p :ˢ Tp, u : Opt]`. -/
abbrev f2_Gu : Ctx ((([],x),x),x) := f2_Gp.cons (f2_OptAt ref1 ref0)
/-- `[options, p :ˢ Tp, u : Opt, i : Nat]`. -/
abbrev f2_Gi : Ctx (((([],x),x),x),x) := f2_Gu.cons f2_Nat
/-- `[options, p :ˢ Tp, u : Opt, i : Nat, r : μ(r. {tpe : u.type} ∧ {id : i.type})]`. -/
abbrev f2_Gir : Ctx ((((([],x),x),x),x),x) :=
  f2_Gi.cons (.mu (.and (fdec f2_tpe (.sngl ref2)) (fdec f2_id (.sngl ref1))))

-- Gi ⊢ ν(r : {tpe : u.type} ∧ {id : i.type}) {tpe = u, id = i} : μ(r. …)   ty_def_path twice
def F2_symLit : HasTy f2_Gi (.val f2_symLit) (.mu (.and (fdec f2_tpe (.sngl ref2)) (fdec f2_id (.sngl ref1)))) :=
  .ty_new_intro (.ty_defs_cons (.ty_defs_one (.ty_def_path (.ty_var rfl))) (.ty_def_path (.ty_var rfl)) rfl)
-- Gir ⊢ p.symbols : Ty⟨p.symbols⟩                      ty_var, ty_sub by subtyp_and12, ty_new_elim, ty_rec_elim
def F2_psym_ir : HasTy f2_Gir (.path (ref3.sel f2_symbols)) (f2_TyAt ref4 ref3 (ref3.sel f2_symbols)) :=
  .ty_rec_elim (T := f2_TyAt ref5 ref4 ref0) (.ty_new_elim (.ty_sub (.ty_var rfl) .subtyp_and12))
-- Gir ⊢ r : {tpe : u.type} ∧ {id : i.type}              ty_var, ty_rec_elim
def F2_r_ir : HasTy f2_Gir (.path ref0) (.and (fdec f2_tpe (.sngl ref2)) (fdec f2_id (.sngl ref1))) :=
  .ty_rec_elim (T := .and (fdec f2_tpe (.sngl ref3)) (fdec f2_id (.sngl ref2))) (.ty_var rfl)
-- Gir ⊢ r : {tpe : Opt} ∧ {id : Nat}       ty_new_elim, ty_sngl at u and at i, ty_rcd_intro, ty_and_intro
def F2_r_SymT : HasTy f2_Gir (.path ref0) (f2_SymTAt ref4 ref3) :=
  .ty_and_intro
    (.ty_rcd_intro (.ty_sngl (.ty_new_elim (.ty_sub F2_r_ir .subtyp_and11)) (.ty_var rfl)))
    (.ty_rcd_intro (.ty_sngl (.ty_new_elim (.ty_sub F2_r_ir .subtyp_and12)) (.ty_var rfl)))
-- Gir ⊢ r : p.symbols.Symbol                          ty_sub by subtyp_sel2 at {Symbol : SymT..SymT}
def F2_r_sym : HasTy f2_Gir (.path ref0) (.sel (ref3.sel f2_symbols) f2_Symbol) :=
  .ty_sub F2_r_SymT (.subtyp_sel2 (.ty_sub F2_psym_ir .subtyp_and11))
-- Gp ⊢ λ(u : Opt). λ(i : Nat). let r = … in r : ∀(u : Opt) ∀(i : Nat) p.symbols.Symbol
--   ty_all_intro twice, ty_let
def F2_newSymbol : HasTy f2_Gp (.val (.lam (f2_OptAt ref1 ref0) (.val (.lam f2_Nat (letTrm (.val f2_symLit))))))
    (.all (f2_OptAt ref1 ref0) (.all f2_Nat (.sel (ref2.sel f2_symbols) f2_Symbol))) :=
  .ty_all_intro (.ty_all_intro (.ty_let F2_symLit F2_r_sym))

/-! ### The two literals -/

-- ⊢ ν(o : {Option : ⊤..⊤}) {Option = ⊤} : μ(o. {Option : ⊤..⊤})    ty_def_typ
def F2_oLit : HasTy .nil (.val (.new f2_To (.cons .nil (.typ f2_Option .top)))) (.mu f2_To) :=
  .ty_new_intro (.ty_defs_one .ty_def_typ)

-- Gopt ⊢ ν(p : Tp) {types = …} ▹ {symbols = …} : μ(p. Tp)
--   ty_def_new at p.types (ty_def_typ, ty_def_typ, ty_def_all, ty_def_typ, ty_def_all)
--   and at p.symbols (ty_def_typ, ty_def_all)
def F2_pLit : HasTy f2_Gopt (.val (.new f2_Tp f2_pDefs)) (.mu f2_Tp) :=
  .ty_new_intro (.ty_defs_cons
    (.ty_defs_one (.ty_def_new rfl
      (.ty_defs_cons
        (.ty_defs_cons
          (.ty_defs_cons (.ty_defs_cons (.ty_defs_one .ty_def_typ) .ty_def_typ rfl) (.ty_def_all F2_newTypeTop) rfl)
          .ty_def_typ rfl)
        (.ty_def_all F2_newTypeRef) rfl)))
    (.ty_def_new rfl (.ty_defs_cons (.ty_defs_one .ty_def_typ) (.ty_def_all F2_newSymbol) rfl)) rfl)

/-! ### The abstract view at the let-bound `pcore` -/

/-- `[options, pcore : μ(p. Tp)]`. -/
abbrev f2_Gpc : Ctx (([],x),x) := f2_Gopt.cons (.mu f2_Tp)

-- Gpc ⊢ pcore : Tp⟨pcore⟩                              ty_var, ty_rec_elim
def F2_pc_open : HasTy f2_Gpc (.path ref0) (f2_TpAt ref1 ref0) := .ty_rec_elim (T := f2_TpAt ref2 ref0) (.ty_var rfl)
-- Gpc ⊢ pcore.types : Tt⟨pcore.types⟩                  ty_sub by subtyp_and11, ty_new_elim, ty_rec_elim
def F2_pct_open : HasTy f2_Gpc (.path (ref0.sel f2_types)) (f2_TtAt ref0 (ref0.sel f2_types)) :=
  .ty_rec_elim (T := f2_TtAt ref1 ref0) (.ty_new_elim (.ty_sub F2_pc_open .subtyp_and11))
-- G ⊢ Tt <: TtAbs           subtyp_and2 of the components, subtyp_typ by subtyp_bot at each type member
def F2_TtAbsSub {s : Sig} {G : Ctx s} (p t : Path s) : Sub G (f2_TtAt p t) (f2_TtAbsAt p t) :=
  .subtyp_and2
    (.subtyp_and2
      (.subtyp_and2
        (.subtyp_and2 (.subtyp_trans (Sub.andProj _ 4) (.subtyp_typ .subtyp_bot .subtyp_refl))
          (.subtyp_trans (Sub.andProj _ 3) (.subtyp_typ .subtyp_bot .subtyp_refl)))
        (Sub.andProj _ 2))
      (.subtyp_trans (Sub.andProj _ 1) (.subtyp_typ .subtyp_bot .subtyp_refl)))
    (Sub.andProj _ 0)
-- Gpc ⊢ pcore.types : μ(t. TtAbs)                      ty_sub, ty_rec_intro
def F2_pct_abs : HasTy f2_Gpc (.path (ref0.sel f2_types)) (.mu (f2_TtAbsAt ref1 ref0)) :=
  .ty_rec_intro (T := f2_TtAbsAt ref1 ref0) (.ty_sub F2_pct_open (F2_TtAbsSub _ _))
-- Gpc ⊢ pcore.symbols : Ty⟨pcore.symbols⟩              ty_sub by subtyp_and12, ty_new_elim, ty_rec_elim
def F2_pcy_open : HasTy f2_Gpc (.path (ref0.sel f2_symbols)) (f2_TyAt ref1 ref0 (ref0.sel f2_symbols)) :=
  .ty_rec_elim (T := f2_TyAt ref2 ref1 ref0) (.ty_new_elim (.ty_sub F2_pc_open .subtyp_and12))
-- Gpc ⊢ pcore.symbols : μ(y. TyAbs)                    ty_sub by subtyp_and2 and subtyp_typ, ty_rec_intro
def F2_pcy_abs : HasTy f2_Gpc (.path (ref0.sel f2_symbols)) (.mu (f2_TyAbsAt ref2 ref1 ref0)) :=
  .ty_rec_intro (T := f2_TyAbsAt ref2 ref1 ref0)
    (.ty_sub F2_pcy_open (.subtyp_and2 (.subtyp_trans .subtyp_and11 (.subtyp_typ .subtyp_bot .subtyp_refl)) .subtyp_and12))
-- Gpc ⊢ pcore : μ(p. {types : μ(t. TtAbs)} ∧ {symbols : μ(y. TyAbs)})   ty_rcd_intro twice, ty_and_intro, ty_rec_intro
def F2_pc_abs : HasTy f2_Gpc (.path ref0) (.mu (f2_AbsAt ref2 ref0)) :=
  .ty_rec_intro (T := f2_AbsAt ref2 ref0) (.ty_and_intro (.ty_rcd_intro F2_pct_abs) (.ty_rcd_intro F2_pcy_abs))
-- Gpc ⊢ let pc = pcore in pc : μ(p. …abstract…)         ty_let, ty_var
def F2_view : HasTy f2_Gpc (.lett (.path ref0) (.path ref0)) (.mu (f2_AbsAt ref2 ref0)) :=
  .ty_let F2_pc_abs (.ty_var rfl)

-- Gopt ⊢ let pcore = ν(p : Tp) … in let pc = pcore in pc : μ(p. …abstract…)      ty_let
def F2_mid : HasTy f2_Gopt (.lett (.val (.new f2_Tp f2_pDefs)) (.lett (.path ref0) (.path ref0)))
    (.mu (f2_AbsAt ref1 ref0)) :=
  .ty_let F2_pLit F2_view
-- ⊢ E6 : ⊤                                             ty_let, ty_sub by subtyp_top before the let of options closes
def F2_d : HasTy .nil E6_prog .top := .ty_let F2_oLit (.ty_sub F2_mid .subtyp_top)

/-- `let pc = pcore in pc` binds `pc` at the abstract type, and the program is typed. -/
theorem E6_typed :
    Nonempty (HasTy f2_Gpc (.lett (.path ref0) (.path ref0)) (.mu (f2_AbsAt ref2 ref0))) ∧
    Nonempty (HasTy .nil E6_prog .top) :=
  ⟨⟨F2_view⟩, ⟨F2_d⟩⟩

/-! ## E7: a module alias used as a prefix (`design-d3.md:1078-1090`)

```text
let core = ν(c : {types : μ(t : {A : ⊤..⊤} ∧ {f : ∀(u : ⊤) ⊤})} ∧ {m : (c.types).type}) {
  types = ν(t : {A : ⊤..⊤} ∧ {f : ∀(u : ⊤) ⊤}) { A = ⊤, f = λ(u : ⊤). u },
  m = c.types }
in core.m.f core
```

`core.m : (core.types).type` by `ty_rec_elim`, `ty_sub` and `ty_new_elim`.  Then
`core.m.f : (core.types.f).type` by `ty_path_elim`, and `core.m.f : ∀(u : ⊤) ⊤` by `ty_sngl`.  The
program has type `⊤`. -/

/-- The field `types`. -/
abbrev e7_types : Label := .trm 0
/-- The field `f`. -/
abbrev e7_f : Label := .trm 1
/-- The field `m`. -/
abbrev e7_m : Label := .trm 2
/-- The type member `A`. -/
abbrev e7_A : Label := .typ 0

/-- `{A : ⊤..⊤} ∧ {f : ∀(u : ⊤) ⊤}`. -/
abbrev e7_Tt {s : Sig} : Ty s := .and (tdec e7_A .top .top) (fdec e7_f (.all .top .top))
/-- `{types : μ(t : …)} ∧ {m : (c.types).type}`, under `c`. -/
abbrev e7_Tc {s : Sig} : Ty (s,x) := .and (fdec e7_types (.mu e7_Tt)) (fdec e7_m (.sngl (ref0.sel e7_types)))
/-- `{A = ⊤} ▹ {f = λ(u : ⊤). u}`, under `t`. -/
abbrev e7_typesDefs {s : Sig} : Defs (s,x) :=
  .cons (.cons .nil (.typ e7_A .top)) (.trm e7_f (.defv (.lam .top (.path ref0))))
/-- `{types = ν(t : …) …} ▹ {m = c.types}`, under `c`. -/
abbrev e7_coreDefs {s : Sig} : Defs (s,x) :=
  .cons (.cons .nil (.trm e7_types (.defv (.new e7_Tt e7_typesDefs)))) (.trm e7_m (.defp (ref0.sel e7_types)))

/-- The program E7. -/
abbrev E7_prog : Tm [] :=
  .lett (.val (.new e7_Tc e7_coreDefs)) (.app ((ref0.sel e7_m).sel e7_f) ref0)

-- [c :ˢ Tc] ⊢ c.types : μ(t. …)                     ty_var, ty_sub by subtyp_and11, ty_new_elim
def E7_ctypes : HasTy (Ctx.nil.consSelf e7_Tc) (.path (ref0.sel e7_types)) (.mu e7_Tt) :=
  .ty_new_elim (.ty_sub (.ty_var rfl) .subtyp_and11)

-- ⊢ ν(c : Tc) {types = …} ▹ {m = c.types} : μ(c. Tc)
--   ty_def_new at c.types (ty_def_typ, ty_def_all), ty_def_path at c.types
def E7_lit : HasTy .nil (.val (.new e7_Tc e7_coreDefs)) (.mu e7_Tc) :=
  .ty_new_intro (.ty_defs_cons
    (.ty_defs_one (.ty_def_new rfl
      (.ty_defs_cons (.ty_defs_one .ty_def_typ) (.ty_def_all (.ty_all_intro (.ty_var rfl))) rfl)))
    (.ty_def_path E7_ctypes) rfl)

/-- `[core : μ(c. Tc)]`. -/
abbrev e7_G : Ctx ([],x) := Ctx.nil.cons (.mu e7_Tc)

-- G ⊢ core : Tc⟨core⟩                                  ty_var, ty_rec_elim
def E7_core : HasTy e7_G (.path ref0) (e7_Tc.substPath ref0) := .ty_rec_elim (T := e7_Tc) (.ty_var rfl)
-- G ⊢ core.m : (core.types).type                       ty_sub by subtyp_and12, ty_new_elim
def E7_m : HasTy e7_G (.path (ref0.sel e7_m)) (.sngl (ref0.sel e7_types)) :=
  .ty_new_elim (.ty_sub E7_core .subtyp_and12)
-- G ⊢ core.types.f : ∀(u : ⊤) ⊤                        ty_sub, ty_new_elim, ty_rec_elim, ty_sub, ty_new_elim
def E7_types_f : HasTy e7_G (.path ((ref0.sel e7_types).sel e7_f)) (.all .top .top) :=
  .ty_new_elim (.ty_sub (.ty_rec_elim (T := e7_Tt) (.ty_new_elim (.ty_sub E7_core .subtyp_and11))) .subtyp_and12)
-- G ⊢ core.m.f : (core.types.f).type                   ty_path_elim
def E7_m_f_sngl : HasTy e7_G (.path ((ref0.sel e7_m).sel e7_f)) (.sngl ((ref0.sel e7_types).sel e7_f)) :=
  .ty_path_elim E7_m E7_types_f
-- G ⊢ core.m.f : ∀(u : ⊤) ⊤                            ty_sngl
def E7_m_f : HasTy e7_G (.path ((ref0.sel e7_m).sel e7_f)) (.all .top .top) := .ty_sngl E7_m_f_sngl E7_types_f
-- G ⊢ core.m.f core : ⊤                                ty_all_elim, with core : ⊤ by ty_sub by subtyp_top
def E7_app : HasTy e7_G (.app ((ref0.sel e7_m).sel e7_f) ref0) .top :=
  .ty_all_elim (T := .top) E7_m_f (.ty_sub (.ty_var rfl) .subtyp_top)

-- ⊢ let core = ν(c : Tc) … in core.m.f core : ⊤          ty_let
def E7_d : HasTy .nil E7_prog .top := .ty_let E7_lit E7_app

theorem E7_typed : Nonempty (HasTy .nil E7_prog .top) := ⟨E7_d⟩

/-! ## E8: replacement at an abstract member (`design-d3.md:1092-1108`)

```text
let g = λ(x : {A : ⊥..⊤} ∧ {f : ∀(u : ⊤) ⊤}). λ(y : x.type). λ(v : y.A). let w = y.f v in v in
let o = ν(o : {A : ⊤..⊤} ∧ {f : ∀(u : ⊤) ⊤} ∧ {me : o.type}) { A = ⊤, f = λ(u : ⊤). u, me = o } in
let h = g o in let k = h o.me in k o
```

`g` is typed at `∀(x : {A : ⊥..⊤} ∧ {f : ∀(u : ⊤) ⊤}) ∀(y : x.type) ∀(v : y.A) x.A`.  In its body,
`y.f : ∀(u : ⊤) ⊤` by `ty_path_elim` and `ty_sngl`, and `v : x.A` by `subtyp_sngl_pq` at
`y ↦ x ⊢ y.A ⇝ x.A`, where `A` is abstract in `x`'s type (`E8_v_xA`).  The last application `k o` asks
`o : o.me.A`, which holds by `subtyp_sel2` at `o.A` and then `subtyp_sngl_qp` at `o ↦ o.me ⊢ o.A ⇝ o.me.A`
(`E8_o_omeA`).  `k o : o.A` mentions the let-bound `o`, and `ty_let` asks a type free of it, so the
derivation lifts `o.A` to `⊤` by `subtyp_sel1` before the `let` of `o` closes.  The program has type
`⊤`. -/

/-- The type member `A`. -/
abbrev e8_A : Label := .typ 0
/-- The field `f`. -/
abbrev e8_f : Label := .trm 0
/-- The field `me`. -/
abbrev e8_me : Label := .trm 1

/-- `{A : ⊥..⊤} ∧ {f : ∀(u : ⊤) ⊤}`, the type of `x`. -/
abbrev e8_X {s : Sig} : Ty s := .and (tdec e8_A .bot .top) (fdec e8_f (.all .top .top))
/-- `∀(x : X) ∀(y : x.type) ∀(v : y.A) x.A`, the type of `g`. -/
abbrev e8_Tg {s : Sig} : Ty s := .all e8_X (.all (.sngl ref0) (.all (.sel ref0 e8_A) (.sel ref2 e8_A)))
/-- `λ(x : X). λ(y : x.type). λ(v : y.A). let w = y.f v in v`. -/
abbrev e8_g {s : Sig} : Val s :=
  .lam e8_X (.val (.lam (.sngl ref0) (.val (.lam (.sel ref0 e8_A) (.lett (.app (ref1.sel e8_f) ref0) (.path ref1))))))
/-- `({A : ⊤..⊤} ∧ {f : ∀(u : ⊤) ⊤}) ∧ {me : o.type}`, under `o`. -/
abbrev e8_To {s : Sig} : Ty (s,x) :=
  .and (.and (tdec e8_A .top .top) (fdec e8_f (.all .top .top))) (fdec e8_me (.sngl ref0))
/-- `{A = ⊤} ▹ {f = λ(u : ⊤). u} ▹ {me = o}`, under `o`. -/
abbrev e8_oDefs {s : Sig} : Defs (s,x) :=
  .cons (.cons (.cons .nil (.typ e8_A .top)) (.trm e8_f (.defv (.lam .top (.path ref0))))) (.trm e8_me (.defp ref0))
/-- `let h = g o in let k = h o.me in k o`, under `g` then `o`. -/
abbrev e8_tail {s : Sig} : Tm ((s,x),x) :=
  .lett (.app ref1 ref0) (.lett (.app ref0 (ref1.sel e8_me)) (.app ref0 ref2))

/-- The program E8. -/
abbrev E8_prog : Tm [] := .lett (.val e8_g) (.lett (.val (.new e8_To e8_oDefs)) e8_tail)

/-! ### The function `g` -/

/-- `[x : X, y : x.type, v : y.A]`. -/
abbrev e8_Gv : Ctx ((([],x),x),x) := ((Ctx.nil.cons e8_X).cons (.sngl ref0)).cons (.sel ref0 e8_A)
/-- `[x : X, y : x.type, v : y.A, w : ⊤]`. -/
abbrev e8_Gw : Ctx (((([],x),x),x),x) := e8_Gv.cons .top

-- Gv ⊢ x.f : ∀(u : ⊤) ⊤                                ty_var, ty_sub by subtyp_and12, ty_new_elim
def E8_xf : HasTy e8_Gv (.path (ref2.sel e8_f)) (.all .top .top) :=
  .ty_new_elim (.ty_sub (.ty_var rfl) .subtyp_and12)
-- Gv ⊢ y.f : (x.f).type                                ty_path_elim at y : x.type
def E8_yf_sngl : HasTy e8_Gv (.path (ref1.sel e8_f)) (.sngl (ref2.sel e8_f)) :=
  .ty_path_elim (.ty_var rfl) E8_xf
-- Gv ⊢ y.f : ∀(u : ⊤) ⊤                                ty_sngl
def E8_yf : HasTy e8_Gv (.path (ref1.sel e8_f)) (.all .top .top) := .ty_sngl E8_yf_sngl E8_xf
-- Gv ⊢ y.f v : ⊤                                       ty_all_elim, with v : ⊤ by ty_sub by subtyp_top
def E8_app : HasTy e8_Gv (.app (ref1.sel e8_f) ref0) .top :=
  .ty_all_elim (T := .top) E8_yf (.ty_sub (.ty_var rfl) .subtyp_top)
-- y ↦ x ⊢ y.A ⇝ x.A                                    rpath at bs = []
def E8_repl_pq : Repl (ref2 : Path (((([],x),x),x),x)) ref3 (.sel ref2 e8_A) (.sel ref3 e8_A) :=
  .rpath (bs := [])
-- Gw ⊢ v : x.A                                         ty_sub by subtyp_sngl_pq at y ↦ x ⊢ y.A ⇝ x.A
def E8_v_xA : HasTy e8_Gw (.path ref1) (.sel ref3 e8_A) :=
  .ty_sub (.ty_var rfl) (.subtyp_sngl_pq (.ty_var rfl) (.ty_var rfl) E8_repl_pq)
-- ⊢ g : ∀(x : X) ∀(y : x.type) ∀(v : y.A) x.A          ty_all_intro three times, ty_let
def E8_g : HasTy .nil (.val e8_g) e8_Tg :=
  .ty_all_intro (.ty_all_intro (.ty_all_intro (.ty_let E8_app E8_v_xA)))

/-! ### The object `o` and the applications -/

/-- `[g : Tg]`. -/
abbrev e8_Gg : Ctx ([],x) := Ctx.nil.cons e8_Tg

-- [g : Tg] ⊢ ν(o : To) {A = ⊤} ▹ {f = λ(u : ⊤). u} ▹ {me = o} : μ(o. To)
--   ty_def_typ, ty_def_all, ty_def_path at o : To
def E8_lit : HasTy e8_Gg (.val (.new e8_To e8_oDefs)) (.mu e8_To) :=
  .ty_new_intro (.ty_defs_cons
    (.ty_defs_cons (.ty_defs_one .ty_def_typ) (.ty_def_all (.ty_all_intro (.ty_var rfl))) rfl)
    (.ty_def_path (.ty_var rfl)) rfl)

/-- `∀(y : o.type) ∀(v : y.A) o.A`, the type of `h`, under `g` then `o`. -/
abbrev e8_Th : Ty (([],x),x) := .all (.sngl ref0) (.all (.sel ref0 e8_A) (.sel ref2 e8_A))
/-- `∀(v : o.me.A) o.A`, the type of `k`, under `g`, `o`, `h`. -/
abbrev e8_Tk : Ty ((([],x),x),x) := .all (.sel (ref1.sel e8_me) e8_A) (.sel ref2 e8_A)

/-- `[g : Tg, o : μ(o. To)]`. -/
abbrev e8_Go : Ctx (([],x),x) := e8_Gg.cons (.mu e8_To)
/-- `[g : Tg, o : μ(o. To), h : Th]`. -/
abbrev e8_Gh : Ctx ((([],x),x),x) := e8_Go.cons e8_Th
/-- `[g : Tg, o : μ(o. To), h : Th, k : Tk]`. -/
abbrev e8_Gk : Ctx (((([],x),x),x),x) := e8_Gh.cons e8_Tk

-- Go ⊢ o : To⟨o⟩                                       ty_var, ty_rec_elim
def E8_o : HasTy e8_Go (.path ref0) (e8_To.substPath ref0) := .ty_rec_elim (T := e8_To) (.ty_var rfl)
-- Go ⊢ o : {A : ⊤..⊤}                                  ty_sub by subtyp_and11 twice
def E8_o_A : HasTy e8_Go (.path ref0) (tdec e8_A .top .top) :=
  .ty_sub E8_o (.subtyp_trans .subtyp_and11 .subtyp_and11)
-- Go ⊢ o : X                                           ty_sub: subtyp_and11, then subtyp_and2 of subtyp_typ and subtyp_and12
def E8_o_X : HasTy e8_Go (.path ref0) e8_X :=
  .ty_sub E8_o (.subtyp_trans .subtyp_and11
    (.subtyp_and2 (.subtyp_trans .subtyp_and11 (.subtyp_typ .subtyp_bot .subtyp_refl)) .subtyp_and12))
-- Go ⊢ g o : ∀(y : o.type) ∀(v : y.A) o.A              ty_all_elim
def E8_app_g : HasTy e8_Go (.app ref1 ref0) e8_Th :=
  .ty_all_elim (T := .all (.sngl ref0) (.all (.sel ref0 e8_A) (.sel ref2 e8_A))) (.ty_var rfl) E8_o_X

-- Gh ⊢ o.me : o.type                                   ty_var, ty_rec_elim, ty_sub by subtyp_and12, ty_new_elim
def E8_ome_h : HasTy e8_Gh (.path (ref1.sel e8_me)) (.sngl ref1) :=
  .ty_new_elim (.ty_sub (.ty_rec_elim (T := e8_To) (.ty_var rfl)) .subtyp_and12)
-- Gh ⊢ h o.me : ∀(v : o.me.A) o.A                      ty_all_elim
def E8_app_h : HasTy e8_Gh (.app ref0 (ref1.sel e8_me)) e8_Tk :=
  .ty_all_elim (T := .all (.sel ref0 e8_A) (.sel ref3 e8_A)) (.ty_var rfl) E8_ome_h

-- Gk ⊢ o : To⟨o⟩                                       ty_var, ty_rec_elim
def E8_o_k : HasTy e8_Gk (.path ref2) (e8_To.substPath ref2) := .ty_rec_elim (T := e8_To) (.ty_var rfl)
-- Gk ⊢ o : {A : ⊤..⊤}                                  ty_sub by subtyp_and11 twice
def E8_o_A_k : HasTy e8_Gk (.path ref2) (tdec e8_A .top .top) :=
  .ty_sub E8_o_k (.subtyp_trans .subtyp_and11 .subtyp_and11)
-- Gk ⊢ o : ⊤                                           ty_var, ty_sub by subtyp_top
def E8_o_top : HasTy e8_Gk (.path ref2) .top := .ty_sub (.ty_var rfl) .subtyp_top
-- Gk ⊢ o.me : o.type                                   ty_sub by subtyp_and12, ty_new_elim
def E8_ome_k : HasTy e8_Gk (.path (ref2.sel e8_me)) (.sngl ref2) := .ty_new_elim (.ty_sub E8_o_k .subtyp_and12)
-- Gk ⊢ o : o.A                                         ty_sub by subtyp_sel2 at o : {A : ⊤..⊤}
def E8_o_oA : HasTy e8_Gk (.path ref2) (.sel ref2 e8_A) := .ty_sub E8_o_top (.subtyp_sel2 E8_o_A_k)
-- o ↦ o.me ⊢ o.A ⇝ o.me.A                              rpath at bs = []
def E8_repl_qp : Repl (ref2 : Path (((([],x),x),x),x)) (ref2.sel e8_me) (.sel ref2 e8_A) (.sel (ref2.sel e8_me) e8_A) :=
  .rpath (bs := [])
-- Gk ⊢ o : o.me.A                                      ty_sub by subtyp_sngl_qp at o.me : o.type, o ↦ o.me
def E8_o_omeA : HasTy e8_Gk (.path ref2) (.sel (ref2.sel e8_me) e8_A) :=
  .ty_sub E8_o_oA (.subtyp_sngl_qp E8_ome_k E8_o_top E8_repl_qp)
-- Gk ⊢ k o : o.A                                       ty_all_elim
def E8_app_k : HasTy e8_Gk (.app ref0 ref2) (.sel ref2 e8_A) :=
  .ty_all_elim (T := .sel ref3 e8_A) (.ty_var rfl) E8_o_omeA

-- Go ⊢ let h = g o in let k = h o.me in k o : o.A      ty_let twice
def E8_lets : HasTy e8_Go e8_tail (.sel ref0 e8_A) := .ty_let E8_app_g (.ty_let E8_app_h E8_app_k)
-- Go ⊢ let h = g o in … : ⊤                            ty_sub by subtyp_sel1 at o : {A : ⊤..⊤}
def E8_lets_top : HasTy e8_Go e8_tail .top := .ty_sub E8_lets (.subtyp_sel1 E8_o_A)

-- ⊢ let g = … in let o = … in … : ⊤                     ty_let twice
def E8_d : HasTy .nil E8_prog .top := .ty_let E8_g (.ty_let E8_lit E8_lets_top)

theorem E8_typed : Nonempty (HasTy .nil E8_prog .top) := ⟨E8_d⟩

end PDot.Source
