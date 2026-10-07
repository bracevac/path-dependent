import Coercions.Captures.Frontend.Surface

/-!
# The surface notation of the Captures front end

Four syntax categories, `capCap`, `capTy`, `capTm` and `capDefs`, and four
entry points, `capCap%`, `capTy%`, `cap%` and `capDefs%`, expand the paper's
notation into a constructor application of `SCap`, `SType`, `STm` or
`SDefs`.  Nothing else happens here: names stay strings, no label is
interned and no de Bruijn index is computed, which is `Resolve.lean`'s
work.  The vanilla rules of `lean/Coercions/Frontend/Notation.lean` are kept
at their precedences.  The added rules are the capture set, the capture
member, the box former, the unboxing term and the ascription.

## Precedence

`^` sits at 60, looser than `∧` at 65, so an intersection closes first and a
written set applies to the whole shape: `{a : ⊤} ∧ {b : ⊤} ^ {k1}` puts the
set on the whole object, which is what a self annotation needs.  If `^` bound
tighter, the set would land on `b` alone.  A `∀`'s body is read at 60, as in
the vanilla file, so it reaches as far right as it can: `∀(u : ⊤) ⊤ ^ {f}`
puts the set on the codomain, and a written `(∀(u : ⊤) ⊤) ^ {f}` needs its
parentheses to put the set on the whole function instead.

## Capture atoms, no new keyword

A capture set is a comma separated list of identifiers, read apart by the
same `nameParts` the vanilla file uses for a dotted name.  One component
named `any` is the atom `SCapAtom.any`.  Any other one component is a name.
Two components `x.C` are a capture member selection.  Three or more are
rejected.  `any` never enters Lean's token table, so `CapAtom.any` and
`List.any` stay usable in every importing module, and a surface program is
free to use `any` as an ordinary variable name anywhere outside a capture
set.

## The two new glyphs

`□` and `⊸` are the version's own, read at `SType.box`/`STm.box` and
`STm.unbox`.  The ascription `(t : T)` has no glyph of its own.  It is the
parenthesis form of a term followed by a colon and a type, which the
vanilla grammar left unused since the calculus has no such term.
-/

namespace CapturesFrontend

open Lean

/-! ## The four categories -/

declare_syntax_cat capCap
declare_syntax_cat capTy
declare_syntax_cat capTm
declare_syntax_cat capDefs

/-- `{a₁, …, aₙ}`, a capture set. -/
syntax:max "{" ident,* "}" : capCap

/-- `⊤`. -/
syntax:max "⊤" : capTy
/-- `⊥`. -/
syntax:max "⊥" : capTy
/-- `{A : S..T}`, a type member declaration. -/
syntax:max "{" ident " : " capTy ".." capTy "}" : capTy
/-- `{a : T}`, a field declaration. -/
syntax:max "{" ident " : " capTy "}" : capTy
/-- `{C^ : c₁..c₂}`, a capture member declaration. -/
syntax:max "{" ident "^" " : " capCap ".." capCap "}" : capTy
/-- `x.A`, a type selection.  One `ident`, split inside the macro. -/
syntax:max ident : capTy
/-- `μ(x. T)`, a recursive self type. -/
syntax:max "μ" "(" ident "." capTy ")" : capTy
/-- `∀(x : S) T`, a dependent function shape.  The body reaches as far
right as it can, so it is read at 60, the level of `^` below. -/
syntax:max "∀" "(" ident " : " capTy ")" capTy:60 : capTy
/-- `S ∧ T`, an intersection, right leaning. -/
syntax:65 capTy:66 " ∧ " capTy:65 : capTy
/-- `□ T`, the box former. -/
syntax:max "□" capTy:max : capTy
/-- `S ^ C`, a shape with a written capture set, looser than `∧`. -/
syntax:60 capTy:61 " ^ " capCap : capTy
/-- Parentheses. -/
syntax:max "(" capTy ")" : capTy

/-- `x`, or `x.a`, or `x.a.b`.  One `ident`, split inside the macro. -/
syntax:max ident : capTm
/-- `λ(x : T). t`. -/
syntax:max "λ" "(" ident " : " capTy ")" "." capTm:60 : capTm
/-- `ν(x : T. d)`, an object literal with its self type. -/
syntax:max "ν" "(" ident " : " capTy "." capDefs ")" : capTm
/-- `t.a` on a receiver that is not an identifier. -/
syntax:80 capTm:80 "." ident : capTm
/-- `t u`, application, left leaning. -/
syntax:70 capTm:70 capTm:71 : capTm
/-- `let x = t in u`, with an optional result type. -/
syntax:max "let" ident (" : " capTy)? " = " capTm " in " capTm:60 : capTm
/-- `□ t`, direct style. -/
syntax:max "□" capTm:max : capTm
/-- `C ⊸ t`, direct style. -/
syntax:max capCap " ⊸ " capTm:max : capTm
/-- `(t : T)`, an ascription: a checking point, erased. -/
syntax:max "(" capTm " : " capTy ")" : capTm
/-- Parentheses. -/
syntax:max "(" capTm ")" : capTm

/-- `{type A = T}`, a type member definition, the vanilla departure. -/
syntax:max "{" "type" ident " = " capTy "}" : capDefs
/-- `{C^ = c}`, a capture member definition. -/
syntax:max "{" ident "^" " = " capCap "}" : capDefs
/-- `{a = t}`, a term member definition. -/
syntax:max "{" ident " = " capTm "}" : capDefs
/-- `d ∧ e`, right leaning. -/
syntax:65 capDefs:66 " ∧ " capDefs:65 : capDefs

/-- Expand a `capCap` into an `SCap`. -/
syntax:max "capCap% " capCap : term
/-- Expand a `capTy` into an `SType`. -/
syntax:max "capTy% " capTy : term
/-- Expand a `capTm` into an `STm`. -/
syntax:max "cap% " capTm : term
/-- Expand a `capDefs` into an `SDefs`. -/
syntax:max "capDefs% " capDefs : term

/-! ## Taking a hierarchical identifier apart, as in the vanilla file -/

/-- The components of a name, outermost first, as strings. -/
def nameParts : Name → List String → List String
  | .anonymous, acc => acc
  | .str p s, acc => nameParts p (s :: acc)
  | .num p i, acc => nameParts p (toString i :: acc)

/-- The receiver and the label of a name in type position.  Only a two
component name is a type, since the one type a name can build is the
selection `x.A`. -/
def tySelName (n : Name) : Option (String × String) :=
  match nameParts n [] with
  | [recv, lbl] => some (recv, lbl)
  | _ => none

/-- The reading of a name in a capture set: `any`, a plain name, or the
selection `x.C`.  Longer names are rejected. -/
def capAtomName (n : Name) : Option SCapAtom :=
  match nameParts n [] with
  | ["any"] => some .any
  | [x] => some (.name x)
  | [x, C] => some (.sel x C)
  | _ => none

/-- A surface identifier in term position. -/
private def surfaceTmOfIdent (x : Ident) : MacroM (TSyntax `term) := do
  match nameParts x.getId [] with
  | [] => Macro.throwErrorAt x "the surface term needs a name here"
  | head :: rest =>
    let mut acc ← `(STm.var $(quote head))
    for c in rest do
      acc ← `(STm.proj $acc $(quote c))
    return acc

/-- A surface identifier in type position. -/
private def surfaceTyOfIdent (x : Ident) : MacroM (TSyntax `term) := do
  match tySelName x.getId with
  | some (recv, lbl) => `(SType.sel $(quote recv) $(quote lbl))
  | none =>
    Macro.throwErrorAt x
      "a surface type built from a name is the selection x.A, which has exactly two components"

/-- A capture atom from an identifier: `any`, a name, or `x.C`. -/
private def capAtomOfIdent (x : Ident) : MacroM (TSyntax `term) := do
  match capAtomName x.getId with
  | some .any => `(SCapAtom.any)
  | some (.name y) => `(SCapAtom.name $(quote y))
  | some (.sel y C) => `(SCapAtom.sel $(quote y) $(quote C))
  | none => Macro.throwErrorAt x "a capture atom is any, a name, or x.C"

/-! ## The macros -/

macro_rules
  | `(capCap% { $xs:ident,* }) => do
      let mut acc ← `(([] : SCap))
      for x in xs.getElems.reverse do
        let a ← capAtomOfIdent x
        acc ← `($a :: $acc)
      return acc

macro_rules
  | `(capTy% ⊤) => `(SType.top)
  | `(capTy% ⊥) => `(SType.bot)
  | `(capTy% { $A:ident : $S:capTy .. $T:capTy }) =>
      `(SType.typ $(quote A.getId.toString) (capTy% $S) (capTy% $T))
  | `(capTy% { $a:ident : $T:capTy }) =>
      `(SType.fld $(quote a.getId.toString) (capTy% $T))
  | `(capTy% { $C:ident ^ : $lo:capCap .. $hi:capCap }) =>
      `(SType.cap $(quote C.getId.toString) (capCap% $lo) (capCap% $hi))
  | `(capTy% $x:ident) => surfaceTyOfIdent x
  | `(capTy% μ ( $x:ident . $T:capTy )) =>
      `(SType.mu $(quote x.getId.toString) (capTy% $T))
  | `(capTy% ∀ ( $x:ident : $S:capTy ) $T:capTy) =>
      `(SType.all $(quote x.getId.toString) (capTy% $S) (capTy% $T))
  | `(capTy% $S:capTy ∧ $T:capTy) => `(SType.and (capTy% $S) (capTy% $T))
  | `(capTy% □ $T:capTy) => `(SType.box (capTy% $T))
  | `(capTy% $S:capTy ^ $C:capCap) => `(SType.capt (capTy% $S) (capCap% $C))
  | `(capTy% ( $T:capTy )) => `(capTy% $T)

macro_rules
  | `(cap% $x:ident) => surfaceTmOfIdent x
  | `(cap% λ ( $x:ident : $T:capTy ) . $t:capTm) =>
      `(STm.lam $(quote x.getId.toString) (capTy% $T) (cap% $t))
  | `(cap% ν ( $x:ident : $T:capTy . $d:capDefs )) =>
      `(STm.obj $(quote x.getId.toString) (capTy% $T) (capDefs% $d))
  | `(cap% $t:capTm . $a:ident) => `(STm.proj (cap% $t) $(quote a.getId.toString))
  | `(cap% $t:capTm $u:capTm) => `(STm.app (cap% $t) (cap% $u))
  | `(cap% let $x:ident = $t:capTm in $u:capTm) =>
      `(STm.«let» $(quote x.getId.toString) (none : Option SType) (cap% $t) (cap% $u))
  | `(cap% let $x:ident : $T:capTy = $t:capTm in $u:capTm) =>
      `(STm.«let» $(quote x.getId.toString) (some (capTy% $T)) (cap% $t) (cap% $u))
  | `(cap% □ $t:capTm) => `(STm.box (cap% $t))
  | `(cap% $C:capCap ⊸ $t:capTm) => `(STm.unbox (capCap% $C) (cap% $t))
  | `(cap% ( $t:capTm : $T:capTy )) => `(STm.asc (cap% $t) (capTy% $T))
  | `(cap% ( $t:capTm )) => `(cap% $t)

macro_rules
  | `(capDefs% { type $A:ident = $T:capTy }) =>
      `(SDefs.typ $(quote A.getId.toString) (capTy% $T))
  | `(capDefs% { $C:ident ^ = $c:capCap }) =>
      `(SDefs.cap $(quote C.getId.toString) (capCap% $c))
  | `(capDefs% { $a:ident = $t:capTm }) =>
      `(SDefs.trm $(quote a.getId.toString) (cap% $t))
  | `(capDefs% $d:capDefs ∧ $e:capDefs) => `(SDefs.and (capDefs% $d) (capDefs% $e))

/-! ## One check per new surface form, and the vanilla forms renamed

Every check reduces in the kernel, so `by decide` is the right tactic, as it
is throughout `Surface.lean`. -/

example : (capCap% {}) = ([] : SCap) := by decide

example : capCap% {f, k1} = [SCapAtom.name "f", SCapAtom.name "k1"] := by decide

example : capCap% {x.C, any} = [SCapAtom.sel "x" "C", SCapAtom.any] := by decide

example :
    capTy% {C^ : {}..{k1, k2}} = SType.cap "C" [] [SCapAtom.name "k1", SCapAtom.name "k2"] := by
  decide

example : capTy% □(⊤ ^ {f}) = SType.box (SType.capt SType.top [SCapAtom.name "f"]) := by decide

/-- `^` is looser than `∧`, so the set sits on the whole intersection, not
on `b` alone: the fix of the design note's own precedence. -/
example :
    capTy% {a : ⊤} ∧ {b : ⊤} ^ {k1} =
      SType.capt (SType.and (SType.fld "a" SType.top) (SType.fld "b" SType.top))
        [SCapAtom.name "k1"] := by
  decide

/-- A `∀`'s body reaches as far right as it can, so the set lands on the
codomain. -/
example :
    capTy% ∀(u : ⊤) ⊤ ^ {f} = SType.all "u" SType.top (SType.capt SType.top [SCapAtom.name "f"]) := by
  decide

/-- Parentheses around the whole function put the set there instead. -/
example :
    capTy% (∀(u : ⊤) ⊤) ^ {f} =
      SType.capt (SType.all "u" SType.top SType.top) [SCapAtom.name "f"] := by
  decide

example : cap% □ f = STm.box (STm.var "f") := by decide

example : cap% {k1} ⊸ e = STm.unbox [SCapAtom.name "k1"] (STm.var "e") := by decide

example : cap% (e : ⊤) = STm.asc (STm.var "e") SType.top := by decide

example : capDefs% {C^ = {k1}} = SDefs.cap "C" [SCapAtom.name "k1"] := by decide

/-- `any` is a name to the lexer and an atom to the macro: no new keyword,
so `CapAtom.any` and `List.any` stay usable in every importing module. -/
example : capAtomName `any = some .any := by decide

example : capAtomName `x.C = some (.sel "x" "C") := by decide

/-- Three or more components are rejected as a capture atom. -/
example : capAtomName `x.y.z = none := by decide

/-! ### The vanilla forms, renamed -/

example : (cap% x) = STm.var "x" := by decide

example : (cap% x.a) = STm.proj (.var "x") "a" := by decide

example : (cap% x.a.b) = STm.proj (.proj (.var "x") "a") "b" := by decide

example : (cap% ( f x ).a) = STm.proj (.app (.var "f") (.var "x")) "a" := by decide

example : (capTy% x.A) = SType.sel "x" "A" := by decide

/-- The rejected undotted name in type position: a bare `x` is never a
type.  Writing `capTy% x` in a term fails the build at this message. -/
example : tySelName `x = none := by decide

example : tySelName `x.a.A = none := by decide

example : tySelName `x.A = some ("x", "A") := by decide

example : nameParts `x [] = ["x"] := by decide

example : nameParts `x.a [] = ["x", "a"] := by decide

example : nameParts `x.a.b [] = ["x", "a", "b"] := by decide

/-! ## The version's programs

C7, C2, S3, S1 and S2 of the version's `DotMNF/Examples.lean`, and the ten
vanilla examples E1 to E10 of the vanilla front end's `Resolve.lean`, with
the prefix renamed.  Here the programs only have to parse.  Resolution and
the comparison against the version's own terms are in `Resolve.lean`. -/

/-- C7, a container of boxed capabilities, with the term level boxes and
the unboxing written out by hand. -/
def C7src : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = □ f1} ∧ {e2 = □ f2})
        in let e = o.e1 in {k1} ⊸ e

/-- C7 as box inference accepts it: no `□` and no `⊸` in terms, the field
boxes and the unboxing are left to box inference. -/
def C7nbSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = f1} ∧ {e2 = f2})
        in let e = o.e1 in (e : (∀(u : ⊤) ⊤) ^ {k1})

/-- C2, explicit capture polymorphism, the client's call in direct style:
`x.run u` is let-inserted by `Resolve.lean` into `let % = x.run in % u`. -/
def C2src : STm :=
  cap% let c = λ(x : (μ(z. {C^ : {}..{k1, k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}})) ^ {k1, k2}).
                λ(u : ⊤). x.run u in
      let a = ν(z : {C^ : {k1}..{k1}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k1}} ∧ {run = λ(u : ⊤). u}) in
      let b = ν(z : {C^ : {k2}..{k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k2}} ∧ {run = λ(u : ⊤). u}) in
      let ga = c a in let gb = c b in gb

/-- S3, a type member at a boxed capturing type, the term level box and
the unboxing written out by hand. -/
def S3src : STm :=
  cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        let o = ν(z : {A : (∀(u : ⊤) ⊤) ^ {f} .. (∀(u : ⊤) ⊤) ^ {f}} ∧ {elem : z.A}.
                   {type A = (∀(u : ⊤) ⊤) ^ {f}} ∧ {elem = □ f})
        in let e = o.elem in {f} ⊸ e

/-- S3 with no term level box: the member's own value is the bare
capability, and box inference has to recover the box at the field.  The
checking point is an ascription rather than a written unboxing. -/
def S3nbSrc : STm :=
  cap% λ(f : (∀(u : ⊤) ⊤) ^ {k1}).
        let o = ν(z : {A : (∀(u : ⊤) ⊤) ^ {f} .. (∀(u : ⊤) ⊤) ^ {f}} ∧ {elem : z.A}.
                   {type A = (∀(u : ⊤) ⊤) ^ {f}} ∧ {elem = f})
        in let e = o.elem in (e : (∀(u : ⊤) ⊤) ^ {f})

/-- S1, `withFile` with an explicit capture parameter over the platform
capability `k1`.  `File := μ(file. {read : (∀(u : ⊤) ⊤) ^ {file}})`.  The
signature is bound by an ascription, not by a `let` annotation, which
would type the result of the whole `let`.  The ascription is what a checking
clause `λ` against `∀` reaches. -/
def S1src : STm :=
  cap% let withFile =
        (λ(cp : (μ(c. {C^ : {}..{k1}})) ^ {}).
           λ(op : (∀(f : (μ(file. {read : (∀(u : ⊤) ⊤) ^ {file}})) ^ {k1}) ⊤) ^ {cp.C}).
             let fl = ν(file : {read : (∀(u : ⊤) ⊤)}. {read = λ(u : ⊤). u}) in op fl
         : (∀(cp : (μ(c. {C^ : {}..{k1}})) ^ {})
              (∀(op : (∀(f : (μ(file. {read : (∀(u : ⊤) ⊤) ^ {file}})) ^ {k1}) ⊤) ^ {cp.C})
                 (⊤ ^ {any})) ^ {k1, cp}) ^ {k1}) in
      let cp = ν(c : {C^ : {k1}..{k1}}. {C^ = {k1}}) in
      let op = λ(f : (μ(file. {read : (∀(u : ⊤) ⊤) ^ {file}})) ^ {k1}). λ(u : ⊤). u in
      let g = withFile cp in
      let r = g op in
      r

/-- S2, a class with a capture-set parameter carried as a capture member
and `any` in the result.  The signature is bound by ascription the same
way. -/
def S2src : STm :=
  cap% let mk =
        (λ(u : ⊤). let it = ν(i : {C^ : {k1}..{k1}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}}.
                            {C^ = {k1}} ∧ {next = λ(v : ⊤). v}) in it
         : (∀(u : ⊤) (μ(i. {C^ : {}..{k1}} ∧ {next : (∀(v : ⊤) ⊤ ^ {i.C}) ^ {i.C}})) ^ {any}) ^
             {k1}) in
    let un = (λ(y : ⊤). y : ⊤) in
    let it = mk un in let n = it.next in let r = n un in r

/-! ### E1 to E10, the vanilla examples, prefix renamed -/

/-- `λ(x : {A : ⊤..⊥}). let y : {B : {a : ⊤}..{a : ⊤}} = x in y`. -/
def E1src : STm :=
  cap% λ(x : {A : ⊤..⊥}). let y : {B : {a : ⊤} .. {a : ⊤}} = x in y

/-- `let x = ν(s : {A : E2A..E2A} ∧ {a : E2A}. {type A = E2A} ∧ {a = λ(y : s.A). y})
in let f = x.a in f f`, with `E2A` the type `∀(y : s.A) s.A`. -/
def E2src : STm :=
  cap% let x = ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}.
                  {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y})
       in let f = x.a in f f

/-- `λ(x : {A : ⊥..{a : ⊤}} ∧ {A : {b : ⊤}..⊤}). λ(z : {b : ⊤}). let y : {a : ⊤} = z in y`. -/
def E3src : STm :=
  cap% λ(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}).
         λ(z : {b : ⊤}). let y : {a : ⊤} = z in y

/-- `λ(x : {B : {A : ⊥..⊤}..{A : {a : ⊤}..⊤}}). λ(w : {A : ⊥..⊤}). λ(n : {a : ⊤}).
let g = λ(y : w.A). y in g n`. -/
def E4src : STm :=
  cap% λ(x : {B : {A : ⊥ .. ⊤} .. {A : {a : ⊤} .. ⊤}}).
         λ(w : {A : ⊥ .. ⊤}). λ(n : {a : ⊤}). let g = λ(y : w.A). y in g n

/-- `λ(w : {A : ⊤..⊤}). let f = λ(v : {A : ⊤..⊤}). ν(z : {a : v.A}. {a = v})
in let o = f w in o.a`. -/
def E5src : STm :=
  cap% λ(w : {A : ⊤..⊤}).
         let f = λ(v : {A : ⊤..⊤}). ν(z : {a : v.A}. {a = v})
         in let o = f w in o.a

/-- `λ(n : {a : ⊤}). ν(x : {T : {a : ⊤}..{a : ⊤}} ∧ {v : x.T}. {type T = {a : ⊤}} ∧ {v = n})`. -/
def E6src : STm :=
  cap% λ(n : {a : ⊤}).
         ν(x : {T : {a : ⊤} .. {a : ⊤}} ∧ {v : x.T}.
             {type T = {a : ⊤}} ∧ {v = n})

/-- `ν(x : {A : x.B..x.B} ∧ {B : x.A..x.A}. {type A = x.B} ∧ {type B = x.A})`. -/
def E7src : STm :=
  cap% ν(x : {A : x.B .. x.B} ∧ {B : x.A .. x.A}.
           {type A = x.B} ∧ {type B = x.A})

/-- `λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A ∧ {a : ⊤}). y.a`. -/
def E8src : STm :=
  cap% λ(x : {A : ⊥ .. {a : ⊤}}). λ(y : x.A ∧ {a : ⊤}). y.a

/-- `λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A). y.a`. -/
def E9src : STm :=
  cap% λ(x : {A : ⊥ .. {a : ⊤}}). λ(y : x.A). y.a

/-- `λ(f : ⊤). λ(g : ⊤). f (g f)`, not already in monadic normal form: the
operand `g f` is let-inserted. -/
def E10src : STm :=
  cap% λ(f : ⊤). λ(g : ⊤). f (g f)

end CapturesFrontend
