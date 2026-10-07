import Coercions.CapturesCC.Frontend.Surface

/-!
# The surface notation of the CapturesCC front end

Six syntax categories, `ccSet`, `ccShape`, `ccTy`, `ccAns`, `ccTm` and
`ccDefs`, and their entry points `ccSet%`, `ccShape%`, `ccTy%`, `ccAns%`,
`cc%` and `ccDefs%`, expand the paper's notation into a constructor
application of `SCap`, `SShape`, `SType`, `SAns`, `STm` or `SDefs`.  A
whole program is `ccProg% [k₁, …] t`.  Nothing else happens here: names
stay strings, no label is interned and no de Bruijn index is computed,
which is `Resolve.lean`'s work.

## Three sorts, not one

A shape (`ccShape`) is the plain type former: a declaration, a selection,
an intersection, an arrow or a box.  A type (`ccTy`) is a shape with a
written capture set, `S ^ C`.  Writing a bare shape where a type is
expected elaborates the empty set, the same convention the vanilla
capture front end already applies at its single `capt` former.  An answer
(`ccAns`) is a type, or a type read under one capture binder bounded by a
set of the enclosing scope, `∃[c ⊑ C] T`, the shape an existential reading
of `fresh` needs.  Only a `let`'s own annotation and an arrow's codomain
are answer positions.  Every other type position is a plain type: a field,
a bound, a box operand, an ascription.

## The arrow's own capture binder

An arrow carries an optional name for its own capture binder:
`∀(x : T) U` leaves it anonymous, `∀[c](x : T) U` names it `c`.  A lambda
carries the same pair, `λ(x : T). t` and `λ[c](x : T). t`.  `let ⟨c, x⟩ = t
in u` is the explicit counterpart at term level: it unpacks an existential
answer by hand, opening a capture binder for the witness and a term binder
for the payload, both read only in `u`.

## Precedence

`^` sits looser than the arrow and the box, and the written shape of an
arrow's codomain or a box's operand needs parentheses to carry a set of
its own.  `∀(x : ⊤) ⊤ ^ {c}` is an arrow whose codomain carries `{c}`.
`(∀(x : ⊤) ⊤) ^ {c}` is the whole arrow under `{c}` instead.  `□` takes
its operand at the tightest level, so a capturing operand needs its own
parentheses, `□(⊤ ^ {f})`.  A bare `□⊤` is a type formed with no set, the
box of the capture-free shape `⊤`, written without parentheses for that
reason alone.  `∧` keeps its vanilla precedence, closing tighter than `^`,
so `{a : ⊤} ∧ {b : ⊤} ^ {k1}` sets the whole intersection.

## Capture atoms, no new keyword

A capture set is a comma separated list of identifiers, read apart by
`nameParts`, the same splitting the vanilla file uses for a dotted name.
One component named `any` is the atom `any`, naming the receiver's own
outer set.  One component named `fresh` is the atom `fresh`, naming a
freshly allocated one.  Any other one component is a plain name.  Two
components `x.C` are a capture member selection.  Three or more are
rejected.  Neither `any` nor `fresh` ever enters Lean's token table, so
`List.any` and every other ordinary use of either word stay available in
every importing module, and a surface program is free to use them as
ordinary variable names anywhere outside a capture set.  The member
spelling `{C^ : lo..hi}` and `{C^ = c}` carries over from the Captures
front end unchanged, since a capture-set parameter desugars to a type
parameter at the same label slot.  The only reserved word beyond the
vanilla `type` is none: `cap`, `unbox` and `letex` are never tokens, since
the surface and the target both write them as plain identifiers
(`.cap`, `.unbox`, `.letex`), and a keyword there would break every module
that imports this one.

## The ascription

`(t : T)` is kept from the Captures front end, a checking point with no
term of its own in either calculus.  It is the parenthesis form of a term
followed by a colon and a type, read only after the plain parenthesised
term fails to match.
-/

namespace CapturesCCFrontend

open Lean

/-! ## The six categories -/

declare_syntax_cat ccSet
declare_syntax_cat ccShape
declare_syntax_cat ccTy
declare_syntax_cat ccAns
declare_syntax_cat ccTm
declare_syntax_cat ccDefs

/-- `{a₁, …, aₙ}`, a capture set. -/
syntax:max "{" ident,* "}" : ccSet

/-- `⊤`. -/
syntax:max "⊤" : ccShape
/-- `⊥`. -/
syntax:max "⊥" : ccShape
/-- `{A : S..T}`, a type member declaration. -/
syntax:max "{" ident " : " ccShape ".." ccShape "}" : ccShape
/-- `{C^ : c₁..c₂}`, a capture member declaration. -/
syntax:max "{" ident "^" " : " ccSet ".." ccSet "}" : ccShape
/-- `{a : T}`, a field declaration.  Its type is a capturing type. -/
syntax:max "{" ident " : " ccTy "}" : ccShape
/-- `x.A`, a type selection.  One `ident`, split inside the macro. -/
syntax:max ident : ccShape
/-- `μ(x. S)`, a recursive self shape. -/
syntax:max "μ" "(" ident "." ccShape ")" : ccShape
/-- `∀(x : T) U`, the arrow's own capture binder left anonymous. -/
syntax:60 "∀" "(" ident " : " ccTy ")" ccAns:60 : ccShape
/-- `∀[c](x : T) U`, the arrow's own capture binder named. -/
syntax:60 "∀" "[" ident "]" "(" ident " : " ccTy ")" ccAns:60 : ccShape
/-- `S ∧ T`, an intersection of shapes, right leaning. -/
syntax:65 ccShape:66 " ∧ " ccShape:65 : ccShape
/-- `□ T`, the box former, its operand at the tightest level. -/
syntax:max "□" ccTy:max : ccShape
/-- Parentheses. -/
syntax:max "(" ccShape ")" : ccShape

/-- `S ^ C`, a shape under a written capture set, the shape read at the
tightest level so that a capturing arrow or box needs its own
parentheses. -/
syntax:70 ccShape:max " ^ " ccSet : ccTy
/-- A bare shape elaborates the empty set. -/
syntax:60 ccShape:60 : ccTy
/-- Parentheses. -/
syntax:max "(" ccTy ")" : ccTy

/-- A plain type is an answer too. -/
syntax:60 ccTy:60 : ccAns
/-- `∃[c ⊑ C] T`, an existential answer. -/
syntax:60 "∃" "[" ident " ⊑ " ccSet "]" ccTy:60 : ccAns

/-- `x`, or `x.a`, or `x.a.b`.  One `ident`, split inside the macro. -/
syntax:max ident : ccTm
/-- `λ(x : T). t`, the arrow's own capture binder left anonymous. -/
syntax:max "λ" "(" ident " : " ccTy ")" "." ccTm:60 : ccTm
/-- `λ[c](x : T). t`, the arrow's own capture binder named. -/
syntax:max "λ" "[" ident "]" "(" ident " : " ccTy ")" "." ccTm:60 : ccTm
/-- `ν(x : S. d)`, an object literal: the self shape and its
definitions, no capture set of its own. -/
syntax:max "ν" "(" ident " : " ccShape "." ccDefs ")" : ccTm
/-- `t.a` on a receiver that is not an identifier. -/
syntax:80 ccTm:80 "." ident : ccTm
/-- `t u`, application, left leaning. -/
syntax:70 ccTm:70 ccTm:71 : ccTm
/-- `let x = t in u`, with an optional result answer. -/
syntax:max "let" ident (" : " ccAns)? " = " ccTm " in " ccTm:60 : ccTm
/-- `let ⟨c, x⟩ = t in u`, an explicit unpacking: a capture binder for the
witness, then a term binder for the payload, both read only in `u`. -/
syntax:max "let" "⟨" ident "," ident "⟩" " = " ccTm " in " ccTm:60 : ccTm
/-- `□ t`, direct style, a box value written by hand. -/
syntax:max "□" ccTm:max : ccTm
/-- `C ⊸ t`, direct style, an unboxing written by hand. -/
syntax:max ccSet " ⊸ " ccTm:max : ccTm
/-- `(t : T)`, an ascription: a checking point, erased. -/
syntax:max "(" ccTm " : " ccTy ")" : ccTm
/-- Parentheses. -/
syntax:max "(" ccTm ")" : ccTm

/-- `{type A = S}`, a type member definition, its body a shape. -/
syntax:max "{" "type" ident " = " ccShape "}" : ccDefs
/-- `{C^ = c}`, a capture member definition. -/
syntax:max "{" ident "^" " = " ccSet "}" : ccDefs
/-- `{a = t}`, a term member definition. -/
syntax:max "{" ident " = " ccTm "}" : ccDefs
/-- `d ∧ e`, right leaning. -/
syntax:65 ccDefs:66 " ∧ " ccDefs:65 : ccDefs

/-- Expand a `ccSet` into an `SCap`. -/
syntax:max "ccSet% " ccSet : term
/-- Expand a `ccShape` into an `SShape`. -/
syntax:max "ccShape% " ccShape : term
/-- Expand a `ccTy` into an `SType`. -/
syntax:max "ccTy% " ccTy : term
/-- Expand a `ccAns` into an `SAns`. -/
syntax:max "ccAns% " ccAns : term
/-- Expand a `ccTm` into an `STm`. -/
syntax:max "cc% " ccTm : term
/-- Expand a `ccDefs` into an `SDefs`. -/
syntax:max "ccDefs% " ccDefs : term
/-- Expand a whole program: the platform capabilities, outermost first,
and the body. -/
syntax:max "ccProg% " "[" ident,* "]" ccTm : term

/-! ## Taking a hierarchical identifier apart, as in the vanilla file -/

/-- The components of a name, outermost first, as strings. -/
def nameParts : Name → List String → List String
  | .anonymous, acc => acc
  | .str p s, acc => nameParts p (s :: acc)
  | .num p i, acc => nameParts p (toString i :: acc)

/-- The receiver and the label of a name in shape position.  Only a two
component name is a shape, since the one shape a name can build is the
selection `x.A`. -/
def tySelName (n : Name) : Option (String × String) :=
  match nameParts n [] with
  | [recv, lbl] => some (recv, lbl)
  | _ => none

/-- The reading of a name inside a capture set: `any`, `fresh`, a plain
name, or the selection `x.C`.  Longer names are rejected. -/
def atomOfName (n : Name) : Option SAtom :=
  match nameParts n [] with
  | ["any"] => some .any
  | ["fresh"] => some .fresh
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

/-- A surface identifier in shape position. -/
private def surfaceShapeOfIdent (x : Ident) : MacroM (TSyntax `term) := do
  match tySelName x.getId with
  | some (recv, lbl) => `(SShape.sel $(quote recv) $(quote lbl))
  | none =>
    Macro.throwErrorAt x
      "a surface shape built from a name is the selection x.A, which has exactly two components"

/-- A capture atom from an identifier: `any`, `fresh`, a name, or `x.C`. -/
private def capAtomOfIdent (x : Ident) : MacroM (TSyntax `term) := do
  match atomOfName x.getId with
  | some .any => `(SAtom.any)
  | some .fresh => `(SAtom.fresh)
  | some (.name y) => `(SAtom.name $(quote y))
  | some (.sel y C) => `(SAtom.sel $(quote y) $(quote C))
  | none => Macro.throwErrorAt x "a capture atom is any, fresh, a name, or x.C"

/-- A `String` literal from an identifier's own name, with no splitting. -/
private def str (x : Ident) : TSyntax `term := quote x.getId.toString

/-! ## The macros -/

macro_rules
  | `(ccSet% { $xs:ident,* }) => do
      let mut acc ← `(([] : SCap))
      for x in xs.getElems.reverse do
        let a ← capAtomOfIdent x
        acc ← `($a :: $acc)
      return acc

macro_rules
  | `(ccShape% ⊤) => `(SShape.top)
  | `(ccShape% ⊥) => `(SShape.bot)
  | `(ccShape% { $A:ident : $S:ccShape .. $T:ccShape }) =>
      `(SShape.typ $(str A) (ccShape% $S) (ccShape% $T))
  | `(ccShape% { $C:ident ^ : $lo:ccSet .. $hi:ccSet }) =>
      `(SShape.cap $(str C) (ccSet% $lo) (ccSet% $hi))
  | `(ccShape% { $a:ident : $T:ccTy }) => `(SShape.fld $(str a) (ccTy% $T))
  | `(ccShape% $x:ident) => surfaceShapeOfIdent x
  | `(ccShape% μ ( $x:ident . $S:ccShape )) => `(SShape.mu $(str x) (ccShape% $S))
  | `(ccShape% ∀ ( $x:ident : $T:ccTy ) $U:ccAns) =>
      `(SShape.all none $(str x) (ccTy% $T) (ccAns% $U))
  | `(ccShape% ∀ [ $k:ident ] ( $x:ident : $T:ccTy ) $U:ccAns) =>
      `(SShape.all (some $(str k)) $(str x) (ccTy% $T) (ccAns% $U))
  | `(ccShape% $S:ccShape ∧ $T:ccShape) => `(SShape.and (ccShape% $S) (ccShape% $T))
  | `(ccShape% □ $T:ccTy) => `(SShape.box (ccTy% $T))
  | `(ccShape% ( $S:ccShape )) => `(ccShape% $S)

macro_rules
  | `(ccTy% $S:ccShape ^ $C:ccSet) => `(SType.capt (ccShape% $S) (ccSet% $C))
  | `(ccTy% $S:ccShape) => `(SType.capt (ccShape% $S) [])
  | `(ccTy% ( $T:ccTy )) => `(ccTy% $T)

macro_rules
  | `(ccAns% $T:ccTy) => `(SAns.ty (ccTy% $T))
  | `(ccAns% ∃ [ $k:ident ⊑ $C:ccSet ] $T:ccTy) =>
      `(SAns.ex $(str k) (ccSet% $C) (ccTy% $T))

macro_rules
  | `(cc% $x:ident) => surfaceTmOfIdent x
  | `(cc% λ ( $x:ident : $T:ccTy ) . $t:ccTm) =>
      `(STm.lam none $(str x) (ccTy% $T) (cc% $t))
  | `(cc% λ [ $k:ident ] ( $x:ident : $T:ccTy ) . $t:ccTm) =>
      `(STm.lam (some $(str k)) $(str x) (ccTy% $T) (cc% $t))
  | `(cc% ν ( $x:ident : $S:ccShape . $d:ccDefs )) =>
      `(STm.obj $(str x) (ccShape% $S) (ccDefs% $d))
  | `(cc% $t:ccTm . $a:ident) => `(STm.proj (cc% $t) $(str a))
  | `(cc% $t:ccTm $u:ccTm) => `(STm.app (cc% $t) (cc% $u))
  | `(cc% let $x:ident = $t:ccTm in $u:ccTm) =>
      `(STm.«let» $(str x) (none : Option SAns) (cc% $t) (cc% $u))
  | `(cc% let $x:ident : $U:ccAns = $t:ccTm in $u:ccTm) =>
      `(STm.«let» $(str x) (some (ccAns% $U)) (cc% $t) (cc% $u))
  | `(cc% let ⟨ $k:ident , $x:ident ⟩ = $t:ccTm in $u:ccTm) =>
      `(STm.letex $(str k) $(str x) (cc% $t) (cc% $u))
  | `(cc% □ $t:ccTm) => `(STm.box (cc% $t))
  | `(cc% $C:ccSet ⊸ $t:ccTm) => `(STm.unbox (ccSet% $C) (cc% $t))
  | `(cc% ( $t:ccTm : $T:ccTy )) => `(STm.asc (cc% $t) (ccTy% $T))
  | `(cc% ( $t:ccTm )) => `(cc% $t)

macro_rules
  | `(ccDefs% { type $A:ident = $S:ccShape }) =>
      `(SDefs.typ $(str A) (ccShape% $S))
  | `(ccDefs% { $C:ident ^ = $c:ccSet }) =>
      `(SDefs.cap $(str C) (ccSet% $c))
  | `(ccDefs% { $a:ident = $t:ccTm }) =>
      `(SDefs.trm $(str a) (cc% $t))
  | `(ccDefs% $d:ccDefs ∧ $e:ccDefs) => `(SDefs.and (ccDefs% $d) (ccDefs% $e))

macro_rules
  | `(ccProg% [ $ps:ident,* ] $t:ccTm) =>
      `(SProg.mk [$(ps.getElems.map str),*] (cc% $t))

/-! ## One check per new or changed surface form

Every check reduces in the kernel, so `by decide` is the right tactic, as
it is throughout `Surface.lean`. -/

example : (ccSet% {}) = ([] : SCap) := by decide

/-- A capture set, with the reserved names and a capture selection. -/
example : (ccSet% {fs, cp.C, any, fresh}) =
    [SAtom.name "fs", SAtom.sel "cp" "C", SAtom.any, SAtom.fresh] := by decide

/-- A bare shape elaborates the empty set. -/
example : (ccTy% ⊤) = SType.capt SShape.top [] := by decide

/-- `S ^ C`, a shape under a written set. -/
example : (ccTy% ⊤ ^ {f}) = SType.capt SShape.top [SAtom.name "f"] := by decide

/-- `∀(x : T) U`, the arrow binder left anonymous, its codomain carrying
the written set since the arrow itself is not parenthesised. -/
example :
    (ccTy% ∀(x : ⊤) ⊤ ^ {c}) =
      SType.capt (SShape.all none "x" (SType.capt SShape.top []) (SAns.ty (SType.capt SShape.top [SAtom.name "c"])))
        [] := by
  decide

/-- The same arrow parenthesised: the set now sits on the whole arrow. -/
example :
    (ccTy% (∀(x : ⊤) ⊤) ^ {c}) =
      SType.capt (SShape.all none "x" (SType.capt SShape.top []) (SAns.ty (SType.capt SShape.top []))) [SAtom.name "c"] := by
  decide

/-- `∀[c](x : T) U`, the arrow binder named. -/
example :
    (ccTy% ∀[k](x : ⊤) ⊤ ^ {k}) =
      SType.capt (SShape.all (some "k") "x" (SType.capt SShape.top []) (SAns.ty (SType.capt SShape.top [SAtom.name "k"])))
        [] := by
  decide

/-- `∃[c ⊑ C] T`, an existential answer: the binder scopes the type, its
own bound read in the outer scope. -/
example :
    (ccAns% ∃[w ⊑ {fs, u}] ⊤ ^ {w}) =
      SAns.ex "w" [SAtom.name "fs", SAtom.name "u"] (SType.capt SShape.top [SAtom.name "w"]) := by
  decide

/-- A plain type is an answer too. -/
example : (ccAns% ⊤ ^ {f}) = SAns.ty (SType.capt SShape.top [SAtom.name "f"]) := by decide

/-- `{C^ : lo..hi}`, a capture member declaration, the Captures front
end's spelling. -/
example :
    (ccShape% {C^ : {}..{k1, k2}}) =
      SShape.cap "C" [] [SAtom.name "k1", SAtom.name "k2"] := by
  decide

/-- `{C^ = c}`, a capture member definition. -/
example : (ccDefs% {C^ = {fs}}) = SDefs.cap "C" [SAtom.name "fs"] := by decide

/-- `□(T ^ {..})`, the box former, its operand parenthesised to carry a
set of its own. -/
example : (ccShape% □(⊤ ^ {f})) = SShape.box (SType.capt SShape.top [SAtom.name "f"]) := by decide

/-- `□ x`, a box value, direct style. -/
example : (cc% □ f) = STm.box (STm.var "f") := by decide

/-- `{..} ⊸ x`, an unboxing, direct style. -/
example : (cc% {k1} ⊸ e) = STm.unbox [SAtom.name "k1"] (STm.var "e") := by decide

/-- `λ[c](x : T). t`, a lambda with its arrow binder named. -/
example :
    (cc% λ[c](x : ⊤ ^ {c}). x) =
      STm.lam (some "c") "x" (SType.capt SShape.top [SAtom.name "c"]) (STm.var "x") := by
  decide

/-- `let ⟨c, x⟩ = t in u`, an explicit unpacking. -/
example :
    (cc% let ⟨k, c⟩ = fc un in c) =
      STm.letex "k" "c" (STm.app (STm.var "fc") (STm.var "un")) (STm.var "c") := by
  decide

/-- `(t : T)`, an ascription: a checking point, erased. -/
example : (cc% (e : ⊤)) = STm.asc (STm.var "e") (SType.capt SShape.top []) := by decide

/-- `ccProg% [k₁, …] t`, a program over a platform. -/
example :
    (ccProg% [k1, fs] λ(x : ⊤). x) =
      SProg.mk ["k1", "fs"] (STm.lam none "x" (SType.capt SShape.top []) (STm.var "x")) := by
  decide

/-- `any` and `fresh` are names to the lexer and atoms to the macro: no
new keyword, so `List.any` and the word `fresh` stay usable in every
importing module. -/
example : atomOfName `any = some .any := by decide

example : atomOfName `fresh = some .fresh := by decide

example : atomOfName `x.C = some (.sel "x" "C") := by decide

/-- Three or more components are rejected as a capture atom. -/
example : atomOfName `x.y.z = none := by decide

/-! ### The forms the Captures front end already carries, renamed -/

example : (cc% x) = STm.var "x" := by decide

example : (cc% x.a) = STm.proj (.var "x") "a" := by decide

example : (cc% x.a.b) = STm.proj (.proj (.var "x") "a") "b" := by decide

example : (cc% ( f x ).a) = STm.proj (.app (.var "f") (.var "x")) "a" := by decide

example : (ccShape% x.A) = SShape.sel "x" "A" := by decide

/-- A bare `x` is never a shape: writing `ccShape% x` fails at this
message. -/
example : tySelName `x = none := by decide

example : tySelName `x.a.A = none := by decide

example : tySelName `x.A = some ("x", "A") := by decide

example : nameParts `x [] = ["x"] := by decide

example : nameParts `x.a [] = ["x", "a"] := by decide

example : nameParts `x.a.b [] = ["x", "a", "b"] := by decide

/-! ## The version's programs

`File` abbreviates `μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}})` throughout. -/

/-- `File`. -/
def fileShape : SShape :=
  ccShape% μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}})

/-- **W2**, `process : (∀(x : File ^ {any}) ⊤) ^ {}`. -/
def W2src : SType :=
  ccTy% (∀(x : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ⊤) ^ {}

/-- **Z1**, `freshCell : (∀(u : ⊤) File ^ {fresh}) ^ {fs}`. -/
def Z1src : SType :=
  ccTy% (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs}

/-- **S1**, `withFile` with an explicit capture parameter over the
platform capability `fs`. -/
def S1src : SType :=
  ccTy% (∀(cp : μ(c. {C^ : {}..{fs}}))
            (∀(op : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {fs}) ⊤) ^ {cp.C}) ⊤ ^ {any})
              ^ {fs, cp}) ^ {fs}

/-- **The caller of `freshCell`**, a plain `let` the typer reads as a
`letex`, over the platform `k1, fs`. -/
def Z1callerSrc : SProg :=
  ccProg% [k1, fs] λ(fc : (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs}).
    λ(un : ⊤). let c = fc un in let w = c in λ(v : ⊤). v

/-- **The `withFile` escape**, written inside an enclosing scope so that
the callback's result `any` reads as that scope's root, the escape the
front end rejects. -/
def EscSrc : STm :=
  cc% λ(g : ⊤).
    let cb : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
                (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ^ {any}) ^ {}
      = λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). f
    in cb

/-- **A, the capture parameter that is called**
(`refute-capturescc.md:183`), a plain use of a capture-parameter arrow. -/
def P1src : STm :=
  cc% λ(h : (∀(u : ⊤) ⊤) ^ {any}). let z = unit in h z

/-- **`Z1_tail`**, the capture parameter applied twice through a `let`,
the `letex` way out at an existential answer. -/
def Z1TailSrc : STm :=
  cc% let c1 = fc un in fc un

end CapturesCCFrontend
