import Coercions.Classifiers.Frontend.Surface

/-!
# The surface notation

Syntax categories `clsKind`, `clsAtom`, `clsSet`, `clsShape`, `clsTy`,
`clsAns`, `clsTm` and `clsDefs`, with `clsDecl` and `platBinder` for a
program's header, expand the paper's notation into constructor applications of
`SKind`, `SAtom`, `SCap`, `SShape`, `SType`, `SAns`, `STm` and `SDefs`.  The
entry points are `clsKind%`, `clsAtom%`, `clsSet%`, `clsShape%`, `clsTy%`,
`clsAns%`, `cls%` and `clsDefs%`.  A whole program is
`clsProg% classifiers K₁, … platform [κ₁, …] t`, with an optional `uses C` and
an optional `kind K` before the body.  A program that declares no classifier
leaves out `classifiers`.

Names stay strings here.  Interning labels and computing de Bruijn indices is
the work of `Resolve.lean`.

## Kinds and projected atoms

A kind is `only[K₁, …]`, which keeps exactly those classifiers, `except[K₁, …]`,
which keeps all but those, or a union or intersection of two kinds.  `except[]`
keeps every classifier and `only[]` keeps none.  A capture atom may be read at
a kind, `a.only[K]`, and so may a set, `{…}.only[K]`, which projects each atom:
`{ctl, io}.only[K]` and `{ctl.only[K], io.only[K]}` are the same set.  A
capture member may be bounded by a kind, `{C^ : K}`, beside the set-bounded
`{C^ : lo..hi}`.  The two never collide, since a kind never starts where a set
does.

## The program header

`classifiers IO, ThreadLocal, Control extends ThreadLocal` declares the
classifiers, each a root or a child of one declared before it.  `platform
[ctl : Control, io : IO]` lists the platform's capabilities, outermost first,
each a plain binder or declared at a classifier.  The optional `uses C` and
`kind K` state the body's use set and kind, which the typer reads and does not
search.  The header words are not reserved.  They are keywords only inside a
header, and `only` and `except` only inside `clsKind`, `clsAtom` and `clsSet`.

## Shapes, types and answers

A shape (`clsShape`) is a declaration, a selection, an intersection, an arrow
or a box.  A type (`clsTy`) is a shape with a written capture set, `S ^ C`.
A bare shape where a type is expected has the empty set.  An answer (`clsAns`)
is a type, or `∃[c ⊑ C] T`, a type under one capture binder bounded by a set
of the enclosing scope.  Only a `let`'s annotation and an arrow's codomain are
answer positions.  Every other type position is a plain type.

## Arrows, lambdas and unpacking

`∀(x : T) U` leaves the arrow's own capture binder anonymous and
`∀[c](x : T) U` names it.  Lambdas are the same, `λ(x : T). t` and
`λ[c](x : T). t`.  `let ⟨c, x⟩ = t in u` unpacks an existential answer by hand,
with a capture binder for the witness and a term binder for the payload, both
visible only in `u`.

## Precedence

`^` is looser than the arrow and the box.  `∀(x : ⊤) ⊤ ^ {c}` is an arrow whose
codomain carries `{c}`, and `(∀(x : ⊤) ⊤) ^ {c}` puts the whole arrow under
`{c}`.  `□` takes its operand at the tightest level, so a capturing operand
needs parentheses, `□(⊤ ^ {f})`.  A bare `□⊤` is the box of a shape with no
set.  `∧` closes tighter than `^`.

## Capture atoms

A capture set is a comma separated list of identifiers, split by `nameParts`.
The name `any` is the atom `any` and `fresh` is the atom `fresh`.  Another
single name is a plain name.  Two components `x.C` select a capture member.
Three or more are rejected, unless a trailing bracket follows.  Then the last
component must be `only` or `except` and the rest is read as the base atom.
Neither `any` nor `fresh` enters Lean's token table, and neither do `cap`,
`unbox` and `letex`, so `List.any` and the like stay usable in importing
modules.  The member spellings `{C^ : lo..hi}` and `{C^ = c}` are those of the
Captures front end.

## The ascription

`(t : T)` is a checking point with no term of its own in either calculus.  It
is read only after the plain parenthesised term fails to match.
-/

namespace ClassifiersFrontend

open Lean

/-! ## The categories -/

declare_syntax_cat clsSet
declare_syntax_cat clsShape
declare_syntax_cat clsTy
declare_syntax_cat clsAns
declare_syntax_cat clsTm
declare_syntax_cat clsDefs

/-- A classifier kind: `only[K₁, …]`, `except[K₁, …]`, or a union or
intersection of two.  `only` and `except` are keywords inside this category
alone (`behavior := both`) and ordinary identifiers elsewhere. -/
declare_syntax_cat clsKind (behavior := both)
/-- `only[K₁, …]`, the empty kind when the list is empty. -/
syntax:max &"only" "[" ident,* "]" : clsKind
/-- `except[K₁, …]`, the kind of every classifier when the list is
empty. -/
syntax:max &"except" "[" ident,* "]" : clsKind
/-- `K ∪ L`. -/
syntax:65 clsKind:66 " ∪ " clsKind:65 : clsKind
/-- `K ∩ L`, tighter than `∪`. -/
syntax:70 clsKind:71 " ∩ " clsKind:70 : clsKind
/-- Parentheses. -/
syntax:max "(" clsKind ")" : clsKind

/-- A capture atom in a set: `x`, `κ`, `x.C`, `any`, `fresh`, or one of
those projected to a kind, `a.only[K]` or `a.except[K]`.  One `ident`,
split inside the macro, with an optional trailing bracket for the
projection. -/
declare_syntax_cat clsAtom
/-- `x`, `κ`, `x.C`, `any`, or `fresh`. -/
syntax:max ident : clsAtom
/-- `x.only[K]`, `x.except[K]`, `x.C.only[K]`, or `any.only[K]`: the
identifier's last component names the projection, the rest is the base
atom. -/
syntax:max ident "[" ident,* "]" : clsAtom

/-- `{a₁, …, aₙ}`, a capture set. -/
syntax:max "{" clsAtom,* "}" : clsSet
/-- `C.only[K]`, a projected set: `K` applied to every atom of `C`. -/
syntax:max clsSet "." &"only" "[" ident,* "]" : clsSet
/-- `C.except[K]`, a projected set. -/
syntax:max clsSet "." &"except" "[" ident,* "]" : clsSet

/-- A classifier declaration: a name, or a name declared as a child of
another. -/
declare_syntax_cat clsDecl
/-- A classifier with no parent. -/
syntax ident : clsDecl
/-- A classifier declared as a child of another. -/
syntax ident &"extends" ident : clsDecl

/-- A platform binder: a name, or a name declared at a classifier. -/
declare_syntax_cat platBinder
/-- A platform binder with no classifier. -/
syntax ident : platBinder
/-- A platform binder declared at a classifier. -/
syntax ident " : " ident : platBinder

/-- `⊤`. -/
syntax:max "⊤" : clsShape
/-- `⊥`. -/
syntax:max "⊥" : clsShape
/-- `{A : S..T}`, a type member declaration. -/
syntax:max "{" ident " : " clsShape ".." clsShape "}" : clsShape
/-- `{C^ : c₁..c₂}`, a capture member declaration. -/
syntax:max "{" ident "^" " : " clsSet ".." clsSet "}" : clsShape
/-- `{C^ : K}`, a kind-bounded capture member declaration. -/
syntax:max "{" ident "^" " : " clsKind "}" : clsShape
/-- `{a : T}`, a field declaration.  Its type is a capturing type. -/
syntax:max "{" ident " : " clsTy "}" : clsShape
/-- `x.A`, a type selection.  One `ident`, split inside the macro. -/
syntax:max ident : clsShape
/-- `μ(x. S)`, a recursive self shape. -/
syntax:max "μ" "(" ident "." clsShape ")" : clsShape
/-- `∀(x : T) U`, the arrow's own capture binder left anonymous. -/
syntax:60 "∀" "(" ident " : " clsTy ")" clsAns:60 : clsShape
/-- `∀[c](x : T) U`, the arrow's own capture binder named. -/
syntax:60 "∀" "[" ident "]" "(" ident " : " clsTy ")" clsAns:60 : clsShape
/-- `S ∧ T`, an intersection of shapes, right leaning. -/
syntax:65 clsShape:66 " ∧ " clsShape:65 : clsShape
/-- `□ T`, the box former, its operand at the tightest level. -/
syntax:max "□" clsTy:max : clsShape
/-- Parentheses. -/
syntax:max "(" clsShape ")" : clsShape

/-- `S ^ C`, a shape under a written capture set, the shape read at the
tightest level so that a capturing arrow or box needs its own
parentheses. -/
syntax:70 clsShape:max " ^ " clsSet : clsTy
/-- A bare shape elaborates the empty set. -/
syntax:60 clsShape:60 : clsTy
/-- Parentheses. -/
syntax:max "(" clsTy ")" : clsTy

/-- A plain type is an answer too. -/
syntax:60 clsTy:60 : clsAns
/-- `∃[c ⊑ C] T`, an existential answer. -/
syntax:60 "∃" "[" ident " ⊑ " clsSet "]" clsTy:60 : clsAns

/-- `x`, or `x.a`, or `x.a.b`.  One `ident`, split inside the macro. -/
syntax:max ident : clsTm
/-- `λ(x : T). t`, the arrow's own capture binder left anonymous. -/
syntax:max "λ" "(" ident " : " clsTy ")" "." clsTm:60 : clsTm
/-- `λ[c](x : T). t`, the arrow's own capture binder named. -/
syntax:max "λ" "[" ident "]" "(" ident " : " clsTy ")" "." clsTm:60 : clsTm
/-- `ν(x : S. d)`, an object literal: the self shape and its
definitions, no capture set of its own. -/
syntax:max "ν" "(" ident " : " clsShape "." clsDefs ")" : clsTm
/-- `t.a` on a receiver that is not an identifier. -/
syntax:80 clsTm:80 "." ident : clsTm
/-- `t u`, application, left leaning. -/
syntax:70 clsTm:70 clsTm:71 : clsTm
/-- `let x = t in u`, with an optional result answer. -/
syntax:max "let" ident (" : " clsAns)? " = " clsTm " in " clsTm:60 : clsTm
/-- `let ⟨c, x⟩ = t in u`, an explicit unpacking: a capture binder for the
witness, then a term binder for the payload, both read only in `u`. -/
syntax:max "let" "⟨" ident "," ident "⟩" " = " clsTm " in " clsTm:60 : clsTm
/-- `□ t`, direct style, a box value written by hand. -/
syntax:max "□" clsTm:max : clsTm
/-- `C ⊸ t`, direct style, an unboxing written by hand. -/
syntax:max clsSet " ⊸ " clsTm:max : clsTm
/-- `(t : T)`, an ascription: a checking point, erased. -/
syntax:max "(" clsTm " : " clsTy ")" : clsTm
/-- Parentheses. -/
syntax:max "(" clsTm ")" : clsTm

/-- `{type A = S}`, a type member definition, its body a shape. -/
syntax:max "{" "type" ident " = " clsShape "}" : clsDefs
/-- `{C^ = c}`, a capture member definition. -/
syntax:max "{" ident "^" " = " clsSet "}" : clsDefs
/-- `{a = t}`, a term member definition. -/
syntax:max "{" ident " = " clsTm "}" : clsDefs
/-- `d ∧ e`, right leaning. -/
syntax:65 clsDefs:66 " ∧ " clsDefs:65 : clsDefs

/-- Expand a `clsKind` into an `SKind`. -/
syntax:max "clsKind% " clsKind : term
/-- Expand a `clsAtom` into an `SAtom`. -/
syntax:max "clsAtom% " clsAtom : term
/-- Expand a `clsSet` into an `SCap`. -/
syntax:max "clsSet% " clsSet : term
/-- Expand a `clsShape` into an `SShape`. -/
syntax:max "clsShape% " clsShape : term
/-- Expand a `clsTy` into an `SType`. -/
syntax:max "clsTy% " clsTy : term
/-- Expand a `clsAns` into an `SAns`. -/
syntax:max "clsAns% " clsAns : term
/-- Expand a `clsTm` into an `STm`. -/
syntax:max "cls% " clsTm : term
/-- Expand a `clsDefs` into an `SDefs`. -/
syntax:max "clsDefs% " clsDefs : term
/-- Expand a whole program: the classifiers it declares, the platform
capabilities with their classifiers, outermost first, an optional
declared use set, an optional declared kind, and the body. -/
syntax:max "clsProg% " (&"classifiers" clsDecl,+)? &"platform" "[" platBinder,* "]"
  (&"uses" clsSet)? (&"kind" clsKind)? clsTm : term

/-! ## Taking a hierarchical identifier apart -/

/-- The components of a name, outermost first, as strings. -/
def nameParts : Name → List String → List String
  | .anonymous, acc => acc
  | .str p s, acc => nameParts p (s :: acc)
  | .num p i, acc => nameParts p (toString i :: acc)

/-- The receiver and the label of a name in shape position.  Only a two
component name is a shape, the selection `x.A`. -/
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
  | some (.proj ..) | none => Macro.throwErrorAt x "a capture atom is any, fresh, a name, or x.C"

/-- A `String` literal from an identifier's own name, with no splitting. -/
private def str (x : Ident) : TSyntax `term := quote x.getId.toString

/-- A `List String` literal from an array of identifiers' own names. -/
private def strs (xs : Array Ident) : TSyntax `term :=
  quote (xs.toList.map (·.getId.toString))

/-- A projected atom from an identifier and its bracket.  The last component
must be `only` or `except` and the rest is the base atom. -/
private def projAtomOfIdent (x : Ident) (ks : Array Ident) : MacroM (TSyntax `term) := do
  let parts := nameParts x.getId []
  let base (rest : List String) : Ident :=
    mkIdent (rest.foldl (fun n s => Name.str n s) .anonymous)
  match parts.reverse with
  | "only" :: rest => do
      let a ← capAtomOfIdent (base rest.reverse)
      `(SAtom.proj $a (SKind.only $(strs ks)))
  | "except" :: rest => do
      let a ← capAtomOfIdent (base rest.reverse)
      `(SAtom.proj $a (SKind.except $(strs ks)))
  | _ => Macro.throwErrorAt x "a projected atom is x.only[K] or x.except[K]"

/-- A classifier declaration, as a name paired with the parent it
extends. -/
private def clsDeclTerm : TSyntax `clsDecl → MacroM (TSyntax `term)
  | `(clsDecl| $c:ident) => `(($(str c), (none : Option String)))
  | `(clsDecl| $c:ident extends $p:ident) => `(($(str c), some $(str p)))
  | _ => Macro.throwUnsupported

/-- A platform binder, as a name paired with the classifier it is
declared at. -/
private def platBinderTerm : TSyntax `platBinder → MacroM (TSyntax `term)
  | `(platBinder| $k:ident) => `(($(str k), (none : Option String)))
  | `(platBinder| $k:ident : $c:ident) => `(($(str k), some $(str c)))
  | _ => Macro.throwUnsupported

/-! ## The macros -/

macro_rules
  | `(clsKind% only [ $ks,* ]) => `(SKind.only $(strs ks.getElems))
  | `(clsKind% except [ $ks,* ]) => `(SKind.except $(strs ks.getElems))
  | `(clsKind% $K:clsKind ∪ $L:clsKind) => `(SKind.union (clsKind% $K) (clsKind% $L))
  | `(clsKind% $K:clsKind ∩ $L:clsKind) => `(SKind.inter (clsKind% $K) (clsKind% $L))
  | `(clsKind% ( $K:clsKind )) => `(clsKind% $K)

macro_rules
  | `(clsAtom% $x:ident) => capAtomOfIdent x
  | `(clsAtom% $x:ident [ $ks,* ]) => projAtomOfIdent x ks.getElems

macro_rules
  | `(clsSet% { $as:clsAtom,* }) => do
      let mut acc ← `(([] : SCap))
      for a in as.getElems.reverse do
        acc ← `((clsAtom% $a) :: $acc)
      return acc
  | `(clsSet% $C:clsSet . only [ $ks,* ]) =>
      `((clsSet% $C).map (SAtom.proj · (SKind.only $(strs ks.getElems))))
  | `(clsSet% $C:clsSet . except [ $ks,* ]) =>
      `((clsSet% $C).map (SAtom.proj · (SKind.except $(strs ks.getElems))))

macro_rules
  | `(clsShape% ⊤) => `(SShape.top)
  | `(clsShape% ⊥) => `(SShape.bot)
  | `(clsShape% { $A:ident : $S:clsShape .. $T:clsShape }) =>
      `(SShape.typ $(str A) (clsShape% $S) (clsShape% $T))
  | `(clsShape% { $C:ident ^ : $lo:clsSet .. $hi:clsSet }) =>
      `(SShape.cap $(str C) (clsSet% $lo) (clsSet% $hi))
  | `(clsShape% { $C:ident ^ : $K:clsKind }) =>
      `(SShape.capk $(str C) (clsKind% $K))
  | `(clsShape% { $a:ident : $T:clsTy }) => `(SShape.fld $(str a) (clsTy% $T))
  | `(clsShape% $x:ident) => surfaceShapeOfIdent x
  | `(clsShape% μ ( $x:ident . $S:clsShape )) => `(SShape.mu $(str x) (clsShape% $S))
  | `(clsShape% ∀ ( $x:ident : $T:clsTy ) $U:clsAns) =>
      `(SShape.all none $(str x) (clsTy% $T) (clsAns% $U))
  | `(clsShape% ∀ [ $k:ident ] ( $x:ident : $T:clsTy ) $U:clsAns) =>
      `(SShape.all (some $(str k)) $(str x) (clsTy% $T) (clsAns% $U))
  | `(clsShape% $S:clsShape ∧ $T:clsShape) => `(SShape.and (clsShape% $S) (clsShape% $T))
  | `(clsShape% □ $T:clsTy) => `(SShape.box (clsTy% $T))
  | `(clsShape% ( $S:clsShape )) => `(clsShape% $S)

macro_rules
  | `(clsTy% $S:clsShape ^ $C:clsSet) => `(SType.capt (clsShape% $S) (clsSet% $C))
  | `(clsTy% $S:clsShape) => `(SType.capt (clsShape% $S) [])
  | `(clsTy% ( $T:clsTy )) => `(clsTy% $T)

macro_rules
  | `(clsAns% $T:clsTy) => `(SAns.ty (clsTy% $T))
  | `(clsAns% ∃ [ $k:ident ⊑ $C:clsSet ] $T:clsTy) =>
      `(SAns.ex $(str k) (clsSet% $C) (clsTy% $T))

macro_rules
  | `(cls% $x:ident) => surfaceTmOfIdent x
  | `(cls% λ ( $x:ident : $T:clsTy ) . $t:clsTm) =>
      `(STm.lam none $(str x) (clsTy% $T) (cls% $t))
  | `(cls% λ [ $k:ident ] ( $x:ident : $T:clsTy ) . $t:clsTm) =>
      `(STm.lam (some $(str k)) $(str x) (clsTy% $T) (cls% $t))
  | `(cls% ν ( $x:ident : $S:clsShape . $d:clsDefs )) =>
      `(STm.obj $(str x) (clsShape% $S) (clsDefs% $d))
  | `(cls% $t:clsTm . $a:ident) => `(STm.proj (cls% $t) $(str a))
  | `(cls% $t:clsTm $u:clsTm) => `(STm.app (cls% $t) (cls% $u))
  | `(cls% let $x:ident = $t:clsTm in $u:clsTm) =>
      `(STm.«let» $(str x) (none : Option SAns) (cls% $t) (cls% $u))
  | `(cls% let $x:ident : $U:clsAns = $t:clsTm in $u:clsTm) =>
      `(STm.«let» $(str x) (some (clsAns% $U)) (cls% $t) (cls% $u))
  | `(cls% let ⟨ $k:ident , $x:ident ⟩ = $t:clsTm in $u:clsTm) =>
      `(STm.letex $(str k) $(str x) (cls% $t) (cls% $u))
  | `(cls% □ $t:clsTm) => `(STm.box (cls% $t))
  | `(cls% $C:clsSet ⊸ $t:clsTm) => `(STm.unbox (clsSet% $C) (cls% $t))
  | `(cls% ( $t:clsTm : $T:clsTy )) => `(STm.asc (cls% $t) (clsTy% $T))
  | `(cls% ( $t:clsTm )) => `(cls% $t)

macro_rules
  | `(clsDefs% { type $A:ident = $S:clsShape }) =>
      `(SDefs.typ $(str A) (clsShape% $S))
  | `(clsDefs% { $C:ident ^ = $c:clsSet }) =>
      `(SDefs.cap $(str C) (clsSet% $c))
  | `(clsDefs% { $a:ident = $t:clsTm }) =>
      `(SDefs.trm $(str a) (cls% $t))
  | `(clsDefs% $d:clsDefs ∧ $e:clsDefs) => `(SDefs.and (clsDefs% $d) (clsDefs% $e))

macro_rules
  | `(clsProg% $[classifiers $ds,*]? platform [ $ps,* ] $[uses $u]? $[kind $k]? $t:clsTm) => do
      let dsTerms ← match ds with
        | some ds => ds.getElems.mapM clsDeclTerm
        | none => pure #[]
      let psTerms ← ps.getElems.mapM platBinderTerm
      let usesTerm ← match u with
        | some s => `(some (clsSet% $s))
        | none => `((none : Option SCap))
      let kindTerm ← match k with
        | some kk => `(some (clsKind% $kk))
        | none => `((none : Option SKind))
      `(SProg.mk [$dsTerms,*] [$psTerms,*] $usesTerm $kindTerm (cls% $t))

/-! ## Checks

One check per surface form.  Each reduces in the kernel, so `by decide`
proves it. -/

example : (clsSet% {}) = ([] : SCap) := by decide

/-- A capture set, with the reserved names and a capture selection. -/
example : (clsSet% {fs, cp.C, any, fresh}) =
    [SAtom.name "fs", SAtom.sel "cp" "C", SAtom.any, SAtom.fresh] := by decide

/-- A bare shape elaborates the empty set. -/
example : (clsTy% ⊤) = SType.capt SShape.top [] := by decide

/-- `S ^ C`, a shape under a written set. -/
example : (clsTy% ⊤ ^ {f}) = SType.capt SShape.top [SAtom.name "f"] := by decide

/-- `∀(x : T) U`, the arrow binder anonymous.  The written set belongs to the
codomain, since the arrow is not parenthesised. -/
example :
    (clsTy% ∀(x : ⊤) ⊤ ^ {c}) =
      SType.capt (SShape.all none "x" (SType.capt SShape.top []) (SAns.ty (SType.capt SShape.top [SAtom.name "c"])))
        [] := by
  decide

/-- The same arrow parenthesised: the set sits on the whole arrow. -/
example :
    (clsTy% (∀(x : ⊤) ⊤) ^ {c}) =
      SType.capt (SShape.all none "x" (SType.capt SShape.top []) (SAns.ty (SType.capt SShape.top []))) [SAtom.name "c"] := by
  decide

/-- `∀[c](x : T) U`, the arrow binder named. -/
example :
    (clsTy% ∀[k](x : ⊤) ⊤ ^ {k}) =
      SType.capt (SShape.all (some "k") "x" (SType.capt SShape.top []) (SAns.ty (SType.capt SShape.top [SAtom.name "k"])))
        [] := by
  decide

/-- `∃[c ⊑ C] T`, an existential answer: the binder scopes the type, its
own bound read in the outer scope. -/
example :
    (clsAns% ∃[w ⊑ {fs, u}] ⊤ ^ {w}) =
      SAns.ex "w" [SAtom.name "fs", SAtom.name "u"] (SType.capt SShape.top [SAtom.name "w"]) := by
  decide

/-- A plain type is an answer too. -/
example : (clsAns% ⊤ ^ {f}) = SAns.ty (SType.capt SShape.top [SAtom.name "f"]) := by decide

/-- `{C^ : lo..hi}`, a capture member declaration, the Captures front
end's spelling. -/
example :
    (clsShape% {C^ : {}..{k1, k2}}) =
      SShape.cap "C" [] [SAtom.name "k1", SAtom.name "k2"] := by
  decide

/-- `{C^ = c}`, a capture member definition. -/
example : (clsDefs% {C^ = {fs}}) = SDefs.cap "C" [SAtom.name "fs"] := by decide

/-- `□(T ^ {..})`, the box former, its operand parenthesised to carry a
set of its own. -/
example : (clsShape% □(⊤ ^ {f})) = SShape.box (SType.capt SShape.top [SAtom.name "f"]) := by decide

/-- `□ x`, a box value, direct style. -/
example : (cls% □ f) = STm.box (STm.var "f") := by decide

/-- `{..} ⊸ x`, an unboxing, direct style. -/
example : (cls% {k1} ⊸ e) = STm.unbox [SAtom.name "k1"] (STm.var "e") := by decide

/-- `λ[c](x : T). t`, a lambda with its arrow binder named. -/
example :
    (cls% λ[c](x : ⊤ ^ {c}). x) =
      STm.lam (some "c") "x" (SType.capt SShape.top [SAtom.name "c"]) (STm.var "x") := by
  decide

/-- `let ⟨c, x⟩ = t in u`, an explicit unpacking. -/
example :
    (cls% let ⟨k, c⟩ = fc un in c) =
      STm.letex "k" "c" (STm.app (STm.var "fc") (STm.var "un")) (STm.var "c") := by
  decide

/-- `(t : T)`, an ascription: a checking point, erased. -/
example : (cls% (e : ⊤)) = STm.asc (STm.var "e") (SType.capt SShape.top []) := by decide

/-- `clsProg% platform [κ₁, …] t`, a program with no classifier and no
declared use set or kind. -/
example :
    (clsProg% platform [k1, fs] λ(x : ⊤). x) =
      SProg.mk [] [("k1", none), ("fs", none)] none none
        (STm.lam none "x" (SType.capt SShape.top []) (STm.var "x")) := by
  decide

/-- `classifiers K extends L`, a classifier declared as a child of
another. -/
example :
    (clsProg% classifiers IO, Control extends IO platform [io : IO] io) =
      SProg.mk [("IO", none), ("Control", some "IO")] [("io", some "IO")] none none
        (STm.var "io") := by
  decide

/-- `only[K]` and `except[K]`, the two kind formers. -/
example : (clsKind% only[Control]) = SKind.only ["Control"] := by decide

example : (clsKind% except[ThreadLocal]) = SKind.except ["ThreadLocal"] := by decide

/-- `∩` binds tighter than `∪`. -/
example :
    (clsKind% only[IO] ∪ only[Control] ∩ except[IO]) =
      SKind.union (.only ["IO"]) (.inter (.only ["Control"]) (.except ["IO"])) := by
  decide

/-- `a.only[K]`, a projected atom, and `{a, b}.only[K]`, a projected set,
distributing the kind over every atom. -/
example :
    (clsAtom% x.only[Control]) = SAtom.proj (.name "x") (.only ["Control"]) := by decide

example :
    (clsAtom% x.C.except[ThreadLocal]) =
      SAtom.proj (.sel "x" "C") (.except ["ThreadLocal"]) := by decide

example :
    (clsAtom% any.only[Control]) = SAtom.proj .any (.only ["Control"]) := by decide

example :
    (clsSet% {ctl, io}.only[Control]) =
      [SAtom.proj (.name "ctl") (.only ["Control"]), SAtom.proj (.name "io") (.only ["Control"])] := by
  decide

/-- **CE1**, `Try.apply`'s header: classifiers, a classified platform, a
declared use set and a declared kind. -/
example :
    (clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
       platform [ctl : Control, io : IO]
       uses {ctl, io}.only[Control]
       kind only[Control]
       λ(u : ⊤). u) =
      SProg.mk [("IO", none), ("ThreadLocal", none), ("Control", some "ThreadLocal")]
        [("ctl", some "Control"), ("io", some "IO")]
        (some [SAtom.proj (.name "ctl") (.only ["Control"]), SAtom.proj (.name "io") (.only ["Control"])])
        (some (.only ["Control"]))
        (STm.lam none "u" (SType.capt SShape.top []) (STm.var "u")) := by
  decide

/-- `only` and `except` are keywords only inside `clsKind`, `clsAtom` and
`clsSet`, so `only` stays an identifier elsewhere and `simp only […]` still
elaborates. -/
def only : Nat := 0

example : only = 0 := rfl

example (n : Nat) : n + 0 = n := by simp only [Nat.add_zero]

/-- The words of a program header stay ordinary identifiers too. -/
example (classifiers platform uses kind : Nat) :
    classifiers + platform + uses + kind = kind + uses + platform + classifiers := by
  omega

/-- `{C^ : K}`, `{C^ : lo..hi}` and `{a : T}` are three different shapes.  A
field whose type is a capturing type is a field, not a member. -/
example : (clsShape% {C^ : only[Control]}) = SShape.capk "C" (.only ["Control"]) := by decide

example :
    (clsShape% {C^ : {k}..{k}}) = SShape.cap "C" [SAtom.name "k"] [SAtom.name "k"] := by decide

example :
    (clsShape% {run : ⊤ ^ {z.C}}) = SShape.fld "run" (SType.capt SShape.top [SAtom.sel "z" "C"]) := by
  decide

/-- `any` and `fresh` are names to the lexer and atoms to the macro. -/
example : atomOfName `any = some .any := by decide

example : atomOfName `fresh = some .fresh := by decide

example : atomOfName `x.C = some (.sel "x" "C") := by decide

/-- Three or more components are rejected as a capture atom. -/
example : atomOfName `x.y.z = none := by decide

/-! ### The forms shared with the Captures front end -/

example : (cls% x) = STm.var "x" := by decide

example : (cls% x.a) = STm.proj (.var "x") "a" := by decide

example : (cls% x.a.b) = STm.proj (.proj (.var "x") "a") "b" := by decide

example : (cls% ( f x ).a) = STm.proj (.app (.var "f") (.var "x")) "a" := by decide

example : (clsShape% x.A) = SShape.sel "x" "A" := by decide

/-- A bare `x` is never a shape. -/
example : tySelName `x = none := by decide

example : tySelName `x.a.A = none := by decide

example : tySelName `x.A = some ("x", "A") := by decide

example : nameParts `x [] = ["x"] := by decide

example : nameParts `x.a [] = ["x", "a"] := by decide

example : nameParts `x.a.b [] = ["x", "a", "b"] := by decide

/-! ## The version's programs

`File` abbreviates `μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}})`. -/

/-- `File`. -/
def fileShape : SShape :=
  clsShape% μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}})

/-- **W2**, `process : (∀(x : File ^ {any}) ⊤) ^ {}`. -/
def W2src : SType :=
  clsTy% (∀(x : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ⊤) ^ {}

/-- **Z1**, `freshCell : (∀(u : ⊤) File ^ {fresh}) ^ {fs}`. -/
def Z1src : SType :=
  clsTy% (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs}

/-- **S1**, `withFile` with an explicit capture parameter over the
platform capability `fs`. -/
def S1src : SType :=
  clsTy% (∀(cp : μ(c. {C^ : {}..{fs}}))
            (∀(op : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {fs}) ⊤) ^ {cp.C}) ⊤ ^ {any})
              ^ {fs, cp}) ^ {fs}

/-- **The caller of `freshCell`**, a plain `let` that the typer reads as a
`letex`. -/
def Z1callerSrc : SProg :=
  clsProg% platform [k1, fs]
    λ(fc : (∀(u : ⊤) μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {fresh}) ^ {fs}).
    λ(un : ⊤). let c = fc un in let w = c in λ(v : ⊤). v

/-- **The `withFile` escape**, written inside an enclosing scope so that the
callback's result `any` reads as that scope's root.  The front end rejects it. -/
def EscSrc : STm :=
  cls% λ(g : ⊤).
    let cb : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
                (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ^ {any}) ^ {}
      = λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). f
    in cb

/-- **A capture parameter that is called.** -/
def P1src : STm :=
  cls% λ(h : (∀(u : ⊤) ⊤) ^ {any}). let z = unit in h z

/-- **`Z1_tail`**, the capture parameter applied twice through a `let`, which
needs the `letex` way out at an existential answer. -/
def Z1TailSrc : STm :=
  cls% let c1 = fc un in fc un

/-! ## The classifier examples -/

/-- **CE1**, `Try.apply`: a declared use set and kind, both the projection of
the platform to `Control`, and a codomain whose own member is bounded by the
same projection.  The types of `b` and `f` are ascriptions, since a `let`
annotation is the answer of the whole `let`. -/
def CE1src : SProg :=
  clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
    platform [ctl : Control, io : IO]
    uses {ctl, io}.only[Control]
    kind only[Control]
    let b = ((λ(u : ⊤ ^ {}). u) : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io}.only[Control]) in
    let f = ((λ(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io}).
                ν(z : {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}. {body = λ(u : ⊤ ^ {}). u})) :
              (∀(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io})
                μ(z. {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}) ^ {body.only[Control]}) ^ {}) in
    let r = f b in
    r

/-- **CE2**, `Future.apply`: the domain writes `any` under a filter, which
resolves to the arrow's own binder under the same filter. -/
def CE2src : SProg :=
  clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
    platform [tl : ThreadLocal, ctl : Control, io : IO]
    uses {tl, ctl, io}.except[ThreadLocal]
    kind except[ThreadLocal]
    let b = ((λ(u : ⊤ ^ {}). u) : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {tl, ctl, io}.except[ThreadLocal]) in
    let f = ((λ(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {any.except[ThreadLocal]}).
                ν(z : {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}. {body = λ(u : ⊤ ^ {}). u})) :
              (∀(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {any.except[ThreadLocal]})
                μ(z. {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}) ^ {body}) ^ {}) in
    let r = f b in
    r

/-- **CE3**, a client of a kind-bounded member.  Two literals, each with the
member set to one platform capability, both pass through `c`, whose parameter
bounds the member by kind alone. -/
def CE3src : SProg :=
  clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
    platform [k1 : Control, k2 : Control]
    uses {k1, k2}
    kind only[Control]
    let c : (∀(x : μ(z. {C^ : only[Control]} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}) ^ {k1, k2})
               (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {x, x.C}) ^ {} =
              λ(x : μ(z. {C^ : only[Control]} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}) ^ {k1, k2}).
                λ(u : ⊤ ^ {}). let g = x.run in g u in
    let a = ν(z : {C^ : {k1}..{k1}} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}.
                  {C^ = {k1}} ∧ {run = λ(u : ⊤ ^ {}). u}) in
    let b = ν(z : {C^ : {k2}..{k2}} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}.
                  {C^ = {k2}} ∧ {run = λ(u : ⊤ ^ {}). u}) in
    let ga = c a in
    let gb = c b in
    c

end ClassifiersFrontend
