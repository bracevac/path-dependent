import Coercions.Nominal.Frontend.Surface

/-!
# The surface notation of the pDOT front end

Three syntax categories, `pdcTy`, `pdcTm` and `pdcDef`, hold the paper's
notation for types, terms and definitions of pDOT.  Three entry points,
`pdcTy%`, `pdc%` and `pdcDefs%`, expand a piece of that notation into an
`SType`, `STm` or `SDefs` (plan XI D-2).  Names stay strings.  `Resolve.lean`
turns them into indices.

The names differ from the paths front end, which owns `pdot%`, `pdotTy%` and
`pdotDefs%`, and from the vanilla front end, which owns `dot%`.  All of them
expand in one module that imports the three front ends.

Application is left leaning at 70 and projection binds tighter at 80.  `∧` is
right leaning at 65.  `λ`, `μ`, `∀` and `let` extend as far right as they can.
Closed forms and parentheses sit at `max`.

An object literal is `ν(x : T) {d₁, …, dₙ}`, or `ν(x) {d₁, …, dₙ}` with the self
type left to inference.  A definition is `type A = T`, `a = t` or `a : T = t`.
The macro folds the definitions from the left onto `SDefs.nil`, one step per
definition in text order, so the spine grows on the right as pDOT's `Defs` do.
`pdcDefs% {…}` expands to the same fold.

A definition list needs a space after each comma.  `Paths/FCdot/Debruijn.lean`
declares the global token `,x`, so `{a = s,xs = s}` does not parse while
`{a = s, xs = s}` does.

Lean's lexer reads `x.a.b` as one `ident` with three components, so the macro
splits it.  In term position, `x` is a variable and `x.a.b` is two nested
projections.  After a receiver that is not an identifier, as in `(f x).a.b`, the
lexer again reads `a.b` as one `ident`, and the macro folds one projection per
component.  In type position a name needs two components or more.  Every
component but the last is a field step.  The last is either the keyword `type`
or a type label.  A name without a dot is never a type, since a selection needs
a receiver.

`Type` is a Lean keyword, so the label `Type` is written `«Type»`.  The name
still reads `Type`, since a name is quoted with `x.getId.toString`.  So are the
other keywords used as labels: `«fun»`, `«at»` and `«type»`.  The macro reads
the name, the kernel never does.

The same lexer rule asks for a space after the dot of `λx. t`.  Written `λx.x`,
the body and the dot merge into the one name `x.x`.
-/

namespace NominalFrontend

open Lean

/-! ## The three categories -/

declare_syntax_cat pdcTy
declare_syntax_cat pdcTm
declare_syntax_cat pdcDef

/-- `⊤`, the top type. -/
syntax:max "⊤" : pdcTy
/-- `⊥`, the bottom type. -/
syntax:max "⊥" : pdcTy
/-- `{A : S..T}`, a type member declaration. -/
syntax:max "{" ident " : " pdcTy ".." pdcTy "}" : pdcTy
/-- `{a : T}`, a term member declaration. -/
syntax:max "{" ident " : " pdcTy "}" : pdcTy
/-- `x.A`, `x.a.A`, `x.type`, `x.a.type`.  One `ident`, split by the macro. -/
syntax:max ident : pdcTy
/-- `μ(x. T)`, a recursive self type. -/
syntax:max "μ" "(" ident "." pdcTy ")" : pdcTy
/-- `∀(x : S) T`, a dependent function type. -/
syntax:max "∀" "(" ident " : " pdcTy ")" pdcTy:60 : pdcTy
/-- `S ∧ T`, an intersection, right leaning. -/
syntax:65 pdcTy:66 " ∧ " pdcTy:65 : pdcTy
/-- Parentheses. -/
syntax:max "(" pdcTy ")" : pdcTy

/-- `x`, `x.a` or `x.a.b`.  One `ident`, split by the macro. -/
syntax:max ident : pdcTm
/-- `λ(x : T). t`. -/
syntax:max "λ" "(" ident " : " pdcTy ")" "." pdcTm:60 : pdcTm
/-- `λx. t`, a lambda whose domain is left to inference. -/
syntax:max "λ" ident "." pdcTm:60 : pdcTm
/-- `ν(x : T) {d₁, …, dₙ}`, an object literal with its self type. -/
syntax:max "ν" "(" ident " : " pdcTy ")" "{" sepBy1(pdcDef, ", ") "}" : pdcTm
/-- `ν(x) {d₁, …, dₙ}`, an object literal whose self type is left to
inference. -/
syntax:max "ν" "(" ident ")" "{" sepBy1(pdcDef, ", ") "}" : pdcTm
/-- `t.a` on a receiver that is not an identifier, for instance `(f x).a`. -/
syntax:80 pdcTm:80 "." ident : pdcTm
/-- `t u`, application, left leaning. -/
syntax:70 pdcTm:70 pdcTm:71 : pdcTm
/-- `let x = t in u`, with an optional written type. -/
syntax:max "let" ident (" : " pdcTy)? " = " pdcTm " in " pdcTm:60 : pdcTm
/-- Parentheses. -/
syntax:max "(" pdcTm ")" : pdcTm
/-- `(t : T)`, an ascription. -/
syntax:max "(" pdcTm " : " pdcTy ")" : pdcTm

/-- `type A = T`, a type member definition. -/
syntax "type" ident " = " pdcTy : pdcDef
/-- `a = t`, a term member definition. -/
syntax ident " = " pdcTm : pdcDef
/-- `a : T = t`, a term member definition with a written type. -/
syntax ident " : " pdcTy " = " pdcTm : pdcDef

/-- Expand a `pdcTy` into an `SType`. -/
syntax:max "pdcTy% " pdcTy : term
/-- Expand a `pdcTm` into an `STm`. -/
syntax:max "pdc% " pdcTm : term
/-- Expand a definition list into an `SDefs`. -/
syntax:max "pdcDefs% " "{" sepBy1(pdcDef, ", ") "}" : term

/-! ## Taking a hierarchical identifier apart -/

/-- The components of a name, outermost first, as strings.  Lean has no
`Name.components`, so the walk is written out. -/
def nameParts : Name → List String → List String
  | .anonymous, acc => acc
  | .str p s, acc => nameParts p (s :: acc)
  | .num p i, acc => nameParts p (toString i :: acc)

/-- A path built from a root and its field steps, root first. -/
def pathOfParts (x : String) (steps : List String) : SPath :=
  steps.foldl SPath.sel (.var x)

/-- The reading of a name in type position. -/
def tyOfName (n : Name) : Option SType :=
  match nameParts n [] with
  | [] | [_] => none
  | x :: rest =>
      match rest.reverse with
      | [] => none
      | last :: midsRev =>
          let p := pathOfParts x midsRev.reverse
          if last = "type" then some (.sngl p) else some (.sel p last)

/-- An `SPath` as syntax, for the macro's output. -/
private def quoteSPath : SPath → MacroM (TSyntax `term)
  | .var x => `(SPath.var $(quote x))
  | .sel p a => do `(SPath.sel $(← quoteSPath p) $(quote a))

/-- A surface identifier in type position. -/
private def surfaceTyOfIdent (x : Ident) : MacroM (TSyntax `term) := do
  match tyOfName x.getId with
  | some (.sngl p) => `(SType.sngl $(← quoteSPath p))
  | some (.sel p A) => `(SType.sel $(← quoteSPath p) $(quote A))
  | _ =>
    Macro.throwErrorAt x
      "a surface type built from a name is p.A or p.type, with two components or more"

/-- A surface identifier in term position. -/
private def surfaceTmOfIdent (x : Ident) : MacroM (TSyntax `term) := do
  match nameParts x.getId [] with
  | [] => Macro.throwErrorAt x "the surface term needs a name here"
  | head :: rest =>
    let mut acc ← `(STm.var $(quote head))
    for c in rest do
      acc ← `(STm.proj $acc $(quote c))
    return acc

/-! ## The macros -/

macro_rules
  | `(pdcTy% ⊤) => `(SType.top)
  | `(pdcTy% ⊥) => `(SType.bot)
  | `(pdcTy% { $A:ident : $S:pdcTy .. $T:pdcTy }) =>
      `(SType.typ $(quote A.getId.toString) (pdcTy% $S) (pdcTy% $T))
  | `(pdcTy% { $a:ident : $T:pdcTy }) =>
      `(SType.fld $(quote a.getId.toString) (pdcTy% $T))
  | `(pdcTy% $x:ident) => surfaceTyOfIdent x
  | `(pdcTy% μ ( $x:ident . $T:pdcTy )) =>
      `(SType.mu $(quote x.getId.toString) (pdcTy% $T))
  | `(pdcTy% ∀ ( $x:ident : $S:pdcTy ) $T:pdcTy) =>
      `(SType.all $(quote x.getId.toString) (pdcTy% $S) (pdcTy% $T))
  | `(pdcTy% $S:pdcTy ∧ $T:pdcTy) => `(SType.and (pdcTy% $S) (pdcTy% $T))
  | `(pdcTy% ( $T:pdcTy )) => `(pdcTy% $T)

/-- One definition onto the spine `acc` built so far. -/
def defStep (acc : TSyntax `term) (d : TSyntax `pdcDef) : MacroM (TSyntax `term) :=
  match d with
  | `(pdcDef| type $A:ident = $T:pdcTy) =>
      `(SDefs.typ $acc $(quote A.getId.toString) (pdcTy% $T))
  | `(pdcDef| $a:ident = $t:pdcTm) =>
      `(SDefs.trm $acc $(quote a.getId.toString) (none : Option SType) (pdc% $t))
  | `(pdcDef| $a:ident : $T:pdcTy = $t:pdcTm) =>
      `(SDefs.trm $acc $(quote a.getId.toString) (some (pdcTy% $T)) (pdc% $t))
  | _ => Macro.throwUnsupported

/-- The definitions folded from the left onto `SDefs.nil`, in text order. -/
def foldDefs (ds : Array (TSyntax `pdcDef)) : MacroM (TSyntax `term) := do
  let mut acc ← `(SDefs.nil)
  for d in ds do
    acc ← defStep acc d
  return acc

/-- `t.a` with `a` one `ident` of one or more components, one projection per
component. -/
private def projOfIdent (t : TSyntax `term) (a : Ident) : MacroM (TSyntax `term) := do
  let mut acc := t
  for c in nameParts a.getId [] do
    acc ← `(STm.proj $acc $(quote c))
  return acc

macro_rules
  | `(pdc% $x:ident) => surfaceTmOfIdent x
  | `(pdc% λ ( $x:ident : $T:pdcTy ) . $t:pdcTm) =>
      `(STm.lam $(quote x.getId.toString) (some (pdcTy% $T)) (pdc% $t))
  | `(pdc% λ $x:ident . $t:pdcTm) =>
      `(STm.lam $(quote x.getId.toString) (none : Option SType) (pdc% $t))
  | `(pdc% ν ( $x:ident : $T:pdcTy ) { $ds:pdcDef,* }) => do
      `(STm.obj $(quote x.getId.toString) (some (pdcTy% $T)) $(← foldDefs ds.getElems))
  | `(pdc% ν ( $x:ident ) { $ds:pdcDef,* }) => do
      `(STm.obj $(quote x.getId.toString) (none : Option SType) $(← foldDefs ds.getElems))
  | `(pdc% $t:pdcTm . $a:ident) => do projOfIdent (← `(pdc% $t)) a
  | `(pdc% $t:pdcTm $u:pdcTm) => `(STm.app (pdc% $t) (pdc% $u))
  | `(pdc% let $x:ident = $t:pdcTm in $u:pdcTm) =>
      `(STm.«let» $(quote x.getId.toString) (none : Option SType) (pdc% $t) (pdc% $u))
  | `(pdc% let $x:ident : $T:pdcTy = $t:pdcTm in $u:pdcTm) =>
      `(STm.«let» $(quote x.getId.toString) (some (pdcTy% $T)) (pdc% $t) (pdc% $u))
  | `(pdc% ( $t:pdcTm )) => `(pdc% $t)
  | `(pdc% ( $t:pdcTm : $T:pdcTy )) => `(STm.asc (pdc% $t) (pdcTy% $T))

macro_rules
  | `(pdcDefs% { $ds:pdcDef,* }) => foldDefs ds.getElems

/-! ## One check per production -/

/-! ### Types -/

example : (pdcTy% ⊤) = SType.top := by decide

example : (pdcTy% ⊥) = SType.bot := by decide

example : (pdcTy% {A : ⊤..⊥}) = SType.typ "A" .top .bot := by decide

example : (pdcTy% {a : ⊤}) = SType.fld "a" .top := by decide

example : (pdcTy% x.A) = SType.sel (.var "x") "A" := by decide

example : (pdcTy% x.f.A) = SType.sel (.sel (.var "x") "f") "A" := by decide

example : (pdcTy% x.type) = SType.sngl (.var "x") := by decide

example : (pdcTy% x.a.type) = SType.sngl (.sel (.var "x") "a") := by decide

example : (pdcTy% μ(x. {a : x.A})) = SType.mu "x" (.fld "a" (.sel (.var "x") "A")) := by decide

example : (pdcTy% ∀(x : ⊤) ⊥) = SType.all "x" .top .bot := by decide

/-- `∧` leans right. -/
example : (pdcTy% ⊤ ∧ ⊥ ∧ ⊤) = SType.and .top (.and .bot .top) := by decide

/-- A parenthesis regroups an intersection to the left. -/
example : (pdcTy% (⊤ ∧ ⊥) ∧ ⊤) = SType.and (.and .top .bot) .top := by decide

/-- `∀` extends as far right as it can. -/
example : (pdcTy% ∀(x : ⊤) ⊥ ∧ ⊤) = SType.all "x" .top (.and .bot .top) := by decide

/-- The label `Type`, written with guillemets because `Type` is a Lean
keyword. -/
example : (pdcTy% {«Type» : ⊤..⊥}) = SType.typ "Type" .top .bot := by decide

example : (pdcTy% t.«Type») = SType.sel (.var "t") "Type" := by decide

/-! ### Terms -/

example : (pdc% x) = STm.var "x" := by decide

/-- `x.a.b` is one `ident`, two projections. -/
example : (pdc% x.a.b) = STm.proj (.proj (.var "x") "a") "b" := by decide

example : (pdc% f x) = STm.app (.var "f") (.var "x") := by decide

/-- Application leans left. -/
example : (pdc% f x y) = STm.app (.app (.var "f") (.var "x")) (.var "y") := by decide

/-- Projection binds tighter than application. -/
example : (pdc% f x.a) = STm.app (.var "f") (.proj (.var "x") "a") := by decide

/-- A receiver that is not an identifier takes the projection rule. -/
example : (pdc% (f x).a) = STm.proj (.app (.var "f") (.var "x")) "a" := by decide

/-- After such a receiver `a.b` is one `ident`, folded into two projections. -/
example : (pdc% (f x).a.b) = STm.proj (.proj (.app (.var "f") (.var "x")) "a") "b" := by
  decide

example : (pdc% λ(x : ⊤). x) = STm.lam "x" (some .top) (.var "x") := by decide

example : (pdc% λx. x) = STm.lam "x" none (.var "x") := by decide

example : (pdc% let y = x in y) = STm.«let» "y" none (.var "x") (.var "y") := by decide

example : (pdc% let y : ⊤ = x in y) = STm.«let» "y" (some .top) (.var "x") (.var "y") := by
  decide

example : (pdc% (x : ⊤)) = STm.asc (.var "x") .top := by decide

example : (pdc% (x)) = STm.var "x" := by decide

example : (pdc% ν(x : {a : ⊤}) {a = x}) =
    STm.obj "x" (some (.fld "a" .top)) (.trm .nil "a" none (.var "x")) := by decide

/-- The definitions nest to the left, in text order. -/
example : (pdc% ν(x) {type A = ⊤, a = x, f : ⊤ = λ(y : ⊤). y}) =
    STm.obj "x" none (.trm (.trm (.typ .nil "A" .top) "a" none (.var "x"))
      "f" (some .top) (.lam "y" (some .top) (.var "y"))) := by decide

/-! ### Definitions -/

example : (pdcDefs% {type A = ⊤, a = x}) =
    SDefs.trm (SDefs.typ .nil "A" .top) "a" none (.var "x") := by decide

/-! ### The context type of E9 -/

example : (pdcTy% μ(z. {a : z.type} ∧ {b : ⊤})) =
    SType.mu "z" (.and (.fld "a" (.sngl (.var "z"))) (.fld "b" .top)) := by decide

/-! ### The name helpers -/

example : nameParts `x.a.b [] = ["x", "a", "b"] := by decide

example : tyOfName `x = none := by decide

end NominalFrontend
