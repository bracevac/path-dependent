import Coercions.Frontend.Surface

/-!
# The surface notation of the vanilla front end

Stages F0.2 and F0.3 of `plan-5e-frontend-stages.md`.  Three syntax categories,
`dotTy`, `dotTm` and `dotDefs`, hold the paper's notation
(`lean/Coercions/paper/sections/source.tex`, `lean/Coercions/paper/macros.tex`).
Three term level entry points, `dotTy%`, `dot%` and `dotDefs%`, expand a piece
of that notation into a constructor application of `SType`, `STm` or `SDefs`.
Nothing else happens here.  Names stay strings, no label is interned and no de
Bruijn index is computed, which is `Resolve.lean`'s work.

## Precedences

The discipline is the one the repo already uses for its own notations
(`lean/Coercions/FCdot/Debruijn.lean`, `lean/Coercions/FCdot/Syntax.lean`).
Application is left leaning at 70, projection binds tighter at 80, `∧` is right
leaning at 65, and `λ`, `ν`, `μ`, `∀`, `let` extend as far right as they can.
The closed forms and the parenthesis forms sit at `max`.

## The one departure from the paper, F0.3

A type member definition is written `{type A = T}`, not `{A = T}`.  The paper
writes the two definition forms alike and separates them by the label's case,
which a parser cannot see.  The keyword removes the ambiguity at the parser
rather than at the elaborator.  Adding `type` to Lean's token table makes the
bare word `type` a keyword in every module that imports this one, so the rest
of the front end does not use it as an identifier.

## Dotted identifiers, F0.2

Lean's lexer reads `x.a` as a single `ident` whose `Name` has two components, so
a rule shaped `ident "." ident` never fires on it.  The macro therefore takes
the name apart itself.  In term position a name of one component is a variable
and a name of `n+1` components is `n` nested projections over the head.  In type
position a name of exactly two components is a selection and any other length is
a macro error.  Surface identifiers are therefore simple names, which is what the
surface wants anyway.  The rule `dotTm:80 "." ident` stays for a receiver that is
not an identifier, for instance `(f x).a`, where the dot really is its own token.
-/

namespace Frontend

open Lean

/-! ## The three categories -/

declare_syntax_cat dotTy
declare_syntax_cat dotTm
declare_syntax_cat dotDefs

/-- `⊤`, the top type. -/
syntax:max "⊤" : dotTy
/-- `⊥`, the bottom type. -/
syntax:max "⊥" : dotTy
/-- `{A : S..T}`, a type member declaration. -/
syntax:max "{" ident " : " dotTy ".." dotTy "}" : dotTy
/-- `{a : T}`, a term member declaration. -/
syntax:max "{" ident " : " dotTy "}" : dotTy
/-- `x.A`, a type selection.  One `ident`, split inside the macro. -/
syntax:max ident : dotTy
/-- `μ(x. T)`, a recursive self type. -/
syntax:max "μ" "(" ident "." dotTy ")" : dotTy
/-- `∀(x : S) T`, a dependent function type. -/
syntax:max "∀" "(" ident " : " dotTy ")" dotTy:60 : dotTy
/-- `S ∧ T`, an intersection, right leaning. -/
syntax:65 dotTy:66 " ∧ " dotTy:65 : dotTy
/-- Parentheses. -/
syntax:max "(" dotTy ")" : dotTy

/-- `x`, or `x.a`, or `x.a.b`.  One `ident`, split inside the macro. -/
syntax:max ident : dotTm
/-- `λ(x : T). t`. -/
syntax:max "λ" "(" ident " : " dotTy ")" "." dotTm:60 : dotTm
/-- `ν(x : T. d)`, an object literal with its self type. -/
syntax:max "ν" "(" ident " : " dotTy "." dotDefs ")" : dotTm
/-- `t.a` on a receiver that is not an identifier, for instance `(f x).a`. -/
syntax:80 dotTm:80 "." ident : dotTm
/-- `t u`, application, left leaning. -/
syntax:70 dotTm:70 dotTm:71 : dotTm
/-- `let x = t in u`, with an optional result type. -/
syntax:max "let" ident (" : " dotTy)? " = " dotTm " in " dotTm:60 : dotTm
/-- Parentheses. -/
syntax:max "(" dotTm ")" : dotTm

/-- `{type A = T}`, a type member definition.  The departure of F0.3. -/
syntax:max "{" "type" ident " = " dotTy "}" : dotDefs
/-- `{a = t}`, a term member definition. -/
syntax:max "{" ident " = " dotTm "}" : dotDefs
/-- `d ∧ e`, right leaning. -/
syntax:65 dotDefs:66 " ∧ " dotDefs:65 : dotDefs

/-- Expand a `dotTy` into an `SType`. -/
syntax:max "dotTy% " dotTy : term
/-- Expand a `dotTm` into an `STm`. -/
syntax:max "dot% " dotTm : term
/-- Expand a `dotDefs` into an `SDefs`. -/
syntax:max "dotDefs% " dotDefs : term

/-! ## Taking a hierarchical identifier apart

The decision each of the two categories makes about a name is a pure function,
`nameParts` and `tySelName`, so that the probes of F0.2 can test it with
`decide` like every other check of this stage.  The two `MacroM` wrappers only
turn the answer into syntax, or report a bad name with `Macro.throwErrorAt`,
which points at the offending identifier rather than at the whole production. -/

/-- The components of a name, outermost first, as strings.  Lean v4.29.1 has no
`Lean.Name.components`, so the walk is written out.  A numeric component cannot
appear in a name the user typed, and is rendered for the sake of totality. -/
def nameParts : Name → List String → List String
  | .anonymous, acc => acc
  | .str p s, acc => nameParts p (s :: acc)
  | .num p i, acc => nameParts p (toString i :: acc)

/-- The receiver and the label of a name in type position.  Only a two
component name is a type, since the one type a name can build is the selection
`x.A`.  An undotted `x` is rejected here. -/
def tySelName (n : Name) : Option (String × String) :=
  match nameParts n [] with
  | [recv, lbl] => some (recv, lbl)
  | _ => none

/-- A surface identifier in term position.  `x` is a variable, `x.a` is one
projection, `x.a.b` is two, outermost last. -/
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

/-! ## The macros -/

macro_rules
  | `(dotTy% ⊤) => `(SType.top)
  | `(dotTy% ⊥) => `(SType.bot)
  | `(dotTy% { $A:ident : $S:dotTy .. $T:dotTy }) =>
      `(SType.typ $(quote A.getId.toString) (dotTy% $S) (dotTy% $T))
  | `(dotTy% { $a:ident : $T:dotTy }) =>
      `(SType.fld $(quote a.getId.toString) (dotTy% $T))
  | `(dotTy% $x:ident) => surfaceTyOfIdent x
  | `(dotTy% μ ( $x:ident . $T:dotTy )) =>
      `(SType.mu $(quote x.getId.toString) (dotTy% $T))
  | `(dotTy% ∀ ( $x:ident : $S:dotTy ) $T:dotTy) =>
      `(SType.all $(quote x.getId.toString) (dotTy% $S) (dotTy% $T))
  | `(dotTy% $S:dotTy ∧ $T:dotTy) => `(SType.and (dotTy% $S) (dotTy% $T))
  | `(dotTy% ( $T:dotTy )) => `(dotTy% $T)

macro_rules
  | `(dot% $x:ident) => surfaceTmOfIdent x
  | `(dot% λ ( $x:ident : $T:dotTy ) . $t:dotTm) =>
      `(STm.lam $(quote x.getId.toString) (dotTy% $T) (dot% $t))
  | `(dot% ν ( $x:ident : $T:dotTy . $d:dotDefs )) =>
      `(STm.obj $(quote x.getId.toString) (dotTy% $T) (dotDefs% $d))
  | `(dot% $t:dotTm . $a:ident) => `(STm.proj (dot% $t) $(quote a.getId.toString))
  | `(dot% $t:dotTm $u:dotTm) => `(STm.app (dot% $t) (dot% $u))
  | `(dot% let $x:ident = $t:dotTm in $u:dotTm) =>
      `(STm.«let» $(quote x.getId.toString) (none : Option SType) (dot% $t) (dot% $u))
  | `(dot% let $x:ident : $T:dotTy = $t:dotTm in $u:dotTm) =>
      `(STm.«let» $(quote x.getId.toString) (some (dotTy% $T)) (dot% $t) (dot% $u))
  | `(dot% ( $t:dotTm )) => `(dot% $t)

macro_rules
  | `(dotDefs% { type $A:ident = $T:dotTy }) =>
      `(SDefs.typ $(quote A.getId.toString) (dotTy% $T))
  | `(dotDefs% { $a:ident = $t:dotTm }) =>
      `(SDefs.trm $(quote a.getId.toString) (dot% $t))
  | `(dotDefs% $d:dotDefs ∧ $e:dotDefs) => `(SDefs.and (dotDefs% $d) (dotDefs% $e))

/-! ## One check per surface form

All of it reduces in the kernel, so `by decide` is the right tactic here, as it
is in `Surface.lean`.  The search of F1 is the opposite case. -/

/-! ### Types -/

example : (dotTy% ⊤) = SType.top := by decide

example : (dotTy% ⊥) = SType.bot := by decide

example : (dotTy% { A : ⊤ .. ⊥ }) = SType.typ "A" .top .bot := by decide

example : (dotTy% { a : ⊤ }) = SType.fld "a" .top := by decide

example : (dotTy% x.A) = SType.sel "x" "A" := by decide

example : (dotTy% μ ( x . { a : x.A } )) = SType.mu "x" (.fld "a" (.sel "x" "A")) := by
  decide

example : (dotTy% ∀ ( x : ⊤ ) ⊥) = SType.all "x" .top .bot := by decide

example : (dotTy% ⊤ ∧ ⊥) = SType.and .top .bot := by decide

/-- `∧` leans right. -/
example : (dotTy% ⊤ ∧ ⊥ ∧ ⊤) = SType.and .top (.and .bot .top) := by decide

example : (dotTy% ( ⊤ )) = SType.top := by decide

/-- A parenthesis regroups an intersection to the left. -/
example : (dotTy% ( ⊤ ∧ ⊥ ) ∧ ⊤) = SType.and (.and .top .bot) .top := by decide

/-- `∀` extends as far right as it can. -/
example : (dotTy% ∀ ( x : ⊤ ) ⊥ ∧ ⊤) = SType.all "x" .top (.and .bot .top) := by decide

/-- A closed form sits at `max`, so it is an intersection's left operand. -/
example : (dotTy% μ ( x . ⊤ ) ∧ ⊤) = SType.and (.mu "x" .top) .top := by decide

/-- The bounds token needs no space around it, and it does not eat the dot of a
selection to its left. -/
example : (dotTy% {A : x.A..⊤}) = SType.typ "A" (.sel "x" "A") .top := by decide

/-! ### Terms -/

example : (dot% x) = STm.var "x" := by decide

example : (dot% λ ( x : ⊤ ) . x) = STm.lam "x" .top (.var "x") := by decide

example :
    (dot% ν ( s : { a : ⊤ } . { a = s } )) =
      STm.obj "s" (.fld "a" .top) (.trm "a" (.var "s")) := by
  decide

example : (dot% f x) = STm.app (.var "f") (.var "x") := by decide

/-- Application leans left. -/
example : (dot% f x y) = STm.app (.app (.var "f") (.var "x")) (.var "y") := by decide

/-- Projection binds tighter than application. -/
example : (dot% f x.a) = STm.app (.var "f") (.proj (.var "x") "a") := by decide

example :
    (dot% let x = y in x) = STm.«let» "x" none (.var "y") (.var "x") := by decide

example :
    (dot% let x : ⊤ = y in x) = STm.«let» "x" (some .top) (.var "y") (.var "x") := by
  decide

example : (dot% ( x )) = STm.var "x" := by decide

/-- `λ` extends as far right as it can, so the application is inside the body. -/
example :
    (dot% λ ( x : ⊤ ) . f x) = STm.lam "x" .top (.app (.var "f") (.var "x")) := by decide

/-! ### Definitions -/

example : (dotDefs% { type A = ⊤ }) = SDefs.typ "A" .top := by decide

example : (dotDefs% { a = x }) = SDefs.trm "a" (.var "x") := by decide

example :
    (dotDefs% { type A = ⊤ } ∧ { a = x }) =
      SDefs.and (.typ "A" .top) (.trm "a" (.var "x")) := by
  decide

/-- `∧` leans right on definitions too. -/
example :
    (dotDefs% { a = x } ∧ { b = y } ∧ { c = z }) =
      SDefs.and (.trm "a" (.var "x")) (.and (.trm "b" (.var "y")) (.trm "c" (.var "z"))) := by
  decide

/-! ### The six probes of F0.2

How Lean v4.29.1 actually parses a dotted name.  The first three go through one
`ident` token each, whatever the number of dots, and the macro splits it.  The
fourth is the only one where the dot is a token of its own, because its receiver
is not an identifier.  The fifth is the type category's reading of the same
token.  The sixth is rejected, and its check is below. -/

example : (dot% x) = STm.var "x" := by decide

example : (dot% x.a) = STm.proj (.var "x") "a" := by decide

example : (dot% x.a.b) = STm.proj (.proj (.var "x") "a") "b" := by decide

example : (dot% ( f x ).a) = STm.proj (.app (.var "f") (.var "x")) "a" := by decide

example : (dotTy% x.A) = SType.sel "x" "A" := by decide

/-- The sixth probe, the rejected undotted name in type position.  A bare `x` is
never a type.  The rejection itself is a macro error, which no tactic can look
at, so what is tested is the decision the macro makes, which is a function and
reduces like everything else here.  Writing `dotTy% x` in a term therefore fails
the build with "a surface type built from a name is the selection x.A, which has
exactly two components". -/
example : tySelName `x = none := by decide

/-- Three components are rejected in type position for the same reason. -/
example : tySelName `x.a.A = none := by decide

/-- Two components are the selection, which is the fifth probe again, this time
at the decision rather than at the expansion. -/
example : tySelName `x.A = some ("x", "A") := by decide

/-- The term category accepts every length, and this is the reading of a dotted
name that Lean's lexer hands the macro. -/
example : nameParts `x [] = ["x"] := by decide

example : nameParts `x.a [] = ["x", "a"] := by decide

example : nameParts `x.a.b [] = ["x", "a", "b"] := by decide

/-! ### A whole program

The sample program of `Surface.lean`, written in the notation. -/

example :
    (dot% λ ( f : { A : ⊤ .. ⊥ } ) .
            ν ( s : { a : ⊤ } ∧ { B : ⊤ .. ⊤ } . { a = f } ∧ { type B = ⊤ } )) =
      STm.lam "f" (.typ "A" .top .bot)
        (.obj "s" (.and (.fld "a" .top) (.typ "B" .top .top))
          (.and (.trm "a" (.var "f")) (.typ "B" .top))) := by
  decide

end Frontend
