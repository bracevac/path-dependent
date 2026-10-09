import Coercions.Paths.Frontend.Surface

/-!
# The surface notation of the paths front end

Three syntax categories, `pdotTy`, `pdotTm` and `pdotDefs`, hold the paper's
notation for types, terms and definitions with paths and singleton types.
Three entry points, `pdotTy%`, `pdot%` and `pdotDefs%`, expand a piece of that
notation into an `SType`, `STm` or `SDefs`.  Names stay strings.  `Resolve.lean`
turns them into indices.

Application is left leaning at 70 and projection binds tighter at 80.  `∧` is
right leaning at 65.  `λ`, `ν`, `μ`, `∀` and `let` extend as far right as they
can.  Closed forms and parentheses sit at `max`.

A type member definition is written `{type A = T}`, because the paper writes
both definition forms alike and tells them apart only by the case of the
label.  This makes `type` a keyword.  A stable field declaration is written
`{val a : T}`.  Here `val` is a non-reserved token, so it stays an ordinary
identifier elsewhere.

Lean's lexer reads `x.a.b` as one `ident` with three components, so the macro
splits it.  In term position, `x` is a variable and `x.a.b` is two nested
projections.  In type position a name needs two components or more.  Every
component but the last is a field step.  The last is either the keyword `type`
or a type label.  A name without a dot is never a type, since a selection needs
a receiver.

The same lexer rule asks for a space after the dot of `λx. t`.  Written `λx.x`,
the body and the dot merge into the one name `x.x`, and the rule for `λx.` never
sees its dot.  So the lambda with its domain left to inference is written with a
space, `λx. x`.
-/

namespace PathsFrontend

open Lean

/-! ## The three categories -/

declare_syntax_cat pdotTy
declare_syntax_cat pdotTm
declare_syntax_cat pdotDefs

/-- `⊤`, the top type. -/
syntax:max "⊤" : pdotTy
/-- `⊥`, the bottom type. -/
syntax:max "⊥" : pdotTy
/-- `{A : S..T}`, a type member declaration. -/
syntax:max "{" ident " : " pdotTy ".." pdotTy "}" : pdotTy
/-- `{a : T}`, a term member declaration. -/
syntax:max "{" ident " : " pdotTy "}" : pdotTy
/-- `{val a : T}`, a stable field declaration.  `val` is a non-reserved token,
so it is not added to the keyword table. -/
syntax:max "{" &"val" ident " : " pdotTy "}" : pdotTy
/-- `x.A`, `x.a.A`, `x.type`, `x.a.type`.  One `ident`, split by the macro. -/
syntax:max ident : pdotTy
/-- `μ(x. T)`, a recursive self type. -/
syntax:max "μ" "(" ident "." pdotTy ")" : pdotTy
/-- `∀(x : S) T`, a dependent function type. -/
syntax:max "∀" "(" ident " : " pdotTy ")" pdotTy:60 : pdotTy
/-- `S ∧ T`, an intersection, right leaning. -/
syntax:65 pdotTy:66 " ∧ " pdotTy:65 : pdotTy
/-- Parentheses. -/
syntax:max "(" pdotTy ")" : pdotTy

/-- `x`, `x.a` or `x.a.b`.  One `ident`, split by the macro. -/
syntax:max ident : pdotTm
/-- `λ(x : T). t`. -/
syntax:max "λ" "(" ident " : " pdotTy ")" "." pdotTm:60 : pdotTm
/-- `ν(x : T. d)`, an object literal with its self type. -/
syntax:max "ν" "(" ident " : " pdotTy "." pdotDefs ")" : pdotTm
/-- `t.a` on a receiver that is not an identifier, for instance `(f x).a`. -/
syntax:80 pdotTm:80 "." ident : pdotTm
/-- `t u`, application, left leaning. -/
syntax:70 pdotTm:70 pdotTm:71 : pdotTm
/-- `let x = t in u`, with an optional result type. -/
syntax:max "let" ident (" : " pdotTy)? " = " pdotTm " in " pdotTm:60 : pdotTm
/-- Parentheses. -/
syntax:max "(" pdotTm ")" : pdotTm
/-- `λx. t`, a lambda whose domain is left to inference. -/
syntax:max "λ" ident "." pdotTm:60 : pdotTm
/-- `ν(x. d)`, an object literal whose self type is left to inference. -/
syntax:max "ν" "(" ident "." pdotDefs ")" : pdotTm
/-- `(t : T)`, an ascription. -/
syntax:max "(" pdotTm " : " pdotTy ")" : pdotTm

/-- `{type A = T}`, a type member definition. -/
syntax:max "{" "type" ident " = " pdotTy "}" : pdotDefs
/-- `{a = t}`, a term member definition. -/
syntax:max "{" ident " = " pdotTm "}" : pdotDefs
/-- `d ∧ e`, right leaning. -/
syntax:65 pdotDefs:66 " ∧ " pdotDefs:65 : pdotDefs
/-- Parentheses, needed for a definition list that nests to the left. -/
syntax:max "(" pdotDefs ")" : pdotDefs
/-- `{a : T = t}`, a term member definition with a written type. -/
syntax:max "{" ident " : " pdotTy " = " pdotTm "}" : pdotDefs

/-- Expand a `pdotTy` into an `SType`. -/
syntax:max "pdotTy% " pdotTy : term
/-- Expand a `pdotTm` into an `STm`. -/
syntax:max "pdot% " pdotTm : term
/-- Expand a `pdotDefs` into an `SDefs`. -/
syntax:max "pdotDefs% " pdotDefs : term

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
  | `(pdotTy% ⊤) => `(SType.top)
  | `(pdotTy% ⊥) => `(SType.bot)
  | `(pdotTy% { $A:ident : $S:pdotTy .. $T:pdotTy }) =>
      `(SType.typ $(quote A.getId.toString) (pdotTy% $S) (pdotTy% $T))
  | `(pdotTy% { $a:ident : $T:pdotTy }) =>
      `(SType.fld $(quote a.getId.toString) (pdotTy% $T))
  | `(pdotTy% { val $a:ident : $T:pdotTy }) =>
      `(SType.vfld $(quote a.getId.toString) (pdotTy% $T))
  | `(pdotTy% $x:ident) => surfaceTyOfIdent x
  | `(pdotTy% μ ( $x:ident . $T:pdotTy )) =>
      `(SType.mu $(quote x.getId.toString) (pdotTy% $T))
  | `(pdotTy% ∀ ( $x:ident : $S:pdotTy ) $T:pdotTy) =>
      `(SType.all $(quote x.getId.toString) (pdotTy% $S) (pdotTy% $T))
  | `(pdotTy% $S:pdotTy ∧ $T:pdotTy) => `(SType.and (pdotTy% $S) (pdotTy% $T))
  | `(pdotTy% ( $T:pdotTy )) => `(pdotTy% $T)

macro_rules
  | `(pdot% $x:ident) => surfaceTmOfIdent x
  | `(pdot% λ ( $x:ident : $T:pdotTy ) . $t:pdotTm) =>
      `(STm.lam $(quote x.getId.toString) (some (pdotTy% $T)) (pdot% $t))
  | `(pdot% ν ( $x:ident : $T:pdotTy . $d:pdotDefs )) =>
      `(STm.obj $(quote x.getId.toString) (some (pdotTy% $T)) (pdotDefs% $d))
  | `(pdot% $t:pdotTm . $a:ident) => `(STm.proj (pdot% $t) $(quote a.getId.toString))
  | `(pdot% $t:pdotTm $u:pdotTm) => `(STm.app (pdot% $t) (pdot% $u))
  | `(pdot% let $x:ident = $t:pdotTm in $u:pdotTm) =>
      `(STm.«let» $(quote x.getId.toString) (none : Option SType) (pdot% $t) (pdot% $u))
  | `(pdot% let $x:ident : $T:pdotTy = $t:pdotTm in $u:pdotTm) =>
      `(STm.«let» $(quote x.getId.toString) (some (pdotTy% $T)) (pdot% $t) (pdot% $u))
  | `(pdot% ( $t:pdotTm )) => `(pdot% $t)
  | `(pdot% λ $x:ident . $t:pdotTm) =>
      `(STm.lam $(quote x.getId.toString) (none : Option SType) (pdot% $t))
  | `(pdot% ν ( $x:ident . $d:pdotDefs )) =>
      `(STm.obj $(quote x.getId.toString) (none : Option SType) (pdotDefs% $d))
  | `(pdot% ( $t:pdotTm : $T:pdotTy )) => `(STm.asc (pdot% $t) (pdotTy% $T))

macro_rules
  | `(pdotDefs% { type $A:ident = $T:pdotTy }) =>
      `(SDefs.typ $(quote A.getId.toString) (pdotTy% $T))
  | `(pdotDefs% { $a:ident = $t:pdotTm }) =>
      `(SDefs.trm $(quote a.getId.toString) (none : Option SType) (pdot% $t))
  | `(pdotDefs% $d:pdotDefs ∧ $e:pdotDefs) => `(SDefs.and (pdotDefs% $d) (pdotDefs% $e))
  | `(pdotDefs% ( $d:pdotDefs )) => `(pdotDefs% $d)
  | `(pdotDefs% { $a:ident : $T:pdotTy = $t:pdotTm }) =>
      `(SDefs.trm $(quote a.getId.toString) (some (pdotTy% $T)) (pdot% $t))

/-! ## One check per surface form -/

/-! ### Types -/

example : (pdotTy% ⊤) = SType.top := by decide

example : (pdotTy% ⊥) = SType.bot := by decide

example : (pdotTy% { A : ⊤ .. ⊥ }) = SType.typ "A" .top .bot := by decide

example : (pdotTy% { a : ⊤ }) = SType.fld "a" .top := by decide

example : (pdotTy% { val a : ⊤ }) = SType.vfld "a" .top := by decide

example : (pdotTy% x.A) = SType.sel (.var "x") "A" := by decide

example : (pdotTy% x.f.A) = SType.sel (.sel (.var "x") "f") "A" := by decide

example : (pdotTy% x.type) = SType.sngl (.var "x") := by decide

example : (pdotTy% x.a.type) = SType.sngl (.sel (.var "x") "a") := by decide

example : (pdotTy% { val f : { A : ⊤..⊥ } }) = SType.vfld "f" (.typ "A" .top .bot) := by
  decide

example : (pdotTy% { a : q.type }) = SType.fld "a" (.sngl (.var "q")) := by decide

example :
    (pdotTy% p.symbols.Symbol) = SType.sel (.sel (.var "p") "symbols") "Symbol" := by
  decide

example : tyOfName `x = none := by decide

example : (pdotTy% μ ( x . { a : x.A } )) = SType.mu "x" (.fld "a" (.sel (.var "x") "A")) := by
  decide

example : (pdotTy% ∀ ( x : ⊤ ) ⊥) = SType.all "x" .top .bot := by decide

example : (pdotTy% ⊤ ∧ ⊥) = SType.and .top .bot := by decide

/-- `∧` leans right. -/
example : (pdotTy% ⊤ ∧ ⊥ ∧ ⊤) = SType.and .top (.and .bot .top) := by decide

example : (pdotTy% ( ⊤ )) = SType.top := by decide

/-- A parenthesis regroups an intersection to the left. -/
example : (pdotTy% ( ⊤ ∧ ⊥ ) ∧ ⊤) = SType.and (.and .top .bot) .top := by decide

/-- `∀` extends as far right as it can. -/
example : (pdotTy% ∀ ( x : ⊤ ) ⊥ ∧ ⊤) = SType.all "x" .top (.and .bot .top) := by decide

/-- A closed form sits at `max`, so it is an intersection's left operand. -/
example : (pdotTy% μ ( x . ⊤ ) ∧ ⊤) = SType.and (.mu "x" .top) .top := by decide

/-- The bounds token needs no spaces and does not take the dot of a selection
to its left. -/
example : (pdotTy% {A : x.a.A..⊤}) = SType.typ "A" (.sel (.sel (.var "x") "a") "A") .top := by
  decide

/-- The label `Type` of gDOT Fig. 2, written with guillemets because `Type` is
a Lean keyword. -/
example : (pdotTy% { «Type» : ⊤..⊥ }) = SType.typ "Type" .top .bot := by decide

example : (match pdotTy% t.«Type» with | .sel _ A => A | _ => "?") = "Type" := by decide

/-! ### Terms -/

example : (pdot% x) = STm.var "x" := by decide

example : (pdot% λ ( x : ⊤ ) . x) = STm.lam "x" (some .top) (.var "x") := by decide

example :
    (pdot% ν ( s : { a : ⊤ } . { a = s } )) =
      STm.obj "s" (some (.fld "a" .top)) (.trm "a" none (.var "s")) := by
  decide

example : (pdot% f x) = STm.app (.var "f") (.var "x") := by decide

/-- Application leans left. -/
example : (pdot% f x y) = STm.app (.app (.var "f") (.var "x")) (.var "y") := by decide

/-- Projection binds tighter than application. -/
example : (pdot% f x.a) = STm.app (.var "f") (.proj (.var "x") "a") := by decide

example :
    (pdot% let x = y in x) = STm.«let» "x" none (.var "y") (.var "x") := by decide

example :
    (pdot% let x : ⊤ = y in x) = STm.«let» "x" (some .top) (.var "y") (.var "x") := by
  decide

example : (pdot% ( x )) = STm.var "x" := by decide

/-- `λ` extends as far right as it can. -/
example :
    (pdot% λ ( x : ⊤ ) . f x) = STm.lam "x" (some .top) (.app (.var "f") (.var "x")) := by
  decide

/-- `x`, `x.a` and `x.a.b` are each one `ident`. -/
example : (pdot% x.a) = STm.proj (.var "x") "a" := by decide

example : (pdot% x.a.b) = STm.proj (.proj (.var "x") "a") "b" := by decide

/-- A receiver that is not an identifier takes the projection rule. -/
example : (pdot% ( f x ).a) = STm.proj (.app (.var "f") (.var "x")) "a" := by decide

example : (pdot% λx. x) = STm.lam "x" none (.var "x") := by decide

/-- The body of `λx.` extends as far right as it can, a path included. -/
example : (pdot% λx. x.a) = STm.lam "x" none (.proj (.var "x") "a") := by decide

example : (pdot% λx. λy. f x y) =
    STm.lam "x" none (.lam "y" none (.app (.app (.var "f") (.var "x")) (.var "y"))) := by decide

example : (pdot% ν(x. {type A = ⊤})) = STm.obj "x" none (.typ "A" .top) := by decide

/-- A literal without a self type inside another one. -/
example : (pdot% ν(x. {c = ν(y. {type A = ⊤})})) =
    STm.obj "x" none (.trm "c" none (.obj "y" none (.typ "A" .top))) := by decide

example : (pdot% (λx. x : ∀(y : ⊤) ⊤)) =
    STm.asc (.lam "x" none (.var "x")) (.all "y" .top .top) := by decide

example : (pdot% f (λx. x)) = STm.app (.var "f") (.lam "x" none (.var "x")) := by decide

example : (pdot% (f x : ⊤).a) = STm.proj (.asc (.app (.var "f") (.var "x")) .top) "a" := by
  decide

/-- An ascription at a singleton type. -/
example : (pdot% (x.a : y.type)) = STm.asc (.proj (.var "x") "a") (.sngl (.var "y")) := by
  decide

example : nameParts `x [] = ["x"] := by decide

example : nameParts `x.a [] = ["x", "a"] := by decide

example : nameParts `x.a.b [] = ["x", "a", "b"] := by decide

/-! ### Definitions -/

example : (pdotDefs% { type A = ⊤ }) = SDefs.typ "A" .top := by decide

example : (pdotDefs% { a = x }) = SDefs.trm "a" none (.var "x") := by decide

example : (pdotDefs% {a : ⊤ = x}) = SDefs.trm "a" (some .top) (.var "x") := by decide

/-- A written field type may name a path. -/
example : (pdotDefs% {a : x.c.A = y}) =
    SDefs.trm "a" (some (.sel (.sel (.var "x") "c") "A")) (.var "y") := by decide

example :
    (pdotDefs% { type A = ⊤ } ∧ { a = x }) =
      SDefs.and (.typ "A" .top) (.trm "a" none (.var "x")) := by
  decide

/-- `∧` leans right on definitions too. -/
example :
    (pdotDefs% { a = x } ∧ { b = y } ∧ { c = z }) =
      SDefs.and (.trm "a" none (.var "x"))
        (.and (.trm "b" none (.var "y")) (.trm "c" none (.var "z"))) := by
  decide

/-- Parentheses regroup a definition list to the left. -/
example :
    (pdotDefs% ( { a = x } ∧ { b = y } ) ∧ { c = z }) =
      SDefs.and (.and (.trm "a" none (.var "x")) (.trm "b" none (.var "y")))
        (.trm "c" none (.var "z")) := by
  decide

/-! ## The example programs in the notation

Each program is a surface term.  Parsing it is the test here.  `Resolve.lean`
resolves them. -/

/-! ### E1p, bad bounds at a path -/

def E1p_src : STm :=
  pdot% λ(w : {val f : {A : ⊤..⊥}}). let y : {B : {a : ⊤}..{a : ⊤}} = w in y

/-! ### X3, with `x` bound by a lambda, and its direct-style twin -/

def X3_src : STm := pdot% λ(x : {val a : {val b : ⊤}}). let y = x.a in y.b

def X3d_src : STm := pdot% λ(x : {val a : {val b : ⊤}}). x.a.b

/-! ### E9, a singleton at a `let` -/

def E9_src : STm :=
  pdot% let q = ν(q : {B : {b : ⊤}..{b : ⊤}}. {type B = {b : ⊤}}) in
        let x = ν(x : {a : q.type}. {a = q}) in
        let y = x.a in
        λ(z : y.B). let w = z in w

/-! ### X1 -/

def X1_src : STm :=
  pdot% ν(z : {val c : μ(w. {A : z.B..z.B})} ∧ {B : z.c.A..z.c.A}.
          {c = ν(w : {A : z.B..z.B}. {type A = z.B})} ∧ {type B = z.c.A})

/-! ### E2p, a function at a path-keyed member, applied to itself -/

def E2p_src : STm :=
  pdot% let x = ν(x : {val c : μ(z. {A : ∀(y : x.c.A) x.c.A .. ∀(y : x.c.A) x.c.A}
                                    ∧ {a : ∀(y : x.c.A) x.c.A})}.
                 {c = ν(z : {A : ∀(y : x.c.A) x.c.A .. ∀(y : x.c.A) x.c.A}
                              ∧ {a : ∀(y : x.c.A) x.c.A}.
                          {type A = ∀(y : x.c.A) x.c.A} ∧ {a = λ(y : x.c.A). y})})
        in let c = x.c in let f = c.a in f f

/-! ### E11, a stable field beside a singleton field -/

def E11_src : STm :=
  pdot% let z = ν(z : {C : ⊤..⊤}. {type C = ⊤}) in
        ν(x : {val a : μ(w. {A : ⊤..⊤})} ∧ {b : z.type}.
          {a = ν(w : {A : ⊤..⊤}. {type A = ⊤})} ∧ {b = z})

/-! ### The base programs -/

def E1_src : STm := pdot% λ(x : {A : ⊤..⊥}). let y : {B : {a : ⊤} .. {a : ⊤}} = x in y

def E2_src : STm :=
  pdot% let x = ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}.
                  {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y})
        in let f = x.a in f f

def E3_src : STm :=
  pdot% λ(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}). λ(z : {b : ⊤}). let y : {a : ⊤} = z in y

def E4_src : STm :=
  pdot% λ(x : {B : {A : ⊥ .. ⊤} .. {A : {a : ⊤} .. ⊤}}).
          λ(w : {A : ⊥ .. ⊤}). λ(n : {a : ⊤}). let g = λ(y : w.A). y in g n

def E5_src : STm :=
  pdot% λ(w : {A : ⊤..⊤}).
          let f = λ(v : {A : ⊤..⊤}). ν(z : {a : v.A}. {a = v}) in let o = f w in o.a

def E6_src : STm :=
  pdot% λ(n : {a : ⊤}). ν(x : {T : {a : ⊤} .. {a : ⊤}} ∧ {v : x.T}. {type T = {a : ⊤}} ∧ {v = n})

def E7_src : STm :=
  pdot% ν(x : {A : x.B .. x.B} ∧ {B : x.A .. x.A}. {type A = x.B} ∧ {type B = x.A})

def E8_src : STm := pdot% λ(x : {A : ⊥ .. {a : ⊤}}). λ(y : x.A ∧ {a : ⊤}). y.a

/-! ### The base programs at a stable field one hop away -/

def E3p_src : STm :=
  pdot% λ(w : {val f : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}}).
          λ(z : {b : ⊤}). let y : {a : ⊤} = z in y

def E4p_src : STm :=
  pdot% λ(x : {val f : {B : {A : ⊥ .. ⊤} .. {A : {a : ⊤} .. ⊤}}}).
          λ(w : {A : ⊥ .. ⊤}). λ(n : {a : ⊤}). let g = λ(y : w.A). y in g n

def E5p_src : STm :=
  pdot% λ(w : {A : ⊤..⊤}).
          let f = λ(v : {A : ⊤..⊤}). ν(z : {val b : μ(u. {a : v.A})}. {b = ν(u : {a : v.A}. {a = v})})
          in let r = f w in let o = r.b in o.a

def E6p_src : STm :=
  pdot% λ(n : {a : ⊤}).
          ν(x : {val c : μ(z. {T : {a : ⊤} .. {a : ⊤}})} ∧ {v : x.c.T}.
            {c = ν(z : {T : {a : ⊤} .. {a : ⊤}}. {type T = {a : ⊤}})} ∧ {v = n})

def E7p_src : STm :=
  pdot% ν(x : {val c : μ(z. {A : x.c.B .. x.c.B} ∧ {B : x.c.A .. x.c.A})}.
          {c = ν(z : {A : x.c.B .. x.c.B} ∧ {B : x.c.A .. x.c.A}.
                 {type A = x.c.B} ∧ {type B = x.c.A})})

def E8p_src : STm := pdot% λ(x : {val f : {A : ⊥ .. {a : ⊤}}}). λ(y : x.f.A ∧ {a : ⊤}). y.a

/-! ### X2, X4 written closed, P3e -/

def X2_src : STm := pdot% ν(x : {a : {A : ⊤..⊥}}. {a = x.a})

/-- X4 closed: `pcore : ⊤` becomes the binder of a lambda. -/
def X4_src : STm :=
  pdot% λ(p : ⊤).
        ν(t : (((({«Type» : ⊤..⊤} ∧ {TypeTop : t.«Type»..t.«Type»})
                    ∧ {newTypeTop : ∀(u : ⊤) t.TypeTop})
                    ∧ {TypeRef : t.«Type» ∧ {symb : p.symbols.Symbol}
                              .. t.«Type» ∧ {symb : p.symbols.Symbol}})
                    ∧ {newTypeRef : ∀(s : p.symbols.Symbol) t.TypeRef}).
          (((({type «Type» = ⊤} ∧ {type TypeTop = t.«Type»})
             ∧ {newTypeTop = λ(u : ⊤). u})
             ∧ {type TypeRef = t.«Type» ∧ {symb : p.symbols.Symbol}})
             ∧ {newTypeRef = λ(s : p.symbols.Symbol).
                  let r = ν(r : {symb : p.symbols.Symbol}. {symb = s}) in r}))

/-- P3e: a term member whose type is a term member declaration. -/
def P3e_src : STm :=
  pdot% ν(x : {a : {C : ∀(y : ⊤) ⊤ .. {v : ⊤}}} ∧ {b : ∀(y : ⊤) ⊤}.
          {a = x.a} ∧ {b = λ(y : ⊤). y})

/-! ### gDOT Fig. 2

The intersections of the self type and the definitions nest to the left, so
they are parenthesized. -/

def Fig2_src : STm :=
  pdot%
  let o = ν(o : {Option : ⊤..⊤}. {type Option = ⊤}) in
  let pcore = ν(p :
      {val types : μ(t. (((({«Type» : ⊤..⊤} ∧ {TypeTop : t.«Type»..t.«Type»})
                          ∧ {newTypeTop : ∀(u : ⊤) t.TypeTop})
                          ∧ {TypeRef : t.«Type» ∧ {symb : p.symbols.Symbol}
                                    .. t.«Type» ∧ {symb : p.symbols.Symbol}})
                          ∧ {newTypeRef : ∀(s : p.symbols.Symbol) t.TypeRef}))}
      ∧ {val symbols : μ(y.
            {Symbol : {tpe : o.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}}
                   .. {tpe : o.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}}}
            ∧ {newSymbol : ∀(u : o.Option ∧ {A : ⊥..p.types.«Type»}) ∀(i : {n : ⊤}) y.Symbol})}.
      {types = ν(t : (((({«Type» : ⊤..⊤} ∧ {TypeTop : t.«Type»..t.«Type»})
                          ∧ {newTypeTop : ∀(u : ⊤) t.TypeTop})
                          ∧ {TypeRef : t.«Type» ∧ {symb : p.symbols.Symbol}
                                    .. t.«Type» ∧ {symb : p.symbols.Symbol}})
                          ∧ {newTypeRef : ∀(s : p.symbols.Symbol) t.TypeRef}).
          (((({type «Type» = ⊤} ∧ {type TypeTop = t.«Type»})
             ∧ {newTypeTop = λ(u : ⊤). u})
             ∧ {type TypeRef = t.«Type» ∧ {symb : p.symbols.Symbol}})
             ∧ {newTypeRef = λ(s : p.symbols.Symbol).
                  let r = ν(r : {symb : p.symbols.Symbol}. {symb = s}) in r}))}
      ∧ {symbols = ν(y :
            {Symbol : {tpe : o.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}}
                   .. {tpe : o.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}}}
            ∧ {newSymbol : ∀(u : o.Option ∧ {A : ⊥..p.types.«Type»}) ∀(i : {n : ⊤}) y.Symbol}.
          {type Symbol = {tpe : o.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}}}
          ∧ {newSymbol = λ(u : o.Option ∧ {A : ⊥..p.types.«Type»}). λ(i : {n : ⊤}).
               let r = ν(r : {tpe : o.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}}.
                         {tpe = u} ∧ {id = i}) in r})}) in
  pcore

/-! ### pDOT Fig. 1: Fig. 2 with `tpe : p.types.Type` -/

def Fig1_src : STm :=
  pdot%
  let o = ν(o : {Option : ⊤..⊤}. {type Option = ⊤}) in
  let pcore = ν(p :
      {val types : μ(t. (((({«Type» : ⊤..⊤} ∧ {TypeTop : t.«Type»..t.«Type»})
                          ∧ {newTypeTop : ∀(u : ⊤) t.TypeTop})
                          ∧ {TypeRef : t.«Type» ∧ {symb : p.symbols.Symbol}
                                    .. t.«Type» ∧ {symb : p.symbols.Symbol}})
                          ∧ {newTypeRef : ∀(s : p.symbols.Symbol) t.TypeRef}))}
      ∧ {val symbols : μ(y.
            {Symbol : {tpe : p.types.«Type»} ∧ {id : {n : ⊤}}
                   .. {tpe : p.types.«Type»} ∧ {id : {n : ⊤}}}
            ∧ {newSymbol : ∀(u : p.types.«Type») ∀(i : {n : ⊤}) y.Symbol})}.
      {types = ν(t : (((({«Type» : ⊤..⊤} ∧ {TypeTop : t.«Type»..t.«Type»})
                          ∧ {newTypeTop : ∀(u : ⊤) t.TypeTop})
                          ∧ {TypeRef : t.«Type» ∧ {symb : p.symbols.Symbol}
                                    .. t.«Type» ∧ {symb : p.symbols.Symbol}})
                          ∧ {newTypeRef : ∀(s : p.symbols.Symbol) t.TypeRef}).
          (((({type «Type» = ⊤} ∧ {type TypeTop = t.«Type»})
             ∧ {newTypeTop = λ(u : ⊤). u})
             ∧ {type TypeRef = t.«Type» ∧ {symb : p.symbols.Symbol}})
             ∧ {newTypeRef = λ(s : p.symbols.Symbol).
                  let r = ν(r : {symb : p.symbols.Symbol}. {symb = s}) in r}))}
      ∧ {symbols = ν(y :
            {Symbol : {tpe : p.types.«Type»} ∧ {id : {n : ⊤}}
                   .. {tpe : p.types.«Type»} ∧ {id : {n : ⊤}}}
            ∧ {newSymbol : ∀(u : p.types.«Type») ∀(i : {n : ⊤}) y.Symbol}.
          {type Symbol = {tpe : p.types.«Type»} ∧ {id : {n : ⊤}}}
          ∧ {newSymbol = λ(u : p.types.«Type»). λ(i : {n : ⊤}).
               let r = ν(r : {tpe : p.types.«Type»} ∧ {id : {n : ⊤}}.
                         {tpe = u} ∧ {id = i}) in r})}) in
  pcore

/-! ## R1, R2 and R7

R1 and R2 reach a singleton's alias through a type member whose bounds are
singletons.  R7 is a direct-style path whose prefix the `let` insertion binds
opaquely, so a member read through it loses the path. -/

/-- `f.type` passed through a type member's bounds to `g.type`. -/
def R1_src : STm :=
  pdot% λ(f : ⊤). λ(g : ⊤). λ(m : {A : f.type .. g.type}). λ(x : f.type).
        let y : g.type = x in y

/-- A singleton variable used at the function type of its own alias. -/
def R2_src : STm :=
  pdot% λ(f : ∀(z : ⊤) ⊤). λ(p : {A : f.type .. ∀(z : ⊤) ⊤}). λ(x : f.type).
        λ(h : ∀(k : ∀(z : ⊤) ⊤) ⊤). h x

/-- The direct-style path `x.a.b`, read at a member one hop further. -/
def R7_src : STm :=
  pdot% λ(x : {val a : μ(z. {B : ⊥..⊤} ∧ {b : z.B})}). λ(h : ∀(k : x.a.B) ⊤). h x.a.b

end PathsFrontend
