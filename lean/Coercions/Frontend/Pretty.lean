import Coercions.Frontend.Resolve
import Coercions.DotMNF.Machine

/-!
# The pretty printer

Stage F3.2 of `plan-5e-frontend-stages.md`.  An unparser from the three
syntaxes of this library back into the paper's notation
(`lean/Coercions/paper/sections/source.tex`, `lean/Coercions/paper/macros.tex`),
so that an `#eval` of a compilation or of a run is readable.  The frozen
inductives carry no `Repr` instance and cannot gain one, since the vanilla tree
does not change, so this module is the only way to look at a `DotMNF.Ty` or a
`DotMNF.Tm` as text.

The module carries no theorem.  The checks at the end are the output of the
printer on the terms of `Resolve.lean`, decided in the kernel, and nothing more
is claimed.

## What the printer needs that the syntax does not carry

A label of the frozen syntax is a sort and a number
(`lean/Coercions/FCdot/Debruijn.lean`), so a name comes back only through a
`LabelTable`.  The table carrying functions are the primitives and their names
end in `With`.  F3.2 writes the three entry points without a table, as
`ppTy : NameEnv s → Ty s → String` and so on, and those are the same functions
at the empty table, where a label prints as its sort and its number, `A0` for
the first type label and `a0` for the first term label.

A bound variable of the frozen syntax is an index, so a name comes back only
through a `NameEnv` of `Resolve.lean`.  Under a binder the printer has to invent
one, since no binder of `DotMNF` or of `Ann.lean` carries a name.  `freshName`
takes the first of eight short names that the environment does not already hold,
and falls back to a name built from the environment's length.  Two binders can
therefore end up with the same name.  The common case is the right hand side of
a `let`, which lives outside the binding and is printed before the binding is in
scope, so a binder there takes the same name the `let` itself will take.  What
comes out is alpha equivalent and shadows, as E2 and E4 below show.  The printer
is for reading and states nothing about its output, so this is a cost of no
consequence.

A state of the machine has a signature and no names at all, so `ppRun` names the
store binders `x0`, `x1` and so on, outermost first.

## No round trip

The output is the paper's notation for a reader.  It is not claimed to parse
back through `dot%`.  Three things stand in the way.  A frozen object literal
has no self type (`DotMNF.Value.obj`), so the printer of the frozen syntax
writes `ν(x. d)`, which the grammar of `Notation.lean` does not have.  A binder
of the de Bruijn syntax has lost the name it was resolved from, so the binding
that let insertion inserts under the name `%` comes back as an ordinary short
name.  A label outside the table prints as its sort and its number.  The
annotated syntax of `Ann.lean` does carry the self type, and `ppATmWith` prints
the full form.

## Recursion

Every function here is structural and says so, so the printer reduces in the
kernel and the checks at the end are `rfl`.  The annotation is not decoration.
`Cont` takes its signature as a datatype parameter
(`lean/Coercions/DotMNF/Machine.lean`), so a walk over a continuation is
structural only when the signature and the name environment stand before the
colon, and Lean falls back to well founded recursion, silently and irreducibly,
when they do not.  That was measured here.

Nothing in this module is part of the metatheory.  No definition here lives in
the `DotMNF` or `FCdot` namespaces.
-/

namespace Frontend

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Path Ty Tm Value Defs Store Cont State)

/-! ## Parentheses

Every printer below takes the precedence of the position it prints into, and
wraps its result when its own form binds more loosely.  The numbers are the ones
the grammar of `Notation.lean` declares: application at 70 and left leaning,
projection at 80, intersection at 65 and right leaning, and the closed forms at
the top.  A lambda and a `let` extend as far right as they can, so they sit at
the bottom of the order, the lambda at 1 and the `let` at 0.  That is what keeps
a lambda bare as the right hand side of a `let` and puts parentheses around a
nested `let` there. -/

/-- The result, in parentheses when the position binds tighter than the form. -/
def parenIf (b : Bool) (str : String) : String :=
  if b then "(" ++ str ++ ")" else str

/-! ## Labels -/

/-- The first name the table interns at this label. -/
def labelName? (Λ : LabelTable) (l : Label) : Option String :=
  match Λ with
  | [] => none
  | (x, l') :: Λ' => if l' = l then some x else labelName? Λ' l
termination_by structural Λ

/-- The name of a label no table holds: the sort and the number. -/
def defaultLabelName : Label → String
  | .typ n => "A" ++ toString n
  | .trm n => "a" ++ toString n

/-- The name of a label, through the table where the table has one. -/
def ppLabel (Λ : LabelTable) (l : Label) : String :=
  (labelName? Λ l).getD (defaultLabelName l)

/-! ## Names for binders -/

/-- The short names a binder is given, in the order they are tried. -/
def binderNames : List String := ["x", "y", "z", "w", "u", "v", "p", "q"]

/-- The first short name the environment does not hold. -/
def freshName (used : List String) : String :=
  match binderNames.find? (fun c => !used.contains c) with
  | some c => c
  | none => "x" ++ toString used.length

/-- The name of a bound variable.  Total, because the environment holds one name
per binder of the signature. -/
def NameEnv.nameAt {s : Sig} (nv : NameEnv s) (i : BVar s .var) : String :=
  match nv, i with
  | .cons _ y, .here => y
  | .cons nv' _, .there i' => NameEnv.nameAt nv' i'
termination_by structural nv

/-- Names for a signature that never had any, outermost binder `x0`. -/
def defaultNames (s : Sig) : NameEnv s :=
  match s with
  | [] => .nil
  | .var :: s' => .cons (defaultNames s') ("x" ++ toString s'.length)
termination_by structural s

/-! ## Types -/

/-- A type in the paper's notation, at the precedence of its position. -/
def ppTyAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (T : Ty s) : String :=
  match T with
  | .top => "⊤"
  | .bot => "⊥"
  | .typ A S U =>
      "{" ++ ppLabel Λ A ++ " : " ++ ppTyAt Λ 0 nv S ++ " .. " ++ ppTyAt Λ 0 nv U ++ "}"
  | .fld a U => "{" ++ ppLabel Λ a ++ " : " ++ ppTyAt Λ 0 nv U ++ "}"
  | .sel (.var x) A => NameEnv.nameAt nv x ++ "." ++ ppLabel Λ A
  | .mu U =>
      let y := freshName (NameEnv.names nv)
      "μ(" ++ y ++ ". " ++ ppTyAt Λ 0 (NameEnv.cons nv y) U ++ ")"
  | .all S U =>
      let y := freshName (NameEnv.names nv)
      parenIf (p > 60)
        ("∀(" ++ y ++ " : " ++ ppTyAt Λ 0 nv S ++ ") " ++ ppTyAt Λ 0 (NameEnv.cons nv y) U)
  | .and S U =>
      parenIf (p > 65) (ppTyAt Λ 66 nv S ++ " ∧ " ++ ppTyAt Λ 65 nv U)
termination_by structural T

/-- A type in the paper's notation, with a label table. -/
def ppTyWith (Λ : LabelTable) (nv : NameEnv s) (T : Ty s) : String := ppTyAt Λ 0 nv T

/-- A type in the paper's notation.  The entry point F3.2 writes.  Labels print
as their sort and their number. -/
def ppTy (nv : NameEnv s) (T : Ty s) : String := ppTyWith [] nv T

/-! ## Terms of the frozen syntax

Application and projection take variables in monadic normal form, so the only
forms that can need parentheses are the lambda and the `let`. -/

mutual
/-- A term in the paper's notation, at the precedence of its position. -/
def ppTmAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (t : Tm s) : String :=
  match t with
  | .path (.var x) => NameEnv.nameAt nv x
  | .val v => ppValueAt Λ p nv v
  | .app x y => NameEnv.nameAt nv x ++ " " ++ NameEnv.nameAt nv y
  | .proj x a => NameEnv.nameAt nv x ++ "." ++ ppLabel Λ a
  | .let t' u =>
      let y := freshName (NameEnv.names nv)
      parenIf (p > 0)
        ("let " ++ y ++ " = " ++ ppTmAt Λ 1 nv t' ++ " in "
          ++ ppTmAt Λ 0 (NameEnv.cons nv y) u)
termination_by structural t
/-- A value in the paper's notation.  An object literal of the frozen syntax has
no self type, so the binder stands alone. -/
def ppValueAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (v : Value s) : String :=
  match v with
  | .obj d =>
      let y := freshName (NameEnv.names nv)
      "ν(" ++ y ++ ". " ++ ppDefsWith Λ (NameEnv.cons nv y) d ++ ")"
  | .lam S t =>
      let y := freshName (NameEnv.names nv)
      parenIf (p > 1)
        ("λ(" ++ y ++ " : " ++ ppTyWith Λ nv S ++ "). "
          ++ ppTmAt Λ 0 (NameEnv.cons nv y) t)
termination_by structural v
/-- A definition list in the paper's notation.  The type member definition is
written with the keyword of F0.3. -/
def ppDefsWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (d : Defs s) : String :=
  match d with
  | .typ A T => "{type " ++ ppLabel Λ A ++ " = " ++ ppTyWith Λ nv T ++ "}"
  | .trm a t => "{" ++ ppLabel Λ a ++ " = " ++ ppTmAt Λ 0 nv t ++ "}"
  | .and d' e => ppDefsWith Λ nv d' ++ " ∧ " ++ ppDefsWith Λ nv e
termination_by structural d
end

/-- A term in the paper's notation, with a label table. -/
def ppTmWith (Λ : LabelTable) (nv : NameEnv s) (t : Tm s) : String := ppTmAt Λ 0 nv t

/-- A value in the paper's notation, with a label table. -/
def ppValueWith (Λ : LabelTable) (nv : NameEnv s) (v : Value s) : String :=
  ppValueAt Λ 0 nv v

/-- A term in the paper's notation.  The entry point F3.2 writes. -/
def ppTm (nv : NameEnv s) (t : Tm s) : String := ppTmWith [] nv t

/-- A value in the paper's notation. -/
def ppValue (nv : NameEnv s) (v : Value s) : String := ppValueWith [] nv v

/-- A definition list in the paper's notation.  The entry point F3.2 writes. -/
def ppDefs (nv : NameEnv s) (d : Defs s) : String := ppDefsWith [] nv d

/-! ## Annotated terms

The syntax of `Ann.lean` is the one a compilation returns, and it is the one
that prints in full.  The self type of a literal and the result type of a `let`
are there to be printed. -/

mutual
/-- An annotated term in the paper's notation, at the precedence of its
position. -/
def ppATmAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (t : ATm s) : String :=
  match t with
  | .path (.var x) => NameEnv.nameAt nv x
  | .lam S t' =>
      let y := freshName (NameEnv.names nv)
      parenIf (p > 1)
        ("λ(" ++ y ++ " : " ++ ppTyWith Λ nv S ++ "). "
          ++ ppATmAt Λ 0 (NameEnv.cons nv y) t')
  | .obj T d =>
      let y := freshName (NameEnv.names nv)
      "ν(" ++ y ++ " : " ++ ppTyWith Λ (NameEnv.cons nv y) T ++ ". "
        ++ ppADefsWith Λ (NameEnv.cons nv y) d ++ ")"
  | .app x y => NameEnv.nameAt nv x ++ " " ++ NameEnv.nameAt nv y
  | .proj x a => NameEnv.nameAt nv x ++ "." ++ ppLabel Λ a
  | .let ann t' u =>
      let y := freshName (NameEnv.names nv)
      let ann? :=
        match ann with
        | none => ""
        | some U => " : " ++ ppTyWith Λ nv U
      parenIf (p > 0)
        ("let " ++ y ++ ann? ++ " = " ++ ppATmAt Λ 1 nv t' ++ " in "
          ++ ppATmAt Λ 0 (NameEnv.cons nv y) u)
termination_by structural t
/-- An annotated definition list in the paper's notation. -/
def ppADefsWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (d : ADefs s) : String :=
  match d with
  | .typ A T => "{type " ++ ppLabel Λ A ++ " = " ++ ppTyWith Λ nv T ++ "}"
  | .trm a t => "{" ++ ppLabel Λ a ++ " = " ++ ppATmAt Λ 0 nv t ++ "}"
  | .and d' e => ppADefsWith Λ nv d' ++ " ∧ " ++ ppADefsWith Λ nv e
termination_by structural d
end

/-- An annotated term in the paper's notation, with a label table. -/
def ppATmWith (Λ : LabelTable) (nv : NameEnv s) (t : ATm s) : String := ppATmAt Λ 0 nv t

/-- An annotated term in the paper's notation. -/
def ppATm (nv : NameEnv s) (t : ATm s) : String := ppATmWith [] nv t

/-- An annotated definition list in the paper's notation. -/
def ppADefs (nv : NameEnv s) (d : ADefs s) : String := ppADefsWith [] nv d

/-! ## Surface phrases

The surface syntax carries its own names and its own labels, so these three need
neither a table nor an environment.  Application and projection take arbitrary
terms here, which is the point of a direct style front end, so the parentheses
matter: the operator of an application is printed at 70 and the operand at 71,
and the receiver of a projection at 80. -/

/-- A surface type in the paper's notation, at the precedence of its position. -/
def ppSTyAt (p : Nat) (T : SType) : String :=
  match T with
  | .top => "⊤"
  | .bot => "⊥"
  | .typ A S U => "{" ++ A ++ " : " ++ ppSTyAt 0 S ++ " .. " ++ ppSTyAt 0 U ++ "}"
  | .fld a U => "{" ++ a ++ " : " ++ ppSTyAt 0 U ++ "}"
  | .sel x A => x ++ "." ++ A
  | .mu x U => "μ(" ++ x ++ ". " ++ ppSTyAt 0 U ++ ")"
  | .all x S U =>
      parenIf (p > 60) ("∀(" ++ x ++ " : " ++ ppSTyAt 0 S ++ ") " ++ ppSTyAt 0 U)
  | .and S U => parenIf (p > 65) (ppSTyAt 66 S ++ " ∧ " ++ ppSTyAt 65 U)
termination_by structural T

/-- A surface type in the paper's notation. -/
def ppSTy (T : SType) : String := ppSTyAt 0 T

mutual
/-- A surface term in the paper's notation, at the precedence of its position. -/
def ppSTmAt (p : Nat) (e : STm) : String :=
  match e with
  | .var x => x
  | .lam x T t =>
      parenIf (p > 1) ("λ(" ++ x ++ " : " ++ ppSTyAt 0 T ++ "). " ++ ppSTmAt 0 t)
  | .obj x T d => "ν(" ++ x ++ " : " ++ ppSTyAt 0 T ++ ". " ++ ppSDefsAt d ++ ")"
  | .app t u => parenIf (p > 70) (ppSTmAt 70 t ++ " " ++ ppSTmAt 71 u)
  | .proj t a => ppSTmAt 80 t ++ "." ++ a
  | .«let» x ann t u =>
      let ann? :=
        match ann with
        | none => ""
        | some U => " : " ++ ppSTyAt 0 U
      parenIf (p > 0)
        ("let " ++ x ++ ann? ++ " = " ++ ppSTmAt 1 t ++ " in " ++ ppSTmAt 0 u)
termination_by structural e
/-- A surface definition list in the paper's notation. -/
def ppSDefsAt (d : SDefs) : String :=
  match d with
  | .typ A T => "{type " ++ A ++ " = " ++ ppSTyAt 0 T ++ "}"
  | .trm a t => "{" ++ a ++ " = " ++ ppSTmAt 0 t ++ "}"
  | .and d' e => ppSDefsAt d' ++ " ∧ " ++ ppSDefsAt e
termination_by structural d
end

/-- A surface term in the paper's notation. -/
def ppSTm (e : STm) : String := ppSTmAt 0 e

/-- A surface definition list in the paper's notation. -/
def ppSDefs (d : SDefs) : String := ppSDefsAt d

/-! ## States of the source machine

The store is printed outermost binder first, the continuation as its frames with
a hole, and the term last.  A state carries no names, so `ppRun` supplies
`defaultNames`. -/

/-- The store as one entry per binder, outermost first. -/
def storeEntries (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (σ : Store s) : List String :=
  match nv, σ with
  | .nil, .nil => []
  | .cons nv' y, .cons σ' v =>
      storeEntries Λ nv' σ' ++ [y ++ " = " ++ ppValueWith Λ nv' v]
termination_by structural nv

/-- The store in the paper's notation. -/
def ppStoreWith (Λ : LabelTable) (nv : NameEnv s) (σ : Store s) : String :=
  match storeEntries Λ nv σ with
  | [] => "·"
  | es => String.intercalate ", " es

/-- The frames of the continuation, outermost first, each with its hole.  The
signature and the environment stand before the colon, which is what makes the
walk structural. -/
def contFrames (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (K : Cont s) : List String :=
  match K with
  | .nil => []
  | .cons K' u =>
      let y := freshName (NameEnv.names nv)
      contFrames Λ nv K' ++ ["let " ++ y ++ " = □ in " ++ ppTmWith Λ (NameEnv.cons nv y) u]
termination_by structural K

/-- The continuation in the paper's notation. -/
def ppContWith (Λ : LabelTable) (nv : NameEnv s) (K : Cont s) : String :=
  match contFrames Λ nv K with
  | [] => "·"
  | fs => String.intercalate ", " fs

/-- A state of the source machine, store then continuation then term. -/
def ppStateWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (st : State s) : String :=
  match st with
  | ⟨σ, K, t⟩ =>
      "⟨" ++ ppStoreWith Λ nv σ ++ " | " ++ ppContWith Λ nv K ++ " | "
        ++ ppTmWith Λ nv t ++ "⟩"

/-- The answer of `compileAndRun`, in full. -/
def ppRun (Λ : LabelTable) : Option ((s : Sig) × State s) → String
  | none => "did not compile"
  | some ⟨s, st⟩ => ppStateWith Λ (defaultNames s) st

/-- The term of the answer of `compileAndRun`, which is what the run tests of
F3.3 read. -/
def ppRunTm (Λ : LabelTable) : Option ((s : Sig) × State s) → String
  | none => "did not compile"
  | some ⟨s, ⟨_, _, t⟩⟩ => ppTmWith Λ (defaultNames s) t

/-! ## Checks

Everything above is structural, so the printer reduces in the kernel and the
checks are `rfl`.  The terms are the ones `Resolve.lean` builds from the surface
notation, so a failure here is a failure of the printer and not of resolution.
-/

section Checks

/-- The surface program E1, back in the notation it was written in. -/
example :
    ppSTm E1src = "λ(x : {A : ⊤ .. ⊥}). let y : {B : {a : ⊤} .. {a : ⊤}} = x in y" := rfl

/-- The annotated term E1 resolves to, printed through the example table.  The
two names come back because the printer invents the same ones. -/
example :
    ppATmWith exampleTable .nil E1ann
      = "λ(x : {A : ⊤ .. ⊥}). let y : {B : {a : ⊤} .. {a : ⊤}} = x in y" := rfl

/-- The same term with no table.  A label is its sort and its number. -/
example :
    ppATm .nil E1ann
      = "λ(x : {A0 : ⊤ .. ⊥}). let y : {A1 : {a0 : ⊤} .. {a0 : ⊤}} = x in y" := rfl

/-- E10, the one program of F3.3 that let insertion changes.  The surface
program is direct style. -/
example : ppSTm E10src = "λ(f : ⊤). λ(g : ⊤). f (g f)" := rfl

/-- Its resolved form carries the inserted binding, under a name of the
printer's own since the term kept none. -/
example :
    ppATmWith exampleTable .nil E10ann
      = "λ(x : ⊤). λ(y : ⊤). let z = y x in x z" := rfl

/-- E2, where the object literal's self binder and the `let` that binds the
literal take the same short name.  The right hand side of a `let` is printed
before the binding is in scope, so this is what shadowing looks like. -/
example :
    ppATmWith exampleTable .nil E2ann
      = "let x = ν(x : {A : ∀(y : x.A) x.A .. ∀(y : x.A) x.A} ∧ {a : ∀(y : x.A) x.A}. "
        ++ "{type A = ∀(y : x.A) x.A} ∧ {a = λ(y : x.A). y}) in let y = x.a in y y" := rfl

/-- E4, the same thing at a lambda in a `let` right hand side. -/
example :
    ppATmWith exampleTable .nil E4ann
      = "λ(x : {B : {A : ⊥ .. ⊤} .. {A : {a : ⊤} .. ⊤}}). λ(y : {A : ⊥ .. ⊤}). "
        ++ "λ(z : {a : ⊤}). let w = λ(w : y.A). w in w z" := rfl

/-- An object literal of the annotated syntax prints its self type, E7. -/
example :
    ppATmWith exampleTable .nil E7ann
      = "ν(x : {A : x.B .. x.B} ∧ {B : x.A .. x.A}. "
        ++ "{type A = x.B} ∧ {type B = x.A})" := rfl

/-- Erasure drops the self type, and the printer of the frozen syntax has
nowhere to put one. -/
example :
    ppTmWith exampleTable .nil (ATm.erase E7ann)
      = "ν(x. {type A = x.B} ∧ {type B = x.A})" := rfl

/-- Intersection is right leaning, so only the left operand needs
parentheses. -/
example :
    ppTy (s := []) .nil (.and (.and .top .bot) (.and .bot .top))
      = "(⊤ ∧ ⊥) ∧ ⊥ ∧ ⊤" := rfl

/-- A function type as the left operand of an intersection needs them too. -/
example :
    ppTy (s := []) .nil (.and (.all .top .top) .bot) = "(∀(x : ⊤) ⊤) ∧ ⊥" := rfl

/-- A binder takes the first short name the environment does not hold. -/
example :
    ppTy (s := []) .nil (.mu (.fld (.trm 0) (.mu (.sel (.var (.there .here)) (.typ 0)))))
      = "μ(x. {a0 : μ(y. x.A0)})" := rfl

/-- The state the driver of `Step.lean` reaches on `let x = λ(z : ⊤). z in x`,
store and continuation and term. -/
example :
    ppRun exampleTable
        (some ⟨[Kind.var], ⟨.cons .nil (.lam .top (.path (.var .here))), .nil,
          .path (.var .here)⟩⟩)
      = "⟨x0 = λ(x : ⊤). x | · | x0⟩" := rfl

/-- The term alone, which is what the run tests of F3.3 read. -/
example :
    ppRunTm exampleTable
        (some ⟨[Kind.var], ⟨.cons .nil (.lam .top (.path (.var .here))), .nil,
          .path (.var .here)⟩⟩)
      = "x0" := rfl

/-- The state before that step: an empty store, one frame, and a value. -/
example :
    ppRun exampleTable
        (some ⟨[], ⟨.nil, .cons .nil (.path (.var .here)),
          .val (.lam .top (.path (.var .here)))⟩⟩)
      = "⟨· | let x = □ in x | λ(x : ⊤). x⟩" := rfl

/-- Nothing to print. -/
example : ppRun exampleTable none = "did not compile" := rfl

end Checks

end Frontend
