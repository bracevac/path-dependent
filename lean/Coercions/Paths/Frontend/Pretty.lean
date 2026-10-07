import Coercions.Paths.Frontend.Resolve
import Coercions.Paths.DotMNF.Machine

/-!
# The pretty printer

An unparser from the three syntaxes of this library back into the paper's
notation, so that a derivation or a run can be read instead of inspected
constructor by constructor.  The frozen inductives of the version carry no
`Repr` instance and cannot gain one, since the version does not change, so
this module is the only way to look at a `Paths.DotMNF.Ty` or a
`Paths.DotMNF.Tm` as text.

The module carries no theorem.  The checks at the end are the output of the
printer on the terms of `Resolve.lean` and `Notation.lean`, decided in the
kernel, and nothing more is claimed.

## Paths

A path has no precedence of its own: `p.a` is always `p`'s own text followed
by `.` and the field's name, so printing a path never needs parentheses, in
the surface syntax or in the frozen one.  A singleton type `p.type` and a
type selection `p.A` print their path the same way and differ only in the
suffix.  A stable field declaration `{val a : T}` prints exactly like a
computation field with the keyword `val` inserted, since the two differ only
in that keyword.

## What the printer needs that the syntax does not carry

A label of the frozen syntax is a sort and a number
(`lean/Coercions/Paths/FCdot/Debruijn.lean`), so a name comes back only
through a `LabelTable`.  The three entry points without a table are the same
functions at the empty table, where a label prints as its sort and its
number, `A0` for the first type label and `a0` for the first term label.

A bound variable of the frozen syntax is an index, so a name comes back only
through a `NameEnv` of `Resolve.lean`.  Under a binder the printer has to
invent one, since no binder of the frozen syntax or of `Ann.lean` carries a
name.  `freshName` takes the first of eight short names the environment does
not already hold, and falls back to a name built from the environment's
length.  Two binders can therefore end up with the same name.  The common
case is the self binder of an object literal bound by a `let`, which is
printed before the `let`'s own binder is in scope, so the self binder takes
the name the `let` will take.  What comes out is alpha equivalent and
shadows, as the second check below shows.

A state of the machine has a signature and no names at all, so `ppRun` names
the store binders `x0`, `x1` and so on, outermost first.

## No round trip

The output is the paper's notation for a reader, and it is not claimed to
parse back through `pdot%`.  Three things stand in the way, beyond the two
the vanilla printer already has.  A frozen object literal has no self type
(`Paths.DotMNF.Value.obj`), so the printer of the frozen syntax writes
`ν(x. d)`, which the grammar of `Notation.lean` does not have.  A binder of
the de Bruijn syntax has lost the name it was resolved from.  A label built
from a word the notation reserves, such as gDOT's own `Type`, prints as that
plain word, which `pdotTy%` cannot read back without the guillemets the
notation needs there.  The annotated syntax of `Ann.lean` does carry the self
type, and `ppATmWith` prints the full form.

## No printer for a path's view

A typed path has a view of the object it names, over a typed store
(`Paths.FCdot.CanonicalForms.lean`).  Printing that view would mean
recovering, from a final store alone, the index into the self binder's block
that the typing derivation picked and the printer never sees.  This module
prints the paths themselves, in a type or inside a run, and stops there.

## Recursion

Every function here is structural and says so, so the printer reduces in the
kernel and the checks at the end are `rfl` or `decide`.  Nothing in this
module is part of the metatheory.  No definition here lives in the
`Paths.DotMNF` or `Paths.FCdot` namespaces.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Rename Label)
open Paths.DotMNF (Path Ty Tm Value Defs Store Cont State)

/-! ## Parentheses

Every printer below takes the precedence of the position it prints into, and
wraps its result when its own form binds more loosely.  The numbers are the
ones the grammar of `Notation.lean` declares: application at 70 and left
leaning, projection at 80, intersection at 65 and right leaning, and the
closed forms, the declarations and a path's own suffix at the top.  A lambda
and a `let` extend as far right as they can, so they sit at the bottom of the
order. -/

/-- The result, in parentheses when the position binds tighter than the
form. -/
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

/-- The name of a bound variable.  Total, because the environment holds one
name per binder of the signature. -/
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

/-! ## Paths

A path prints as its root's name followed by its field steps, each one
through the label table at the term sort.  Unlike every other form here, a
path never needs parentheses: `.` already groups to the left on its own. -/

/-- A path in the paper's notation, with a label table. -/
def ppPathWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (p : Path s) : String :=
  match p with
  | .var x => NameEnv.nameAt nv x
  | .sel p' a => ppPathWith Λ nv p' ++ "." ++ ppLabel Λ a
termination_by structural p

/-- A path in the paper's notation, with no label table. -/
def ppPath (nv : NameEnv s) (p : Path s) : String := ppPathWith [] nv p

/-! ## Types -/

/-- A type in the paper's notation, at the precedence of its position.  The
stable field, the singleton and the path selection sit beside the
computation field and the plain selection, through the same path printer. -/
def ppTyAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (T : Ty s) : String :=
  match T with
  | .top => "⊤"
  | .bot => "⊥"
  | .typ A S U =>
      "{" ++ ppLabel Λ A ++ " : " ++ ppTyAt Λ 0 nv S ++ " .. " ++ ppTyAt Λ 0 nv U ++ "}"
  | .fld a U => "{" ++ ppLabel Λ a ++ " : " ++ ppTyAt Λ 0 nv U ++ "}"
  | .vfld a U => "{val " ++ ppLabel Λ a ++ " : " ++ ppTyAt Λ 0 nv U ++ "}"
  | .sngl p => ppPathWith Λ nv p ++ ".type"
  | .sel p A => ppPathWith Λ nv p ++ "." ++ ppLabel Λ A
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

/-- A type in the paper's notation, with no label table.  Labels print as
their sort and their number. -/
def ppTy (nv : NameEnv s) (T : Ty s) : String := ppTyWith [] nv T

/-! ## Terms of the frozen syntax

Application and projection take variables in monadic normal form, and so
does the path term, exactly as in the version without paths.  The only forms
that can need parentheses are the lambda and the `let`. -/

mutual
/-- A term in the paper's notation, at the precedence of its position. -/
def ppTmAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (t : Tm s) : String :=
  match t with
  | .path x => NameEnv.nameAt nv x
  | .val v => ppValueAt Λ p nv v
  | .app x y => NameEnv.nameAt nv x ++ " " ++ NameEnv.nameAt nv y
  | .proj x a => NameEnv.nameAt nv x ++ "." ++ ppLabel Λ a
  | .let t' u =>
      let y := freshName (NameEnv.names nv)
      parenIf (p > 0)
        ("let " ++ y ++ " = " ++ ppTmAt Λ 1 nv t' ++ " in "
          ++ ppTmAt Λ 0 (NameEnv.cons nv y) u)
termination_by structural t
/-- A value in the paper's notation.  An object literal of the frozen syntax
has no self type, so the binder stands alone. -/
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
written with the `type` keyword, exactly as the version without paths. -/
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

/-- A term in the paper's notation, with no label table. -/
def ppTm (nv : NameEnv s) (t : Tm s) : String := ppTmWith [] nv t

/-- A value in the paper's notation. -/
def ppValue (nv : NameEnv s) (v : Value s) : String := ppValueWith [] nv v

/-- A definition list in the paper's notation, with no label table. -/
def ppDefs (nv : NameEnv s) (d : Defs s) : String := ppDefsWith [] nv d

/-! ## Annotated terms

The syntax of `Ann.lean` is the one a compilation returns, and it is the one
that prints in full.  The self type of a literal and the result type of a
`let` are there to be printed, and the self type can itself be a stable
field, a singleton or a path selection. -/

mutual
/-- An annotated term in the paper's notation, at the precedence of its
position. -/
def ppATmAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (t : ATm s) : String :=
  match t with
  | .path x => NameEnv.nameAt nv x
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

The surface syntax carries its own names and its own labels, and a surface
path carries its own names too, so these need neither a table nor an
environment.  Application and projection take arbitrary terms here, which is
the point of a direct style front end, so the parentheses matter: the
operator of an application is printed at 70 and the operand at 71, and the
receiver of a projection at 80. -/

/-- A surface path, root first. -/
def ppSPathAt (p : SPath) : String :=
  match p with
  | .var x => x
  | .sel p' a => ppSPathAt p' ++ "." ++ a
termination_by structural p

/-- A surface path. -/
def ppSPath (p : SPath) : String := ppSPathAt p

/-- A surface type in the paper's notation, at the precedence of its
position. -/
def ppSTyAt (p : Nat) (T : SType) : String :=
  match T with
  | .top => "⊤"
  | .bot => "⊥"
  | .typ A S U => "{" ++ A ++ " : " ++ ppSTyAt 0 S ++ " .. " ++ ppSTyAt 0 U ++ "}"
  | .fld a U => "{" ++ a ++ " : " ++ ppSTyAt 0 U ++ "}"
  | .vfld a U => "{val " ++ a ++ " : " ++ ppSTyAt 0 U ++ "}"
  | .sngl p => ppSPathAt p ++ ".type"
  | .sel p A => ppSPathAt p ++ "." ++ A
  | .mu x U => "μ(" ++ x ++ ". " ++ ppSTyAt 0 U ++ ")"
  | .all x S U =>
      parenIf (p > 60) ("∀(" ++ x ++ " : " ++ ppSTyAt 0 S ++ ") " ++ ppSTyAt 0 U)
  | .and S U => parenIf (p > 65) (ppSTyAt 66 S ++ " ∧ " ++ ppSTyAt 65 U)
termination_by structural T

/-- A surface type in the paper's notation. -/
def ppSTy (T : SType) : String := ppSTyAt 0 T

mutual
/-- A surface term in the paper's notation, at the precedence of its
position.  A path in term position has no form of its own: it is nested
`proj`, printed exactly as the vanilla direct-style projection is. -/
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

The store is printed outermost binder first, the continuation as its frames
with a hole, and the term last.  A state carries no names, so `ppRun`
supplies `defaultNames`. -/

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
signature and the environment stand before the colon, which is what makes
the walk structural. -/
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

/-- The term of the answer of `compileAndRun`, which is what the run tests
read. -/
def ppRunTm (Λ : LabelTable) : Option ((s : Sig) × State s) → String
  | none => "did not compile"
  | some ⟨_, ⟨_, _, t⟩⟩ => ppTmWith Λ (defaultNames _) t

/-! ## Checks

Everything above is structural, so the printer reduces in the kernel and the
checks are `rfl` or `decide`.  The terms are the ones `Notation.lean` and
`Resolve.lean` build, so a failure here is a failure of the printer and not
of resolution.
-/

section Checks

/-- The surface program E1, back in the notation it was written in. -/
example :
    ppSTm E1_src = "λ(x : {A : ⊤ .. ⊥}). let y : {B : {a : ⊤} .. {a : ⊤}} = x in y" := rfl

/-- E1 resolves to no path form, so the printed result matches the surface
text, with a table that happens to keep the same names. -/
example :
    (resolve pathsTable E1_src).map (ppATmWith pathsTable .nil)
      = some "λ(x : {A : ⊤ .. ⊥}). let y : {B : {a : ⊤} .. {a : ⊤}} = x in y" := by
  decide +kernel

/-- The same term with no table.  A label is its sort and its number. -/
example :
    (resolve pathsTable E1_src).map (ppATmWith [] .nil)
      = some "λ(x : {A0 : ⊤ .. ⊥}). let y : {A1 : {a0 : ⊤} .. {a0 : ⊤}} = x in y" := by
  decide +kernel

/-- The surface program E2, written with the self binder `s` and the outer
`let` binder `f`. -/
example :
    ppSTm E2_src
      = "let x = ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}. "
        ++ "{type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y}) in let f = x.a in f f" := rfl

/-- E2 resolved: the self binder and the `let` that binds the literal take the
same short name `x`, since the printer invents both and the right hand side
of a `let` is printed before its own binder is in scope.  What comes out is
alpha equivalent to the surface text and shadows, exactly as the vanilla
printer's E2 does. -/
example :
    (resolve pathsTable E2_src).map (ppATmWith pathsTable .nil)
      = some
        ("let x = ν(x : {A : ∀(y : x.A) x.A .. ∀(y : x.A) x.A} ∧ {a : ∀(y : x.A) x.A}. "
          ++ "{type A = ∀(y : x.A) x.A} ∧ {a = λ(y : x.A). y}) in let y = x.a in y y") := by
  decide +kernel

/-- E7's literal is already at the top level, so the printer's own binder
choice agrees with the surface name and the two forms print alike. -/
example :
    ppSTm E7_src = "ν(x : {A : x.B .. x.B} ∧ {B : x.A .. x.A}. {type A = x.B} ∧ {type B = x.A})" :=
  rfl

/-- The annotated form prints the same text, self type included. -/
example :
    (resolve pathsTable E7_src).map (ppATmWith pathsTable .nil)
      = some "ν(x : {A : x.B .. x.B} ∧ {B : x.A .. x.A}. {type A = x.B} ∧ {type B = x.A})" := by
  decide +kernel

/-- Erasure drops the self type, and the printer of the frozen syntax has
nowhere to put one. -/
example :
    (resolve pathsTable E7_src).map (fun a => ppTmWith pathsTable .nil a.erase)
      = some "ν(x. {type A = x.B} ∧ {type B = x.A})" := by
  decide +kernel

/-- X1, a stable field `{val c : T}` beside an ordinary one, and a type
selection two field steps deep, `z.c.A`. -/
example :
    ppSTm X1_src
      = "ν(z : {val c : μ(w. {A : z.B .. z.B})} ∧ {B : z.c.A .. z.c.A}. "
        ++ "{c = ν(w : {A : z.B .. z.B}. {type A = z.B})} ∧ {type B = z.c.A})" := rfl

/-- The resolved form keeps the `val` keyword and the two-step selection, the
printer's own binder names in place of the surface ones. -/
example :
    (resolve pathsTable X1_src).map (ppATmWith pathsTable .nil)
      = some
        ("ν(x : {val c : μ(y. {A : x.B .. x.B})} ∧ {B : x.c.A .. x.c.A}. "
          ++ "{c = ν(y : {A : x.B .. x.B}. {type A = x.B})} ∧ {type B = x.c.A})") := by
  decide +kernel

/-- E9, a singleton at a `let`: `q.type` and, after resolution, `x.type`. -/
example :
    ppSTm E9_src
      = "let q = ν(q : {B : {b : ⊤} .. {b : ⊤}}. {type B = {b : ⊤}}) in "
        ++ "let x = ν(x : {a : q.type}. {a = q}) in let y = x.a in "
        ++ "λ(z : y.B). let w = z in w" := rfl

/-- The singleton survives resolution and printing, at the printer's own
binder name for the first `let`. -/
example :
    (resolve pathsTable E9_src).map (ppATmWith pathsTable .nil)
      = some
        ("let x = ν(x : {B : {b : ⊤} .. {b : ⊤}}. {type B = {b : ⊤}}) in "
          ++ "let y = ν(y : {a : x.type}. {a = x}) in let z = y.a in "
          ++ "λ(w : z.B). let u = w in u") := by
  decide +kernel

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
    ppRun [] (some ⟨[Kind.var], ⟨.cons .nil (.lam .top (.path .here)), .nil, .path .here⟩⟩)
      = "⟨x0 = λ(x : ⊤). x | · | x0⟩" := rfl

/-- The term alone, which is what the run tests read. -/
example :
    ppRunTm [] (some ⟨[Kind.var], ⟨.cons .nil (.lam .top (.path .here)), .nil, .path .here⟩⟩)
      = "x0" := rfl

/-- Nothing to print. -/
example : ppRun [] none = "did not compile" := rfl

end Checks

end PathsFrontend
