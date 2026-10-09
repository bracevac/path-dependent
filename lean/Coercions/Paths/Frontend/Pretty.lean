import Coercions.Paths.Frontend.Resolve
import Coercions.Paths.DotMNF.Machine

/-!
# The pretty printer

Printers from the three term syntaxes (surface, annotated, DOT-MNF) back into
the paper's notation, so that a derivation or a run can be read as text.  The
DOT-MNF syntax has no `Repr` instance.  The module has no theorems.  The checks
at the end are decided in the kernel.

A label of DOT-MNF is a sort and a number, so a name comes back only through a
`LabelTable`.  Without a table a label prints as its sort and number, `A0` for
the first type label and `a0` for the first term label.  A bound variable is an
index, so a name comes back through a `NameEnv`.  Under a binder the printer
invents a name with `freshName`, the first of eight short names not yet in the
environment.  Two binders can get the same name.  For example the self binder
of a literal bound by a `let` is printed before the `let` binder is in scope.
The output is alpha equivalent and shadows.  A machine state has no names, so
`ppRun` calls the store binders `x0`, `x1` and so on.

A path never needs parentheses.  `{val a : T}` prints like `{a : T}` with the
keyword.

The output is not meant to parse back through `pdot%`.  The DOT-MNF printer
writes `ν(x. d)` for a literal, because that syntax has no self type.  The
notation reads that text as a literal whose self type is left to inference.
Binders lose their source names.  A label such as `Type` prints without the
guillemets the notation needs.  The annotated printer `ppATmWith` prints the
self type.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Rename Label)
open Paths.DotMNF (Path Ty Tm Value Defs Store Cont State)

/-! ## Parentheses

Each printer takes the precedence of its position and parenthesizes a form that
binds more loosely.  The numbers are those of `Notation.lean`. -/

/-- Wrap in parentheses when `b`. -/
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

/-- The name of a bound variable. -/
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

/-! ## Paths -/

/-- A path in the paper's notation, with a label table. -/
def ppPathWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (p : Path s) : String :=
  match p with
  | .var x => NameEnv.nameAt nv x
  | .sel p' a => ppPathWith Λ nv p' ++ "." ++ ppLabel Λ a
termination_by structural p

/-- A path in the paper's notation, with no label table. -/
def ppPath (nv : NameEnv s) (p : Path s) : String := ppPathWith [] nv p

/-! ## Types -/

/-- A type in the paper's notation, at the precedence of its position. -/
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

/-! ## Terms of DOT-MNF

Only the lambda and the `let` can need parentheses. -/

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
/-- A value in the paper's notation.  A literal has no self type here. -/
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
/-- A definition list in the paper's notation. -/
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

These are the terms a compilation returns.  They print the self type of a
literal and the type of a `let`. -/

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

Surface syntax carries its names, so these need no table or environment.  The
operator of an application is printed at 70, the operand at 71 and the
receiver of a projection at 80. -/

/-- A surface path, root first. -/
def ppSPathAt (p : SPath) : String :=
  match p with
  | .var x => x
  | .sel p' a => ppSPathAt p' ++ "." ++ a
termination_by structural p

/-- A surface path. -/
def ppSPath (p : SPath) : String := ppSPathAt p

/-- A surface type in the paper's notation, at the precedence of its position. -/
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
/-- A surface term in the paper's notation, at the precedence of its position.
A path in term position is nested `proj`. -/
def ppSTmAt (p : Nat) (e : STm) : String :=
  match e with
  | .var x => x
  | .lam x (some T) t =>
      parenIf (p > 1) ("λ(" ++ x ++ " : " ++ ppSTyAt 0 T ++ "). " ++ ppSTmAt 0 t)
  | .lam x none t => parenIf (p > 1) ("λ" ++ x ++ ". " ++ ppSTmAt 0 t)
  | .obj x (some T) d => "ν(" ++ x ++ " : " ++ ppSTyAt 0 T ++ ". " ++ ppSDefsAt d ++ ")"
  | .obj x none d => "ν(" ++ x ++ ". " ++ ppSDefsAt d ++ ")"
  | .app t u => parenIf (p > 70) (ppSTmAt 70 t ++ " " ++ ppSTmAt 71 u)
  | .proj t a => ppSTmAt 80 t ++ "." ++ a
  | .«let» x ann t u =>
      let ann? :=
        match ann with
        | none => ""
        | some U => " : " ++ ppSTyAt 0 U
      parenIf (p > 0)
        ("let " ++ x ++ ann? ++ " = " ++ ppSTmAt 1 t ++ " in " ++ ppSTmAt 0 u)
  | .asc t T => "(" ++ ppSTmAt 0 t ++ " : " ++ ppSTyAt 0 T ++ ")"
termination_by structural e
/-- A surface definition list in the paper's notation. -/
def ppSDefsAt (d : SDefs) : String :=
  match d with
  | .typ A T => "{type " ++ A ++ " = " ++ ppSTyAt 0 T ++ "}"
  | .trm a none t => "{" ++ a ++ " = " ++ ppSTmAt 0 t ++ "}"
  | .trm a (some T) t => "{" ++ a ++ " : " ++ ppSTyAt 0 T ++ " = " ++ ppSTmAt 0 t ++ "}"
  | .and d' e => ppSDefsAt d' ++ " ∧ " ++ ppSDefsAt e
termination_by structural d
end

/-- A surface term in the paper's notation. -/
def ppSTm (e : STm) : String := ppSTmAt 0 e

/-- A surface definition list in the paper's notation. -/
def ppSDefs (d : SDefs) : String := ppSDefsAt d

/-! ## States of the source machine

The store is printed outermost binder first, then the continuation as frames
with a hole, then the term. -/

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

/-- The frames of the continuation, outermost first, each with its hole. -/
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

/-- The term of the answer of `compileAndRun`. -/
def ppRunTm (Λ : LabelTable) : Option ((s : Sig) × State s) → String
  | none => "did not compile"
  | some ⟨_, ⟨_, _, t⟩⟩ => ppTmWith Λ (defaultNames _) t

/-! ## Checks -/

section Checks

/-- The surface program E1, back in the notation it was written in. -/
example :
    ppSTm E1_src = "λ(x : {A : ⊤ .. ⊥}). let y : {B : {a : ⊤} .. {a : ⊤}} = x in y" := rfl

/-- E1 resolved prints as the surface text. -/
example :
    (resolve pathsTable E1_src).map (ppATmWith pathsTable .nil)
      = some "λ(x : {A : ⊤ .. ⊥}). let y : {B : {a : ⊤} .. {a : ⊤}} = x in y" := by
  decide +kernel

/-- The same term with no table. -/
example :
    (resolve pathsTable E1_src).map (ppATmWith [] .nil)
      = some "λ(x : {A0 : ⊤ .. ⊥}). let y : {A1 : {a0 : ⊤} .. {a0 : ⊤}} = x in y" := by
  decide +kernel

/-- The surface program E2. -/
example :
    ppSTm E2_src
      = "let x = ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}. "
        ++ "{type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y}) in let f = x.a in f f" := rfl

/-- E2 resolved.  The self binder and the `let` binder both get the name `x`,
because the literal is printed before the `let` binder is in scope. -/
example :
    (resolve pathsTable E2_src).map (ppATmWith pathsTable .nil)
      = some
        ("let x = ν(x : {A : ∀(y : x.A) x.A .. ∀(y : x.A) x.A} ∧ {a : ∀(y : x.A) x.A}. "
          ++ "{type A = ∀(y : x.A) x.A} ∧ {a = λ(y : x.A). y}) in let y = x.a in y y") := by
  decide +kernel

/-- E7 is a top level literal, so the invented binder name agrees with the
surface name. -/
example :
    ppSTm E7_src = "ν(x : {A : x.B .. x.B} ∧ {B : x.A .. x.A}. {type A = x.B} ∧ {type B = x.A})" :=
  rfl

/-- The annotated form prints the same text. -/
example :
    (resolve pathsTable E7_src).map (ppATmWith pathsTable .nil)
      = some "ν(x : {A : x.B .. x.B} ∧ {B : x.A .. x.A}. {type A = x.B} ∧ {type B = x.A})" := by
  decide +kernel

/-- Erasure drops the self type. -/
example :
    (resolve pathsTable E7_src).map (fun a => ppTmWith pathsTable .nil a.erase)
      = some "ν(x. {type A = x.B} ∧ {type B = x.A})" := by
  decide +kernel

/-- X1: a stable field beside an ordinary one, and the selection `z.c.A`. -/
example :
    ppSTm X1_src
      = "ν(z : {val c : μ(w. {A : z.B .. z.B})} ∧ {B : z.c.A .. z.c.A}. "
        ++ "{c = ν(w : {A : z.B .. z.B}. {type A = z.B})} ∧ {type B = z.c.A})" := rfl

/-- X1 resolved keeps `val` and the selection.  Binder names are invented. -/
example :
    (resolve pathsTable X1_src).map (ppATmWith pathsTable .nil)
      = some
        ("ν(x : {val c : μ(y. {A : x.B .. x.B})} ∧ {B : x.c.A .. x.c.A}. "
          ++ "{c = ν(y : {A : x.B .. x.B}. {type A = x.B})} ∧ {type B = x.c.A})") := by
  decide +kernel

/-- E9: a singleton at a `let`. -/
example :
    ppSTm E9_src
      = "let q = ν(q : {B : {b : ⊤} .. {b : ⊤}}. {type B = {b : ⊤}}) in "
        ++ "let x = ν(x : {a : q.type}. {a = q}) in let y = x.a in "
        ++ "λ(z : y.B). let w = z in w" := rfl

/-- E9 resolved keeps the singleton. -/
example :
    (resolve pathsTable E9_src).map (ppATmWith pathsTable .nil)
      = some
        ("let x = ν(x : {B : {b : ⊤} .. {b : ⊤}}. {type B = {b : ⊤}}) in "
          ++ "let y = ν(y : {a : x.type}. {a = x}) in let z = y.a in "
          ++ "λ(w : z.B). let u = w in u") := by
  decide +kernel

/-- Only the left operand of `∧` needs parentheses. -/
example :
    ppTy (s := []) .nil (.and (.and .top .bot) (.and .bot .top))
      = "(⊤ ∧ ⊥) ∧ ⊥ ∧ ⊤" := rfl

/-- So does a function type there. -/
example :
    ppTy (s := []) .nil (.and (.all .top .top) .bot) = "(∀(x : ⊤) ⊤) ∧ ⊥" := rfl

/-- A binder takes the first short name not in the environment. -/
example :
    ppTy (s := []) .nil (.mu (.fld (.trm 0) (.mu (.sel (.var (.there .here)) (.typ 0)))))
      = "μ(x. {a0 : μ(y. x.A0)})" := rfl

/-- The final state of `let x = λ(z : ⊤). z in x`. -/
example :
    ppRun [] (some ⟨[Kind.var], ⟨.cons .nil (.lam .top (.path .here)), .nil, .path .here⟩⟩)
      = "⟨x0 = λ(x : ⊤). x | · | x0⟩" := rfl

/-- The term alone. -/
example :
    ppRunTm [] (some ⟨[Kind.var], ⟨.cons .nil (.lam .top (.path .here)), .nil, .path .here⟩⟩)
      = "x0" := rfl

/-- Nothing to print. -/
example : ppRun [] none = "did not compile" := rfl

/-- A lambda with its domain left to inference prints without parentheses. -/
example : ppSTm (pdot% λx. x) = "λx. x" := rfl

/-- A literal with its self type left to inference, and a written field type. -/
example : ppSTm (pdot% ν(x. {a : ⊤ = x})) = "ν(x. {a : ⊤ = x})" := rfl

/-- An ascription prints in its own parentheses. -/
example : ppSTm (pdot% (λx. x : ⊤)) = "(λx. x : ⊤)" := rfl

/-- A written field type at a path, and a nested literal without a self type. -/
example :
    ppSTm (pdot% ν(x. {c = ν(y. {type A = ⊤})} ∧ {a : x.c.A = x}))
      = "ν(x. {c = ν(y. {type A = ⊤})} ∧ {a : x.c.A = x})" := rfl

end Checks

end PathsFrontend
