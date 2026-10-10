import Coercions.CapturesCC.Frontend.Resolve
import Coercions.CapturesCC.Frontend.Pipeline

/-!
# The pretty printer

An unparser from the syntaxes of this library back into the paper's notation,
so that an `#eval` of a compilation or of a run is readable.  The version's
inductives carry no `Repr` instance, so this module is the way to see a
`CapturesCC.DotMNF.Ty` or `Tm` as text.

A plain DOT type splits into a shape, the type former, and a type, a shape
with a capture set `S ^ C`.  An answer is a type, or a type under one capture
binder bounded by a set of the enclosing scope, `∃[c ⊑ C] T`.  The mutual
block has one function for each: `ppShapeAt`, `ppTyAt` and `ppETyAt`.
Parentheses follow the grammar's precedences, `^` at 60 and `∧` at 65.  Under
`^`, an arrow or an intersection is parenthesised by testing `Shape.isAtomic`.

## Invisible binders

The calculus opens binders that no surface phrase writes.  An arrow opens its
own capture binder before its parameter.  A closure's body also opens a body
root.  An object's definitions sit under a class root and the self.  A `let`
with an existential answer and a written unpacking each open a capture binder
for the witness.  The printer invents a name for each, from two disjoint
pools, `binderNames` for term binders and `capBinderNames` for capture
binders.  An invented name avoids every name in scope.  The arrow's own
capture binder always prints named, `∀[κ](x : T) U`, since the elaborated
shape does not record whether the program named it.

## No round trip

The output is for a reader, not a parser.  An object literal of the version has no
self shape, a let-inserted binder gets an invented name, and a label outside
the table prints as its sort and number.  The annotated syntax of `Ann.lean`
carries the self shape, so `ppATmWith` prints an object literal in full.

Every function here is structural, so the checks at the end are `rfl`.
-/

namespace CapturesCCFrontend

open CapturesCC.FCdot (Kind Sig BVar Rename Label)
open CapturesCC.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Tm Value Defs Store Cont State
  Platform)
open CapturesCC.DotMNF.Examples (unitTy la)

/-! ## Parentheses -/

/-- Parenthesise when the position binds tighter than the form. -/
def parenIf (b : Bool) (str : String) : String :=
  if b then "(" ++ str ++ ")" else str

/-- A level above every real precedence, for operands that must be closed. -/
def atomPrec : Nat := 100

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

/-! ## Names for binders

Two disjoint pools, one per kind.  When a pool is used up, the name is built
from the count of names already used. -/

/-- The short names a term binder is given, in the order they are tried. -/
def binderNames : List String := ["x", "y", "z", "w", "u", "v", "p", "q"]

/-- The short names a capture binder is given, in the order they are
tried. -/
def capBinderNames : List String := ["k", "j", "i", "h", "g", "e", "d", "b"]

/-- The first name of a pool the list `used` does not hold. -/
def firstFresh (pool : List String) (used : List String) : Option String :=
  pool.find? (fun c => !used.contains c)

/-- The first term name `used` does not hold. -/
def freshName (used : List String) : String :=
  match firstFresh binderNames used with
  | some c => c
  | none => "x" ++ toString used.length

/-- The first capture name `used` does not hold. -/
def freshCapName (used : List String) : String :=
  match firstFresh capBinderNames used with
  | some c => c
  | none => "k" ++ toString used.length

/-! ## Name environments -/

/-- Every name in scope, of either kind, innermost first. -/
def NameEnv.allNames {s : Sig} (nv : NameEnv s) : List String := nv.names ++ nv.capNames

/-- The name of a bound term variable.  Capture binders are skipped. -/
def NameEnv.nameAt {s : Sig} (nv : NameEnv s) (i : BVar s .var) : String :=
  match nv, i with
  | .cons _ y, .here => y
  | .cons nv' _, .there i' => NameEnv.nameAt nv' i'
  | .consC nv' _, .there i' => NameEnv.nameAt nv' i'
termination_by structural nv

/-- The name of a bound capture variable. -/
def NameEnv.capNameAt {s : Sig} (nv : NameEnv s) (i : BVar s .cap) : String :=
  match nv, i with
  | .consC _ y, .here => y
  | .cons nv' _, .there i' => NameEnv.capNameAt nv' i'
  | .consC nv' _, .there i' => NameEnv.capNameAt nv' i'
termination_by structural nv

/-- Names for a signature that has none, outermost `x0` or `k0`, each kind
counted on its own.  Used for the store of a run. -/
def defaultNames (s : Sig) : NameEnv s :=
  match s with
  | [] => .nil
  | .var :: s' => .cons (defaultNames s') ("x" ++ toString s'.length)
  | .cap :: s' => .consC (defaultNames s') ("k" ++ toString s'.length)
termination_by structural s

/-- Names for a signature whose outermost binders are named by `pre`.  The
other binders take invented names.  This reads a run over a named platform. -/
def namesOver (pre : List String) (s : Sig) : NameEnv s :=
  match s with
  | [] => .nil
  | .var :: s' => .cons (namesOver pre s') (pre.getD s'.length ("x" ++ toString s'.length))
  | .cap :: s' => .consC (namesOver pre s') (pre.getD s'.length ("k" ++ toString s'.length))
termination_by structural s

/-! ## Capture sets -/

/-- A capture atom. -/
def ppCapAtomWith {s : Sig} (Λ : LabelTable) (nv : NameEnv s) : CapAtom s → String
  | .var x => nv.nameAt x
  | .cvar κ => nv.capNameAt κ
  | .sel x A => nv.nameAt x ++ "." ++ ppLabel Λ A
  | .any => "any"
  | .fresh => "fresh"

/-- The atoms of a capture set, in the order the set holds them. -/
def ppCapEntries {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (C : CaptureSet s) : List String :=
  match C with
  | [] => []
  | a :: C' => ppCapAtomWith Λ nv a :: ppCapEntries Λ nv C'
termination_by structural C

/-- A capture set in the paper's notation, with a label table. -/
def ppCapWith {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (C : CaptureSet s) : String :=
  "{" ++ String.intercalate ", " (ppCapEntries Λ nv C) ++ "}"

/-- A capture set in the paper's notation, with no label table. -/
def ppCap {s : Sig} (nv : NameEnv s) (C : CaptureSet s) : String := ppCapWith [] nv C

/-! ## Shapes, types and answers -/

/-- A shape that needs no parentheses as the left side of `^`: everything
but an intersection and an arrow. -/
def Shape.isAtomic {s : Sig} : Shape s → Bool
  | .all _ _ => false
  | .and _ _ => false
  | _ => true

mutual
/-- A type, at the precedence of its position. -/
def ppTyAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (T : Ty s) : String :=
  match T with
  | .capt [] S => ppShapeAt Λ p nv S
  | .capt C S =>
      let sStr :=
        if Shape.isAtomic S then ppShapeAt Λ atomPrec nv S
        else "(" ++ ppShapeAt Λ 0 nv S ++ ")"
      parenIf (p > 60) (sStr ++ " ^ " ++ ppCapWith Λ nv C)
termination_by structural T
/-- A shape, at the precedence of its position. -/
def ppShapeAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (S : Shape s) : String :=
  match S with
  | .top => "⊤"
  | .bot => "⊥"
  | .typ A S T =>
      "{" ++ ppLabel Λ A ++ " : " ++ ppShapeAt Λ 0 nv S ++ " .. " ++ ppShapeAt Λ 0 nv T ++ "}"
  | .fld a T => "{" ++ ppLabel Λ a ++ " : " ++ ppTyAt Λ 0 nv T ++ "}"
  | .cap C lo hi =>
      "{" ++ ppLabel Λ C ++ "^ : " ++ ppCapWith Λ nv lo ++ " .. " ++ ppCapWith Λ nv hi ++ "}"
  | .sel p A => nv.nameAt p.root ++ "." ++ ppLabel Λ A
  | .mu S =>
      let y := freshName (NameEnv.allNames nv)
      "μ(" ++ y ++ ". " ++ ppShapeAt Λ 0 (NameEnv.cons nv y) S ++ ")"
  | .all T U =>
      let κ := freshCapName (NameEnv.allNames nv)
      let nv1 := NameEnv.consC nv κ
      let x := freshName (NameEnv.allNames nv1)
      parenIf (p > 60)
        ("∀[" ++ κ ++ "](" ++ x ++ " : " ++ ppTyAt Λ 0 nv1 T ++ ") "
          ++ ppETyAt Λ 0 (NameEnv.cons nv1 x) U)
  | .and S T =>
      parenIf (p > 65) (ppShapeAt Λ 66 nv S ++ " ∧ " ++ ppShapeAt Λ 65 nv T)
  | .box T => "□ " ++ ppTyAt Λ atomPrec nv T
termination_by structural S
/-- An answer, at the precedence of its position. -/
def ppETyAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (E : ETy s) : String :=
  match E with
  | .ty T => ppTyAt Λ p nv T
  | .ex C T =>
      let κ := freshCapName (NameEnv.allNames nv)
      "∃[" ++ κ ++ " ⊑ " ++ ppCapWith Λ nv C ++ "] " ++ ppTyAt Λ 60 (NameEnv.consC nv κ) T
termination_by structural E
end

/-- A type in the paper's notation, with a label table. -/
def ppTyWith (Λ : LabelTable) (nv : NameEnv s) (T : Ty s) : String := ppTyAt Λ 0 nv T

/-- A type in the paper's notation, with no label table. -/
def ppTy (nv : NameEnv s) (T : Ty s) : String := ppTyWith [] nv T

/-- A shape in the paper's notation, with a label table. -/
def ppShapeWith (Λ : LabelTable) (nv : NameEnv s) (S : Shape s) : String := ppShapeAt Λ 0 nv S

/-- A shape in the paper's notation, with no label table. -/
def ppShape (nv : NameEnv s) (S : Shape s) : String := ppShapeWith [] nv S

/-- An answer in the paper's notation, with a label table. -/
def ppETyWith (Λ : LabelTable) (nv : NameEnv s) (E : ETy s) : String := ppETyAt Λ 0 nv E

/-- An answer in the paper's notation, with no label table. -/
def ppETy (nv : NameEnv s) (E : ETy s) : String := ppETyWith [] nv E

/-! ## Terms of the version's syntax

Application, projection and unboxing take variables, so only the lambda and
the `let` can need parentheses. -/

mutual
/-- A term in the paper's notation, at the precedence of its position. -/
def ppTmAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (t : Tm s) : String :=
  match t with
  | .path (.var x) => nv.nameAt x
  | .val v => ppValueAt Λ p nv v
  | .app x y => nv.nameAt x ++ " " ++ nv.nameAt y
  | .proj x a => nv.nameAt x ++ "." ++ ppLabel Λ a
  | .let t' u =>
      let y := freshName (NameEnv.allNames nv)
      parenIf (p > 0)
        ("let " ++ y ++ " = " ++ ppTmAt Λ 1 nv t' ++ " in "
          ++ ppTmAt Λ 0 (NameEnv.cons nv y) u)
  | .unbox C x => ppCapWith Λ nv C ++ " ⊸ " ++ nv.nameAt x
  | .letex t' u =>
      let κ := freshCapName (NameEnv.allNames nv)
      let x := freshName (κ :: NameEnv.allNames nv)
      parenIf (p > 0)
        ("let ⟨" ++ κ ++ ", " ++ x ++ "⟩ = " ++ ppTmAt Λ 1 nv t' ++ " in "
          ++ ppTmAt Λ 0 ((NameEnv.consC nv κ).cons x) u)
termination_by structural t
/-- A value in the paper's notation.  An object literal has no self shape, so
the binder stands alone. -/
def ppValueAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (v : Value s) : String :=
  match v with
  | .obj d =>
      let y := freshName (NameEnv.allNames nv)
      let κ := freshCapName (y :: NameEnv.allNames nv)
      "ν(" ++ y ++ ". " ++ ppDefsWith Λ ((NameEnv.consC nv κ).cons y) d ++ ")"
  | .lam T t =>
      let κ := freshCapName (NameEnv.allNames nv)
      let nv1 := NameEnv.consC nv κ
      let r := freshCapName (NameEnv.allNames nv1)
      let nv2 := NameEnv.consC nv1 r
      let y := freshName (NameEnv.allNames nv2)
      parenIf (p > 1)
        ("λ(" ++ y ++ " : " ++ ppTyWith Λ nv1 T ++ "). "
          ++ ppTmAt Λ 0 (NameEnv.cons nv2 y) t)
  | .box x => "□ " ++ nv.nameAt x
termination_by structural v
/-- A definition list in the paper's notation. -/
def ppDefsWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (d : Defs s) : String :=
  match d with
  | .typ A S => "{type " ++ ppLabel Λ A ++ " = " ++ ppShapeWith Λ nv S ++ "}"
  | .cap C c => "{" ++ ppLabel Λ C ++ "^ = " ++ ppCapWith Λ nv c ++ "}"
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

/-- A value in the paper's notation, with no label table. -/
def ppValue (nv : NameEnv s) (v : Value s) : String := ppValueWith [] nv v

/-- A definition list in the paper's notation, with no label table. -/
def ppDefs (nv : NameEnv s) (d : Defs s) : String := ppDefsWith [] nv d

/-! ## Annotated terms

The annotated syntax prints in full: the self shape of a literal, the result
answer of a `let` and the ascription.  An unboxing with no set prints with the
empty set. -/

mutual
/-- An annotated term in the paper's notation, at the precedence of its
position. -/
def ppATmAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (t : ATm s) : String :=
  match t with
  | .path (.var x) => nv.nameAt x
  | .lam T t' =>
      let κ := freshCapName (NameEnv.allNames nv)
      let nv1 := NameEnv.consC nv κ
      let r := freshCapName (NameEnv.allNames nv1)
      let nv2 := NameEnv.consC nv1 r
      let y := freshName (NameEnv.allNames nv2)
      parenIf (p > 1)
        ("λ(" ++ y ++ " : " ++ ppTyWith Λ nv1 T ++ "). "
          ++ ppATmAt Λ 0 (NameEnv.cons nv2 y) t')
  | .obj S d =>
      let y := freshName (NameEnv.allNames nv)
      let κ := freshCapName (y :: NameEnv.allNames nv)
      "ν(" ++ y ++ " : " ++ ppShapeAt Λ 0 (NameEnv.cons nv y) S ++ ". "
        ++ ppADefsWith Λ ((NameEnv.consC nv κ).cons y) d ++ ")"
  | .app x y => nv.nameAt x ++ " " ++ nv.nameAt y
  | .proj x a => nv.nameAt x ++ "." ++ ppLabel Λ a
  | .let ann t' u =>
      let y := freshName (NameEnv.allNames nv)
      let ann? :=
        match ann with
        | none => ""
        | some E => " : " ++ ppETyWith Λ nv E
      parenIf (p > 0)
        ("let " ++ y ++ ann? ++ " = " ++ ppATmAt Λ 1 nv t' ++ " in "
          ++ ppATmAt Λ 0 (NameEnv.cons nv y) u)
  | .letex t' u =>
      let κ := freshCapName (NameEnv.allNames nv)
      let x := freshName (κ :: NameEnv.allNames nv)
      parenIf (p > 0)
        ("let ⟨" ++ κ ++ ", " ++ x ++ "⟩ = " ++ ppATmAt Λ 1 nv t' ++ " in "
          ++ ppATmAt Λ 0 ((NameEnv.consC nv κ).cons x) u)
  | .box x => "□ " ++ nv.nameAt x
  | .unbox C x => ppCapWith Λ nv (C.getD []) ++ " ⊸ " ++ nv.nameAt x
  | .asc t' T => "(" ++ ppATmAt Λ 1 nv t' ++ " : " ++ ppTyWith Λ nv T ++ ")"
termination_by structural t
/-- An annotated definition list in the paper's notation. -/
def ppADefsWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (d : ADefs s) : String :=
  match d with
  | .typ A S => "{type " ++ ppLabel Λ A ++ " = " ++ ppShapeAt Λ 0 nv S ++ "}"
  | .cap C c => "{" ++ ppLabel Λ C ++ "^ = " ++ ppCapWith Λ nv c ++ "}"
  | .trm a t => "{" ++ ppLabel Λ a ++ " = " ++ ppATmAt Λ 0 nv t ++ "}"
  | .and d' e => ppADefsWith Λ nv d' ++ " ∧ " ++ ppADefsWith Λ nv e
termination_by structural d
end

/-- An annotated term in the paper's notation, with a label table. -/
def ppATmWith (Λ : LabelTable) (nv : NameEnv s) (t : ATm s) : String := ppATmAt Λ 0 nv t

/-- An annotated term in the paper's notation, with no label table. -/
def ppATm (nv : NameEnv s) (t : ATm s) : String := ppATmWith [] nv t

/-- An annotated definition list in the paper's notation, with a label
table. -/
def ppADefs (nv : NameEnv s) (d : ADefs s) : String := ppADefsWith [] nv d

/-! ## Surface phrases

The surface syntax carries its own names and labels, so these need neither a
table nor an environment. -/

/-- A surface capture atom. -/
def ppSAtom : SAtom → String
  | .name x => x
  | .sel x C => x ++ "." ++ C
  | .any => "any"
  | .fresh => "fresh"

/-- The atoms of a surface capture set, in order. -/
def ppSCapEntries (c : SCap) : List String :=
  match c with
  | [] => []
  | a :: c' => ppSAtom a :: ppSCapEntries c'
termination_by structural c

/-- A surface capture set in the paper's notation. -/
def ppSCap (c : SCap) : String := "{" ++ String.intercalate ", " (ppSCapEntries c) ++ "}"

/-- The surface twin of `Shape.isAtomic`. -/
def sShapeIsAtomic : SShape → Bool
  | .all _ _ _ _ => false
  | .and _ _ => false
  | _ => true

mutual
/-- A surface shape, at the precedence of its position. -/
def ppSShapeAt (p : Nat) (S : SShape) : String :=
  match S with
  | .top => "⊤"
  | .bot => "⊥"
  | .typ A S T => "{" ++ A ++ " : " ++ ppSShapeAt 0 S ++ " .. " ++ ppSShapeAt 0 T ++ "}"
  | .cap C lo hi => "{" ++ C ++ "^ : " ++ ppSCap lo ++ " .. " ++ ppSCap hi ++ "}"
  | .fld a T => "{" ++ a ++ " : " ++ ppSTyAt 0 T ++ "}"
  | .sel x A => x ++ "." ++ A
  | .mu x S => "μ(" ++ x ++ ". " ++ ppSShapeAt 0 S ++ ")"
  | .all κ x T U =>
      let arrow? :=
        match κ with
        | none => "∀(" ++ x ++ " : " ++ ppSTyAt 0 T ++ ") "
        | some c => "∀[" ++ c ++ "](" ++ x ++ " : " ++ ppSTyAt 0 T ++ ") "
      parenIf (p > 60) (arrow? ++ ppSAnsAt 0 U)
  | .and S T => parenIf (p > 65) (ppSShapeAt 66 S ++ " ∧ " ++ ppSShapeAt 65 T)
  | .box T => "□ " ++ ppSTyAt atomPrec T
termination_by structural S
/-- A surface type, at the precedence of its position. -/
def ppSTyAt (p : Nat) (T : SType) : String :=
  match T with
  | .capt S [] => ppSShapeAt p S
  | .capt S C =>
      let sStr :=
        if sShapeIsAtomic S then ppSShapeAt atomPrec S else "(" ++ ppSShapeAt 0 S ++ ")"
      parenIf (p > 60) (sStr ++ " ^ " ++ ppSCap C)
termination_by structural T
/-- A surface answer, at the precedence of its position. -/
def ppSAnsAt (p : Nat) (U : SAns) : String :=
  match U with
  | .ty T => ppSTyAt p T
  | .ex κ C T => "∃[" ++ κ ++ " ⊑ " ++ ppSCap C ++ "] " ++ ppSTyAt 60 T
termination_by structural U
end

/-- A surface shape in the paper's notation. -/
def ppSShape (S : SShape) : String := ppSShapeAt 0 S

/-- A surface type in the paper's notation. -/
def ppSTy (T : SType) : String := ppSTyAt 0 T

/-- A surface answer in the paper's notation. -/
def ppSAns (U : SAns) : String := ppSAnsAt 0 U

mutual
/-- A surface term in the paper's notation, at the precedence of its
position. -/
def ppSTmAt (p : Nat) (e : STm) : String :=
  match e with
  | .var x => x
  | .lam κ x T t =>
      let binder? :=
        match κ with
        | none => "λ"
        | some c => "λ[" ++ c ++ "]"
      let param? :=
        match T with
        | none => x ++ ". "
        | some T => "(" ++ x ++ " : " ++ ppSTyAt 0 T ++ "). "
      parenIf (p > 1) (binder? ++ param? ++ ppSTmAt 0 t)
  | .obj x (some S) d => "ν(" ++ x ++ " : " ++ ppSShapeAt 0 S ++ ". " ++ ppSDefsAt d ++ ")"
  | .obj x none d => "ν(" ++ x ++ ". " ++ ppSDefsAt d ++ ")"
  | .app t u => parenIf (p > 70) (ppSTmAt 70 t ++ " " ++ ppSTmAt 71 u)
  | .proj t a => ppSTmAt 80 t ++ "." ++ a
  | .«let» x ann t u =>
      let ann? :=
        match ann with
        | none => ""
        | some U => " : " ++ ppSAnsAt 0 U
      parenIf (p > 0)
        ("let " ++ x ++ ann? ++ " = " ++ ppSTmAt 1 t ++ " in " ++ ppSTmAt 0 u)
  | .letex κ x t u =>
      parenIf (p > 0)
        ("let ⟨" ++ κ ++ ", " ++ x ++ "⟩ = " ++ ppSTmAt 1 t ++ " in " ++ ppSTmAt 0 u)
  | .box t => "□ " ++ ppSTmAt atomPrec t
  | .unbox C t => ppSCap C ++ " ⊸ " ++ ppSTmAt atomPrec t
  | .asc t T => "(" ++ ppSTmAt 1 t ++ " : " ++ ppSTyAt 0 T ++ ")"
termination_by structural e
/-- A surface definition list in the paper's notation. -/
def ppSDefsAt (d : SDefs) : String :=
  match d with
  | .typ A S => "{type " ++ A ++ " = " ++ ppSShapeAt 0 S ++ "}"
  | .cap C c => "{" ++ C ++ "^ = " ++ ppSCap c ++ "}"
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

The store prints outermost binder first, then the continuation as its frames
with a hole, then the term. -/

/-- The store as one entry per binder, outermost first.  A capture slot shows
its name alone. -/
def storeEntries (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (σ : Store s) : List String :=
  match nv, σ with
  | .nil, .nil => []
  | .cons nv' y, .cons σ' v =>
      storeEntries Λ nv' σ' ++ [y ++ " = " ++ ppValueWith Λ nv' v]
  | .consC nv' y, .consC σ' => storeEntries Λ nv' σ' ++ [y]
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
      let y := freshName (NameEnv.allNames nv)
      contFrames Λ nv K' ++ ["let " ++ y ++ " = □ in " ++ ppTmWith Λ (NameEnv.cons nv y) u]
  | .consE K' u =>
      let κ := freshCapName (NameEnv.allNames nv)
      let x := freshName (κ :: NameEnv.allNames nv)
      contFrames Λ nv K' ++
        ["let ⟨" ++ κ ++ ", " ++ x ++ "⟩ = □ in "
          ++ ppTmWith Λ ((NameEnv.consC nv κ).cons x) u]
termination_by structural K

/-- The continuation in the paper's notation. -/
def ppContWith (Λ : LabelTable) (nv : NameEnv s) (K : Cont s) : String :=
  match contFrames Λ nv K with
  | [] => "·"
  | fs => String.intercalate ", " fs

/-- A state of the source machine, store then continuation then term. -/
def ppStateWith (Λ : LabelTable) {s : Sig} (nv : NameEnv s) (st : State s) : String :=
  "⟨" ++ ppStoreWith Λ nv st.σ ++ " | " ++ ppContWith Λ nv st.K ++ " | "
    ++ ppTmWith Λ nv st.t ++ "⟩"

/-- The answer of `compileAndRun`, in full. -/
def ppRun (Λ : LabelTable) : Verdict ((s : Sig) × State s) → String
  | .ok ⟨s, st⟩ => ppStateWith Λ (defaultNames s) st
  | .rejected r => "rejected: " ++ Reason.name r
  | .unknown => "did not compile"

/-- The term of the answer of `compileAndRun`. -/
def ppRunTm (Λ : LabelTable) : Verdict ((s : Sig) × State s) → String
  | .ok ⟨s, st⟩ => ppTmWith Λ (defaultNames s) st.t
  | .rejected r => "rejected: " ++ Reason.name r
  | .unknown => "did not compile"

/-- The answer of `compileAndRun` over a platform named by `pre`, in full. -/
def ppRunOver (Λ : LabelTable) (pre : List String) :
    Verdict ((s : Sig) × State s) → String
  | .ok ⟨s, st⟩ => ppStateWith Λ (namesOver pre s) st
  | .rejected r => "rejected: " ++ Reason.name r
  | .unknown => "did not compile"

/-- The term of the answer of `compileAndRun` over a platform named by
`pre`. -/
def ppRunTmOver (Λ : LabelTable) (pre : List String) :
    Verdict ((s : Sig) × State s) → String
  | .ok ⟨s, st⟩ => ppTmWith Λ (namesOver pre s) st.t
  | .rejected r => "rejected: " ++ Reason.name r
  | .unknown => "did not compile"

/-! ## Checks

The small terms are built by hand, one construct at a time.  The larger ones
are surface programs from `Typer.lean` and `Resolve.lean`. -/

section Checks

/-- A capture set with a capture variable, `any` and `fresh`. -/
example :
    ppCapWith Λc (NameEnv.consC .nil "k0")
      [CapAtom.cvar .here, CapAtom.any, CapAtom.fresh]
      = "{k0, any, fresh}" := rfl

/-- A box over a capturing shape, as the operand of `∧`. -/
example :
    ppShape (s := [Kind.cap]) (.consC .nil "k0")
      (.and (.box (Ty.capt [CapAtom.cvar .here] .top)) .bot)
      = "□ (⊤ ^ {k0}) ∧ ⊥" := rfl

/-- An arrow shape.  The arrow's own capture binder prints named. -/
example :
    ppShape (.nil : NameEnv ([] : Sig)) (Shape.all unitTy (.ty unitTy))
      = "∀[k](x : ⊤) ⊤" := rfl

/-- A lambda whose body reads neither the arrow's binder nor the body root. -/
example :
    ppATmWith Λc (.nil : NameEnv ([] : Sig)) (ATm.lam unitTy (.path (.var .here)))
      = "λ(x : ⊤). x" := rfl

/-- An object literal whose one field reads the self.  Shape and definitions
print the same name for it. -/
example :
    ppATmWith Λc (.nil : NameEnv ([] : Sig))
      (ATm.obj (Shape.fld la unitTy) (ADefs.trm la (.path (.var .here))))
      = "ν(x : {a : ⊤}. {a = x})" := rfl

/-- A `let` with an existential answer.  The witness binder scopes over the
type alone. -/
example :
    ppATmWith Λc (.nil : NameEnv ([] : Sig))
      (ATm.lam unitTy
        (.let (some (.ex [CapAtom.var .here] (.capt [CapAtom.cvar .here] .top)))
          (.path (.var .here)) (.path (.var .here))))
      = "λ(x : ⊤). let y : ∃[i ⊑ {x}] ⊤ ^ {i} = x in y" := rfl

/-- A written unpacking. -/
example :
    ppATmWith Λc (.nil : NameEnv ([] : Sig))
      (ATm.lam unitTy
        (.letex (.path (.var .here)) (.unbox (some [CapAtom.cvar (.there .here)]) .here)))
      = "λ(x : ⊤). let ⟨i, y⟩ = x in {i} ⊸ y" := rfl

/-- `Z1callerAnn`, the resolved caller of `freshCell`.  Resolution keeps no
`let`-bound names, so these are invented. -/
example :
    ppATmWith Λc z1Names Z1callerAnn
      = "let x = fc un in let y = x in λ(z : ⊤). z" := rfl

-- The surface printer on C7 reads every name back as written.  The string is
-- long, hence the local `maxRecDepth`.
set_option maxRecDepth 4000 in
example :
    ppSTm C7src
      = "λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}). "
        ++ "let o = ν(z : {e1 : □ ((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □ ((∀(u : ⊤) ⊤) ^ {k2})}. "
        ++ "{e1 = f1} ∧ {e2 = f2}) in let e = o.e1 in (e : (∀(u : ⊤) ⊤) ^ {k1})" := rfl

/-- The surface printer on W2's `process`.  The parameter's `any` prints as
the atom. -/
example :
    ppSTm W2defSrc
      = "λ(x : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). u" := rfl

/-- `deepSrc`, with `any` deeper in a domain than its outer set. -/
example : ppSTm deepSrc = "λ(x : {read : ⊤ ^ {any}}). x" := rfl

/-- A lambda with an empty domain. -/
example : ppSTm (cc% λx. x) = "λx. x" := rfl

/-- The same with the arrow's own binder named. -/
example : ppSTm (cc% λ[c]x. let y : ⊤ ^ {c} = x in y) = "λ[c]x. let y : ⊤ ^ {c} = x in y" := rfl

/-- A literal without a self shape, with a written field type. -/
example : ppSTm (cc% ν(x. {a : ⊤ ^ {any} = x})) = "ν(x. {a : ⊤ ^ {any} = x})" := rfl

/-- An ascription over a lambda with an empty domain. -/
example : ppSTm (cc% (λx. x : ⊤)) = "(λx. x : ⊤)" := rfl

/-- A state over a store with both kinds of binder. -/
example :
    ppStateWith Λc ((NameEnv.consC .nil "k0").cons "x0")
      (⟨Store.cons (Store.consC .nil) (Value.lam unitTy (.path (.var .here))), Cont.nil,
          Tm.path (.var .here)⟩ : State ((([] : Sig),c),x))
      = "⟨k0, x0 = λ(x : ⊤). x | · | x0⟩" := rfl

/-- A continuation with a `let` frame and an unpacking frame. -/
example :
    ppContWith Λc (.nil : NameEnv ([] : Sig))
      (Cont.consE (Cont.cons Cont.nil (.path (.var .here))) (Tm.unbox [] .here) :
        Cont ([] : Sig))
      = "let x = □ in x, let ⟨k, x⟩ = □ in {} ⊸ x" := rfl

/-- A run of W2's `process`.  The typer reads its `any` as the arrow's own
binder. -/
example :
    ppRun Λc (compileAndRun {} 10 Λc πc W2defSrc)
      = "⟨k0, k1 | · | λ(x : μ(x. {read : (∀[j](y : ⊤) ⊤) ^ {x}}) ^ {k}). "
        ++ "λ(y : ⊤). y⟩" := rfl

/-- The term of the same run. -/
example :
    ppRunTm Λc (compileAndRun {} 10 Λc πc W2defSrc)
      = "λ(x : μ(x. {read : (∀[j](y : ⊤) ⊤) ^ {x}}) ^ {k}). λ(y : ⊤). y" := rfl

/-- A rejected program prints its reason. -/
example : ppRun Λc (compileAndRun {} 5 Λc πc deepSrc) = "rejected: anyNotOk" := rfl

end Checks

end CapturesCCFrontend
