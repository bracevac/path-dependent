import Coercions.Captures.Frontend.Resolve
import Coercions.Captures.DotMNF.Machine

/-!
# The pretty printer

An unparser from the four syntaxes of this library back into the paper's
notation, so that an `#eval` of a compilation or a run is readable.  It
follows `Frontend/Pretty.lean` and adds capture sets, the capture member
`{C^ : c₁..c₂}`, the box former `□`, the unboxing term `C ⊸ x` and the
ascription `(t : T)`.  The syntax inductives have no `Repr` instance, so this
module is how a `Captures.DotMNF.Ty` or `Tm` is shown as text.

The module has no theorem.  The checks at the end decide the printer's output
on terms built elsewhere in this front end.

## Shapes and types

The version splits a type into a shape, the plain type former, and a type, a
shape with a capture set written `S ^ C`.  So there are two printers,
`ppShapeAt` and `ppTyAt`.  A type with the empty set prints as its shape.  A
type with a written set prints `S ^ C` at precedence 60, as the grammar reads
it (`^` at 60, looser than `∧` at 65).  The shape is read one level tighter
on the left, so a `∀` or a further `^` there gets parentheses.

`□ T` and `C ⊸ x` are closed forms, so they never need parentheses.  Their
operand is read at the level `atomPrec`, which parenthesizes it unless it is
atomic.  This matters for the shape-level box `Shape.box : Ty s → Shape s`, whose operand can be
`S ^ C`.  The term-level `Value.box` and `Tm.unbox` take a variable, so they
print a name.

## Two kinds of binder

A name environment (`Resolve.lean`) holds a name per term binder and per
capture binder.  `NameEnv.nameAt` reads a term binder's name and
`NameEnv.capNameAt` a capture binder's.  They are separate functions because
`BVar` is indexed by kind.  `defaultNames` invents `x0`, `x1`, … for term
binders and `k0`, `k1`, … for capture binders, each kind counted on its own.
`ppRun` uses these names.  A caller can pass the names of a concrete platform
(`πc` of `Resolve.lean`) instead, and `ppRunOver` gives a list of platform
names to the outermost binders of the state a run reaches.

## No round trip

The output is for a reader, not a parser.  As in the vanilla printer, an
object literal of `Tm` has no self type, a let-inserted binder takes an
ordinary short name, and a label outside the table prints as its sort and
number.  The annotated syntax of `Ann.lean` carries the self type with its
written set, and `ppATmWith` prints it in full.

Every function is structural, so the printer reduces in the kernel and the
checks are `rfl`.
-/

namespace CapturesFrontend

open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (Path CapAtom CaptureSet Shape Ty Tm Value Defs Store Cont State Platform)

/-! ## Parentheses -/

/-- The string, in parentheses when the flag holds. -/
def parenIf (b : Bool) (str : String) : String :=
  if b then "(" ++ str ++ ")" else str

/-- The level of an operand that must be closed: tighter than every real
precedence, so a box or an unboxing always parenthesizes a `∧` or a `^` it
wraps. -/
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

/-! ## Names for binders -/

/-- The short names a binder is given, in the order they are tried. -/
def binderNames : List String := ["x", "y", "z", "w", "u", "v", "p", "q"]

/-- The first short name the environment does not hold. -/
def freshName (used : List String) : String :=
  match binderNames.find? (fun c => !used.contains c) with
  | some c => c
  | none => "x" ++ toString used.length

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

/-- Invented names for a signature, outermost `x0` or `k0`, each kind counted
on its own. -/
def defaultNames (s : Sig) : NameEnv s :=
  match s with
  | [] => .nil
  | .var :: s' => .cons (defaultNames s') ("x" ++ toString s'.length)
  | .cap :: s' => .consC (defaultNames s') ("k" ++ toString s'.length)
termination_by structural s

/-! ## Capture sets -/

/-- A capture atom, through a name environment of either kind. -/
def ppCapAtomWith {s : Sig} (Λ : LabelTable) (nv : NameEnv s) : CapAtom s → String
  | .var x => NameEnv.nameAt nv x
  | .cvar κ => NameEnv.capNameAt nv κ
  | .sel x A => NameEnv.nameAt nv x ++ "." ++ ppLabel Λ A
  | .any => "any"

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

/-! ## Shapes and types

`ppShapeAt` prints a shape, `ppTyAt` a shape with its capture set. -/

mutual
/-- A type, at the precedence of its position. -/
def ppTyAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (T : Ty s) : String :=
  match T with
  | .capt [] S => ppShapeAt Λ p nv S
  | .capt C S => parenIf (p > 60) (ppShapeAt Λ 61 nv S ++ " ^ " ++ ppCapWith Λ nv C)
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
  | .sel p A => NameEnv.nameAt nv p.root ++ "." ++ ppLabel Λ A
  | .mu S =>
      let y := freshName (NameEnv.names nv)
      "μ(" ++ y ++ ". " ++ ppShapeAt Λ 0 (NameEnv.cons nv y) S ++ ")"
  | .all T U =>
      let y := freshName (NameEnv.names nv)
      parenIf (p > 60)
        ("∀(" ++ y ++ " : " ++ ppTyAt Λ 0 nv T ++ ") " ++ ppTyAt Λ 0 (NameEnv.cons nv y) U)
  | .and S T =>
      parenIf (p > 65) (ppShapeAt Λ 66 nv S ++ " ∧ " ++ ppShapeAt Λ 65 nv T)
  | .box T => "□ " ++ ppTyAt Λ atomPrec nv T
termination_by structural S
end

/-- A type in the paper's notation, with a label table. -/
def ppTyWith (Λ : LabelTable) (nv : NameEnv s) (T : Ty s) : String := ppTyAt Λ 0 nv T

/-- A type in the paper's notation, with no label table. -/
def ppTy (nv : NameEnv s) (T : Ty s) : String := ppTyWith [] nv T

/-- A shape in the paper's notation, with a label table. -/
def ppShapeWith (Λ : LabelTable) (nv : NameEnv s) (S : Shape s) : String := ppShapeAt Λ 0 nv S

/-- A shape in the paper's notation, with no label table. -/
def ppShape (nv : NameEnv s) (S : Shape s) : String := ppShapeWith [] nv S

/-! ## Terms of the version's syntax

Application, projection and unboxing take variables, so only the lambda and
the `let` can need parentheses. -/

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
  | .unbox C x => ppCapWith Λ nv C ++ " ⊸ " ++ NameEnv.nameAt nv x
termination_by structural t
/-- A value in the paper's notation.  An object literal has no self type, so
the binder stands alone. -/
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
  | .box x => "□ " ++ NameEnv.nameAt nv x
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

The syntax of `Ann.lean` is what a compilation returns.  It prints in full:
the self shape of a literal, its capture set when written, the result type of
a `let` and the ascription. -/

mutual
/-- An annotated term in the paper's notation, at the precedence of its
position. -/
def ppATmAt (Λ : LabelTable) {s : Sig} (p : Nat) (nv : NameEnv s) (t : ATm s) : String :=
  match t with
  | .path (.var x) => NameEnv.nameAt nv x
  | .lam T t' =>
      let y := freshName (NameEnv.names nv)
      parenIf (p > 1)
        ("λ(" ++ y ++ " : " ++ ppTyWith Λ nv T ++ "). "
          ++ ppATmAt Λ 0 (NameEnv.cons nv y) t')
  | .obj S U d =>
      let y := freshName (NameEnv.names nv)
      let nv' := NameEnv.cons nv y
      let selfPart :=
        match U with
        | none => ppShapeAt Λ 0 nv' S
        | some C => ppShapeAt Λ 61 nv' S ++ " ^ " ++ ppCapWith Λ nv C
      "ν(" ++ y ++ " : " ++ selfPart ++ ". " ++ ppADefsWith Λ nv' d ++ ")"
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
  | .box x => "□ " ++ NameEnv.nameAt nv x
  | .unbox C x => ppCapWith Λ nv C ++ " ⊸ " ++ NameEnv.nameAt nv x
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
def ppSCapAtom : SCapAtom → String
  | .name x => x
  | .sel x C => x ++ "." ++ C
  | .any => "any"

/-- The atoms of a surface capture set, in order. -/
def ppSCapEntries (c : SCap) : List String :=
  match c with
  | [] => []
  | a :: c' => ppSCapAtom a :: ppSCapEntries c'
termination_by structural c

/-- A surface capture set in the paper's notation. -/
def ppSCap (c : SCap) : String := "{" ++ String.intercalate ", " (ppSCapEntries c) ++ "}"

/-- A surface type in the paper's notation, at the precedence of its
position. -/
def ppSTyAt (p : Nat) (T : SType) : String :=
  match T with
  | .top => "⊤"
  | .bot => "⊥"
  | .typ A S U => "{" ++ A ++ " : " ++ ppSTyAt 0 S ++ " .. " ++ ppSTyAt 0 U ++ "}"
  | .fld a U => "{" ++ a ++ " : " ++ ppSTyAt 0 U ++ "}"
  | .cap C lo hi => "{" ++ C ++ "^ : " ++ ppSCap lo ++ " .. " ++ ppSCap hi ++ "}"
  | .sel x A => x ++ "." ++ A
  | .mu x U => "μ(" ++ x ++ ". " ++ ppSTyAt 0 U ++ ")"
  | .all x S U =>
      parenIf (p > 60) ("∀(" ++ x ++ " : " ++ ppSTyAt 0 S ++ ") " ++ ppSTyAt 0 U)
  | .and S U => parenIf (p > 65) (ppSTyAt 66 S ++ " ∧ " ++ ppSTyAt 65 U)
  | .box T => "□ " ++ ppSTyAt atomPrec T
  | .capt S C => parenIf (p > 60) (ppSTyAt 61 S ++ " ^ " ++ ppSCap C)
termination_by structural T

/-- A surface type in the paper's notation. -/
def ppSTy (T : SType) : String := ppSTyAt 0 T

mutual
/-- A surface term in the paper's notation, at the precedence of its
position. -/
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
  | .box t => "□ " ++ ppSTmAt atomPrec t
  | .unbox C t => ppSCap C ++ " ⊸ " ++ ppSTmAt atomPrec t
  | .asc t T => "(" ++ ppSTmAt 1 t ++ " : " ++ ppSTyAt 0 T ++ ")"
termination_by structural e
/-- A surface definition list in the paper's notation. -/
def ppSDefsAt (d : SDefs) : String :=
  match d with
  | .typ A T => "{type " ++ A ++ " = " ++ ppSTyAt 0 T ++ "}"
  | .trm a none t => "{" ++ a ++ " = " ++ ppSTmAt 0 t ++ "}"
  | .trm a (some T) t => "{" ++ a ++ " : " ++ ppSTyAt 0 T ++ " = " ++ ppSTmAt 0 t ++ "}"
  | .and d' e => ppSDefsAt d' ++ " ∧ " ++ ppSDefsAt e
  | .cap C c => "{" ++ C ++ "^ = " ++ ppSCap c ++ "}"
termination_by structural d
end

/-- A surface term in the paper's notation. -/
def ppSTm (e : STm) : String := ppSTmAt 0 e

/-- A surface definition list in the paper's notation. -/
def ppSDefs (d : SDefs) : String := ppSDefsAt d

/-! ## States of the source machine

The store is printed outermost binder first, then the continuation as frames
with a hole, then the term.  A capture slot has no value and prints its name
alone. -/

/-- The store as one entry per binder, outermost first. -/
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

/-- The answer of `compileAndRun`, with invented names. -/
def ppRun (Λ : LabelTable) : Option ((s : Sig) × State s) → String
  | none => "did not compile"
  | some ⟨s, st⟩ => ppStateWith Λ (defaultNames s) st

/-- The term of the answer of `compileAndRun`. -/
def ppRunTm (Λ : LabelTable) : Option ((s : Sig) × State s) → String
  | none => "did not compile"
  | some ⟨s, ⟨_, _, t⟩⟩ => ppTmWith Λ (defaultNames s) t

/-! ## A run over a named platform

A run starts at a platform whose capabilities are named in the program text,
`k1` and `k2` for `πc`.  The state it reaches has a longer signature, so the
printer takes the platform's names as a list, outermost first.  Binders past
the list get the names `defaultNames` gives. -/

/-- Names for a signature whose outermost binders are named by `pre` and whose
other binders take invented names. -/
def namesOver (pre : List String) (s : Sig) : NameEnv s :=
  match s with
  | [] => .nil
  | .var :: s' => .cons (namesOver pre s') (pre.getD s'.length ("x" ++ toString s'.length))
  | .cap :: s' => .consC (namesOver pre s') (pre.getD s'.length ("k" ++ toString s'.length))
termination_by structural s

/-- The answer of `compileAndRun` over a platform named by `pre`. -/
def ppRunOver (Λ : LabelTable) (pre : List String) : Option ((s : Sig) × State s) → String
  | none => "did not compile"
  | some ⟨s, st⟩ => ppStateWith Λ (namesOver pre s) st

/-- The term of the answer of `compileAndRun` over a platform named by
`pre`. -/
def ppRunTmOver (Λ : LabelTable) (pre : List String) : Option ((s : Sig) × State s) → String
  | none => "did not compile"
  | some ⟨s, ⟨_, _, t⟩⟩ => ppTmWith Λ (namesOver pre s) t

/-! ## Checks

The terms are the ones `Resolve.lean` and `Notation.lean` build. -/

section Checks

/-- E1, with every capture set empty, prints as the vanilla printer would. -/
example :
    ppATmWith Λc .nil E1ann
      = "λ(x : {A : ⊤ .. ⊥}). let y : {B : {a : ⊤} .. {a : ⊤}} = x in y" := rfl

/-- E7, an object literal with two mutually selecting type members and no
written capture set: the self binder prints alone. -/
example :
    ppATmWith Λc .nil E7ann
      = "ν(x : {A : x.B .. x.B} ∧ {B : x.A .. x.A}. "
        ++ "{type A = x.B} ∧ {type B = x.A})" := rfl

/-- Erasure drops the annotations, and an object literal of `Tm` has no self
type. -/
example :
    ppTmWith Λc .nil (ATm.erase E7ann)
      = "ν(x. {type A = x.B} ∧ {type B = x.A})" := rfl

/-- E10, where let insertion changes the surface program: the inserted binder
takes a name of the printer's own. -/
example :
    ppATmWith Λc .nil E10ann
      = "λ(x : ⊤). λ(y : ⊤). let z = y x in x z" := rfl

-- C7 with its boxes and unboxing written by hand.  The string is long, so
-- `maxRecDepth` is raised.
set_option maxRecDepth 4000 in
example :
    ppSTm C7src
      = "λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}). "
        ++ "let o = ν(z : {e1 : □ ((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □ ((∀(u : ⊤) ⊤) ^ {k2})}. "
        ++ "{e1 = □ f1} ∧ {e2 = □ f2}) in let e = o.e1 in {k1} ⊸ e" := rfl

-- S3, a type member at a boxed capturing type.
set_option maxRecDepth 4000 in
example :
    ppSTm S3src
      = "λ(f : (∀(u : ⊤) ⊤) ^ {k1}). "
        ++ "let o = ν(z : {A : (∀(u : ⊤) ⊤) ^ {f} .. (∀(u : ⊤) ⊤) ^ {f}} ∧ {elem : z.A}. "
        ++ "{type A = (∀(u : ⊤) ⊤) ^ {f}} ∧ {elem = □ f}) in let e = o.elem in {f} ⊸ e" := rfl

/-- A lambda with an empty domain. -/
example : ppSTm (cap% λx. x) = "λx. x" := rfl

/-- A literal without a self shape, with a written field type. -/
example : ppSTm (cap% ν(x. {a : ⊤ ^ {any} = x})) = "ν(x. {a : ⊤ ^ {any} = x})" := rfl

/-- An ascription over a lambda with an empty domain. -/
example : ppSTm (cap% (λx. x : ⊤)) = "(λx. x : ⊤)" := rfl

/-- An object literal with a written self capture set, resolved through the
platform `πc`.  The self shape and its set both print, and `k1` prints under
the platform's name. -/
example :
    ((resolveTop Λc πc (cap% λ(f : ⊤ ^ {k1}). ν(z : {a : ⊤} ^ {f}. {a = f}))).map
        (ppATmWith Λc πc.names))
      = some "λ(x : ⊤ ^ {k1}). ν(y : {a : ⊤} ^ {x}. {a = x})" := rfl

/-- A box over a capturing shape, as the operand of `∧`.  The box's operand is
parenthesized and the box itself is not. -/
example :
    ppShape (s := [Kind.cap]) (.consC .nil "k0")
      (.and (.box (Ty.capt [.cvar .here] .top)) .bot)
      = "□ (⊤ ^ {k0}) ∧ ⊥" := rfl

/-- A store with both kinds of binder: a term slot prints its value, a capture
slot its name. -/
example :
    ppRun Λc
        (some ⟨([] : Sig),x,c,
          ⟨.consC (.cons .nil (.lam (Ty.capt [] .top) (.path (.var .here)))), .nil,
            .path (.var (.there .here))⟩⟩)
      = "⟨x0 = λ(x : ⊤). x, k1 | · | x0⟩" := rfl

/-- The state before a step: an empty store, one frame, and a value. -/
example :
    ppRun Λc
        (some ⟨[], ⟨.nil, .cons .nil (.path (.var .here)),
          .val (.lam (Ty.capt [] .top) (.path (.var .here)))⟩⟩)
      = "⟨· | let x = □ in x | λ(x : ⊤). x⟩" := rfl

/-- Nothing to print. -/
example : ppRun Λc (none : Option ((s : Sig) × State s)) = "did not compile" := rfl

/-- A state over the platform `k1, k2` with one allocated slot.  The capture
slots take the platform's names and the term slot an invented one. -/
example :
    ppRunOver Λc ["k1", "k2"]
        (some ⟨([] : Sig),c,c,x,
          ⟨.cons (.consC (.consC .nil)) (.lam (Ty.capt [] .top) (.path (.var .here))), .nil,
            .path (.var .here)⟩⟩)
      = "⟨k1, k2, x2 = λ(x : ⊤). x | · | x2⟩" := rfl

end Checks

end CapturesFrontend
