import Coercions.Classifiers.Frontend.Resolve
import Coercions.Classifiers.Frontend.Pipeline

/-!
# The pretty printer

An unparser from the four syntaxes of this library back into the paper's
notation, so that an `#eval` of a compilation or of a run is readable.  The
syntax of the version has no `Repr` instance, so this module is the only way
to look at a `Classifiers.DotMNF.Ty` or `Tm` as text.

It prints the capture binder an arrow opens before its parameter, the class
root an object literal opens before its self, the existential answer
`∃[c ⊑ C] T`, the unpacking `let ⟨c, x⟩ = t in u`, the atom `fresh`, projected
atoms `a.only[K]` and `a.except[K]`, kind-bounded capture members `{C^ : K}`,
and kinds read off a classifier table.

## Shapes, types and answers

A *shape* is the type former.  A *type* is a shape with a capture set, `S ^ C`
(`lean/Coercions/Classifiers/DotMNF/Syntax.lean`).  An *answer* is a type, or
`∃[c ⊑ C] T`.  So the mutual block has `ppShapeAt`, `ppTyAt` and `ppETyAt`.
The grammar reads `S ^ C` with `S` closed on the left, so a capturing arrow or
intersection under `^` needs parentheses.  `ppTyAt` tests `Shape.isAtomic`
for this, because a precedence bound alone does not force the parentheses
around an intersection there.  Elsewhere `^` closes at 60 and `∧` at 65.

## Classifier kinds

A kind is a list of holed subtrees, each a root classifier minus excluded
classifiers (`lean/Coercions/Classifiers/Cls/Kind.lean`).  The elaborated
syntax holds a classifier's tree position and not its surface name.  So
`clsNameOf?` reads a classifier table backwards, and `ppClsName` falls back to
the raw position, a chain of child indices off `⊤`, for an unnamed classifier.
A subtree with no exclusion is `only[name]` and one rooted at `⊤` is
`except[names]`.  Any other subtree is a subtraction, `name \ {names}`, which
the grammar does not parse.  A kind of several subtrees is their union.  Every
printer takes the classifier table beside the label table.

## Invented binder names

The calculus opens binders that no surface phrase writes, and elaborated
syntax does not record names.  An arrow opens its own capture binder before
its domain and parameter.  A closure's body opens a *body root* too.  An
object literal's definitions sit under a *class root* and the self.  A `let`
with an existential answer and a `letex` each open a capture binder for the
witness.  The printer invents names for them from two disjoint pools,
`capBinderNames` and `binderNames`.  Every invented name avoids all names in
scope, so a deeper binder never shadows an outer one.  An arrow's capture
binder always prints named, `∀[κ](x : T) U`.

## No round trip

The output is for a reader and not a parser input.  A let-inserted binder gets
an invented name.  A label outside the table prints as its sort and number.  A
classifier outside the table prints as its raw tree position.  A kind that is
neither a bare `only` nor a bare `except` prints as a subtraction.  The
annotated syntax of `Ann.lean` carries the self shape, so `ppATmWith` prints an
object literal's self shape in full.  The syntax of the version has no self
shape for a literal, so the binder stands alone there.

Every function is structural, so the printer reduces in the kernel and the
checks at the end are `rfl` or `decide`.  Nothing here belongs to the
metatheory.
-/

namespace ClassifiersFrontend

open Classifiers
open Classifiers.FCdot (Kind Sig BVar Rename Label)
open Classifiers.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Tm Value Defs Store Cont State
  Platform)
open Classifiers.DotMNF.Examples (unitTy la)

/-! ## Parentheses -/

/-- The result, in parentheses when the position binds tighter than the
form. -/
def parenIf (b : Bool) (str : String) : String :=
  if b then "(" ++ str ++ ")" else str

/-- The level of an operand that must be closed.  It is tighter than every
real precedence. -/
def atomPrec : Nat := 100

/-! ## Labels -/

/-- The first name the table interns at this label. -/
def labelName? (Λ : LabelTable) (l : Label) : Option String :=
  match Λ with
  | [] => none
  | (x, l') :: Λ' => if l' = l then some x else labelName? Λ' l

/-- The name of a label no table holds: the sort and the number. -/
def defaultLabelName : Label → String
  | .typ n => "A" ++ toString n
  | .trm n => "a" ++ toString n

/-- The name of a label, through the table where the table has one. -/
def ppLabel (Λ : LabelTable) (l : Label) : String :=
  (labelName? Λ l).getD (defaultLabelName l)

/-! ## Classifier names

A classifier is a path of child indices from the root
(`lean/Coercions/Classifiers/Cls/Core.lean`).  The elaborated syntax carries
that path and not the declared name. -/

/-- The first name the table gives this classifier. -/
def clsNameOf? (κt : ClsTable) (c : Cls.Classifier) : Option String :=
  match κt with
  | [] => none
  | (x, c') :: κt' => if c' = c then some x else clsNameOf? κt' c
termination_by structural κt

/-- A classifier no table names, as its chain of child indices off `⊤`. -/
def ppClassifierRaw (c : Cls.Classifier) : String :=
  match c with
  | .top => "⊤"
  | .child n a => ppClassifierRaw a ++ "." ++ toString n
termination_by structural c

/-- A classifier's name, through the table where the table has one, its raw
tree position otherwise. -/
def ppClsName (κt : ClsTable) (c : Cls.Classifier) : String :=
  (clsNameOf? κt c).getD (ppClassifierRaw c)

/-- One holed subtree of a kind.  A root with nothing excluded is `only[name]`,
the whole tree minus names is `except[names]`, and any other subtree is a
subtraction. -/
def ppSubtreeWith (κt : ClsTable) (t : Cls.Subtree) : String :=
  match t.excls with
  | [] => "only[" ++ ppClsName κt t.root ++ "]"
  | es =>
      match t.root with
      | .top => "except[" ++ String.intercalate ", " (es.map (ppClsName κt)) ++ "]"
      | _ => ppClsName κt t.root ++ " \\ {" ++ String.intercalate ", " (es.map (ppClsName κt))
        ++ "}"

/-- A kind in the paper's notation, through a classifier table: the union of
its subtrees. -/
def ppClsKindWith (κt : ClsTable) (K : Cls.Kind) : String :=
  match K with
  | [] => "∅"
  | [t] => ppSubtreeWith κt t
  | t :: K' => ppSubtreeWith κt t ++ " ∪ " ++ ppClsKindWith κt K'
termination_by structural K

/-- A kind in the paper's notation, with every classifier at its raw tree
position. -/
def ppClsKind (K : Cls.Kind) : String := ppClsKindWith [] K

/-! ## Names for binders

Two disjoint pools, one per kind.  A pool that runs out falls back to a name
built from the count of names in use. -/

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

/-- Names for a signature without any.  A binder is named `x` or `k` followed
by the number of binders outside it. -/
def defaultNames (s : Sig) : NameEnv s :=
  match s with
  | [] => .nil
  | .var :: s' => .cons (defaultNames s') ("x" ++ toString s'.length)
  | .cap :: s' => .consC (defaultNames s') ("k" ++ toString s'.length)
termination_by structural s

/-- Names for a signature whose outermost binders are named by `pre`.  The
others take invented names.  This reads a run over a named platform. -/
def namesOver (pre : List String) (s : Sig) : NameEnv s :=
  match s with
  | [] => .nil
  | .var :: s' => .cons (namesOver pre s') (pre.getD s'.length ("x" ++ toString s'.length))
  | .cap :: s' => .consC (namesOver pre s') (pre.getD s'.length ("k" ++ toString s'.length))
termination_by structural s

/-! ## Capture sets -/

/-- A capture atom.  A projected atom prints its base atom, then its kind. -/
def ppCapAtomWith {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (a : CapAtom s) :
    String :=
  match a with
  | .var x => nv.nameAt x
  | .cvar κ => nv.capNameAt κ
  | .sel x A => nv.nameAt x ++ "." ++ ppLabel Λ A
  | .any => "any"
  | .fresh => "fresh"
  | .proj a φ => ppCapAtomWith Λ κt nv a ++ "." ++ ppClsKindWith κt φ
termination_by structural a

/-- The atoms of a capture set, in the order the set holds them. -/
def ppCapEntries {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (C : CaptureSet s) :
    List String :=
  match C with
  | [] => []
  | a :: C' => ppCapAtomWith Λ κt nv a :: ppCapEntries Λ κt nv C'
termination_by structural C

/-- A capture set in the paper's notation. -/
def ppCapWith {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (C : CaptureSet s) :
    String :=
  "{" ++ String.intercalate ", " (ppCapEntries Λ κt nv C) ++ "}"

/-- A capture set in the paper's notation, with no tables. -/
def ppCap {s : Sig} (nv : NameEnv s) (C : CaptureSet s) : String := ppCapWith [] [] nv C

/-! ## Shapes, types and answers -/

/-- A shape that needs no parentheses as the left side of `^`: everything
but an intersection and an arrow. -/
def Shape.isAtomic {s : Sig} : Shape s → Bool
  | .all _ _ => false
  | .and _ _ => false
  | _ => true

mutual
/-- A type, at the precedence of its position. -/
def ppTyAt (Λ : LabelTable) (κt : ClsTable) {s : Sig} (p : Nat) (nv : NameEnv s) (T : Ty s) :
    String :=
  match T with
  | .capt [] S => ppShapeAt Λ κt p nv S
  | .capt C S =>
      let sStr :=
        if Shape.isAtomic S then ppShapeAt Λ κt atomPrec nv S
        else "(" ++ ppShapeAt Λ κt 0 nv S ++ ")"
      parenIf (p > 60) (sStr ++ " ^ " ++ ppCapWith Λ κt nv C)
termination_by structural T
/-- A shape, at the precedence of its position. -/
def ppShapeAt (Λ : LabelTable) (κt : ClsTable) {s : Sig} (p : Nat) (nv : NameEnv s) (S : Shape s) :
    String :=
  match S with
  | .top => "⊤"
  | .bot => "⊥"
  | .typ A S T =>
      "{" ++ ppLabel Λ A ++ " : " ++ ppShapeAt Λ κt 0 nv S ++ " .. " ++ ppShapeAt Λ κt 0 nv T
        ++ "}"
  | .fld a T => "{" ++ ppLabel Λ a ++ " : " ++ ppTyAt Λ κt 0 nv T ++ "}"
  | .cap C lo hi =>
      "{" ++ ppLabel Λ C ++ "^ : " ++ ppCapWith Λ κt nv lo ++ " .. " ++ ppCapWith Λ κt nv hi
        ++ "}"
  | .capk C φ => "{" ++ ppLabel Λ C ++ "^ : " ++ ppClsKindWith κt φ ++ "}"
  | .sel p A => nv.nameAt p.root ++ "." ++ ppLabel Λ A
  | .mu S =>
      let y := freshName (NameEnv.allNames nv)
      "μ(" ++ y ++ ". " ++ ppShapeAt Λ κt 0 (NameEnv.cons nv y) S ++ ")"
  | .all T U =>
      let κ := freshCapName (NameEnv.allNames nv)
      let nv1 := NameEnv.consC nv κ
      let x := freshName (NameEnv.allNames nv1)
      parenIf (p > 60)
        ("∀[" ++ κ ++ "](" ++ x ++ " : " ++ ppTyAt Λ κt 0 nv1 T ++ ") "
          ++ ppETyAt Λ κt 0 (NameEnv.cons nv1 x) U)
  | .and S T =>
      parenIf (p > 65) (ppShapeAt Λ κt 66 nv S ++ " ∧ " ++ ppShapeAt Λ κt 65 nv T)
  | .box T => "□ " ++ ppTyAt Λ κt atomPrec nv T
termination_by structural S
/-- An answer, at the precedence of its position. -/
def ppETyAt (Λ : LabelTable) (κt : ClsTable) {s : Sig} (p : Nat) (nv : NameEnv s) (E : ETy s) :
    String :=
  match E with
  | .ty T => ppTyAt Λ κt p nv T
  | .ex C T =>
      let κ := freshCapName (NameEnv.allNames nv)
      "∃[" ++ κ ++ " ⊑ " ++ ppCapWith Λ κt nv C ++ "] " ++ ppTyAt Λ κt 60 (NameEnv.consC nv κ) T
termination_by structural E
end

/-- A type in the paper's notation. -/
def ppTyWith (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (T : Ty s) : String :=
  ppTyAt Λ κt 0 nv T

/-- A type in the paper's notation, with no tables. -/
def ppTy (nv : NameEnv s) (T : Ty s) : String := ppTyWith [] [] nv T

/-- A shape in the paper's notation. -/
def ppShapeWith (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (S : Shape s) : String :=
  ppShapeAt Λ κt 0 nv S

/-- A shape in the paper's notation, with no tables. -/
def ppShape (nv : NameEnv s) (S : Shape s) : String := ppShapeWith [] [] nv S

/-- An answer in the paper's notation. -/
def ppETyWith (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (E : ETy s) : String :=
  ppETyAt Λ κt 0 nv E

/-- An answer in the paper's notation, with no tables. -/
def ppETy (nv : NameEnv s) (E : ETy s) : String := ppETyWith [] [] nv E

/-! ## Terms of the version's syntax

Application, projection and unboxing take variables, so only the lambda and
the `let` can need parentheses.  A closure's body sits under the body root and
the arrow's capture binder as well as the parameter.  An object's definitions
sit under the class root as well as the self.  These invisible binders get
invented names, so a use set that reaches one still prints. -/

mutual
/-- A term in the paper's notation, at the precedence of its position. -/
def ppTmAt (Λ : LabelTable) (κt : ClsTable) {s : Sig} (p : Nat) (nv : NameEnv s) (t : Tm s) :
    String :=
  match t with
  | .path (.var x) => nv.nameAt x
  | .val v => ppValueAt Λ κt p nv v
  | .app x y => nv.nameAt x ++ " " ++ nv.nameAt y
  | .proj x a => nv.nameAt x ++ "." ++ ppLabel Λ a
  | .let t' u =>
      let y := freshName (NameEnv.allNames nv)
      parenIf (p > 0)
        ("let " ++ y ++ " = " ++ ppTmAt Λ κt 1 nv t' ++ " in "
          ++ ppTmAt Λ κt 0 (NameEnv.cons nv y) u)
  | .unbox C x => ppCapWith Λ κt nv C ++ " ⊸ " ++ nv.nameAt x
  | .letex t' u =>
      let κ := freshCapName (NameEnv.allNames nv)
      let x := freshName (κ :: NameEnv.allNames nv)
      parenIf (p > 0)
        ("let ⟨" ++ κ ++ ", " ++ x ++ "⟩ = " ++ ppTmAt Λ κt 1 nv t' ++ " in "
          ++ ppTmAt Λ κt 0 ((NameEnv.consC nv κ).cons x) u)
termination_by structural t
/-- A value in the paper's notation.  An object literal has no self type, so
the binder stands alone. -/
def ppValueAt (Λ : LabelTable) (κt : ClsTable) {s : Sig} (p : Nat) (nv : NameEnv s) (v : Value s) :
    String :=
  match v with
  | .obj d =>
      let y := freshName (NameEnv.allNames nv)
      let κ := freshCapName (y :: NameEnv.allNames nv)
      "ν(" ++ y ++ ". " ++ ppDefsWith Λ κt ((NameEnv.consC nv κ).cons y) d ++ ")"
  | .lam T t =>
      let κ := freshCapName (NameEnv.allNames nv)
      let nv1 := NameEnv.consC nv κ
      let r := freshCapName (NameEnv.allNames nv1)
      let nv2 := NameEnv.consC nv1 r
      let y := freshName (NameEnv.allNames nv2)
      parenIf (p > 1)
        ("λ(" ++ y ++ " : " ++ ppTyWith Λ κt nv1 T ++ "). "
          ++ ppTmAt Λ κt 0 (NameEnv.cons nv2 y) t)
  | .box x => "□ " ++ nv.nameAt x
termination_by structural v
/-- A definition list in the paper's notation. -/
def ppDefsWith (Λ : LabelTable) (κt : ClsTable) {s : Sig} (nv : NameEnv s) (d : Defs s) : String :=
  match d with
  | .typ A S => "{type " ++ ppLabel Λ A ++ " = " ++ ppShapeWith Λ κt nv S ++ "}"
  | .cap C c => "{" ++ ppLabel Λ C ++ "^ = " ++ ppCapWith Λ κt nv c ++ "}"
  | .trm a t => "{" ++ ppLabel Λ a ++ " = " ++ ppTmAt Λ κt 0 nv t ++ "}"
  | .and d' e => ppDefsWith Λ κt nv d' ++ " ∧ " ++ ppDefsWith Λ κt nv e
termination_by structural d
end

/-- A term in the paper's notation. -/
def ppTmWith (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (t : Tm s) : String :=
  ppTmAt Λ κt 0 nv t

/-- A value in the paper's notation. -/
def ppValueWith (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (v : Value s) : String :=
  ppValueAt Λ κt 0 nv v

/-- A term in the paper's notation, with no tables. -/
def ppTm (nv : NameEnv s) (t : Tm s) : String := ppTmWith [] [] nv t

/-- A value in the paper's notation, with no tables. -/
def ppValue (nv : NameEnv s) (v : Value s) : String := ppValueWith [] [] nv v

/-- A definition list in the paper's notation, with no tables. -/
def ppDefs (nv : NameEnv s) (d : Defs s) : String := ppDefsWith [] [] nv d

/-! ## Annotated terms

The syntax of `Ann.lean` is what a compilation returns.  It prints in full,
with the self shape of a literal, the result answer of a `let` and the
ascription.  An unboxing without a set prints with the empty set. -/

mutual
/-- An annotated term in the paper's notation, at the precedence of its
position. -/
def ppATmAt (Λ : LabelTable) (κt : ClsTable) {s : Sig} (p : Nat) (nv : NameEnv s) (t : ATm s) :
    String :=
  match t with
  | .path (.var x) => nv.nameAt x
  | .lam T t' =>
      let κ := freshCapName (NameEnv.allNames nv)
      let nv1 := NameEnv.consC nv κ
      let r := freshCapName (NameEnv.allNames nv1)
      let nv2 := NameEnv.consC nv1 r
      let y := freshName (NameEnv.allNames nv2)
      parenIf (p > 1)
        ("λ(" ++ y ++ " : " ++ ppTyWith Λ κt nv1 T ++ "). "
          ++ ppATmAt Λ κt 0 (NameEnv.cons nv2 y) t')
  | .obj S d =>
      let y := freshName (NameEnv.allNames nv)
      let κ := freshCapName (y :: NameEnv.allNames nv)
      "ν(" ++ y ++ " : " ++ ppShapeAt Λ κt 0 (NameEnv.cons nv y) S ++ ". "
        ++ ppADefsWith Λ κt ((NameEnv.consC nv κ).cons y) d ++ ")"
  | .app x y => nv.nameAt x ++ " " ++ nv.nameAt y
  | .proj x a => nv.nameAt x ++ "." ++ ppLabel Λ a
  | .let ann t' u =>
      let y := freshName (NameEnv.allNames nv)
      let ann? :=
        match ann with
        | none => ""
        | some E => " : " ++ ppETyWith Λ κt nv E
      parenIf (p > 0)
        ("let " ++ y ++ ann? ++ " = " ++ ppATmAt Λ κt 1 nv t' ++ " in "
          ++ ppATmAt Λ κt 0 (NameEnv.cons nv y) u)
  | .letex t' u =>
      let κ := freshCapName (NameEnv.allNames nv)
      let x := freshName (κ :: NameEnv.allNames nv)
      parenIf (p > 0)
        ("let ⟨" ++ κ ++ ", " ++ x ++ "⟩ = " ++ ppATmAt Λ κt 1 nv t' ++ " in "
          ++ ppATmAt Λ κt 0 ((NameEnv.consC nv κ).cons x) u)
  | .box x => "□ " ++ nv.nameAt x
  | .unbox C x => ppCapWith Λ κt nv (C.getD []) ++ " ⊸ " ++ nv.nameAt x
  | .asc t' T => "(" ++ ppATmAt Λ κt 1 nv t' ++ " : " ++ ppTyWith Λ κt nv T ++ ")"
termination_by structural t
/-- An annotated definition list in the paper's notation. -/
def ppADefsWith (Λ : LabelTable) (κt : ClsTable) {s : Sig} (nv : NameEnv s) (d : ADefs s) :
    String :=
  match d with
  | .typ A S => "{type " ++ ppLabel Λ A ++ " = " ++ ppShapeAt Λ κt 0 nv S ++ "}"
  | .cap C c => "{" ++ ppLabel Λ C ++ "^ = " ++ ppCapWith Λ κt nv c ++ "}"
  | .trm a t => "{" ++ ppLabel Λ a ++ " = " ++ ppATmAt Λ κt 0 nv t ++ "}"
  | .and d' e => ppADefsWith Λ κt nv d' ++ " ∧ " ++ ppADefsWith Λ κt nv e
termination_by structural d
end

/-- An annotated term in the paper's notation. -/
def ppATmWith (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (t : ATm s) : String :=
  ppATmAt Λ κt 0 nv t

/-- An annotated term in the paper's notation, with no tables. -/
def ppATm (nv : NameEnv s) (t : ATm s) : String := ppATmWith [] [] nv t

/-- An annotated definition list in the paper's notation, with no tables. -/
def ppADefs (nv : NameEnv s) (d : ADefs s) : String := ppADefsWith [] [] nv d

/-! ## Surface phrases

The surface syntax carries its own names, so these printers need no table and
no name environment. -/

/-- A classifier kind, at the precedence of its position: `∪` at 65, `∩` at
70, as the grammar reads them. -/
def ppSKindAt (p : Nat) (K : SKind) : String :=
  match K with
  | .only cs => "only[" ++ String.intercalate ", " cs ++ "]"
  | .except cs => "except[" ++ String.intercalate ", " cs ++ "]"
  | .union K L => parenIf (p > 65) (ppSKindAt 66 K ++ " ∪ " ++ ppSKindAt 65 L)
  | .inter K L => parenIf (p > 70) (ppSKindAt 71 K ++ " ∩ " ++ ppSKindAt 70 L)
termination_by structural K

/-- A classifier kind in the paper's notation. -/
def ppSKind (K : SKind) : String := ppSKindAt 0 K

/-- A surface capture atom.  A projected atom prints its base atom, then
its kind. -/
def ppSAtom (a : SAtom) : String :=
  match a with
  | .name x => x
  | .sel x C => x ++ "." ++ C
  | .any => "any"
  | .fresh => "fresh"
  | .proj a K => ppSAtom a ++ "." ++ ppSKindAt 0 K
termination_by structural a

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
/-- A surface shape, at the precedence of its position.  `∀` sits at 60,
`∧` at 65, as the grammar reads them. -/
def ppSShapeAt (p : Nat) (S : SShape) : String :=
  match S with
  | .top => "⊤"
  | .bot => "⊥"
  | .typ A S T => "{" ++ A ++ " : " ++ ppSShapeAt 0 S ++ " .. " ++ ppSShapeAt 0 T ++ "}"
  | .cap C lo hi => "{" ++ C ++ "^ : " ++ ppSCap lo ++ " .. " ++ ppSCap hi ++ "}"
  | .capk C K => "{" ++ C ++ "^ : " ++ ppSKindAt 0 K ++ "}"
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
/-- A surface type, at the precedence of its position.  `sShapeIsAtomic`
decides the parentheses left of `^`. -/
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
      let arrow? :=
        match κ with
        | none => "λ(" ++ x ++ " : " ++ ppSTyAt 0 T ++ "). "
        | some c => "λ[" ++ c ++ "](" ++ x ++ " : " ++ ppSTyAt 0 T ++ "). "
      parenIf (p > 1) (arrow? ++ ppSTmAt 0 t)
  | .obj x S d => "ν(" ++ x ++ " : " ++ ppSShapeAt 0 S ++ ". " ++ ppSDefsAt d ++ ")"
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
  | .trm a t => "{" ++ a ++ " = " ++ ppSTmAt 0 t ++ "}"
  | .and d' e => ppSDefsAt d' ++ " ∧ " ++ ppSDefsAt e
termination_by structural d
end

/-- A surface term in the paper's notation. -/
def ppSTm (e : STm) : String := ppSTmAt 0 e

/-- A surface definition list in the paper's notation. -/
def ppSDefs (d : SDefs) : String := ppSDefsAt d

/-! ## States of the source machine

The store is printed outermost binder first, then the continuation as frames
with a hole, then the term.  A store slot at a capture binder holds no value.
An unpacking frame opens a capture binder and a term binder over its body. -/

/-- The store as one entry per binder, outermost first.  A capture slot has
no value to show. -/
def storeEntries (Λ : LabelTable) (κt : ClsTable) {s : Sig} (nv : NameEnv s) (σ : Store s) :
    List String :=
  match nv, σ with
  | .nil, .nil => []
  | .cons nv' y, .cons σ' v =>
      storeEntries Λ κt nv' σ' ++ [y ++ " = " ++ ppValueWith Λ κt nv' v]
  | .consC nv' y, .consC σ' => storeEntries Λ κt nv' σ' ++ [y]
termination_by structural nv

/-- The store in the paper's notation. -/
def ppStoreWith (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (σ : Store s) : String :=
  match storeEntries Λ κt nv σ with
  | [] => "·"
  | es => String.intercalate ", " es

/-- The frames of the continuation, outermost first, each with its hole. -/
def contFrames (Λ : LabelTable) (κt : ClsTable) {s : Sig} (nv : NameEnv s) (K : Cont s) :
    List String :=
  match K with
  | .nil => []
  | .cons K' u =>
      let y := freshName (NameEnv.allNames nv)
      contFrames Λ κt nv K' ++ ["let " ++ y ++ " = □ in " ++ ppTmWith Λ κt (NameEnv.cons nv y) u]
  | .consE K' u =>
      let κ := freshCapName (NameEnv.allNames nv)
      let x := freshName (κ :: NameEnv.allNames nv)
      contFrames Λ κt nv K' ++
        ["let ⟨" ++ κ ++ ", " ++ x ++ "⟩ = □ in "
          ++ ppTmWith Λ κt ((NameEnv.consC nv κ).cons x) u]
termination_by structural K

/-- The continuation in the paper's notation. -/
def ppContWith (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (K : Cont s) : String :=
  match contFrames Λ κt nv K with
  | [] => "·"
  | fs => String.intercalate ", " fs

/-- A state of the source machine, store then continuation then term. -/
def ppStateWith (Λ : LabelTable) (κt : ClsTable) {s : Sig} (nv : NameEnv s) (st : State s) :
    String :=
  "⟨" ++ ppStoreWith Λ κt nv st.σ ++ " | " ++ ppContWith Λ κt nv st.K ++ " | "
    ++ ppTmWith Λ κt nv st.t ++ "⟩"

/-- The answer of `compileAndRun`, in full, with default names. -/
def ppRun (Λ : LabelTable) (κt : ClsTable) : Verdict ((s : Sig) × State s) → String
  | .ok ⟨s, st⟩ => ppStateWith Λ κt (defaultNames s) st
  | .rejected r => "rejected: " ++ Reason.name r
  | .unknown => "did not compile"

/-- The term of the answer of `compileAndRun`. -/
def ppRunTm (Λ : LabelTable) (κt : ClsTable) : Verdict ((s : Sig) × State s) → String
  | .ok ⟨s, st⟩ => ppTmWith Λ κt (defaultNames s) st.t
  | .rejected r => "rejected: " ++ Reason.name r
  | .unknown => "did not compile"

/-- The answer of `compileAndRun` over a platform named by `pre`. -/
def ppRunOver (Λ : LabelTable) (κt : ClsTable) (pre : List String) :
    Verdict ((s : Sig) × State s) → String
  | .ok ⟨s, st⟩ => ppStateWith Λ κt (namesOver pre s) st
  | .rejected r => "rejected: " ++ Reason.name r
  | .unknown => "did not compile"

/-- The term of the answer of `compileAndRun` over a platform named by
`pre`. -/
def ppRunTmOver (Λ : LabelTable) (κt : ClsTable) (pre : List String) :
    Verdict ((s : Sig) × State s) → String
  | .ok ⟨s, st⟩ => ppTmWith Λ κt (namesOver pre s) st.t
  | .rejected r => "rejected: " ++ Reason.name r
  | .unknown => "did not compile"

/-! ## Checks

Small terms built by hand exercise one construct at a time.  The larger ones
are the surface programs and examples of `Resolve.lean` and `Typer.lean`. -/

section Checks

open Classifiers.DotMNF.Examples (E1Filt E3AbsTy E3k1 E3k2)

/-- `clsNameOf?` reads the table backwards. -/
example : clsNameOf? exCls Cls.Control = some "Control" := rfl

/-- A classifier no table names prints as its raw tree position. -/
example : clsNameOf? [] Cls.Control = none := rfl
example : ppClsName [] Cls.Control = "⊤.1.0" := rfl

/-- A kind with no exclusion is `only[name]`. -/
example : ppClsKindWith exCls (Cls.only Cls.Control) = "only[Control]" := rfl

/-- A kind rooted at `⊤` is `except[names]`. -/
example : ppClsKindWith exCls (Cls.except Cls.ThreadLocal) = "except[ThreadLocal]" := rfl

/-- A union of kinds prints as `∪`. -/
example :
    ppClsKindWith exCls (Cls.only Cls.IO ++ Cls.only Cls.Control) = "only[IO] ∪ only[Control]" :=
  rfl

/-- A kind that is neither a bare `only` nor a bare `except` prints as a
subtraction. -/
example :
    ppClsKindWith exCls [⟨Cls.ThreadLocal, [Cls.Control]⟩] = "ThreadLocal \\ {Control}" := rfl

/-- A capture set with a capture variable, `any` and `fresh`. -/
example :
    ppCapWith Λc [] (NameEnv.consC .nil "k0")
      [CapAtom.cvar .here, CapAtom.any, CapAtom.fresh]
      = "{k0, any, fresh}" := rfl

/-- **CE1's declared use set, `E1Filt`**, prints as the two platform
capabilities, each projected at `only[Control]`. -/
example : ppCapWith Λk exCls E1Names E1Filt = "{ctl.only[Control], io.only[Control]}" := rfl

/-- **The kind-bounded member of `E3AbsTy`**: a capture member bounded by a
kind, beside a field that reads it through the self. -/
example :
    ppTyWith Λk exCls E3Names (E3AbsTy E3k1 E3k2) =
      "μ(x. {C^ : only[Control]} ∧ {run : (∀[k](y : ⊤) ⊤) ^ {x.C}}) ^ {k1, k2}" := rfl
