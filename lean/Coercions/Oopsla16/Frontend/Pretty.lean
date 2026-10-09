import Coercions.Oopsla16.Frontend.Pipeline

/-!
# The pretty printer

An unparser back into the notation of the paper, so that an `#eval` of a
resolved program or of a run is readable.  The inductives of `Oopsla16` have
no `Repr` instance, so this is how one looks at a type, a term, a member list
or a run as text.

A label of the calculus is a bare position, and the position restarts at zero
inside every literal.  Different names in different literals can therefore
share a number, and the calculus resolves a selection by the number alone.
`ppLabel` prints the name the table offers and the number, `name#l`, so a
table that pairs a name with the wrong position shows up in the output.

A bound variable is an index, so its name comes from a `NameEnv` of
`Resolve.lean`, extended at each binder.  `freshName` picks the first short
name the environment does not hold.  A store location has no surface syntax,
so `defaultLocNames` names the locations of a store `ℓ0`, `ℓ1`, … in
allocation order.

Everything is structural, so the printer reduces in the kernel and the checks
at the end are `decide +kernel`.  The printer is not part of the metatheory.
-/

namespace Oopsla16Frontend

open FCdot (Kind Sig BVar)
open Oopsla16 (Lb Ty Tm Dm Dms Vr Store)

/-! ## Parentheses

As in `Notation.lean`, `∧` has precedence 65 and `∨` 60, both right leaning.
Every other former is closed or a name followed by a label, so it needs none. -/

/-- The string, in parentheses when `b` holds. -/
def parenIf (b : Bool) (str : String) : String :=
  if b then "(" ++ str ++ ")" else str

/-! ## Labels -/

/-- The first name the table offers for this position, if any. -/
def labelName? (Λ : LabelTable) (l : Lb) : Option String :=
  match Λ with
  | [] => none
  | (x, l') :: Λ' => if l' = l then some x else labelName? Λ' l
termination_by structural Λ

/-- A label as `name#l`, or `#l` when the table has no name for it. -/
def ppLabel (Λ : LabelTable) (l : Lb) : String :=
  match labelName? Λ l with
  | some x => x ++ "#" ++ toString l
  | none => "#" ++ toString l

/-! ## Names for binders -/

/-- The binder names, in the order they are tried. -/
def binderNames : List String := ["x", "y", "z", "w", "u", "v", "p", "q"]

/-- The first short name the environment does not already hold. -/
def freshName (used : List String) : String :=
  match binderNames.find? (fun s => !used.contains s) with
  | some s => s
  | none => "x" ++ toString used.length

/-- The name of a bound variable. -/
def NameEnv.nameAt {s : Sig} (ν : NameEnv s) (i : BVar s .var) : String :=
  match ν, i with
  | .cons _ y, .here => y
  | .cons ν' _, .there i' => NameEnv.nameAt ν' i'
termination_by structural ν

/-! ## Names for store locations -/

/-- Names for a store scope, oldest location first. -/
def defaultLocNames : (σ : Sig) → NameEnv σ
  | [] => .nil
  | .var :: σ' => .cons (defaultLocNames σ') ("ℓ" ++ toString σ'.length)
termination_by structural σ => σ

/-- A variable of either zone: a store location through the location names,
an abstract variable through the local environment. -/
def ppVr {σ s : Sig} (νσ : NameEnv σ) (ν : NameEnv s) : Vr σ s → String
  | .conc l => NameEnv.nameAt νσ l
  | .abs i => NameEnv.nameAt ν i

/-! ## Types -/

/-- A type in the paper's notation, at the precedence `p` of its position.  `νσ`
names the store locations and `ν` the local binders in scope. -/
def ppTyAt (Λ : LabelTable) {σ s : Sig} (νσ : NameEnv σ) (p : Nat) (ν : NameEnv s) :
    Ty σ s → String
  | .TBot => "⊥"
  | .TTop => "⊤"
  | .TFun l S U =>
      let y := freshName (NameEnv.names ν)
      "{def " ++ ppLabel Λ l ++ "(" ++ y ++ " : " ++ ppTyAt Λ νσ 0 ν S ++ ") : "
        ++ ppTyAt Λ νσ 0 (NameEnv.cons ν y) U ++ "}"
  | .TTyp l S U =>
      "{type " ++ ppLabel Λ l ++ " : " ++ ppTyAt Λ νσ 0 ν S ++ " .. "
        ++ ppTyAt Λ νσ 0 ν U ++ "}"
  | .TSel p l => ppVr νσ ν p ++ "." ++ ppLabel Λ l
  | .TBind T =>
      let y := freshName (NameEnv.names ν)
      "μ(" ++ y ++ ". " ++ ppTyAt Λ νσ 0 (NameEnv.cons ν y) T ++ ")"
  | .TAnd S T =>
      parenIf (p > 65) (ppTyAt Λ νσ 66 ν S ++ " ∧ " ++ ppTyAt Λ νσ 65 ν T)
  | .TOr S T =>
      parenIf (p > 60) (ppTyAt Λ νσ 61 ν S ++ " ∨ " ++ ppTyAt Λ νσ 60 ν T)
termination_by structural T => T

/-- A type with a label table and no store. -/
def ppTyWith (Λ : LabelTable) (ν : NameEnv s) (T : Ty [] s) : String :=
  ppTyAt Λ .nil 0 ν T

/-- A type with no label table, so a label prints as its position. -/
def ppTy (ν : NameEnv s) (T : Ty [] s) : String := ppTyWith [] ν T

/-! ## Terms, members and member lists

A member's label is the length of the list below it (`Dms.get?`). -/

mutual
/-- A term in the paper's notation. -/
def ppTmAt (Λ : LabelTable) {σ s : Sig} (νσ : NameEnv σ) (ν : NameEnv s) : Tm σ s → String
  | .tvar v => ppVr νσ ν v
  | .tobj D =>
      let y := freshName (NameEnv.names ν)
      "new {" ++ y ++ " ⇒ " ++ ppDmsWith Λ νσ (NameEnv.cons ν y) D ++ "}"
  | .tapp t l u => ppTmAt Λ νσ ν t ++ "." ++ ppLabel Λ l ++ "(" ++ ppTmAt Λ νσ ν u ++ ")"
termination_by structural t => t
/-- A member at the position `l` its list gives it. -/
def ppDmAt (Λ : LabelTable) {σ s : Sig} (νσ : NameEnv σ) (ν : NameEnv s) (l : Lb) : Dm σ s → String
  | .dfun S U t =>
      let y := freshName (NameEnv.names ν)
      let sAnn := match S with
        | none => ""
        | some S' => " : " ++ ppTyAt Λ νσ 0 ν S'
      let uAnn := match U with
        | none => ""
        | some U' => " : " ++ ppTyAt Λ νσ 0 (NameEnv.cons ν y) U'
      "def " ++ ppLabel Λ l ++ "(" ++ y ++ sAnn ++ ")" ++ uAnn ++ " = "
        ++ ppTmAt Λ νσ (NameEnv.cons ν y) t
  | .dty T => "type " ++ ppLabel Λ l ++ " = " ++ ppTyAt Λ νσ 0 ν T
termination_by structural d => d
/-- A member list, newest member first, as written. -/
def ppDmsWith (Λ : LabelTable) {σ s : Sig} (νσ : NameEnv σ) (ν : NameEnv s) : Dms σ s → String
  | .dnil => ""
  | .dcons d ds' =>
      let one := ppDmAt Λ νσ ν ds'.length d
      let rest := ppDmsWith Λ νσ ν ds'
      if rest = "" then one else one ++ "  " ++ rest
termination_by structural ds => ds
end

/-- A term with no label table. -/
def ppTm {σ s : Sig} (νσ : NameEnv σ) (ν : NameEnv s) (t : Tm σ s) : String :=
  ppTmAt [] νσ ν t

/-! ## The annotated syntax of `Ann.lean` -/

mutual
/-- An annotated term.  A literal prints its self type when written, and an
ascription prints as `(t : T)`. -/
def ppATmAt (Λ : LabelTable) {s : Sig} (ν : NameEnv s) : ATm s → String
  | .var i => NameEnv.nameAt ν i
  | .obj self ds =>
      let y := freshName (NameEnv.names ν)
      let selfAnn := match self with
        | none => ""
        | some T => " : " ++ ppTyWith Λ (NameEnv.cons ν y) T
      "new {" ++ y ++ selfAnn ++ " ⇒ " ++ ppADmsWith Λ (NameEnv.cons ν y) ds ++ "}"
  | .app t l u => ppATmAt Λ ν t ++ "." ++ ppLabel Λ l ++ "(" ++ ppATmAt Λ ν u ++ ")"
  | .asc t T => "(" ++ ppATmAt Λ ν t ++ " : " ++ ppTyWith Λ ν T ++ ")"
termination_by structural t => t
/-- An annotated member, at the position its list gives it. -/
def ppADmAt (Λ : LabelTable) {s : Sig} (ν : NameEnv s) (l : Lb) : ADm s → String
  | .dfun S U t =>
      let y := freshName (NameEnv.names ν)
      let sAnn := match S with
        | none => ""
        | some S' => " : " ++ ppTyWith Λ ν S'
      let uAnn := match U with
        | none => ""
        | some U' => " : " ++ ppTyWith Λ (NameEnv.cons ν y) U'
      "def " ++ ppLabel Λ l ++ "(" ++ y ++ sAnn ++ ")" ++ uAnn ++ " = "
        ++ ppATmAt Λ (NameEnv.cons ν y) t
  | .dty T => "type " ++ ppLabel Λ l ++ " = " ++ ppTyWith Λ ν T
termination_by structural d => d
/-- An annotated member list, newest member first. -/
def ppADmsWith (Λ : LabelTable) {s : Sig} (ν : NameEnv s) : ADms s → String
  | .dnil => ""
  | .dcons d ds' =>
      let one := ppADmAt Λ ν ds'.length d
      let rest := ppADmsWith Λ ν ds'
      if rest = "" then one else one ++ "  " ++ rest
termination_by structural ds => ds
end

/-- An annotated term, with a label table. -/
def ppATmWith (Λ : LabelTable) (ν : NameEnv s) (t : ATm s) : String := ppATmAt Λ ν t

/-- An annotated term, with no label table. -/
def ppATm (ν : NameEnv s) (t : ATm s) : String := ppATmWith [] ν t

/-! ## Surface phrases

Surface names are strings, so these need neither a table nor an environment. -/

/-- A surface type, at the precedence of its position. -/
def ppSTyAt (p : Nat) : SType → String
  | .top => "⊤"
  | .bot => "⊥"
  | .typ L S U => "{type " ++ L ++ " : " ++ ppSTyAt 0 S ++ " .. " ++ ppSTyAt 0 U ++ "}"
  | .fn m x S U => "{def " ++ m ++ "(" ++ x ++ " : " ++ ppSTyAt 0 S ++ ") : " ++ ppSTyAt 0 U ++ "}"
  | .sel x L => x ++ "." ++ L
  | .mu z T => "μ(" ++ z ++ ". " ++ ppSTyAt 0 T ++ ")"
  | .and S T => parenIf (p > 65) (ppSTyAt 66 S ++ " ∧ " ++ ppSTyAt 65 T)
  | .or S T => parenIf (p > 60) (ppSTyAt 61 S ++ " ∨ " ++ ppSTyAt 60 T)
termination_by structural T => T

/-- A surface type. -/
def ppSTy (T : SType) : String := ppSTyAt 0 T

mutual
/-- A surface term. -/
def ppSTmAt : STm → String
  | .var x => x
  | .obj z self ds =>
      let selfAnn := match self with
        | none => ""
        | some T => " : " ++ ppSTyAt 0 T
      "new {" ++ z ++ selfAnn ++ " ⇒ " ++ ppSDmsAt ds ++ "}"
  | .call t m u => ppSTmAt t ++ "." ++ m ++ "(" ++ ppSTmAt u ++ ")"
  | .asc t T => "(" ++ ppSTmAt t ++ " : " ++ ppSTyAt 0 T ++ ")"
termination_by structural e => e
/-- A surface member. -/
def ppSDmAt : SDm → String
  | .typ L T => "type " ++ L ++ " = " ++ ppSTyAt 0 T
  | .fn m x S U t =>
      let sAnn := match S with
        | none => ""
        | some S' => " : " ++ ppSTyAt 0 S'
      let uAnn := match U with
        | none => ""
        | some U' => " : " ++ ppSTyAt 0 U'
      "def " ++ m ++ "(" ++ x ++ sAnn ++ ")" ++ uAnn ++ " = " ++ ppSTmAt t
termination_by structural d => d
/-- A surface member list, newest member first. -/
def ppSDmsAt : SDms → String
  | .nil => ""
  | .cons d ds' =>
      let one := ppSDmAt d
      let rest := ppSDmsAt ds'
      if rest = "" then one else one ++ "  " ++ rest
termination_by structural ds => ds
end

/-- A surface term. -/
def ppSTm (e : STm) : String := ppSTmAt e

/-- A surface member list. -/
def ppSDms (ds : SDms) : String := ppSDmsAt ds

/-! ## A run of the source machine

A configuration prints as the store, one entry per location oldest first,
beside the running term. -/

/-- The store's entries, oldest location first. -/
def storeEntries {σ : Sig} (νσ : NameEnv σ) (Λ : LabelTable) : {σ' : Sig} → Store σ σ' → List String
  | _, .nil => []
  | _, .cons G' ds =>
      let entries := storeEntries νσ Λ G'
      let y := "ℓ" ++ toString entries.length
      entries ++ [y ++ " = {" ++ ppDmsWith Λ νσ .nil ds ++ "}"]
termination_by structural G => G

/-- A configuration of the source machine: its store, then its term. -/
def ppState (Λ : LabelTable) {σ : Sig} (G : Store σ σ) (t : Tm σ []) : String :=
  let νσ := defaultLocNames σ
  let store := storeEntries νσ Λ G
  let storeStr := if store.isEmpty then "·" else String.intercalate ", " store
  "⟨" ++ storeStr ++ " | " ++ ppTmAt Λ νσ .nil t ++ "⟩"

/-- The result of `compileAndRun`, in full. -/
def ppRun (Λ : LabelTable) : Option (Next []) → String
  | none => "did not compile"
  | some n => ppState Λ n.G' n.t'

/-! ## Checks -/

section Checks

/-! ### Surface phrases and precedence -/

example : ppSTy (o16Ty% { type A : ⊥ .. ⊤ }) = "{type A : ⊥ .. ⊤}" := by decide +kernel

/-- `∧` binds tighter than `∨`, so a mixed chain needs no parentheses. -/
example : ppSTy (o16Ty% ⊤ ∧ ⊥ ∨ ⊤) = "⊤ ∧ ⊥ ∨ ⊤" := by decide +kernel
example : ppSTy (o16Ty% ⊤ ∨ (⊥ ∧ ⊤)) = "⊤ ∨ ⊥ ∧ ⊤" := by decide +kernel

/-- A union inside an intersection keeps its parentheses. -/
example : ppSTy (o16Ty% (⊤ ∨ ⊥) ∧ ⊤) = "(⊤ ∨ ⊥) ∧ ⊤" := by decide +kernel
example : ppSTy (o16Ty% ⊤ ∧ (⊥ ∨ ⊤)) = "⊤ ∧ (⊥ ∨ ⊤)" := by decide +kernel

/-- A chain of calls prints as `Notation.lean` parses it. -/
example : ppSTm (o16% x.m(y).n(z)) = "x.m(y).n(z)" := by decide +kernel

/-! ### A label's position beside its name

`recArgTable` pairs `"apply"` and `"f"` with position `0`, in different
literals.  `labelName?` answers the first match, `"apply"`, and `ppLabel` still
prints the `0`. -/

example : ppLabel recArgTable 0 = "apply#0" := by decide +kernel
example : ppLabel recArgTable 2 = "A#2" := by decide +kernel
example : ppLabel [] 2 = "#2" := by decide +kernel

/-! ### Fresh binder names -/

/-- The `μ` binder takes `"x"` and the method's parameter under it takes
`"y"`. -/
example : ppTyAt recArgTable (NameEnv.nil.cons "z") 0 (NameEnv.nil.cons "z")
    (Oopsla16.Ty.TBind (.TAnd (.TFun 0 .TTop (.TSel (.abs .here) 2)) .TTop))
    = "μ(x. {def apply#0(y : ⊤) : y.A#2} ∧ ⊤)" := by decide +kernel

/-! ### The annotated syntax -/

/-- Both literals of `RecursiveArg.prog` carry the self type their Curry style
method needs, and the printer shows it after the colon. -/
example : (resolve recArgTable recArgSrc).map (ppATmWith recArgTable .nil) = some
    ("new {x : {def apply#0(y : μ(y. {def apply#0(z : ⊤) : y.B#1})) : ⊤} ∧ ⊤ ⇒ "
      ++ "def apply#0(y) = y}.apply#0(new {x : {type A#2 : x.B#1 .. x.B#1} ∧ "
      ++ "{type B#1 : ⊤ .. ⊤} ∧ {def apply#0(y : ⊤) : x.A#2} ∧ ⊤ ⇒ "
      ++ "type A#2 = x.B#1  type B#1 = ⊤  def apply#0(y) = y})") := by
  decide +kernel

/-- With its self types erased, each literal prints with an empty slot: no
colon after the binder. -/
example : (resolve recArgTable recArgSrc.eraseSelf).map (ppATmWith recArgTable .nil) = some
    ("new {x ⇒ def apply#0(y) = y}.apply#0(new {x ⇒ type A#2 = x.B#1  type B#1 = ⊤  "
      ++ "def apply#0(y) = y})") := by
  decide +kernel

/-! ### Erased sources -/

/-- The Scala form of `CurryCall.prog` prints with each parameter type written
and no other annotation. -/
example : ppSTm curryCallSrc.scalaForm
    = "new {c ⇒ def apply(y : ⊤) = new {i ⇒ def apply(y : ⊤) = y}.apply(y)}.apply("
      ++ "new {i ⇒ def apply(y : ⊤) = y})" := by
  decide +kernel

/-- The printed text reads back in the notation as the same surface term. -/
example : (o16% new {c ⇒ def apply(y : ⊤) = new {i ⇒ def apply(y : ⊤) = y}.apply(y)}.apply(
      new {i ⇒ def apply(y : ⊤) = y})) = curryCallSrc.scalaForm := by
  decide +kernel

/-! ### Runs -/

/-- The recursive argument example answers in three steps.  The caller
allocates at `ℓ0`, the argument at `ℓ1`, and the call returns `ℓ1`. -/
example : ppRun recArgTable
    (compileAndRun {} 3 recArgTable recArgSrc)
    = "⟨ℓ0 = {def apply#0(x) = x}, ℓ1 = {type A#2 = ℓ1.B#1  type B#1 = ⊤  "
      ++ "def apply#0(x) = x} | ℓ1⟩" := by
  decide +kernel

/-- `ex1` before any step: the store is empty. -/
example : ppRun ex1Table (compileAndRun {} 0 ex1Table ex1src)
    = "⟨· | new {x ⇒ def T#0(y : {type T#0 : ⊥ .. ⊤}) : {def T#0(z : y.T#0) : y.T#0} = "
      ++ "new {z ⇒ def T#0(w : y.T#0) : y.T#0 = w}}⟩" := by
  decide +kernel

/-- `ex1` answers in one step: the literal allocates at `ℓ0`. -/
example : ppRun ex1Table (compileAndRun {} 1 ex1Table ex1src)
    = "⟨ℓ0 = {def T#0(x : {type T#0 : ⊥ .. ⊤}) : {def T#0(y : x.T#0) : x.T#0} = "
      ++ "new {y ⇒ def T#0(z : x.T#0) : x.T#0 = z}} | ℓ0⟩" := by
  decide +kernel

/-- A failed compile prints as such. -/
example : ppRun [] none = "did not compile" := by decide +kernel

end Checks

end Oopsla16Frontend
