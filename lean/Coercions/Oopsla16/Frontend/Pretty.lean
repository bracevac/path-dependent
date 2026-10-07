import Coercions.Oopsla16.Frontend.Pipeline

/-!
# The pretty printer

An unparser back into the paper's notation, so that an `#eval` of a
resolved program or of a run is readable.  The frozen inductives of
`Oopsla16` carry no `Repr` instance and cannot gain one, since the version
does not change, so this module is the only way to look at a type, a term, a
member list or a run as text.

## Labels, and why a position is shown beside every name

A label of the version is a bare position, one namespace shared by type and
method members, and the position restarts at zero inside every literal
(`Oopsla16/Syntax.lean:30-33`).  So two different literals routinely give two
different names the same number, and a selection resolves by number alone:
if a table ever paired the wrong name with a position, the term that comes
out would type as if the other member had been written, with nothing in the
derivation to say so.  `ppLabel` prints the name the table offers *and* the
number itself, `name#l`, so the pairing a run actually used is visible next
to the name a program's source gave it, and a silent mismatch is something a
reader can catch by eye.

## Names for binders and for store locations

A bound variable of the version's own syntax is an index, so a name for it
comes back only through a `NameEnv` of `Resolve.lean`, built up one entry per
binder as the printer walks under one.  `freshName` invents the first short
name the environment does not already hold.  Two binders can end up sharing a
name when one is printed before the other comes into scope, which is no more
than what shadowing already means.

A store location is not a user binder at all: no surface program ever writes
one, since the version's own grammar has no syntax for a location
(`Oopsla16/Syntax.lean`).  A completed
store names its locations `ℓ0`, `ℓ1`, … in the order they were allocated,
through `defaultLocNames`, and that is also how a `Vr.conc` prints inside a
type or a term reachable from that store.

## Recursion

Every function here is structural and says so, so the printer reduces in the
kernel and the checks at the end are `rfl` or `decide +kernel`.  Nothing in
this module is part of the metatheory, and no definition here lives in the
`Oopsla16` or `FCdotR` namespaces.
-/

namespace Oopsla16Frontend

open FCdot (Kind Sig BVar)
open Oopsla16 (Lb Ty Tm Dm Dms Vr Store)

/-! ## Parentheses

The grammar of `Notation.lean` gives `∧` precedence 65 and `∨` precedence
60, both right leaning, so `∧` binds tighter.  No other type former needs
parentheses: the method and type member declarations and `μ(…)` are closed
forms, and a selection is a name followed by a label.  No term former needs
parentheses either, since a call always writes its argument inside its own
parentheses and an object literal is a closed form. -/

/-- The result, in parentheses when the position binds more loosely than the
form itself. -/
def parenIf (b : Bool) (str : String) : String :=
  if b then "(" ++ str ++ ")" else str

/-! ## Labels -/

/-- The first name the table offers for this position, if any. -/
def labelName? (Λ : LabelTable) (l : Lb) : Option String :=
  match Λ with
  | [] => none
  | (x, l') :: Λ' => if l' = l then some x else labelName? Λ' l
termination_by structural Λ

/-- A label, as the name the table offers beside the bare position, `name#l`
or `#l` when the table offers no name. -/
def ppLabel (Λ : LabelTable) (l : Lb) : String :=
  match labelName? Λ l with
  | some x => x ++ "#" ++ toString l
  | none => "#" ++ toString l

/-! ## Names for binders -/

/-- The short names a binder is given, in the order they are tried. -/
def binderNames : List String := ["x", "y", "z", "w", "u", "v", "p", "q"]

/-- The first short name the environment does not already hold. -/
def freshName (used : List String) : String :=
  match binderNames.find? (fun s => !used.contains s) with
  | some s => s
  | none => "x" ++ toString used.length

/-- The name of a bound variable.  Total, because the environment holds one
name per binder of the signature. -/
def NameEnv.nameAt {s : Sig} (ν : NameEnv s) (i : BVar s .var) : String :=
  match ν, i with
  | .cons _ y, .here => y
  | .cons ν' _, .there i' => NameEnv.nameAt ν' i'
termination_by structural ν

/-! ## Names for store locations

No surface program writes a location, so a completed store is named
afresh, outermost (oldest) first: `ℓ0` for the first location a run
allocates. -/

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

/-- A type in the paper's notation, at the precedence of its position.  `νσ`
names the store locations a selection may read, fixed for one call.  `ν`
names the local binders in scope, growing under `μ` and under a method's
parameter. -/
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

/-- A type in the paper's notation, with a label table and no store in
reach: a closed program before it runs. -/
def ppTyWith (Λ : LabelTable) (ν : NameEnv s) (T : Ty [] s) : String :=
  ppTyAt Λ .nil 0 ν T

/-- A type with no label table.  A label prints as its bare position. -/
def ppTy (ν : NameEnv s) (T : Ty [] s) : String := ppTyWith [] ν T

/-! ## Terms, members and member lists of the frozen syntax

A member carries no label of its own.  Its label is the length of the list
below it, exactly as the version reads it (`Dms.get?`). -/

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
/-- A member list, in the order it was written: the newest member, at the
position its tail gives it, first. -/
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

/-! ## The annotated syntax of `Ann.lean`

`ATm` sits at the empty store scope throughout, so it names no location and
every selection is a name from `ν` alone. -/

mutual
/-- An annotated term in the paper's notation.  An object literal prints its
self type when one was written, and an ascription prints as `(t : T)`. -/
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
/-- An annotated member list, newest member first, same order as written. -/
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

Surface names are already strings, so these need neither a table nor an
environment.  The precedences follow `Notation.lean`: `∧` at 65, `∨` at 60,
both right leaning. -/

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
/-- A surface member list, same order as written. -/
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

A store is printed one entry per location, oldest first, and a configuration
is the store beside the running term.  `defaultLocNames` names the store's
own locations, and those are exactly the names a selection inside it
prints through. -/

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

/-! ## Checks

Everything above is structural, so the printer reduces in the kernel and the
checks below close by `decide +kernel`, which runs the printer itself rather
than trusting it.  Nothing here is a theorem about the calculus. -/

section Checks

/-! ### Surface phrases, and the grammar's own precedence -/

example : ppSTy (o16Ty% { type A : ⊥ .. ⊤ }) = "{type A : ⊥ .. ⊤}" := by decide +kernel

/-- `∧` binds tighter than `∨`, so a mixed chain needs no parentheses in
either order. -/
example : ppSTy (o16Ty% ⊤ ∧ ⊥ ∨ ⊤) = "⊤ ∧ ⊥ ∨ ⊤" := by decide +kernel
example : ppSTy (o16Ty% ⊤ ∨ (⊥ ∧ ⊤)) = "⊤ ∨ ⊥ ∧ ⊤" := by decide +kernel

/-- The other way round, a union inside an intersection keeps its
parentheses: the looser form does not disappear just because it sits on the
tighter one's side. -/
example : ppSTy (o16Ty% (⊤ ∨ ⊥) ∧ ⊤) = "(⊤ ∨ ⊥) ∧ ⊤" := by decide +kernel
example : ppSTy (o16Ty% ⊤ ∧ (⊥ ∨ ⊤)) = "⊤ ∧ (⊥ ∨ ⊤)" := by decide +kernel

/-- A chain of calls keeps building on the previous one, exactly as
`Notation.lean` parses it. -/
example : ppSTm (o16% x.m(y).n(z)) = "x.m(y).n(z)" := by decide +kernel

/-! ### A label's position shown beside its name

`recArgTable` pairs `"apply"` with position `0` in the caller's literal and
`"f"` with the very same position `0` in the argument's literal, which is
legal.  `labelName?` is a first
match, so it answers `"apply"` for position `0` wherever it is asked, and
`ppLabel` still prints the `0` beside it.  A reader who expects `"f"` there
and sees `apply#0` instead has caught exactly the ambiguity positional
labels allow. -/

example : ppLabel recArgTable 0 = "apply#0" := by decide +kernel
example : ppLabel recArgTable 2 = "A#2" := by decide +kernel
example : ppLabel [] 2 = "#2" := by decide +kernel

/-! ### Binders, named fresh under one another -/

/-- The outer `μ` binder takes `"x"`, the first name tried, and the method's
own parameter, printed one level under it, takes the next name the
environment does not hold, `"y"`. -/
example : ppTyAt recArgTable (NameEnv.nil.cons "z") 0 (NameEnv.nil.cons "z")
    (Oopsla16.Ty.TBind (.TAnd (.TFun 0 .TTop (.TSel (.abs .here) 2)) .TTop))
    = "μ(x. {def apply#0(y : ⊤) : y.A#2} ∧ ⊤)" := by decide +kernel

/-! ### The annotated syntax, self types included -/

/-- `RecursiveArg.prog`'s two literals both carry the self type their Curry
style method needs (`Ann.lean`), and the printer shows it after the colon.
Both self binders take `"x"` again, since each literal starts its own fresh
environment. -/
example : (resolve recArgTable recArgSrc).map (ppATmWith recArgTable .nil) = some
    ("new {x : {def apply#0(y : μ(y. {def apply#0(z : ⊤) : y.B#1})) : ⊤} ∧ ⊤ ⇒ "
      ++ "def apply#0(y) = y}.apply#0(new {x : {type A#2 : x.B#1 .. x.B#1} ∧ "
      ++ "{type B#1 : ⊤ .. ⊤} ∧ {def apply#0(y : ⊤) : x.A#2} ∧ ⊤ ⇒ "
      ++ "type A#2 = x.B#1  type B#1 = ⊤  def apply#0(y) = y})") := by
  decide +kernel

/-! ### Two runs, printed and pinned at their step counts -/

/-- The recursive argument example answers in three steps: the caller
allocates at `ℓ0`, the argument allocates at `ℓ1`, and the call returns the
argument's own location, found through its identity method.  Pinned beside
`Pipeline.lean`'s own count for this run. -/
example : ppRun recArgTable
    (compileAndRun { views := 2, sub := 6, typer := 6 } 3 recArgTable recArgSrc)
    = "⟨ℓ0 = {def apply#0(x) = x}, ℓ1 = {type A#2 = ℓ1.B#1  type B#1 = ⊤  "
      ++ "def apply#0(x) = x} | ℓ1⟩" := by
  decide +kernel

/-- `ex1` at the default budget, before any step: the store is empty and the
term is the literal the resolver returned. -/
example : ppRun ex1Table (compileAndRun {} 0 ex1Table ex1src)
    = "⟨· | new {x ⇒ def T#0(y : {type T#0 : ⊥ .. ⊤}) : {def T#0(z : y.T#0) : y.T#0} = "
      ++ "new {z ⇒ def T#0(w : y.T#0) : y.T#0 = w}}⟩" := by
  decide +kernel

/-- `ex1` answers in one step: the one literal allocates and the term is
already that location, since a bare literal is its own answer once
allocated. -/
example : ppRun ex1Table (compileAndRun {} 1 ex1Table ex1src)
    = "⟨ℓ0 = {def T#0(x : {type T#0 : ⊥ .. ⊤}) : {def T#0(y : x.T#0) : x.T#0} = "
      ++ "new {y ⇒ def T#0(z : x.T#0) : x.T#0 = z}} | ℓ0⟩" := by
  decide +kernel

/-- Nothing to print. -/
example : ppRun [] none = "did not compile" := by decide +kernel

end Checks

end Oopsla16Frontend
