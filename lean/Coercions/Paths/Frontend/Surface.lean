import Lean
import Coercions.Paths.FCdot.Debruijn

/-!
# The surface syntax of the paths front end

The elaborator of `Notation.lean` produces a value of one of the four
first-order, unindexed inductives below and nothing else.  Every
`Sig`-indexed construction happens afterwards, in the ordinary Lean functions
of `Resolve.lean`.  Interposing this surface term is what buys resolution,
let-insertion and typing as ordinary functions with ordinary theorems.

Beyond the vanilla surface, `SPath` names a term by its root and its field
steps, written `x.a.b`.  A path reaches into `SType` through three forms: a
stable field declaration `{val a : T}`, a singleton `p.type` and a selection
`p.A` at a path rather than at a bare variable.  A path in term position stays
nested projections.  `Resolve.lean` inserts the `let` that names each prefix.

Labels are strings here.  They are interned by a `LabelTable`, not by the
parser, so that the examples can pass the very table the hand-written terms of
`lean/Coercions/Paths/DotMNF/Examples.lean` use and get literal equalities.
The default table reads the sort off the first character, an upper case
letter a type label and anything else a term label, which is the paper's own
convention.

`Scoped` and `LabelsIn` are the two decidable side conditions under which
resolution is total, which is the totality theorem proved in `Resolve.lean`.
Both are `Bool` valued, so they are decidable by construction and need no
instance.  `SPath.Scoped` asks that a path's root is a bound name.  A field
step carries no name of its own, so it adds nothing to ask.  `SPath.LabelsIn`
asks that every field step is a term label.

Every mutual block here carries `termination_by structural`.  Lean infers
structural recursion for all of them without it, but later tests rely on
these functions reducing in the kernel, so the annotation is written out: a
later edit that would make Lean fall back to well founded recursion fails the
build instead of silently costing `by decide` and `by rfl`.  `#assert_no_wf`
checks that for a whole namespace at once: it walks the environment and fails
when a definition under the given namespace was compiled by well founded
recursion.

Nothing in this module is part of the metatheory.  No definition here lives
in the `Paths.DotMNF` or `Paths.FCdot` namespaces.
-/

namespace PathsFrontend

open Paths.FCdot (Label)

/-! ## The named abstract syntax -/

/-- A surface path: a variable and a chain of field steps, by name. -/
inductive SPath : Type where
  /-- A variable, by name. -/
  | var (x : String)
  /-- `p.a`, one more field step. -/
  | sel (p : SPath) (a : String)
deriving DecidableEq, Repr, Inhabited

/-- Surface types, with binders and labels as strings. -/
inductive SType : Type where
  /-- `⊤`. -/
  | top
  /-- `⊥`. -/
  | bot
  /-- `{A : S..T}`, a type member declaration. -/
  | typ (A : String) (S T : SType)
  /-- `{a : T}`, a term member declaration. -/
  | fld (a : String) (T : SType)
  /-- `{val a : T}`, a stable field declaration. -/
  | vfld (a : String) (T : SType)
  /-- `p.type`, the singleton of a path. -/
  | sngl (p : SPath)
  /-- `p.A`, a type selection at a path. -/
  | sel (p : SPath) (A : String)
  /-- `μ(x. T)`, a recursive self type. -/
  | mu (x : String) (T : SType)
  /-- `∀(x : S) T`, a dependent function type. -/
  | all (x : String) (S : SType) (T : SType)
  /-- `S ∧ T`, an intersection. -/
  | and (S T : SType)
deriving DecidableEq, Repr, Inhabited

mutual
/-- Surface terms.  Application and selection take arbitrary terms, which is
the point of a direct style front end.  Let insertion of `Resolve.lean` puts
them back into monadic normal form.  A path in term position, `x.a.b`, is
still nested `proj`, not a new form: `Resolve.lean` is what names its
prefixes. -/
inductive STm : Type where
  /-- A variable, by name. -/
  | var (x : String)
  /-- `λ(x : T). t`. -/
  | lam (x : String) (T : SType) (t : STm)
  /-- `ν(x : T. d)`.  The self type is annotated because `HasTy.obj` types the
  definitions against a context entry carrying it
  (`lean/Coercions/Paths/DotMNF/Typing.lean`) and `Value.obj` has no slot for
  it (`lean/Coercions/Paths/DotMNF/Syntax.lean`). -/
  | obj (x : String) (T : SType) (d : SDefs)
  /-- `t u`, direct style. -/
  | app (t u : STm)
  /-- `t.a`, direct style. -/
  | proj (t : STm) (a : String)
  /-- `let x = t in u`, with an optional result type.  The annotation is the
  first rung of the typer's avoidance ladder. -/
  | «let» (x : String) (ann : Option SType) (t u : STm)
/-- Surface definition members. -/
inductive SDefs : Type where
  /-- `{type A = T}`. -/
  | typ (A : String) (T : SType)
  /-- `{a = t}`. -/
  | trm (a : String) (t : STm)
  /-- `d ∧ e`. -/
  | and (d e : SDefs)
end

deriving instance DecidableEq, Repr for STm, SDefs

instance : Inhabited STm := ⟨.var ""⟩
instance : Inhabited SDefs := ⟨.typ "" .top⟩

/-! ## The label table

Type labels and term labels are disjoint in the target
(`lean/Coercions/Paths/FCdot/Debruijn.lean`), so a lookup that wants one sort
has to say so.  `labelTyp?` and `labelTrm?` are those two lookups. -/

/-- A label table maps surface names to target labels, first entry first. -/
abbrev LabelTable := List (String × Label)

/-- The first entry for a name, at whatever sort it was interned. -/
def labelFind? : LabelTable → String → Option Label
  | [], _ => none
  | (y, l) :: Λ, x => if x = y then some l else labelFind? Λ x

/-- The entry for a name, and `none` unless it is a type label. -/
def labelTyp? (Λ : LabelTable) (A : String) : Option Label :=
  match labelFind? Λ A with
  | some (.typ n) => some (.typ n)
  | _ => none

/-- The entry for a name, and `none` unless it is a term label. -/
def labelTrm? (Λ : LabelTable) (a : String) : Option Label :=
  match labelFind? Λ a with
  | some (.trm n) => some (.trm n)
  | _ => none

/-- The paper's convention: an upper case first character is a type label. -/
def nameIsTyp (x : String) : Bool :=
  match x.toList with
  | c :: _ => c.isUpper
  | [] => false

/-! ### The default table of a program

The names in label position, in order of first appearance, each numbered
within its own sort. -/

/-- The field steps of a surface path, with repetitions, root first. -/
def labelNamesPath : SPath → List String
  | .var _ => []
  | .sel p a => labelNamesPath p ++ [a]

/-- The names in label position of a surface type, with repetitions, in the
order they appear. -/
def labelNamesTy : SType → List String
  | .top | .bot => []
  | .typ A S T => A :: (labelNamesTy S ++ labelNamesTy T)
  | .fld a T => a :: labelNamesTy T
  | .vfld a T => a :: labelNamesTy T
  | .sngl p => labelNamesPath p
  | .sel p A => labelNamesPath p ++ [A]
  | .mu _ T => labelNamesTy T
  | .all _ S T => labelNamesTy S ++ labelNamesTy T
  | .and S T => labelNamesTy S ++ labelNamesTy T

mutual
/-- The names in label position of a surface term, with repetitions. -/
def labelNamesTm (e : STm) : List String :=
  match e with
  | .var _ => []
  | .lam _ T t => labelNamesTy T ++ labelNamesTm t
  | .obj _ T d => labelNamesTy T ++ labelNamesDefs d
  | .app t u => labelNamesTm t ++ labelNamesTm u
  | .proj t a => labelNamesTm t ++ [a]
  | .«let» _ ann t u =>
      (match ann with | none => [] | some U => labelNamesTy U)
        ++ labelNamesTm t ++ labelNamesTm u
termination_by structural e
/-- The names in label position of surface definitions, with repetitions. -/
def labelNamesDefs (d : SDefs) : List String :=
  match d with
  | .typ A T => A :: labelNamesTy T
  | .trm a t => a :: labelNamesTm t
  | .and d e => labelNamesDefs d ++ labelNamesDefs e
termination_by structural d
end

/-- Append a name unless it is already there. -/
def pushNew (acc : List String) (x : String) : List String :=
  if acc.contains x then acc else acc ++ [x]

/-- Deduplicate, keeping the first appearance of each name. -/
def dedupNames : List String → List String → List String
  | acc, [] => acc
  | acc, x :: xs => dedupNames (pushNew acc x) xs

/-- Number the names, each within its own sort. -/
def internNames : Nat → Nat → List String → LabelTable
  | _, _, [] => []
  | i, j, x :: xs =>
      if nameIsTyp x then (x, .typ i) :: internNames (i + 1) j xs
      else (x, .trm j) :: internNames i (j + 1) xs

/-- The default label table of a program: every name in label position, once,
in order of first appearance, at the sort its first character names. -/
def labelsOfProgram (e : STm) : LabelTable :=
  internNames 0 0 (dedupNames [] (labelNamesTm e))

/-! ## Scoping

`Scoped Γ` holds when every free name of the phrase is in `Γ`.  Innermost
binder first, matching the `NameEnv` used in `Resolve.lean`.  The self binder
of `ν(x : T. d)` scopes over its own annotation, as `Defs (s,x)` requires
(`lean/Coercions/Paths/DotMNF/Syntax.lean`).  The binder of a `let` does not
scope over the `let`'s annotation, matching the `U.weaken` of the rule
(`lean/Coercions/Paths/DotMNF/Typing.lean`).  A path's own field steps carry
no binder, so `SPath.Scoped` asks only that its root is in `Γ`. -/

/-- Every free name of a surface path is in the list: the root is, and a
field step adds no name of its own. -/
def SPath.Scoped : List String → SPath → Bool
  | Γ, .var x => Γ.contains x
  | Γ, .sel p _ => SPath.Scoped Γ p

/-- Every free name of a surface type is in the list. -/
def SType.Scoped : List String → SType → Bool
  | _, .top => true
  | _, .bot => true
  | Γ, .typ _ S T => SType.Scoped Γ S && SType.Scoped Γ T
  | Γ, .fld _ T => SType.Scoped Γ T
  | Γ, .vfld _ T => SType.Scoped Γ T
  | Γ, .sngl p => SPath.Scoped Γ p
  | Γ, .sel p _ => SPath.Scoped Γ p
  | Γ, .mu x T => SType.Scoped (x :: Γ) T
  | Γ, .all x S T => SType.Scoped Γ S && SType.Scoped (x :: Γ) T
  | Γ, .and S T => SType.Scoped Γ S && SType.Scoped Γ T

mutual
/-- Every free name of a surface term is in the list. -/
def STm.Scoped (Γ : List String) (e : STm) : Bool :=
  match e with
  | .var x => Γ.contains x
  | .lam x T t => SType.Scoped Γ T && STm.Scoped (x :: Γ) t
  | .obj x T d => SType.Scoped (x :: Γ) T && SDefs.Scoped (x :: Γ) d
  | .app t u => STm.Scoped Γ t && STm.Scoped Γ u
  | .proj t _ => STm.Scoped Γ t
  | .«let» x ann t u =>
      (match ann with | none => true | some U => SType.Scoped Γ U)
        && STm.Scoped Γ t && STm.Scoped (x :: Γ) u
termination_by structural e
/-- Every free name of surface definitions is in the list. -/
def SDefs.Scoped (Γ : List String) (d : SDefs) : Bool :=
  match d with
  | .typ _ T => SType.Scoped Γ T
  | .trm _ t => STm.Scoped Γ t
  | .and d e => SDefs.Scoped Γ d && SDefs.Scoped Γ e
termination_by structural d
end

/-! ## Labelling

`LabelsIn Λ` holds when every name in label position is in the table at the
sort its position demands.  Every field step of a path is a term label, read
by `SPath.LabelsIn`. -/

/-- Every field step of a surface path is a term label of the table. -/
def SPath.LabelsIn : LabelTable → SPath → Bool
  | _, .var _ => true
  | Λ, .sel p a => SPath.LabelsIn Λ p && (labelTrm? Λ a).isSome

/-- Every label of a surface type is in the table at the right sort. -/
def SType.LabelsIn : LabelTable → SType → Bool
  | _, .top => true
  | _, .bot => true
  | Λ, .typ A S T =>
      (labelTyp? Λ A).isSome && SType.LabelsIn Λ S && SType.LabelsIn Λ T
  | Λ, .fld a T => (labelTrm? Λ a).isSome && SType.LabelsIn Λ T
  | Λ, .vfld a T => (labelTrm? Λ a).isSome && SType.LabelsIn Λ T
  | Λ, .sngl p => SPath.LabelsIn Λ p
  | Λ, .sel p A => SPath.LabelsIn Λ p && (labelTyp? Λ A).isSome
  | Λ, .mu _ T => SType.LabelsIn Λ T
  | Λ, .all _ S T => SType.LabelsIn Λ S && SType.LabelsIn Λ T
  | Λ, .and S T => SType.LabelsIn Λ S && SType.LabelsIn Λ T

mutual
/-- Every label of a surface term is in the table at the right sort. -/
def STm.LabelsIn (Λ : LabelTable) (e : STm) : Bool :=
  match e with
  | .var _ => true
  | .lam _ T t => SType.LabelsIn Λ T && STm.LabelsIn Λ t
  | .obj _ T d => SType.LabelsIn Λ T && SDefs.LabelsIn Λ d
  | .app t u => STm.LabelsIn Λ t && STm.LabelsIn Λ u
  | .proj t a => STm.LabelsIn Λ t && (labelTrm? Λ a).isSome
  | .«let» _ ann t u =>
      (match ann with | none => true | some U => SType.LabelsIn Λ U)
        && STm.LabelsIn Λ t && STm.LabelsIn Λ u
termination_by structural e
/-- Every label of surface definitions is in the table at the right sort. -/
def SDefs.LabelsIn (Λ : LabelTable) (d : SDefs) : Bool :=
  match d with
  | .typ A T => (labelTyp? Λ A).isSome && SType.LabelsIn Λ T
  | .trm a t => (labelTrm? Λ a).isSome && STm.LabelsIn Λ t
  | .and d e => SDefs.LabelsIn Λ d && SDefs.LabelsIn Λ e
termination_by structural d
end

/-! ## The well-founded check

Every recursive definition of this front end is structural.  This command
fails the build the moment one of them is not: it walks the constants of a
namespace and reports every one whose compiled value calls into the
`WellFounded` namespace.  A plain `Nat` recursion compiles to
`WellFounded.Nat.fix`, not `WellFounded.fix` itself, so the test asks for the
namespace, not one exact name: a probe with one well-founded `Nat → Nat`
definition is caught either way. -/

open Lean Elab Command in
/-- Fails when a definition under the namespace `ns` is compiled by
well-founded recursion. -/
elab "#assert_no_wf " ns:ident : command => do
  let env ← getEnv
  let bad := env.constants.fold (init := #[]) fun acc n ci =>
    match ci with
    | .defnInfo d =>
      if ns.getId.isPrefixOf n &&
          d.value.getUsedConstants.any (`WellFounded).isPrefixOf then
        acc.push n
      else acc
    | _ => acc
  unless bad.isEmpty do throwError "well-founded definitions: {bad}"

/-! ## The test helper

A check that runs compiled code goes through `#eval expect ...`, where a
false result throws and so fails the build.  It is the form for a check too
slow to reduce in the kernel.  The tests of this module reduce, so they are
`by decide`. -/

/-- Fail the build, from `#eval`, when a check comes out false. -/
def expect (b : Bool) (msg : String) : IO Unit :=
  if b then pure () else throw (IO.userError msg)

/-! ## Sanity

Everything of this module is structural, so these reduce in the kernel and
are written in the repo's own idiom.  The program is
`λ(f : {A : ⊤..⊥}). ν(s : {a : ⊤} ∧ {B : ⊤..⊤}. {a = f} ∧ {type B = ⊤})`,
exactly the vanilla sample, since it touches no path. -/

/-- The sample program of the checks below. -/
private def sampleProgram : STm :=
  .lam "f" (.typ "A" .top .bot)
    (.obj "s" (.and (.fld "a" .top) (.typ "B" .top .top))
      (.and (.trm "a" (.var "f")) (.typ "B" .top)))

/-- Names in label position, once each, in order of first appearance, and the
sort read off the first character. -/
example : labelsOfProgram sampleProgram = [("A", .typ 0), ("a", .trm 0), ("B", .typ 1)] := by
  decide

/-- A type label is not a term label. -/
example : labelTrm? (labelsOfProgram sampleProgram) "A" = none := by decide

/-- And a term label is not a type label. -/
example : labelTyp? (labelsOfProgram sampleProgram) "a" = none := by decide

/-- The sample program is closed and its labels are all in its own table. -/
example : STm.Scoped [] sampleProgram = true := by decide

example : STm.LabelsIn (labelsOfProgram sampleProgram) sampleProgram = true := by decide

/-- An empty table labels nothing. -/
example : STm.LabelsIn [] sampleProgram = false := by decide

/-- A free name is out of scope, and a selection needs its receiver. -/
example : STm.Scoped [] (.var "x") = false := by decide

/-- A path's own root is what `SPath.Scoped` asks for. -/
example : SPath.Scoped ["x"] (.var "x") = true := by decide

example : SPath.Scoped [] (.var "x") = false := by decide

/-- A field step adds no name of its own: the root still decides it. -/
example : SPath.Scoped ["x"] (.sel (.var "x") "a") = true := by decide

example : SPath.Scoped [] (.sel (.var "x") "a") = false := by decide

/-- Every field step of a path must be a term label. -/
example : SPath.LabelsIn [("a", .trm 0)] (.sel (.var "x") "a") = true := by decide

example : SPath.LabelsIn [] (.sel (.var "x") "a") = false := by decide

/-- A type selection reads its receiver from a path. -/
example : SType.Scoped ["x"] (.sel (.var "x") "A") = true := by decide

example : SType.Scoped [] (.sel (.var "x") "A") = false := by decide

example : SType.LabelsIn [("A", .typ 0), ("a", .trm 0)] (.sel (.sel (.var "x") "a") "A") = true := by
  decide

/-- A stable field declaration scopes and labels exactly as a term field. -/
example : SType.Scoped ["x"] (.vfld "a" (.sel (.var "x") "A")) = true := by decide

example : SType.LabelsIn [("A", .typ 0), ("a", .trm 0)] (.vfld "a" (.sel (.var "x") "A")) = true := by
  decide

/-- A singleton reads its receiver from a path, same as a type selection. -/
example : SType.Scoped ["x"] (.sngl (.sel (.var "x") "a")) = true := by decide

example : SType.Scoped [] (.sngl (.var "x")) = false := by decide

example : SType.LabelsIn [("a", .trm 0)] (.sngl (.sel (.var "x") "a")) = true := by decide

example : SType.LabelsIn [] (.sngl (.sel (.var "x") "a")) = false := by decide

/-- The self binder of `ν` scopes over its own annotation. -/
example : STm.Scoped [] (.obj "s" (.sel (.var "s") "A") (.typ "B" .top)) = true := by decide

/-- The binder of a `let` does not scope over the `let`'s annotation. -/
example :
    STm.Scoped [] (.«let» "x" (some (.sel (.var "x") "A")) (.var "y") (.var "x")) = false := by
  decide

end PathsFrontend
