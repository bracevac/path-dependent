import Coercions.CapturesCC.FCdot.Debruijn
import Lean

/-!
# The surface syntax of the CapturesCC front end

The elaborator of `Notation.lean` produces a value of one of the named
inductives below and nothing else.  Every `Sig`-indexed construction happens
afterwards, in the ordinary Lean functions of `Resolve.lean`.  The named
syntax, the label table, and the two side conditions `Scoped` and `LabelsIn`
follow the vanilla ones of `lean/Coercions/Frontend/Surface.lean`.

Shapes, capturing types and answers are three separate sorts here, not one.
A shape is the plain type former: a declaration, a selection, an
intersection, an arrow or a box.  A type is a shape paired with a capture
set, written `S ^ C`.  An answer is a type, or a type under one capture
binder bounded by a set of the enclosing scope, the shape an existential
reading of `fresh` needs.  Keeping the three apart means a written `∃` can
only sit where an answer is expected: the codomain of an arrow and nowhere
else.

An arrow carries an optional name for its own capture binder, written
`∀[c](x : T) U` when named and `∀(x : T) U` otherwise, and a lambda carries
the same optional name for the arrow it occurs at, `λ[c](x : T). t`.  An
object literal is just a shape and its definitions: it carries no capture
set of its own, since the calculus reads an object's set off its class
root, not off a written annotation.  `letex ⟨c, x⟩ = t in u` unpacks an
existential answer by hand, opening a capture binder for the witness and a
term binder for the payload.  The ascription `(t : T)` is kept, a checking
point the calculus itself has no term for.

Labels are strings here, interned by a `LabelTable` the caller supplies, as
in the vanilla line.  A capture member sits at a type label, the same slot a
type-member bound sits at, since the version desugars a capture-set
parameter to a type parameter.

The capture atom `any` stands for the receiver's own outer set and `fresh`
for a freshly allocated one.  Both are inert in resolution, carried through
unread, since what each one reads back to is a function of the
context the typer builds, not of the surface term alone.

Every mutual block here carries `termination_by structural`, so the kernel
reduces every function of this module and the sanity checks below are all
`by decide`.
-/

namespace CapturesCCFrontend

open CapturesCC.FCdot (Label)

/-! ## The named abstract syntax -/

/-- A capture atom: a name, written `x`, `κ`, or the two-part `x.C`, the
atom `any` standing for the receiver's own outer set, or the atom `fresh`
standing for a freshly allocated one. -/
inductive SAtom : Type where
  /-- A term variable or a platform capability, by name. -/
  | name (x : String)
  /-- `x.C`, a capture member selection. -/
  | sel (x C : String)
  /-- `any`. -/
  | any
  /-- `fresh`. -/
  | fresh
deriving DecidableEq, Repr, Inhabited

/-- A capture set, written `{a₁, …, aₙ}`. -/
abbrev SCap := List SAtom

/-- Add a name to the front of a list of names, only when the name is
written.  Used to open an arrow's own capture binder, which a program may
leave anonymous. -/
def optCons (o : Option String) (l : List String) : List String :=
  match o with
  | none => l
  | some n => n :: l

mutual
/-- Surface shapes, with binders and labels as strings.  Bounds of a type
member and of a capture member are shapes, as the calculus reads them. -/
inductive SShape : Type where
  /-- `⊤`. -/
  | top
  /-- `⊥`. -/
  | bot
  /-- `{A : S..T}`, a type member declaration. -/
  | typ (A : String) (S T : SShape)
  /-- `{a : T}`, a field declaration.  Its type is a capturing type. -/
  | fld (a : String) (T : SType)
  /-- `{C^ : c₁..c₂}`, a capture member declaration, at a type label. -/
  | cap (C : String) (lo hi : SCap)
  /-- `x.A`, a type selection on a variable. -/
  | sel (x : String) (A : String)
  /-- `μ(x. S)`, a recursive self shape. -/
  | mu (x : String) (S : SShape)
  /-- `∀(x : T) U` or `∀[c](x : T) U`, a dependent arrow on a capturing
  domain and an answer codomain.  `κ` names the arrow's own capture binder
  when the program writes it. -/
  | all (κ : Option String) (x : String) (T : SType) (U : SAns)
  /-- `S ∧ T`, an intersection of shapes. -/
  | and (S T : SShape)
  /-- `□ T`, the box former.  Inert, not a declaration. -/
  | box (T : SType)
/-- A capturing type: a shape with a written capture set, `S ^ C`. -/
inductive SType : Type where
  | capt (S : SShape) (C : SCap)
/-- An answer: a type, or a type under one capture binder bounded by a set
of the enclosing scope, written `∃[c ⊑ C] T`. -/
inductive SAns : Type where
  | ty (T : SType)
  | ex (κ : String) (C : SCap) (T : SType)
end

deriving instance DecidableEq, Repr for SShape, SType, SAns

instance : Inhabited SShape := ⟨.top⟩
instance : Inhabited SType := ⟨.capt .top []⟩
instance : Inhabited SAns := ⟨.ty default⟩

mutual
/-- Surface terms.  Application and selection take arbitrary terms, which is
the point of a direct style front end.  Let insertion of `Resolve.lean` puts
them back into monadic normal form. -/
inductive STm : Type where
  /-- A variable, by name. -/
  | var (x : String)
  /-- `λ(x : T). t` or `λ[c](x : T). t`, `κ` naming the arrow's own capture
  binder when the program writes it. -/
  | lam (κ : Option String) (x : String) (T : SType) (t : STm)
  /-- `ν(x : S. d)`, an object literal: the self shape and its definitions,
  no capture set of its own. -/
  | obj (x : String) (S : SShape) (d : SDefs)
  /-- `t u`, direct style. -/
  | app (t u : STm)
  /-- `t.a`, direct style. -/
  | proj (t : STm) (a : String)
  /-- `let x = t in u`, with an optional result answer. -/
  | «let» (x : String) (ann : Option SAns) (t u : STm)
  /-- `let ⟨c, x⟩ = t in u`, an explicit unpacking of an existential
  answer: a capture binder for the witness, then a term binder for the
  payload. -/
  | letex (κ x : String) (t u : STm)
  /-- `□ t`, direct style, a box value written by hand. -/
  | box (t : STm)
  /-- `C ⊸ t`, direct style, an unboxing written by hand. -/
  | unbox (C : SCap) (t : STm)
  /-- `(t : T)`, a checking point.  Erased, the calculus has no such term. -/
  | asc (t : STm) (T : SType)
/-- Surface definition members. -/
inductive SDefs : Type where
  /-- `{type A = S}`. -/
  | typ (A : String) (S : SShape)
  /-- `{C^ = c}`, a capture definition. -/
  | cap (C : String) (c : SCap)
  /-- `{a = t}`. -/
  | trm (a : String) (t : STm)
  /-- `d ∧ e`. -/
  | and (d e : SDefs)
end

deriving instance DecidableEq, Repr for STm, SDefs

instance : Inhabited STm := ⟨.var ""⟩
instance : Inhabited SDefs := ⟨.typ "" .top⟩

/-- A whole program: the platform capabilities, outermost first, and the
body run against them. -/
structure SProg where
  platform : List String
  body : STm
deriving DecidableEq, Repr

/-! ## The label table

Type labels and term labels are disjoint in the target
(`lean/Coercions/CapturesCC/FCdot/Debruijn.lean`), so a lookup that wants one
sort has to say so.  `labelTyp?` and `labelTrm?` are those two lookups.  A
capture member's label sits at the type sort, the same slot a type-member
bound sits at. -/

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

/-! ## Capture sets: scoping and labelling

A capture set binds no name of its own, so these two functions are plain
list recursions, used from the shape, type, answer and term side conditions
below. -/

/-- Every name of a capture set is in scope.  `K` lists the capture
binders, `Γ` the term variables.  A plain name may be either kind, the
receiver of `x.C` must be a term variable, and `any` and `fresh` name
nothing. -/
def SCap.Scoped (K Γ : List String) : SCap → Bool
  | [] => true
  | .name x :: c => (Γ.contains x || K.contains x) && SCap.Scoped K Γ c
  | .sel x _ :: c => Γ.contains x && SCap.Scoped K Γ c
  | .any :: c => SCap.Scoped K Γ c
  | .fresh :: c => SCap.Scoped K Γ c

/-- Every capture-member selection of a capture set is at a type label.
`any` and `fresh` and a plain name name no label. -/
def SCap.LabelsIn (Λ : LabelTable) : SCap → Bool
  | [] => true
  | .name _ :: c => SCap.LabelsIn Λ c
  | .sel _ C :: c => (labelTyp? Λ C).isSome && SCap.LabelsIn Λ c
  | .any :: c => SCap.LabelsIn Λ c
  | .fresh :: c => SCap.LabelsIn Λ c

/-! ## Scoping

`Scoped K Γ` holds when every free name of the phrase is in scope at the
kind its position needs.  `K` lists the capture binders, the platform
capabilities among them, and `Γ` the term variables.  A name in term
position, the receiver of a selection `x.A` and the receiver of a capture
member `x.C` must be term variables.  A plain name in a capture set may be
either kind.

An arrow's own capture binder, named or not, scopes over its domain and, with
the parameter, over its codomain: `optCons κ K` is the capture context
either way, naming the binder when the program does.  The existential
binder of an answer scopes over its type alone, and its own bound is read
in the outer scope.  The binder of a `let` does not scope over the `let`'s
annotation, and an unpacking's two binders scope only over its own payload.
None of `typ`, `cap`, `fld` or the definition forms binds a name over a
body.  Only `mu`, `all`, the capture binder of `all` and of `ex`, the self
of `obj`, and the two binders of `let` and `letex` do. -/

mutual
/-- Every free name of a surface shape is in scope. -/
def SShape.Scoped (K Γ : List String) (S : SShape) : Bool :=
  match S with
  | .top => true
  | .bot => true
  | .typ _ S T => SShape.Scoped K Γ S && SShape.Scoped K Γ T
  | .fld _ T => SType.Scoped K Γ T
  | .cap _ lo hi => SCap.Scoped K Γ lo && SCap.Scoped K Γ hi
  | .sel x _ => Γ.contains x
  | .mu x S => SShape.Scoped K (x :: Γ) S
  | .all κ x T U => SType.Scoped (optCons κ K) Γ T && SAns.Scoped (optCons κ K) (x :: Γ) U
  | .and S T => SShape.Scoped K Γ S && SShape.Scoped K Γ T
  | .box T => SType.Scoped K Γ T
termination_by structural S
/-- Every free name of a surface type is in scope. -/
def SType.Scoped (K Γ : List String) (T : SType) : Bool :=
  match T with
  | .capt S C => SShape.Scoped K Γ S && SCap.Scoped K Γ C
termination_by structural T
/-- Every free name of a surface answer is in scope.  The existential's own
bound is read in the outer scope.  Its binder scopes over the type alone. -/
def SAns.Scoped (K Γ : List String) (U : SAns) : Bool :=
  match U with
  | .ty T => SType.Scoped K Γ T
  | .ex κ C T => SCap.Scoped K Γ C && SType.Scoped (κ :: K) Γ T
termination_by structural U
end

mutual
/-- Every free name of a surface term is in scope. -/
def STm.Scoped (K Γ : List String) (e : STm) : Bool :=
  match e with
  | .var x => Γ.contains x
  | .lam κ x T t => SType.Scoped (optCons κ K) Γ T && STm.Scoped (optCons κ K) (x :: Γ) t
  | .obj x S d => SShape.Scoped K (x :: Γ) S && SDefs.Scoped K (x :: Γ) d
  | .app t u => STm.Scoped K Γ t && STm.Scoped K Γ u
  | .proj t _ => STm.Scoped K Γ t
  | .«let» x ann t u =>
      (match ann with | none => true | some U => SAns.Scoped K Γ U)
        && STm.Scoped K Γ t && STm.Scoped K (x :: Γ) u
  | .letex κ x t u => STm.Scoped K Γ t && STm.Scoped (κ :: K) (x :: Γ) u
  | .box t => STm.Scoped K Γ t
  | .unbox C t => SCap.Scoped K Γ C && STm.Scoped K Γ t
  | .asc t T => STm.Scoped K Γ t && SType.Scoped K Γ T
termination_by structural e
/-- Every free name of surface definitions is in scope. -/
def SDefs.Scoped (K Γ : List String) (d : SDefs) : Bool :=
  match d with
  | .typ _ S => SShape.Scoped K Γ S
  | .cap _ c => SCap.Scoped K Γ c
  | .trm _ t => STm.Scoped K Γ t
  | .and d e => SDefs.Scoped K Γ d && SDefs.Scoped K Γ e
termination_by structural d
end

/-! ## Labelling

`LabelsIn Λ` holds when every name in label position is in the table at the
sort its position demands.  A capture member's own label, like a
type-member bound's, is a type label. -/

mutual
/-- Every label of a surface shape is in the table at the right sort. -/
def SShape.LabelsIn (Λ : LabelTable) (S : SShape) : Bool :=
  match S with
  | .top => true
  | .bot => true
  | .typ A S T => (labelTyp? Λ A).isSome && SShape.LabelsIn Λ S && SShape.LabelsIn Λ T
  | .fld a T => (labelTrm? Λ a).isSome && SType.LabelsIn Λ T
  | .cap C lo hi => (labelTyp? Λ C).isSome && SCap.LabelsIn Λ lo && SCap.LabelsIn Λ hi
  | .sel _ A => (labelTyp? Λ A).isSome
  | .mu _ S => SShape.LabelsIn Λ S
  | .all _ _ T U => SType.LabelsIn Λ T && SAns.LabelsIn Λ U
  | .and S T => SShape.LabelsIn Λ S && SShape.LabelsIn Λ T
  | .box T => SType.LabelsIn Λ T
termination_by structural S
/-- Every label of a surface type is in the table at the right sort. -/
def SType.LabelsIn (Λ : LabelTable) (T : SType) : Bool :=
  match T with
  | .capt S C => SShape.LabelsIn Λ S && SCap.LabelsIn Λ C
termination_by structural T
/-- Every label of a surface answer is in the table at the right sort. -/
def SAns.LabelsIn (Λ : LabelTable) (U : SAns) : Bool :=
  match U with
  | .ty T => SType.LabelsIn Λ T
  | .ex _ C T => SCap.LabelsIn Λ C && SType.LabelsIn Λ T
termination_by structural U
end

mutual
/-- Every label of a surface term is in the table at the right sort. -/
def STm.LabelsIn (Λ : LabelTable) (e : STm) : Bool :=
  match e with
  | .var _ => true
  | .lam _ _ T t => SType.LabelsIn Λ T && STm.LabelsIn Λ t
  | .obj _ S d => SShape.LabelsIn Λ S && SDefs.LabelsIn Λ d
  | .app t u => STm.LabelsIn Λ t && STm.LabelsIn Λ u
  | .proj t a => STm.LabelsIn Λ t && (labelTrm? Λ a).isSome
  | .«let» _ ann t u =>
      (match ann with | none => true | some U => SAns.LabelsIn Λ U)
        && STm.LabelsIn Λ t && STm.LabelsIn Λ u
  | .letex _ _ t u => STm.LabelsIn Λ t && STm.LabelsIn Λ u
  | .box t => STm.LabelsIn Λ t
  | .unbox C t => SCap.LabelsIn Λ C && STm.LabelsIn Λ t
  | .asc t T => STm.LabelsIn Λ t && SType.LabelsIn Λ T
termination_by structural e
/-- Every label of surface definitions is in the table at the right sort. -/
def SDefs.LabelsIn (Λ : LabelTable) (d : SDefs) : Bool :=
  match d with
  | .typ A S => (labelTyp? Λ A).isSome && SShape.LabelsIn Λ S
  | .cap C c => (labelTyp? Λ C).isSome && SCap.LabelsIn Λ c
  | .trm a t => (labelTrm? Λ a).isSome && STm.LabelsIn Λ t
  | .and d e => SDefs.LabelsIn Λ d && SDefs.LabelsIn Λ e
termination_by structural d
end

/-! ## The test helper

A check that runs compiled code instead of reducing in the kernel is
written `#eval expect ...`, where a false result throws and so fails the
build.  Every check of this module is structural and reduces, so these are
all `by decide`. -/

/-- Fail the build, from `#eval`, when a check comes out false. -/
def expect (b : Bool) (msg : String) : IO Unit :=
  if b then pure () else throw (IO.userError msg)

/-! ## `#assert_no_wf`

Every recursive definition of this front end is meant to compile by
structural recursion, so that the kernel reduces it and a per-example fact
is a `decide` theorem.  A clause a later edit adds without a matching
`termination_by structural` case can make Lean fall back to well founded
recursion silently.  This command catches that at `lake build` time instead
of at the much later point where `decide` stops reducing. -/

open Lean Elab Command in
/-- Fails when a definition under the namespace `ns` is compiled by
well-founded recursion.  The compiler picks a specialised combinator for the
measure's type, `WellFounded.Nat.fix` for a `Nat` measure rather than the
generic `WellFounded.fix`, so the test is membership in the whole
`WellFounded` namespace, not equality with one constant. -/
elab "#assert_no_wf " ns:ident : command => do
  let env ← getEnv
  let bad := env.constants.fold (init := #[]) fun acc n ci =>
    match ci with
    | .defnInfo d =>
      if ns.getId.isPrefixOf n && d.value.getUsedConstants.any (`WellFounded).isPrefixOf then
        acc.push n
      else acc
    | _ => acc
  unless bad.isEmpty do throwError "well-founded definitions: {bad}"

/-! ## Sanity

Everything above is structural, so these reduce in the kernel.  The sample
program is `λ[c](f : ⊤). ν(s : {a : ⊤} ∧ {C^ : {}..{f}}. {a = f} ∧ {C^ =
{f}})`, and its label table names `a` a term label and `C` a type label. -/

/-- A small hand table: `a` a term label, `C` a type label. -/
private def Λ0 : LabelTable := [("a", .trm 0), ("C", .typ 0)]

/-- The sample program of the checks below. -/
private def sampleProgram : STm :=
  .lam (some "c") "f" (.capt .top [])
    (.obj "s"
      (.and (.fld "a" (.capt .top [])) (.cap "C" [] [SAtom.name "f"]))
      (.and (.trm "a" (.var "f")) (.cap "C" [SAtom.name "f"])))

example : STm.Scoped [] [] sampleProgram = true := by decide
example : STm.LabelsIn Λ0 sampleProgram = true := by decide

/-- A free name is out of scope. -/
example : STm.Scoped [] [] (.var "x") = false := by decide

/-- The self binder of `ν` scopes over its own shape. -/
example : STm.Scoped [] [] (.obj "s" (.sel "s" "A") (.typ "B" .top)) = true := by decide

/-- The binder of a `let` does not scope over the `let`'s annotation. -/
example :
    STm.Scoped [] [] (.«let» "x" (some (.ty (.capt (.sel "x" "A") []))) (.var "y") (.var "x"))
      = false := by decide

/-- `cap`: a capture member's bounds are scoped as capture sets. -/
example : SShape.Scoped ["k1"] [] (.cap "C" [SAtom.name "k1"] [SAtom.name "k1"]) = true := by
  decide

example : SShape.Scoped [] [] (.cap "C" [SAtom.name "k1"] []) = false := by decide

/-- `box`: scoping passes through. -/
example : SShape.Scoped [] ["f"] (.box (.capt .top [SAtom.name "f"])) = true := by decide

/-- `capt`: both the shape and the written set are scoped. -/
example : SType.Scoped [] ["f"] (.capt .top [SAtom.name "f"]) = true := by decide

example : SType.Scoped [] [] (.capt .top [SAtom.name "f"]) = false := by decide

/-- `fresh` names nothing, so a set holding only it is scoped anywhere. -/
example : SCap.Scoped [] [] [SAtom.fresh] = true := by decide

/-- `all`: an anonymous arrow binder scopes its domain under `K` alone, and
its codomain under `K` and the parameter. -/
example : SShape.Scoped [] [] (.all none "x" (.capt .top []) (.ty (.capt (.sel "x" "A") []))) =
    true := by decide

/-- `all`: a named arrow binder is in scope in the domain's set, and stays
in scope for the codomain. -/
example :
    SShape.Scoped [] [] (.all (some "c") "x" (.capt .top [SAtom.name "c"])
      (.ty (.capt .top [SAtom.name "c"]))) = true := by decide

example : SShape.Scoped [] [] (.all none "x" (.capt .top [SAtom.name "c"]) (.ty (.capt .top []))) =
    false := by decide

/-- `ex`: the binder scopes over the type, and the written bound is read in
the outer scope, not under its own binder. -/
example : SAns.Scoped [] [] (.ex "c" [] (.capt .top [SAtom.name "c"])) = true := by decide

example : SAns.Scoped [] [] (.ex "c" [SAtom.name "c"] (.capt .top [])) = false := by decide

/-- `lam`: a named arrow binder scopes the same way a written `all` does. -/
example :
    STm.Scoped [] [] (.lam (some "c") "x" (.capt .top [SAtom.name "c"]) (.var "x")) = true := by
  decide

/-- `letex`: both binders scope only over the payload, not over the bound
term. -/
example : STm.Scoped [] [] (.letex "c" "x" (.var "y") (.unbox [SAtom.name "c"] (.var "x"))) =
    false := by decide

example :
    STm.Scoped [] ["y"] (.letex "c" "x" (.var "y") (.unbox [SAtom.name "c"] (.var "x"))) =
      true := by decide

/-- `STm.box`: scoping passes through. -/
example : STm.Scoped [] ["f"] (.box (.var "f")) = true := by decide

/-- `STm.unbox`: the set and the operand are both scoped. -/
example : STm.Scoped ["k1"] ["e"] (.unbox [SAtom.name "k1"] (.var "e")) = true := by decide

example : STm.Scoped [] ["e"] (.unbox [SAtom.name "k1"] (.var "e")) = false := by decide

/-- `STm.asc`: the term and the type are both scoped. -/
example : STm.Scoped [] ["e"] (.asc (.var "e") (.capt .top [])) = true := by decide

/-- `SDefs.cap`: the value is scoped as a capture set. -/
example : SDefs.Scoped ["k1"] [] (.cap "C" [SAtom.name "k1"]) = true := by decide

example : SDefs.Scoped [] [] (.cap "C" [SAtom.name "k1"]) = false := by decide

/-- `cap`: the member's own label is in the table, at the type sort. -/
example : SShape.LabelsIn Λ0 (.cap "C" [] []) = true := by decide

example : SShape.LabelsIn [] (.cap "C" [] []) = false := by decide

/-- A capture member selection in a set needs its label too. -/
example : SType.LabelsIn Λ0 (.capt .top [SAtom.sel "s" "C"]) = true := by decide

example : SType.LabelsIn Λ0 (.capt .top [SAtom.sel "s" "g"]) = false := by decide

/-- `box`: labelling passes through. -/
example : SShape.LabelsIn Λ0 (.box (.capt .top [SAtom.name "f"])) = true := by decide

/-- `all`: both the domain and the codomain are labelled. -/
example :
    SShape.LabelsIn Λ0 (.all none "x" (.capt .top [SAtom.sel "s" "C"])
      (.ty (.capt .top [SAtom.sel "s" "C"]))) = true := by decide

example :
    SShape.LabelsIn Λ0 (.all none "x" (.capt .top [SAtom.sel "s" "g"]) (.ty (.capt .top []))) =
      false := by decide

/-- `ex`: the type under the binder is labelled.  The written bound is not a
label position. -/
example : SAns.LabelsIn Λ0 (.ex "c" [] (.capt .top [SAtom.sel "s" "C"])) = true := by decide

example : SAns.LabelsIn Λ0 (.ex "c" [] (.capt .top [SAtom.sel "s" "g"])) = false := by decide

/-- `STm.box`: labelling passes through. -/
example : STm.LabelsIn Λ0 (.box (.var "f")) = true := by decide

/-- `STm.unbox`: the set is labelled too. -/
example : STm.LabelsIn Λ0 (.unbox [SAtom.sel "s" "C"] (.var "e")) = true := by decide

example : STm.LabelsIn Λ0 (.unbox [SAtom.sel "s" "g"] (.var "e")) = false := by decide

/-- `STm.asc`: the term and the type are both labelled. -/
example : STm.LabelsIn Λ0 (.asc (.var "e") (.capt .top [SAtom.sel "s" "C"])) = true := by decide

/-- `STm.letex`: both the bound term and the payload are labelled. -/
example :
    STm.LabelsIn Λ0 (.letex "c" "x" (.var "e") (.unbox [SAtom.sel "s" "C"] (.var "x"))) =
      true := by decide

example :
    STm.LabelsIn Λ0 (.letex "c" "x" (.var "e") (.unbox [SAtom.sel "s" "g"] (.var "x"))) =
      false := by decide

/-- `SDefs.cap`: the member's own label is in the table, and its value
labelled. -/
example : SDefs.LabelsIn Λ0 (.cap "C" [SAtom.sel "s" "C"]) = true := by decide

example : SDefs.LabelsIn [] (.cap "C" []) = false := by decide

/-- A capture binder is no term variable: `k1` is in scope in a capture set
and out of scope in term position. -/
example : STm.Scoped ["k1"] [] (.var "k1") = false := by decide
example : SType.Scoped ["k1"] [] (.capt .top [SAtom.name "k1"]) = true := by decide

/-- The receiver of a capture member is a term variable. -/
example : SType.Scoped ["k1"] [] (.capt .top [SAtom.sel "k1" "C"]) = false := by decide

end CapturesCCFrontend
