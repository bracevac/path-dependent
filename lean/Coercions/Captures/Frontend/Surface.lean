import Coercions.Captures.FCdot.Debruijn
import Lean

/-!
# Surface syntax

The elaborator of `Notation.lean` produces one of the inductives `SCapAtom`,
`SType`, `STm`, `SDefs` and the abbreviation `SCap`, and nothing else.
Names and labels are strings.  `Resolve.lean` does the `Sig`-indexed work.

The syntax, the label table and the side conditions `Scoped` and `LabelsIn`
follow `lean/Coercions/Frontend/Surface.lean`, with a clause for each added
form: capture atoms and sets, the box, the unboxing, the ascription and the
capture member definition.  `Scoped` also tells term variables from capture
binders, since a name in term position must be a term variable.

A capture member sits at a type label, the slot of a type-member bound, since
a capture-set parameter desugars to a type parameter.  A caller supplies the
`LabelTable` that interns labels.

Two further conditions are decided here.

* `AnyPlaced`.  The atom `any` stands for the receiver's own outer set, which
  `Ty.expand` reads back.  It is allowed only where that expansion reaches:
  the outer set of a parameter type, a field type, a `let` type, an ascription
  and a function codomain.  It is rejected at a type-member bound, at the
  lower bound of a capture member and under a box, as in `Shape.anyOk` and
  `Ty.anyOk` of `DotMNF/Syntax.lean`.
* `CaptPlaced`.  A written `S ^ C` may stand only where the resolver reads it.

`NoAny` is the stricter condition: no `any` at all.

Every definition is structural, so the checks at the end are `by decide`.
-/

namespace CapturesFrontend

open Captures.FCdot (Label)

/-! ## Syntax -/

/-- A capture atom: a name `x` or `κ`, a selection `x.C`, or `any`. -/
inductive SCapAtom : Type where
  /-- A term variable or a platform capability, by name. -/
  | name (x : String)
  /-- `x.C`, a capture member selection. -/
  | sel (x C : String)
  /-- `any`. -/
  | any
deriving DecidableEq, Repr, Inhabited

/-- A capture set, written `{a₁, …, aₙ}`. -/
abbrev SCap := List SCapAtom

/-- Surface types.  A plain constructor reads as a shape.  Only `capt` carries
a written capture set. -/
inductive SType : Type where
  /-- `⊤`. -/
  | top
  /-- `⊥`. -/
  | bot
  /-- `{A : S..T}`, a type member declaration.  Bounds are shapes. -/
  | typ (A : String) (S T : SType)
  /-- `{a : T}`, a field declaration.  Its type is a capturing type. -/
  | fld (a : String) (T : SType)
  /-- `{C^ : c₁..c₂}`, a capture member declaration, at a type label. -/
  | cap (C : String) (lo hi : SCap)
  /-- `x.A`, a type selection on a variable. -/
  | sel (x : String) (A : String)
  /-- `μ(x. T)`, a recursive self shape. -/
  | mu (x : String) (T : SType)
  /-- `∀(x : S) T`, a dependent function shape, on capturing types. -/
  | all (x : String) (S T : SType)
  /-- `S ∧ T`, an intersection of shapes. -/
  | and (S T : SType)
  /-- `□ T`, the box former.  Inert, not a declaration. -/
  | box (T : SType)
  /-- `S ^ C`, a shape with a written capture set, a capturing type. -/
  | capt (S : SType) (C : SCap)
deriving DecidableEq, Repr, Inhabited

mutual
/-- Surface terms.  Application and selection take arbitrary terms.  Let
insertion in `Resolve.lean` restores monadic normal form. -/
inductive STm : Type where
  /-- A variable, by name. -/
  | var (x : String)
  /-- `λ(x : T). t`. -/
  | lam (x : String) (T : SType) (t : STm)
  /-- `ν(x : T. d)`.  If `T` is written `S ^ U`, `U` is the object's own
  capture set.  Otherwise the typer chooses it. -/
  | obj (x : String) (T : SType) (d : SDefs)
  /-- `t u`, direct style. -/
  | app (t u : STm)
  /-- `t.a`, direct style. -/
  | proj (t : STm) (a : String)
  /-- `let x = t in u`, with an optional result type. -/
  | «let» (x : String) (ann : Option SType) (t u : STm)
  /-- `□ t`, a box value. -/
  | box (t : STm)
  /-- `C ⊸ t`, an unboxing. -/
  | unbox (C : SCap) (t : STm)
  /-- `(t : T)`, a checking point.  Erased. -/
  | asc (t : STm) (T : SType)
/-- Surface definition members. -/
inductive SDefs : Type where
  /-- `{type A = T}`. -/
  | typ (A : String) (T : SType)
  /-- `{a = t}`. -/
  | trm (a : String) (t : STm)
  /-- `d ∧ e`. -/
  | and (d e : SDefs)
  /-- `{C^ = c}`, a capture definition. -/
  | cap (C : String) (c : SCap)
end

deriving instance DecidableEq, Repr for STm, SDefs

instance : Inhabited STm := ⟨.var ""⟩
instance : Inhabited SDefs := ⟨.typ "" .top⟩

/-! ## The label table

Type labels and term labels are disjoint in the target
(`FCdot/Debruijn.lean`), so a lookup names the sort it wants.  `labelTyp?` and
`labelTrm?` are the two lookups. -/

/-- A label table maps surface names to target labels, first entry first. -/
abbrev LabelTable := List (String × Label)

/-- The first entry for a name, of either sort. -/
def labelFind? : LabelTable → String → Option Label
  | [], _ => none
  | (y, l) :: Λ, x => if x = y then some l else labelFind? Λ x

/-- The entry for a name, if it is a type label. -/
def labelTyp? (Λ : LabelTable) (A : String) : Option Label :=
  match labelFind? Λ A with
  | some (.typ n) => some (.typ n)
  | _ => none

/-- The entry for a name, if it is a term label. -/
def labelTrm? (Λ : LabelTable) (a : String) : Option Label :=
  match labelFind? Λ a with
  | some (.trm n) => some (.trm n)
  | _ => none

/-! ## Capture sets -/

/-- Every name of a capture set is in scope.  `K` lists the capture binders and
`Γ` the term variables.  A plain name may be either kind, the receiver of `x.C`
must be a term variable, and `any` names nothing. -/
def SCap.Scoped (K Γ : List String) : SCap → Bool
  | [] => true
  | .name x :: c => (Γ.contains x || K.contains x) && SCap.Scoped K Γ c
  | .sel x _ :: c => Γ.contains x && SCap.Scoped K Γ c
  | .any :: c => SCap.Scoped K Γ c

/-- Every selection `x.C` of a capture set has a type label `C`. -/
def SCap.LabelsIn (Λ : LabelTable) : SCap → Bool
  | [] => true
  | .name _ :: c => SCap.LabelsIn Λ c
  | .sel _ C :: c => (labelTyp? Λ C).isSome && SCap.LabelsIn Λ c
  | .any :: c => SCap.LabelsIn Λ c

/-- No `any` atom anywhere in a capture set. -/
def SCap.NoAny : SCap → Bool
  | [] => true
  | .any :: _ => false
  | .name _ :: c => SCap.NoAny c
  | .sel _ _ :: c => SCap.NoAny c

/-! ## Scoping

`Scoped K Γ` holds when every free name is in scope at the kind its position
needs.  `K` lists the capture binders, the platform capabilities among them,
and `Γ` the term variables.  A name in term position and the receiver of
`x.A` or `x.C` must be term variables.  Every surface binder binds a term
variable, so `K` is fixed and only `Γ` grows.

The self binder of `ν(x : S ^ U. d)` scopes over the self shape `S` but not
over `U`, the object's own set.  The binder of a `let` does not scope over its
annotation.  Binders are `mu`, `all`, the self of `obj` and the variable of
`let`. -/

/-- Every free name of a surface type is in scope. -/
def SType.Scoped (K : List String) : List String → SType → Bool
  | _, .top => true
  | _, .bot => true
  | Γ, .typ _ S T => SType.Scoped K Γ S && SType.Scoped K Γ T
  | Γ, .fld _ T => SType.Scoped K Γ T
  | Γ, .cap _ lo hi => SCap.Scoped K Γ lo && SCap.Scoped K Γ hi
  | Γ, .sel x _ => Γ.contains x
  | Γ, .mu x T => SType.Scoped K (x :: Γ) T
  | Γ, .all x S T => SType.Scoped K Γ S && SType.Scoped K (x :: Γ) T
  | Γ, .and S T => SType.Scoped K Γ S && SType.Scoped K Γ T
  | Γ, .box T => SType.Scoped K Γ T
  | Γ, .capt S C => SType.Scoped K Γ S && SCap.Scoped K Γ C

/-- The self shape of an object's annotation: `S` of a written `S ^ U`,
the whole annotation otherwise. -/
def SType.selfShape : SType → SType
  | .capt S _ => S
  | T => T

/-- The object's own set, when the annotation is written `S ^ U`. -/
def SType.selfSet : SType → Option SCap
  | .capt _ U => some U
  | _ => none

/-- The self annotation of `ν(x : T. d)` is in scope: its shape under the
self binder, and a written outer set outside it. -/
def SType.SelfScoped (K Γ : List String) (x : String) (T : SType) : Bool :=
  SType.Scoped K (x :: Γ) T.selfShape &&
    (match T.selfSet with | none => true | some U => SCap.Scoped K Γ U)

mutual
/-- Every free name of a surface term is in scope. -/
def STm.Scoped (K Γ : List String) (e : STm) : Bool :=
  match e with
  | .var x => Γ.contains x
  | .lam x T t => SType.Scoped K Γ T && STm.Scoped K (x :: Γ) t
  | .obj x T d => SType.SelfScoped K Γ x T && SDefs.Scoped K (x :: Γ) d
  | .app t u => STm.Scoped K Γ t && STm.Scoped K Γ u
  | .proj t _ => STm.Scoped K Γ t
  | .«let» x ann t u =>
      (match ann with | none => true | some U => SType.Scoped K Γ U)
        && STm.Scoped K Γ t && STm.Scoped K (x :: Γ) u
  | .box t => STm.Scoped K Γ t
  | .unbox C t => SCap.Scoped K Γ C && STm.Scoped K Γ t
  | .asc t T => STm.Scoped K Γ t && SType.Scoped K Γ T
termination_by structural e
/-- Every free name of surface definitions is in scope. -/
def SDefs.Scoped (K Γ : List String) (d : SDefs) : Bool :=
  match d with
  | .typ _ T => SType.Scoped K Γ T
  | .trm _ t => STm.Scoped K Γ t
  | .and d e => SDefs.Scoped K Γ d && SDefs.Scoped K Γ e
  | .cap _ c => SCap.Scoped K Γ c
termination_by structural d
end

/-! ## Labelling

`LabelsIn Λ` holds when every name in label position is in the table at the
sort its position demands.  A capture member's label is a type label. -/

/-- Every label of a surface type is in the table at the right sort. -/
def SType.LabelsIn : LabelTable → SType → Bool
  | _, .top => true
  | _, .bot => true
  | Λ, .typ A S T =>
      (labelTyp? Λ A).isSome && SType.LabelsIn Λ S && SType.LabelsIn Λ T
  | Λ, .fld a T => (labelTrm? Λ a).isSome && SType.LabelsIn Λ T
  | Λ, .cap C lo hi =>
      (labelTyp? Λ C).isSome && SCap.LabelsIn Λ lo && SCap.LabelsIn Λ hi
  | Λ, .sel _ A => (labelTyp? Λ A).isSome
  | Λ, .mu _ T => SType.LabelsIn Λ T
  | Λ, .all _ S T => SType.LabelsIn Λ S && SType.LabelsIn Λ T
  | Λ, .and S T => SType.LabelsIn Λ S && SType.LabelsIn Λ T
  | Λ, .box T => SType.LabelsIn Λ T
  | Λ, .capt S C => SType.LabelsIn Λ S && SCap.LabelsIn Λ C

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
  | .box t => STm.LabelsIn Λ t
  | .unbox C t => SCap.LabelsIn Λ C && STm.LabelsIn Λ t
  | .asc t T => STm.LabelsIn Λ t && SType.LabelsIn Λ T
termination_by structural e
/-- Every label of surface definitions is in the table at the right sort. -/
def SDefs.LabelsIn (Λ : LabelTable) (d : SDefs) : Bool :=
  match d with
  | .typ A T => (labelTyp? Λ A).isSome && SType.LabelsIn Λ T
  | .trm a t => (labelTrm? Λ a).isSome && STm.LabelsIn Λ t
  | .and d e => SDefs.LabelsIn Λ d && SDefs.LabelsIn Λ e
  | .cap C c => (labelTyp? Λ C).isSome && SCap.LabelsIn Λ c
termination_by structural d
end

/-! ## `any` in its position

`Ty.anyOk` ignores the outer set of the type it tests.  `Shape.anyOk` of an
arrow asks `noAny` of the domain's own outer set.  For a type-member bound, a
capture member's lower bound and a box, it asks `noAny` of the whole operand.
Only `capt` of `SType` carries a set, so only it is read as a type, and its
set is ignored unless a position above asks for it.

`NoAny` says no `any` occurs anywhere.  `AnyPlaced` is weaker: every `any` is
where a position above reads it. -/

mutual
/-- No `any` anywhere in the type. -/
def SType.NoAny (T : SType) : Bool :=
  match T with
  | .top => true
  | .bot => true
  | .typ _ S T => SType.NoAny S && SType.NoAny T
  | .fld _ T => SType.NoAny T
  | .cap _ lo hi => SCap.NoAny lo && SCap.NoAny hi
  | .sel _ _ => true
  | .mu _ T => SType.NoAny T
  | .all _ S T => SType.NoAny S && SType.NoAny T
  | .and S T => SType.NoAny S && SType.NoAny T
  | .box T => SType.NoAny T
  | .capt S C => SCap.NoAny C && SType.NoAny S
termination_by structural T
/-- Every `any` of the type is where the expansion reads it.  The domain of
`all` also asks `NoAny` of its own written set, the arrow clause of
`Shape.anyOk`. -/
def SType.AnyPlaced (T : SType) : Bool :=
  match T with
  | .top => true
  | .bot => true
  | .typ _ S T => SType.NoAny S && SType.NoAny T
  | .fld _ T => SType.AnyPlaced T
  | .cap _ lo _ => SCap.NoAny lo
  | .sel _ _ => true
  | .mu _ T => SType.AnyPlaced T
  | .all _ S T =>
      (match S with | .capt _ C => SCap.NoAny C | _ => true)
        && SType.AnyPlaced S && SType.AnyPlaced T
  | .and S T => SType.AnyPlaced S && SType.AnyPlaced T
  | .box T => SType.NoAny T
  | .capt S _ => SType.AnyPlaced S
termination_by structural T
end

mutual
/-- Every `any` of a term's annotations is where it is read.  A set outside an
annotation, such as an unboxing's set or a capture definition's value, is
never expanded, so it holds no `any`.  A lambda's domain also asks `NoAny` of
its own written set.  The self shape of `obj` is read like a field type. -/
def STm.AnyPlaced (e : STm) : Bool :=
  match e with
  | .var _ => true
  | .lam _ T t =>
      (match T with | .capt _ C => SCap.NoAny C | _ => true)
        && SType.AnyPlaced T && STm.AnyPlaced t
  | .obj _ T d => SType.AnyPlaced T && SDefs.AnyPlaced d
  | .app t u => STm.AnyPlaced t && STm.AnyPlaced u
  | .proj t _ => STm.AnyPlaced t
  | .«let» _ ann t u =>
      (match ann with | none => true | some T => SType.AnyPlaced T)
        && STm.AnyPlaced t && STm.AnyPlaced u
  | .box t => STm.AnyPlaced t
  | .unbox C t => SCap.NoAny C && STm.AnyPlaced t
  | .asc t T => STm.AnyPlaced t && SType.AnyPlaced T
termination_by structural e
/-- Every `any` of definitions' annotations is where it is read.  A type
definition is like a type-member bound, so it holds no `any`, and neither
does a capture definition's value. -/
def SDefs.AnyPlaced (d : SDefs) : Bool :=
  match d with
  | .typ _ T => SType.NoAny T
  | .trm _ t => STm.AnyPlaced t
  | .and d e => SDefs.AnyPlaced d && SDefs.AnyPlaced e
  | .cap _ c => SCap.NoAny c
termination_by structural d
end

/-! ## Capturing types

A written `S ^ C` is a capturing type.  The resolver reads it at a type
position: a function's domain or codomain, a field type, a `let` type, an
ascription, a box operand and the self annotation of an object.  At a
type-member bound and at a type definition it boxes it, since a type argument
is boxed.  Elsewhere, in the body of a `μ`, an operand of `∧` or under a
written `^`, resolution fails.  `CaptPlaced` says no `S ^ C` sits at such a
position. -/

/-- The phrase is written `S ^ C`. -/
def SType.isCapt : SType → Bool
  | .capt _ _ => true
  | _ => false

/-- No written `S ^ C` sits at a shape position where resolution fails. -/
def SType.CaptPlaced (T : SType) : Bool :=
  match T with
  | .top => true
  | .bot => true
  | .typ _ S T => SType.CaptPlaced S && SType.CaptPlaced T
  | .fld _ T => SType.CaptPlaced T
  | .cap _ _ _ => true
  | .sel _ _ => true
  | .mu _ T => !T.isCapt && SType.CaptPlaced T
  | .all _ S T => SType.CaptPlaced S && SType.CaptPlaced T
  | .and S T => !S.isCapt && !T.isCapt && SType.CaptPlaced S && SType.CaptPlaced T
  | .box T => SType.CaptPlaced T
  | .capt S _ => !S.isCapt && SType.CaptPlaced S
termination_by structural T

mutual
/-- No written `S ^ C` of a term's annotations sits where resolution fails. -/
def STm.CaptPlaced (e : STm) : Bool :=
  match e with
  | .var _ => true
  | .lam _ T t => SType.CaptPlaced T && STm.CaptPlaced t
  | .obj _ T d => SType.CaptPlaced T && SDefs.CaptPlaced d
  | .app t u => STm.CaptPlaced t && STm.CaptPlaced u
  | .proj t _ => STm.CaptPlaced t
  | .«let» _ ann t u =>
      (match ann with | none => true | some T => SType.CaptPlaced T)
        && STm.CaptPlaced t && STm.CaptPlaced u
  | .box t => STm.CaptPlaced t
  | .unbox _ t => STm.CaptPlaced t
  | .asc t T => STm.CaptPlaced t && SType.CaptPlaced T
termination_by structural e
/-- No written `S ^ C` of definitions sits where resolution fails. -/
def SDefs.CaptPlaced (d : SDefs) : Bool :=
  match d with
  | .typ _ T => SType.CaptPlaced T
  | .trm _ t => STm.CaptPlaced t
  | .and d e => SDefs.CaptPlaced d && SDefs.CaptPlaced e
  | .cap _ _ => true
termination_by structural d
end

/-! ## Test helper -/

/-- Fail the build, from `#eval`, when a check is false. -/
def expect (b : Bool) (msg : String) : IO Unit :=
  if b then pure () else throw (IO.userError msg)

/-! ## `#assert_no_wf`

Every recursive definition of the front end is structural, so the kernel
reduces it.  Lean can fall back to well-founded recursion silently.  This
command catches that at build time. -/

open Lean Elab Command in
/-- Fails when a definition under the namespace `ns` is compiled by
well-founded recursion.  Lean picks a combinator specialised to the measure,
such as `WellFounded.Nat.fix`, so the test is membership in the `WellFounded`
namespace. -/
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

/-! ## Checks

The sample program is `λ(f : ⊤). ν(s : {a : ⊤} ∧ {C^ : {}..{f}}. {a = f} ∧
{C^ = {f}})`.  Its label table has `a` as a term label and `C` as a type
label. -/

/-- `a` is a term label, `C` a type label. -/
private def Λ0 : LabelTable := [("a", .trm 0), ("C", .typ 0)]

/-- The sample program. -/
private def sampleProgram : STm :=
  .lam "f" .top
    (.obj "s"
      (.and (.fld "a" .top) (.cap "C" [] [SCapAtom.name "f"]))
      (.and (.trm "a" (.var "f")) (.cap "C" [SCapAtom.name "f"])))

example : STm.Scoped [] [] sampleProgram = true := by decide
example : STm.LabelsIn Λ0 sampleProgram = true := by decide
example : STm.AnyPlaced sampleProgram = true := by decide

/-- A free name is out of scope. -/
example : STm.Scoped [] [] (.var "x") = false := by decide

/-- The self binder of `ν` scopes over its own annotation. -/
example : STm.Scoped [] [] (.obj "s" (.sel "s" "A") (.typ "B" .top)) = true := by decide

/-- The binder of a `let` does not scope over the `let`'s annotation. -/
example :
    STm.Scoped [] [] (.«let» "x" (some (.sel "x" "A")) (.var "y") (.var "x")) = false := by
  decide

/-- A capture member's bounds are scoped as capture sets. -/
example : SType.Scoped ["k1"] [] (.cap "C" [SCapAtom.name "k1"] [SCapAtom.name "k1"]) = true := by
  decide

example : SType.Scoped [] [] (.cap "C" [SCapAtom.name "k1"] []) = false := by decide

/-- Scoping passes through a box. -/
example : SType.Scoped [] ["f"] (.box (.capt .top [SCapAtom.name "f"])) = true := by decide

/-- Both the shape and the written set are scoped. -/
example : SType.Scoped [] ["f"] (.capt .top [SCapAtom.name "f"]) = true := by decide

example : SType.Scoped [] [] (.capt .top [SCapAtom.name "f"]) = false := by decide

/-- Scoping passes through `STm.box`. -/
example : STm.Scoped [] ["f"] (.box (.var "f")) = true := by decide

/-- The set and the operand of an unboxing are scoped. -/
example : STm.Scoped ["k1"] ["e"] (.unbox [SCapAtom.name "k1"] (.var "e")) = true := by decide

example : STm.Scoped [] ["e"] (.unbox [SCapAtom.name "k1"] (.var "e")) = false := by decide

/-- The term and the type of an ascription are scoped. -/
example : STm.Scoped [] ["e"] (.asc (.var "e") .top) = true := by decide

/-- The value of a capture definition is scoped as a capture set. -/
example : SDefs.Scoped ["k1"] [] (.cap "C" [SCapAtom.name "k1"]) = true := by decide

example : SDefs.Scoped [] [] (.cap "C" [SCapAtom.name "k1"]) = false := by decide

/-- A capture member's label is in the table at the type sort. -/
example : SType.LabelsIn Λ0 (.cap "C" [] []) = true := by decide

example : SType.LabelsIn [] (.cap "C" [] []) = false := by decide

/-- A capture member selection in a set needs its label too. -/
example : SType.LabelsIn Λ0 (.capt .top [SCapAtom.sel "s" "C"]) = true := by decide

example : SType.LabelsIn Λ0 (.capt .top [SCapAtom.sel "s" "g"]) = false := by decide

/-- Labelling passes through a box. -/
example : SType.LabelsIn Λ0 (.box (.capt .top [SCapAtom.name "f"])) = true := by decide

/-- The shape and the written set are both labelled. -/
example : SType.LabelsIn Λ0 (.capt .top [SCapAtom.sel "s" "C"]) = true := by decide

/-- Labelling passes through `STm.box`. -/
example : STm.LabelsIn Λ0 (.box (.var "f")) = true := by decide

/-- The set of an unboxing is labelled. -/
example : STm.LabelsIn Λ0 (.unbox [SCapAtom.sel "s" "C"] (.var "e")) = true := by decide

example : STm.LabelsIn Λ0 (.unbox [SCapAtom.sel "s" "g"] (.var "e")) = false := by decide

/-- The term and the type of an ascription are labelled. -/
example : STm.LabelsIn Λ0 (.asc (.var "e") (.capt .top [SCapAtom.name "f"])) = true := by decide

/-- A capture definition's label is in the table and its value is labelled. -/
example : SDefs.LabelsIn Λ0 (.cap "C" [SCapAtom.sel "s" "C"]) = true := by decide

example : SDefs.LabelsIn [] (.cap "C" []) = false := by decide

/-- `any` at the outer set of a field's type is where `Ty.anyOk` reads it. -/
example : SType.AnyPlaced (.fld "a" (.capt .top [.any])) = true := by decide

/-- `any` at a type-member bound is rejected. -/
example : SType.AnyPlaced (.typ "A" (.capt .top [.any]) .top) = false := by decide

/-- `any` at a capture member's lower bound is rejected.  The upper bound is
unchecked, as in `Shape.anyOk`. -/
example : SType.AnyPlaced (.cap "C" [.any] []) = false := by decide
example : SType.AnyPlaced (.cap "C" [] [.any]) = true := by decide

/-- `any` under a box is rejected. -/
example : SType.AnyPlaced (.box (.capt .top [.any])) = false := by decide

/-- `any` at the outer set of a function's domain is rejected.  Further in, at
a field or a codomain, it is admitted. -/
example : SType.AnyPlaced (.all "u" (.capt .top [.any]) .top) = false := by decide
example :
    SType.AnyPlaced (.all "u" .top (.capt (.fld "a" (.capt .top [.any])) [])) = true := by
  decide

/-- `any` at the outer set of a lambda's domain is rejected. -/
example : STm.AnyPlaced (.lam "x" (.capt .top [.any]) (.var "x")) = false := by decide

/-- `any` at the outer set of a `capt` node elsewhere is admitted. -/
example : SType.AnyPlaced (.capt .top [.any]) = true := by decide

/-- `any` passes through `box` and `asc`.  An unboxing's own set holds none. -/
example : STm.AnyPlaced (.box (.var "f")) = true := by decide
example : STm.AnyPlaced (.unbox [.any] (.var "e")) = false := by decide
example : STm.AnyPlaced (.asc (.var "e") (.capt .top [.any])) = true := by decide

/-- A capture definition's value holds no `any`. -/
example : SDefs.AnyPlaced (.cap "C" [.any]) = false := by decide
example : SDefs.AnyPlaced (.cap "C" []) = true := by decide

/-- A type definition, like a bound, holds no `any`. -/
example : SDefs.AnyPlaced (.typ "A" (.fld "a" (.capt .top [.any]))) = false := by decide

/-- A capture binder is no term variable. -/
example : STm.Scoped ["k1"] [] (.var "k1") = false := by decide
example : SType.Scoped ["k1"] [] (.capt .top [SCapAtom.name "k1"]) = true := by decide

/-- The receiver of a capture member is a term variable. -/
example : SType.Scoped ["k1"] [] (.capt .top [SCapAtom.sel "k1" "C"]) = false := by decide

/-- The set written on a self annotation is read outside the self binder. -/
example : STm.Scoped [] [] (.obj "s" (.capt (.fld "a" .top) [SCapAtom.name "s"]) (.trm "a" (.var "s")))
    = false := by decide
example : STm.Scoped [] [] (.obj "s" (.capt (.fld "a" (.sel "s" "A")) []) (.trm "a" (.var "s")))
    = true := by decide

/-- `S ^ C` at a bound is boxed, so it is placed. -/
example : SType.CaptPlaced (.typ "A" (.capt .top [.name "f"]) (.capt .top [.name "f"])) = true := by
  decide

/-- `S ^ C` as an operand of `∧`, as the body of a `μ` or under another `^`
is not placed. -/
example : SType.CaptPlaced (.and (.capt .top [.name "f"]) .top) = false := by decide
example : SType.CaptPlaced (.mu "z" (.capt .top [.name "f"])) = false := by decide
example : SType.CaptPlaced (.capt (.capt .top [.name "f"]) []) = false := by decide

/-- A self annotation `S ^ U` and a type definition at a capturing type are
placed. -/
example : STm.CaptPlaced (.obj "s" (.capt (.fld "a" .top) [.name "f"])
    (.typ "A" (.capt .top [.name "f"]))) = true := by decide

end CapturesFrontend
