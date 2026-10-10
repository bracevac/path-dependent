import Coercions.Classifiers.FCdot.Debruijn
import Coercions.Classifiers.Cls.Core
import Lean

/-!
# The surface syntax of the Classifiers front end

The elaborator of `Notation.lean` produces a value of one of the inductives
below and nothing else.  Resolution into the typed calculus happens afterwards
in `Resolve.lean`.  The named syntax, the label table and the side conditions
`Scoped` and `LabelsIn` follow `lean/Coercions/Frontend/Surface.lean`.

There are three sorts.  A shape is the plain type former: a declaration, a
selection, an intersection, an arrow or a box.  A type is a shape with a
capture set, written `S ^ C`.  An answer is a type, or a type under one capture
binder bounded by a set of the enclosing scope, written `∃[c ⊑ C] T`.  A
written `∃` is the codomain of an arrow or the annotation of a `let`.

An arrow may name its own capture binder, `∀[c](x : T) U`, and a lambda may
name the binder of its arrow, `λ[c](x : T). t`.  An object literal has a shape
and definitions but no capture set, since its set is read off its class root.
`letex ⟨c, x⟩ = t in u` unpacks an existential answer by hand.  The ascription
`(t : T)` is a checking point and has no term in the calculus.

Three annotations may be left to inference: a lambda's domain, `λx. t`, a
literal's self shape, `ν(x. d)`, and the type of a term member, which a program
may write as `{a : T = t}`.  Each is an `Option`, `none` when not written.  A
domain is one slot, its shape and its set together, so `λ(x : S). t` keeps
meaning the pure `S ^ {}`.  The domain's type is `SDom`, which is
`Option SType`.  `SDom.capt S C` is the written domain `S ^ C`, so a term built
by constructor writes a domain as `.capt S C`, as it writes any type.  No kind
is left to inference: a kind is written intent.

Labels are strings, interned by a `LabelTable` the caller supplies.  A capture
member sits at a type label, like a type-member bound, since a capture-set
parameter is desugared to a type parameter.

The capture atom `any` stands for the capabilities of the enclosing scope and
`fresh` for a newly allocated one.  Resolution carries both through unread.
The typer gives them a meaning by position, see `readAt` in `Decide.lean`.

A capture atom may be projected to a classifier kind, `a.only[K]` or
`a.except[K]`.  A capture member may be bounded by a kind, `{C^ : K}`, beside
the set-bounded `{C^ : lo..hi}`.  A kind is `only`, `except`, or their union
and intersection.  Classifier names are a third namespace beside the term and
capture binders that `Scoped` tracks, and `ClassifiersIn` checks that every
name a kind mentions is declared.  A program (`SProg`) carries its classifier
declarations, the platform's binders each with an optional classifier, and an
optional declared use set and kind for its body.

Every mutual block is structural, so the kernel reduces every function here
and the checks at the end are all `by decide`.
-/

namespace ClassifiersFrontend

open Classifiers.FCdot (Label)

/-! ## The named abstract syntax -/

/-- A classifier kind.  `only[K₁, …]` keeps the named classifiers and
`except[K₁, …]` drops them, so `except []` keeps every classifier and
`only []` keeps none.  `∪` and `∩` combine two kinds. -/
inductive SKind : Type where
  | only (cs : List String)
  | except (cs : List String)
  | union (K L : SKind)
  | inter (K L : SKind)
deriving DecidableEq, Repr, Inhabited

/-- A capture atom: a name `x` or `κ`, a member selection `x.C`, `any`,
`fresh`, or an atom projected to a kind, `a.only[K]` or `a.except[K]`. -/
inductive SAtom : Type where
  /-- A term variable or a platform capability, by name. -/
  | name (x : String)
  /-- `x.C`, a capture member selection. -/
  | sel (x C : String)
  /-- `any`. -/
  | any
  /-- `fresh`. -/
  | fresh
  /-- `a.only[K]` or `a.except[K]`, an atom read at a classifier kind. -/
  | proj (a : SAtom) (K : SKind)
deriving DecidableEq, Repr, Inhabited

/-- A capture set, written `{a₁, …, aₙ}`. -/
abbrev SCap := List SAtom

/-- Add a name to the front of a list when it is written.  Opens an arrow's
own capture binder, which a program may leave anonymous. -/
def optCons (o : Option String) (l : List String) : List String :=
  match o with
  | none => l
  | some n => n :: l

mutual
/-- Surface shapes, with binders and labels as strings. -/
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
  /-- `{C^ : K}`, a kind-bounded capture member, at a type label. -/
  | capk (C : String) (K : SKind)
  /-- `x.A`, a type selection on a variable. -/
  | sel (x : String) (A : String)
  /-- `μ(x. S)`, a recursive self shape. -/
  | mu (x : String) (S : SShape)
  /-- `∀(x : T) U` or `∀[c](x : T) U`, a dependent arrow.  `κ` names the
  arrow's own capture binder when the program writes it. -/
  | all (κ : Option String) (x : String) (T : SType) (U : SAns)
  /-- `S ∧ T`, an intersection of shapes. -/
  | and (S T : SShape)
  /-- `□ T`, the box former. -/
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

/-- A lambda's domain: a written capturing type, or `none`, left to
inference. -/
abbrev SDom := Option SType

/-- The written domain `S ^ C`.  With it a domain built by constructor reads
`.capt S C`, the way every other written type does. -/
def SDom.capt (S : SShape) (C : SCap) : SDom := some (.capt S C)

mutual
/-- Surface terms.  Application and selection take arbitrary terms.  Let
insertion in `Resolve.lean` brings them to monadic normal form. -/
inductive STm : Type where
  /-- A variable, by name. -/
  | var (x : String)
  /-- `λ(x : T). t` or `λ[c](x : T). t`, `κ` naming the arrow's own capture
  binder when written.  `λx. t` and `λ[c]x. t` leave the domain to
  inference. -/
  | lam (κ : Option String) (x : String) (T : SDom) (t : STm)
  /-- `ν(x : S. d)`, an object literal: the self shape and its definitions.
  `ν(x. d)` leaves the self shape to inference. -/
  | obj (x : String) (S : Option SShape) (d : SDefs)
  /-- `t u`, direct style. -/
  | app (t u : STm)
  /-- `t.a`, direct style. -/
  | proj (t : STm) (a : String)
  /-- `let x = t in u`, with an optional result answer. -/
  | «let» (x : String) (ann : Option SAns) (t u : STm)
  /-- `letex ⟨c, x⟩ = t in u`, an explicit unpacking of an existential
  answer. -/
  | letex (κ x : String) (t u : STm)
  /-- `□ t`, a box value written by hand. -/
  | box (t : STm)
  /-- `C ⊸ t`, an unboxing written by hand. -/
  | unbox (C : SCap) (t : STm)
  /-- `(t : T)`, a checking point.  Erased. -/
  | asc (t : STm) (T : SType)
/-- Surface definition members. -/
inductive SDefs : Type where
  /-- `{type A = S}`. -/
  | typ (A : String) (S : SShape)
  /-- `{C^ = c}`, a capture definition. -/
  | cap (C : String) (c : SCap)
  /-- `{a = t}`, or `{a : T = t}` with a written type. -/
  | trm (a : String) (T : Option SType) (t : STm)
  /-- `d ∧ e`. -/
  | and (d e : SDefs)
end

deriving instance DecidableEq, Repr for STm, SDefs

instance : Inhabited STm := ⟨.var ""⟩
instance : Inhabited SDefs := ⟨.typ "" .top⟩

/-- A classifier declaration list: each name with the parent it extends, or
`none`. -/
abbrev SClsDecls := List (String × Option String)

/-- A platform binder list: each capability name with its classifier, or
`none`. -/
abbrev SPlatform := List (String × Option String)

/-- A whole program: the classifiers it declares, the platform capabilities
with their classifiers (outermost first), an optional declared use set and
kind for the body, and the body. -/
structure SProg where
  classifiers : SClsDecls
  platform : SPlatform
  uses : Option SCap
  kind : Option SKind
  body : STm
deriving DecidableEq, Repr

/-! ## The label table

Type labels and term labels are disjoint in FCdot
(`lean/Coercions/Classifiers/FCdot/Debruijn.lean`), so `labelTyp?` and
`labelTrm?` look up one sort each. -/

/-- A label table maps surface names to labels, first entry first. -/
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

/-! ## Capture sets: scoping and labelling -/

/-- Every name of a capture atom is in scope.  `K` lists the capture
binders and `Γ` the term variables.  A plain name may be either, the receiver
of `x.C` must be a term variable, and `any` and `fresh` name nothing.  A
projected atom scopes as its base atom does, since its kind names only
classifiers, which `ClassifiersIn` checks. -/
def SAtom.Scoped (K Γ : List String) : SAtom → Bool
  | .name x => Γ.contains x || K.contains x
  | .sel x _ => Γ.contains x
  | .any => true
  | .fresh => true
  | .proj a _ => SAtom.Scoped K Γ a

/-- Every name of a capture set is in scope. -/
def SCap.Scoped (K Γ : List String) : SCap → Bool
  | [] => true
  | .name x :: c => (Γ.contains x || K.contains x) && SCap.Scoped K Γ c
  | .sel x _ :: c => Γ.contains x && SCap.Scoped K Γ c
  | .any :: c => SCap.Scoped K Γ c
  | .fresh :: c => SCap.Scoped K Γ c
  | .proj a _ :: c => SAtom.Scoped K Γ a && SCap.Scoped K Γ c

/-- Every capture-member selection of a capture atom is at a type label.  A
projected atom is labelled as its base atom is. -/
def SAtom.LabelsIn (Λ : LabelTable) : SAtom → Bool
  | .name _ => true
  | .sel _ C => (labelTyp? Λ C).isSome
  | .any => true
  | .fresh => true
  | .proj a _ => SAtom.LabelsIn Λ a

/-- Every capture-member selection of a capture set is at a type label. -/
def SCap.LabelsIn (Λ : LabelTable) : SCap → Bool
  | [] => true
  | .name _ :: c => SCap.LabelsIn Λ c
  | .sel _ C :: c => (labelTyp? Λ C).isSome && SCap.LabelsIn Λ c
  | .any :: c => SCap.LabelsIn Λ c
  | .fresh :: c => SCap.LabelsIn Λ c
  | .proj a _ :: c => SAtom.LabelsIn Λ a && SCap.LabelsIn Λ c

/-! ## Classifier names

Classifier names are strings, mapped to classifiers by a `ClsTable` as labels
are by a `LabelTable`.  `Resolve.lean` builds the table from a program's
declarations.  `ClassifiersIn κt` holds when every classifier name a phrase
mentions, in `only`, `except` or a platform binder, is in the table. -/

/-- A classifier table maps surface names to classifiers, first entry first. -/
abbrev ClsTable := List (String × Classifiers.Cls.Classifier)

/-- The first entry for a classifier name. -/
def clsFind? (κt : ClsTable) (x : String) : Option Classifiers.Cls.Classifier :=
  match κt with
  | [] => none
  | (y, c) :: κt => if x = y then some c else clsFind? κt x
termination_by structural κt

/-- Every classifier name a kind mentions is in the table. -/
def SKind.ClassifiersIn (κt : ClsTable) (K : SKind) : Bool :=
  match K with
  | .only cs => cs.all fun c => (clsFind? κt c).isSome
  | .except cs => cs.all fun c => (clsFind? κt c).isSome
  | .union K L => SKind.ClassifiersIn κt K && SKind.ClassifiersIn κt L
  | .inter K L => SKind.ClassifiersIn κt K && SKind.ClassifiersIn κt L
termination_by structural K

/-- Every classifier name a capture atom mentions is in the table. -/
def SAtom.ClassifiersIn (κt : ClsTable) (a : SAtom) : Bool :=
  match a with
  | .name _ => true
  | .sel _ _ => true
  | .any => true
  | .fresh => true
  | .proj a K => SAtom.ClassifiersIn κt a && SKind.ClassifiersIn κt K
termination_by structural a

/-- Every classifier name a capture set mentions is in the table. -/
def SCap.ClassifiersIn (κt : ClsTable) (c : SCap) : Bool :=
  c.all (SAtom.ClassifiersIn κt)

/-- Every classifier a platform binder is declared at is in the table. -/
def SPlatform.ClassifiersIn (κt : ClsTable) (ps : SPlatform) : Bool :=
  ps.all fun b =>
    match b.2 with
    | none => true
    | some c => (clsFind? κt c).isSome

/-! ## Scoping

`Scoped K Γ` holds when every free name of the phrase is in scope at the kind
its position needs.  `K` lists the capture binders, the platform capabilities
among them, and `Γ` the term variables.  A name in term position, the
receiver of `x.A` and the receiver of `x.C` must be term variables.  A plain
name in a capture set may be either.

An arrow's own capture binder, named or not, scopes over its domain and, with
the parameter, over its codomain.  The existential binder of an answer scopes
over its type alone, and its bound is read in the outer scope.  The binder of
a `let` does not scope over the `let`'s annotation.  The two binders of a
`letex` scope only over its body.  The forms that bind a name are `mu`, `all`,
the capture binder of `all` and of `ex`, the self of `obj`, and `let` and
`letex`. -/

mutual
/-- Every free name of a surface shape is in scope. -/
def SShape.Scoped (K Γ : List String) (S : SShape) : Bool :=
  match S with
  | .top => true
  | .bot => true
  | .typ _ S T => SShape.Scoped K Γ S && SShape.Scoped K Γ T
  | .fld _ T => SType.Scoped K Γ T
  | .cap _ lo hi => SCap.Scoped K Γ lo && SCap.Scoped K Γ hi
  | .capk _ _ => true
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
  | .lam κ x T t =>
      (match T with | none => true | some T => SType.Scoped (optCons κ K) Γ T)
        && STm.Scoped (optCons κ K) (x :: Γ) t
  | .obj x S d =>
      (match S with | none => true | some S => SShape.Scoped K (x :: Γ) S)
        && SDefs.Scoped K (x :: Γ) d
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
  | .trm _ T t =>
      (match T with | none => true | some T => SType.Scoped K Γ T) && STm.Scoped K Γ t
  | .and d e => SDefs.Scoped K Γ d && SDefs.Scoped K Γ e
termination_by structural d
end

/-! ## Labelling

`LabelsIn Λ` holds when every name in label position is in the table at the
sort its position demands. -/

mutual
/-- Every label of a surface shape is in the table at the right sort. -/
def SShape.LabelsIn (Λ : LabelTable) (S : SShape) : Bool :=
  match S with
  | .top => true
  | .bot => true
  | .typ A S T => (labelTyp? Λ A).isSome && SShape.LabelsIn Λ S && SShape.LabelsIn Λ T
  | .fld a T => (labelTrm? Λ a).isSome && SType.LabelsIn Λ T
  | .cap C lo hi => (labelTyp? Λ C).isSome && SCap.LabelsIn Λ lo && SCap.LabelsIn Λ hi
  | .capk C _ => (labelTyp? Λ C).isSome
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
  | .lam _ _ T t =>
      (match T with | none => true | some T => SType.LabelsIn Λ T) && STm.LabelsIn Λ t
  | .obj _ S d =>
      (match S with | none => true | some S => SShape.LabelsIn Λ S) && SDefs.LabelsIn Λ d
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
  | .trm a T t =>
      (labelTrm? Λ a).isSome &&
        (match T with | none => true | some T => SType.LabelsIn Λ T) && STm.LabelsIn Λ t
  | .and d e => SDefs.LabelsIn Λ d && SDefs.LabelsIn Λ e
termination_by structural d
end

/-! ## Classifier names in shapes, types, answers, terms and definitions

A classifier name sits in the kind of a kind-bounded member `capk` and in the
kind of a projected atom in a capture set.  Every other form passes the check
to its parts. -/

mutual
/-- Every classifier name of a surface shape is in the table. -/
def SShape.ClassifiersIn (κt : ClsTable) (S : SShape) : Bool :=
  match S with
  | .top => true
  | .bot => true
  | .typ _ S T => SShape.ClassifiersIn κt S && SShape.ClassifiersIn κt T
  | .fld _ T => SType.ClassifiersIn κt T
  | .cap _ lo hi => SCap.ClassifiersIn κt lo && SCap.ClassifiersIn κt hi
  | .capk _ K => SKind.ClassifiersIn κt K
  | .sel _ _ => true
  | .mu _ S => SShape.ClassifiersIn κt S
  | .all _ _ T U => SType.ClassifiersIn κt T && SAns.ClassifiersIn κt U
  | .and S T => SShape.ClassifiersIn κt S && SShape.ClassifiersIn κt T
  | .box T => SType.ClassifiersIn κt T
termination_by structural S
/-- Every classifier name of a surface type is in the table. -/
def SType.ClassifiersIn (κt : ClsTable) (T : SType) : Bool :=
  match T with
  | .capt S C => SShape.ClassifiersIn κt S && SCap.ClassifiersIn κt C
termination_by structural T
/-- Every classifier name of a surface answer is in the table. -/
def SAns.ClassifiersIn (κt : ClsTable) (U : SAns) : Bool :=
  match U with
  | .ty T => SType.ClassifiersIn κt T
  | .ex _ C T => SCap.ClassifiersIn κt C && SType.ClassifiersIn κt T
termination_by structural U
end

mutual
/-- Every classifier name of a surface term is in the table. -/
def STm.ClassifiersIn (κt : ClsTable) (e : STm) : Bool :=
  match e with
  | .var _ => true
  | .lam _ _ T t =>
      (match T with | none => true | some T => SType.ClassifiersIn κt T)
        && STm.ClassifiersIn κt t
  | .obj _ S d =>
      (match S with | none => true | some S => SShape.ClassifiersIn κt S)
        && SDefs.ClassifiersIn κt d
  | .app t u => STm.ClassifiersIn κt t && STm.ClassifiersIn κt u
  | .proj t _ => STm.ClassifiersIn κt t
  | .«let» _ ann t u =>
      (match ann with | none => true | some U => SAns.ClassifiersIn κt U)
        && STm.ClassifiersIn κt t && STm.ClassifiersIn κt u
  | .letex _ _ t u => STm.ClassifiersIn κt t && STm.ClassifiersIn κt u
  | .box t => STm.ClassifiersIn κt t
  | .unbox C t => SCap.ClassifiersIn κt C && STm.ClassifiersIn κt t
  | .asc t T => STm.ClassifiersIn κt t && SType.ClassifiersIn κt T
termination_by structural e
/-- Every classifier name of surface definitions is in the table. -/
def SDefs.ClassifiersIn (κt : ClsTable) (d : SDefs) : Bool :=
  match d with
  | .typ _ S => SShape.ClassifiersIn κt S
  | .cap _ c => SCap.ClassifiersIn κt c
  | .trm _ T t =>
      (match T with | none => true | some T => SType.ClassifiersIn κt T)
        && STm.ClassifiersIn κt t
  | .and d e => SDefs.ClassifiersIn κt d && SDefs.ClassifiersIn κt e
termination_by structural d
end

/-! ## The test helper

`#eval expect ...` runs compiled code, and a false result fails the build. -/

/-- Fail the build, from `#eval`, when a check comes out false. -/
def expect (b : Bool) (msg : String) : IO Unit :=
  if b then pure () else throw (IO.userError msg)

/-! ## `#assert_no_wf`

Every recursive definition of this front end is meant to be structural, so
that the kernel reduces it.  A clause added without a matching
`termination_by structural` case can make Lean fall back to well-founded
recursion silently.  This command reports that at build time. -/

open Lean Elab Command in
/-- Fails when a definition under the namespace `ns` is compiled by
well-founded recursion.  Lean picks a specialised combinator for the
measure's type, such as `WellFounded.Nat.fix`, so the test is membership in
the `WellFounded` namespace, not equality with one constant. -/
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

The sample program is `λ[c](f : ⊤). ν(s : {a : ⊤} ∧ {C^ : {}..{f}}. {a = f} ∧
{C^ = {f}})`.  Its label table names `a` a term label and `C` a type label. -/

/-- `a` is a term label and `C` a type label. -/
private def Λ0 : LabelTable := [("a", .trm 0), ("C", .typ 0)]

/-- The sample program of the checks below. -/
private def sampleProgram : STm :=
  .lam (some "c") "f" (.capt .top [])
    (.obj "s"
      (some (.and (.fld "a" (.capt .top [])) (.cap "C" [] [SAtom.name "f"])))
      (.and (.trm "a" none (.var "f")) (.cap "C" [SAtom.name "f"])))

example : STm.Scoped [] [] sampleProgram = true := by decide
example : STm.LabelsIn Λ0 sampleProgram = true := by decide

/-- A free name is out of scope. -/
example : STm.Scoped [] [] (.var "x") = false := by decide

/-- The self binder of `ν` scopes over its own shape. -/
example : STm.Scoped [] [] (.obj "s" (some (.sel "s" "A")) (.typ "B" .top)) = true := by decide

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

/-- `all`: an anonymous arrow binder scopes its domain under `K` alone and
its codomain under `K` and the parameter. -/
example : SShape.Scoped [] [] (.all none "x" (.capt .top []) (.ty (.capt (.sel "x" "A") []))) =
    true := by decide

/-- `all`: a named arrow binder is in scope in the domain and the codomain. -/
example :
    SShape.Scoped [] [] (.all (some "c") "x" (.capt .top [SAtom.name "c"])
      (.ty (.capt .top [SAtom.name "c"]))) = true := by decide

example : SShape.Scoped [] [] (.all none "x" (.capt .top [SAtom.name "c"]) (.ty (.capt .top []))) =
    false := by decide

/-- `ex`: the binder scopes over the type, and the bound is read in the outer
scope. -/
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

/-- `ex`: the type under the binder is labelled.  The bound is not a label
position. -/
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

/-- `SDefs.cap`: the member's label is in the table and its value is
labelled. -/
example : SDefs.LabelsIn Λ0 (.cap "C" [SAtom.sel "s" "C"]) = true := by decide

example : SDefs.LabelsIn [] (.cap "C" []) = false := by decide

/-! ### Slots left to inference -/

/-- A domain built by constructor is the written slot. -/
example : (SDom.capt .top [] : SDom) = some (.capt .top []) := by decide

/-- An empty domain and an empty self shape are in scope, and the body and the
definitions are scoped under the binder. -/
example : STm.Scoped [] [] (.lam none "x" none (.var "x")) = true := by decide
example : STm.Scoped [] [] (.obj "s" none (.trm "a" none (.var "s"))) = true := by decide

/-- A named arrow binder scopes over the body of a lambda with an empty
domain. -/
example :
    STm.Scoped [] [] (.lam (some "c") "x" none
      (.«let» "y" (some (.ty (.capt .top [SAtom.name "c"]))) (.var "x") (.var "y"))) = true := by
  decide

/-- A written field type is scoped under the self binder. -/
example : STm.Scoped [] [] (.obj "s" none (.trm "a" (some (.capt (.sel "s" "A") [])) (.var "s"))) =
    true := by decide
example : STm.Scoped [] [] (.obj "s" none (.trm "a" (some (.capt (.sel "t" "A") [])) (.var "s"))) =
    false := by decide

/-- A written field type is labelled. -/
example : SDefs.LabelsIn Λ0 (.trm "a" (some (.capt (.fld "b" (.capt .top [])) [])) (.var "s")) =
    false := by decide
example : SDefs.LabelsIn Λ0 (.trm "a" (some (.capt (.fld "a" (.capt .top [])) [])) (.var "s")) =
    true := by decide

/-- An empty slot needs no label.  A type definition under it still does. -/
example : STm.LabelsIn [] (.lam none "x" none (.var "x")) = true := by decide
example : STm.LabelsIn [] (.lam none "x" none (.obj "s" none (.typ "B" .top))) = false := by decide

/-- A capture binder is no term variable: `k1` is in scope in a capture set
and out of scope in term position. -/
example : STm.Scoped ["k1"] [] (.var "k1") = false := by decide
example : SType.Scoped ["k1"] [] (.capt .top [SAtom.name "k1"]) = true := by decide

/-- The receiver of a capture member is a term variable. -/
example : SType.Scoped ["k1"] [] (.capt .top [SAtom.sel "k1" "C"]) = false := by decide

/-- `SAtom.proj`: a projected atom scopes as its base atom does. -/
example : SCap.Scoped [] ["x"] [SAtom.proj (.name "x") (.only ["K"])] = true := by decide

example : SCap.Scoped [] [] [SAtom.proj (.name "x") (.only ["K"])] = false := by decide

/-- `SShape.capk`: a kind-bounded member binds no name over a body. -/
example : SShape.Scoped [] [] (.capk "C" (.except [])) = true := by decide

/-- `SShape.capk`: the member's own label is in the table, at the type
sort. -/
example : SShape.LabelsIn Λ0 (.capk "C" (.only ["K"])) = true := by decide

example : SShape.LabelsIn [] (.capk "C" (.only ["K"])) = false := by decide

/-- A table of one classifier, `K1`. -/
private def κ1 : ClsTable := [("K1", .child 0 .top)]

/-- A table of two classifiers, `K1` and its child `K2`. -/
private def κ12 : ClsTable := [("K1", .child 0 .top), ("K2", .child 0 (.child 0 .top))]

/-- `clsFind?`: the first entry for a name, none for an undeclared one. -/
example : clsFind? κ12 "K2" = some (.child 0 (.child 0 .top)) := by decide

example : clsFind? κ1 "K2" = none := by decide

/-- `ClassifiersIn`: `only` and `except` read their own names, `∪` and
`∩` read both sides. -/
example : SKind.ClassifiersIn κ12 (.only ["K1", "K2"]) = true := by decide

example : SKind.ClassifiersIn κ1 (.only ["K1", "K2"]) = false := by decide

example : SKind.ClassifiersIn κ1 (.except ["K1"]) = true := by decide

example : SKind.ClassifiersIn κ12 (.union (.only ["K1"]) (.except ["K2"])) = true := by
  decide

example : SKind.ClassifiersIn κ1 (.union (.only ["K1"]) (.except ["K2"])) = false := by decide

example : SKind.ClassifiersIn κ12 (.inter (.only ["K1"]) (.except ["K2"])) = true := by
  decide

/-- `ClassifiersIn`: a projected atom reads its kind's names, besides its
base atom's. -/
example : SAtom.ClassifiersIn κ1 (.proj (.name "x") (.only ["K1"])) = true := by decide

example : SAtom.ClassifiersIn [] (.proj (.name "x") (.only ["K1"])) = false := by decide

/-- `ClassifiersIn`: a kind-bounded member reads its kind's names and a
set-bounded one reads none. -/
example : SShape.ClassifiersIn κ1 (.capk "C" (.only ["K1"])) = true := by decide

example : SShape.ClassifiersIn [] (.cap "C" [] [SAtom.name "k1"]) = true := by decide

/-- `ClassifiersIn`: a platform binder's classifier is in the table, and a
plain binder names none. -/
example : SPlatform.ClassifiersIn κ1 [("k1", some "K1"), ("k2", none)] = true := by decide

example : SPlatform.ClassifiersIn κ1 [("k1", some "K2")] = false := by decide

/-- `ClassifiersIn`: an empty slot names no classifier, and a written field
type has its kinds read. -/
example : STm.ClassifiersIn [] (.lam none "x" none (.var "x")) = true := by decide

example :
    STm.ClassifiersIn κ1 (.obj "s" none
      (.trm "a" (some (.capt .top [SAtom.proj (.name "s") (.only ["K1"])])) (.var "s"))) =
      true := by decide

example :
    STm.ClassifiersIn [] (.obj "s" none
      (.trm "a" (some (.capt .top [SAtom.proj (.name "s") (.only ["K1"])])) (.var "s"))) =
      false := by decide

end ClassifiersFrontend
