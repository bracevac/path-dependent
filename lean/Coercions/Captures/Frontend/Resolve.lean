import Coercions.Captures.Frontend.Ann
import Coercions.Captures.Frontend.Notation
import Coercions.Captures.DotMNF.Examples

/-!
# Name resolution and let insertion for the Captures front end

Three functions take a surface phrase to the annotated de Bruijn syntax of
`Ann.lean`: `resolveTy` for a type, `resolveTm` for a term and `resolveDefs`
for a definition list.  They are the only place where a surface name becomes
an index.

## Names of two kinds

A signature of the version has term binders and capture binders.  A name
environment records one surface name per binder, innermost first, with its
kind.  A name in term position, the receiver of a type selection `x.A` and
the receiver of a capture member `x.C` are looked up among the term binders
only.  A plain name in a capture set takes the innermost binder of either
kind, and becomes the atom of a term variable or of a capture binder by the
kind it finds.  The platform capabilities are the outermost capture binders,
in the order given, so `["k1", "k2"]` gives `k1` at `.there .here` and `k2`
at `.here`, the version's own `k1` and `k2`
(`lean/Coercions/Captures/DotMNF/Examples.lean`).

## Types, shapes and boxes

`resolveT` reads a phrase as a type.  A bare shape is pure and `S ^ C`
carries `C`.  The shape a subphrase stands for at a shape position is read
off its type.  At a type-member bound and at a type definition, a phrase
written `S ^ C` becomes the box `□(S ^ C)`, the compiler's rule that a type
argument is boxed.  At every other shape position, the body of a `μ`, an
operand of `∧` and the shape under a written `^`, a written `S ^ C` is a
resolution failure.  An explicit `□ T` is accepted everywhere.

## The atom `any`

Every annotation is tested where it stands and then expanded by the frozen
`Ty.expand` at the platform set `P`, the reading the version gives the top
of a program.  A function's domain is tested by the arrow clause of the
frozen `Shape.anyOk`: no `any` in its own outer set, and its shape `anyOk`.
A `let` type and an ascription are tested by the frozen `Ty.anyOk`, which
ignores the type's own outer set.  The self annotation of an object is
tested as the type `μ S ^ U` it stands for, with `U` empty when it is not
written, and expanded the same way.  A type definition, the set of an
unboxing and a capture definition are read nowhere, so they are tested to
hold no `any` at all.  With a platform set free of `any`, nothing the
resolver emits holds `any` (`resolve_noAny`).

## Let insertion

Let insertion uses an explicit spine of bindings, as the vanilla front end
does, which keeps the three resolvers structural on the surface phrase.  The
two vanilla direct style forms, application and projection, atomize their
operands, and so do the two forms of the version, `□ t` and `C ⊸ t`.  The
inserted binder is named `"%"`, which no identifier of the notation can
equal.

This module imports `Notation.lean` for the programs at the end, and Lean's
token table is global.  So the Greek nu that opens an object literal is a
keyword here and cannot be a local name.  The name environment is written
`nv` below for that reason.

Nothing in this module is part of the metatheory.  No definition here lives
in a namespace of the version.
-/

namespace CapturesFrontend

open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (Path CapAtom CaptureSet Shape Ty Tm Defs Platform)

/-! ## Name environments -/

/-- One surface name per binder of the signature, innermost binder first. -/
inductive NameEnv : Sig → Type where
  /-- The empty environment. -/
  | nil : NameEnv []
  /-- One more term binder, with its surface name. -/
  | cons : NameEnv s → String → NameEnv (s,x)
  /-- One more capture binder, with its surface name. -/
  | consC : NameEnv s → String → NameEnv (s,c)

/-- The innermost binder of a name, of either kind, with its kind. -/
def NameEnv.find? {s : Sig} (nv : NameEnv s) (z : String) : Option ((k : Kind) × BVar s k) :=
  match nv with
  | .nil => none
  | .cons nv y =>
      if z = y then some ⟨.var, .here⟩ else (nv.find? z).map fun p => ⟨p.1, .there p.2⟩
  | .consC nv y =>
      if z = y then some ⟨.cap, .here⟩ else (nv.find? z).map fun p => ⟨p.1, .there p.2⟩
termination_by structural nv

/-- The innermost term binder of a name.  Capture binders are skipped. -/
def NameEnv.findVar? {s : Sig} (nv : NameEnv s) (z : String) : Option (BVar s .var) :=
  match nv with
  | .nil => none
  | .cons nv y => if z = y then some .here else (nv.findVar? z).map .there
  | .consC nv _ => (nv.findVar? z).map .there
termination_by structural nv

/-- The names of the term binders, innermost first. -/
def NameEnv.names {s : Sig} (nv : NameEnv s) : List String :=
  match nv with
  | .nil => []
  | .cons nv y => y :: nv.names
  | .consC nv _ => nv.names
termination_by structural nv

/-- The names of the capture binders, innermost first. -/
def NameEnv.capNames {s : Sig} (nv : NameEnv s) : List String :=
  match nv with
  | .nil => []
  | .cons nv _ => nv.capNames
  | .consC nv y => y :: nv.capNames
termination_by structural nv

/-! ## The platform

A platform is a prefix of capture binders.  `PlatformNames` carries the
signature, the version's evidence that it is a platform prefix, the names of
its capabilities and its own capture set, every capability once, outermost
first.  That set is the version's `platSet` for `["k1", "k2"]`. -/

/-- A platform: its capture binders, their names and their set. -/
structure PlatformNames where
  /-- The signature of the platform's capture binders. -/
  sig : Sig
  /-- The evidence that the signature is a prefix of capture binders. -/
  plat : Platform sig
  /-- The names of the capabilities. -/
  names : NameEnv sig
  /-- The platform's own capture set. -/
  set : CaptureSet sig

/-- The empty platform. -/
def PlatformNames.empty : PlatformNames := ⟨[], .nil, .nil, []⟩

/-- One more capability, innermost. -/
def PlatformNames.push (π : PlatformNames) (y : String) : PlatformNames :=
  ⟨π.sig,c, .cons π.plat, π.names.consC y,
    CaptureSet.weaken (k := .cap) π.set ++ [CapAtom.cvar .here]⟩

/-- Push the names in order, the first one outermost. -/
def PlatformNames.pushAll (π : PlatformNames) (ys : List String) : PlatformNames :=
  match ys with
  | [] => π
  | y :: ys => (π.push y).pushAll ys
termination_by structural ys

/-- The platform of the given capability names, the first one outermost. -/
def PlatformNames.ofList (ys : List String) : PlatformNames := PlatformNames.empty.pushAll ys

/-! ## Covering, the monotonicity of scoping

The direct style clauses of `resolveTm` resolve the operand under the
environment that `atomize` returns, which is the one it was given or that
one with a single inserted term binder on the front.  So the totality proof
needs scoping to survive a larger list of term variables. -/

/-- Every name of the first list is a name of the second. -/
def Covers (Γ Γ' : List String) : Prop :=
  ∀ z, Γ.contains z = true → Γ'.contains z = true

/-- Every list covers itself. -/
theorem Covers.rfl' (Γ : List String) : Covers Γ Γ := fun _ h => h

/-- A list is covered by itself with one more name in front. -/
theorem Covers.tail (Γ : List String) (y : String) : Covers Γ (y :: Γ) := by
  intro z hz
  simp only [List.contains_cons, hz, Bool.or_true]

/-- Covering survives one more name in front of both lists. -/
theorem Covers.cons {Γ Γ' : List String} (h : Covers Γ Γ') (x : String) :
    Covers (x :: Γ) (x :: Γ') := by
  intro z hz
  simp only [List.contains_cons] at hz ⊢
  cases hzx : (z == x) with
  | true => simp
  | false =>
      simp only [hzx, Bool.false_or] at hz ⊢
      exact h z hz

/-- Scoping of a capture set survives a larger list of term variables. -/
theorem SCap.Scoped_covers (K : List String) : ∀ (c : SCap) {Γ Γ' : List String},
    Covers Γ Γ' → SCap.Scoped K Γ c = true → SCap.Scoped K Γ' c = true
  | [], _, _, _, _ => rfl
  | .name x :: c, _, _, h, hs => by
      simp only [SCap.Scoped, Bool.and_eq_true, Bool.or_eq_true] at hs ⊢
      refine ⟨?_, SCap.Scoped_covers K c h hs.2⟩
      rcases hs.1 with h1 | h1
      · exact Or.inl (h x h1)
      · exact Or.inr h1
  | .sel x _ :: c, _, _, h, hs => by
      simp only [SCap.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨h x hs.1, SCap.Scoped_covers K c h hs.2⟩
  | .any :: c, _, _, h, hs => SCap.Scoped_covers K c h hs

/-- Scoping of a type survives a larger list of term variables. -/
theorem SType.Scoped_covers (K : List String) : ∀ (T : SType) {Γ Γ' : List String},
    Covers Γ Γ' → SType.Scoped K Γ T = true → SType.Scoped K Γ' T = true
  | .top, _, _, _, _ => rfl
  | .bot, _, _, _, _ => rfl
  | .typ _ S T, _, _, h, hs => by
      simp only [SType.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.Scoped_covers K S h hs.1, SType.Scoped_covers K T h hs.2⟩
  | .fld _ T, _, _, h, hs => SType.Scoped_covers K T h hs
  | .cap _ lo hi, _, _, h, hs => by
      simp only [SType.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SCap.Scoped_covers K lo h hs.1, SCap.Scoped_covers K hi h hs.2⟩
  | .sel x _, _, _, h, hs => h x hs
  | .mu x T, _, _, h, hs => SType.Scoped_covers K T (h.cons x) hs
  | .all x S T, _, _, h, hs => by
      simp only [SType.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.Scoped_covers K S h hs.1, SType.Scoped_covers K T (h.cons x) hs.2⟩
  | .and S T, _, _, h, hs => by
      simp only [SType.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.Scoped_covers K S h hs.1, SType.Scoped_covers K T h hs.2⟩
  | .box T, _, _, h, hs => SType.Scoped_covers K T h hs
  | .capt S C, _, _, h, hs => by
      simp only [SType.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.Scoped_covers K S h hs.1, SCap.Scoped_covers K C h hs.2⟩

/-- Scoping of a self annotation survives a larger list of term variables. -/
theorem SType.SelfScoped_covers (K : List String) (x : String) (T : SType)
    {Γ Γ' : List String} (h : Covers Γ Γ') (hs : SType.SelfScoped K Γ x T = true) :
    SType.SelfScoped K Γ' x T = true := by
  simp only [SType.SelfScoped, Bool.and_eq_true] at hs ⊢
  refine ⟨SType.Scoped_covers K _ (h.cons x) hs.1, ?_⟩
  have h2 := hs.2
  cases hU : T.selfSet with
  | none => rfl
  | some U =>
      rw [hU] at h2
      exact SCap.Scoped_covers K U h h2

mutual
/-- Scoping of a term survives a larger list of term variables. -/
theorem STm.Scoped_covers (K : List String) : ∀ (e : STm) {Γ Γ' : List String},
    Covers Γ Γ' → STm.Scoped K Γ e = true → STm.Scoped K Γ' e = true
  | .var x, _, _, h, hs => h x hs
  | .lam x T t, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.Scoped_covers K T h hs.1, STm.Scoped_covers K t (h.cons x) hs.2⟩
  | .obj x T d, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.SelfScoped_covers K x T h hs.1, SDefs.Scoped_covers K d (h.cons x) hs.2⟩
  | .app t u, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨STm.Scoped_covers K t h hs.1, STm.Scoped_covers K u h hs.2⟩
  | .proj t _, _, _, h, hs => STm.Scoped_covers K t h hs
  | .«let» x ann t u, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      refine ⟨⟨?_, STm.Scoped_covers K t h hs.1.2⟩, STm.Scoped_covers K u (h.cons x) hs.2⟩
      cases ann with
      | none => rfl
      | some U => exact SType.Scoped_covers K U h hs.1.1
  | .box t, _, _, h, hs => STm.Scoped_covers K t h hs
  | .unbox C t, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SCap.Scoped_covers K C h hs.1, STm.Scoped_covers K t h hs.2⟩
  | .asc t T, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨STm.Scoped_covers K t h hs.1, SType.Scoped_covers K T h hs.2⟩
/-- Scoping of a definition list survives a larger list of term variables. -/
theorem SDefs.Scoped_covers (K : List String) : ∀ (d : SDefs) {Γ Γ' : List String},
    Covers Γ Γ' → SDefs.Scoped K Γ d = true → SDefs.Scoped K Γ' d = true
  | .typ _ T, _, _, h, hs => SType.Scoped_covers K T h hs
  | .trm _ t, _, _, h, hs => STm.Scoped_covers K t h hs
  | .and d e, _, _, h, hs => by
      simp only [SDefs.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SDefs.Scoped_covers K d h hs.1, SDefs.Scoped_covers K e h hs.2⟩
  | .cap _ c, _, _, h, hs => SCap.Scoped_covers K c h hs
end

/-- A name among the term binders has a term binder. -/
theorem NameEnv.findVar?_isSome : ∀ {s : Sig} (nv : NameEnv s) (x : String),
    nv.names.contains x = true → (nv.findVar? x).isSome = true
  | _, .nil, _, h => by simp [NameEnv.names] at h
  | _, .cons nv y, x, h => by
      by_cases hxy : x = y
      · simp [NameEnv.findVar?, hxy]
      · have hy : (x == y) = false := by simp [hxy]
        have h' : nv.names.contains x = true := by
          simp only [NameEnv.names, List.contains_cons, hy, Bool.false_or] at h
          exact h
        simp [NameEnv.findVar?, hxy, NameEnv.findVar?_isSome nv x h']
  | _, .consC nv _, x, h => by
      have h' : nv.names.contains x = true := h
      simp [NameEnv.findVar?, NameEnv.findVar?_isSome nv x h']

/-- A name among the binders of either kind has a binder. -/
theorem NameEnv.find?_isSome : ∀ {s : Sig} (nv : NameEnv s) (x : String),
    (nv.names.contains x || nv.capNames.contains x) = true → (nv.find? x).isSome = true
  | _, .nil, _, h => by simp [NameEnv.names, NameEnv.capNames] at h
  | _, .cons nv y, x, h => by
      by_cases hxy : x = y
      · simp [NameEnv.find?, hxy]
      · have hy : (x == y) = false := by simp [hxy]
        have h' : (nv.names.contains x || nv.capNames.contains x) = true := by
          simp only [NameEnv.names, NameEnv.capNames, List.contains_cons, hy,
            Bool.false_or] at h
          exact h
        simp [NameEnv.find?, hxy, NameEnv.find?_isSome nv x h']
  | _, .consC nv y, x, h => by
      by_cases hxy : x = y
      · simp [NameEnv.find?, hxy]
      · have hy : (x == y) = false := by simp [hxy]
        have h' : (nv.names.contains x || nv.capNames.contains x) = true := by
          simp only [NameEnv.names, NameEnv.capNames, List.contains_cons, hy,
            Bool.false_or] at h
          exact h
        simp [NameEnv.find?, hxy, NameEnv.find?_isSome nv x h']

/-! ## The spine of inserted bindings

A `Spine s s'` is a stack of `let` bindings that takes a term of the inner
signature `s'` back to a term of the outer signature `s`.  `Spine.rename` is
the weakening that moves a variable of `s` into `s'`.  `Rename.comp f g` is
`g ∘ f`, so the composition below is in the order it is printed. -/

/-- A stack of inserted `let` bindings. -/
inductive Spine : Sig → Sig → Type where
  /-- No binding. -/
  | nil : Spine s s
  /-- One binding, then the rest under it. -/
  | cons : ATm s → Spine (s,x) s' → Spine s s'

/-- Wrap a term of the inner signature in the bindings of the spine. -/
def Spine.plug {s s' : Sig} (sp : Spine s s') (u : ATm s') : ATm s :=
  match sp with
  | .nil => u
  | .cons t sp => .let none t (sp.plug u)
termination_by structural sp

/-- The weakening a spine induces on its outer signature. -/
def Spine.rename {s s' : Sig} (sp : Spine s s') : Rename s s' :=
  match sp with
  | .nil => Rename.id
  | .cons _ sp => Rename.comp Rename.succ sp.rename
termination_by structural sp

/-- Stack one spine under another. -/
def Spine.append {s s' s'' : Sig} (sp : Spine s s') (sp' : Spine s' s'') : Spine s s'' :=
  match sp with
  | .nil => sp'
  | .cons t sp => .cons t (sp.append sp')
termination_by structural sp

/-- A resolved term brought into variable position: the bindings that had to be
inserted, the environment they extend, and the variable that stands for it. -/
structure Atomic (s : Sig) where
  /-- The signature after the insertions. -/
  sig : Sig
  /-- The insertions. -/
  spine : Spine s sig
  /-- The environment at that signature. -/
  names : NameEnv sig
  /-- The variable standing for the term. -/
  var : BVar sig .var

/-- Bring a resolved term into variable position.  A variable is already there
and nothing is inserted.  Anything else is bound by one fresh `let`. -/
def atomize {s : Sig} (nv : NameEnv s) (t : ATm s) : Atomic s :=
  match t with
  | .path (.var i) => ⟨s, .nil, nv, i⟩
  | _ => ⟨(s,x), .cons t .nil, nv.cons "%", .here⟩

/-- `atomize` extends the term binders by at most one name. -/
theorem atomize_names_covers {s : Sig} (nv : NameEnv s) (t : ATm s) :
    Covers nv.names (atomize nv t).names.names := by
  cases t with
  | path p => cases p with | var _ => exact Covers.rfl' _
  | lam _ _ => exact Covers.tail _ _
  | obj _ _ _ => exact Covers.tail _ _
  | app _ _ => exact Covers.tail _ _
  | proj _ _ => exact Covers.tail _ _
  | «let» _ _ _ => exact Covers.tail _ _
  | box _ => exact Covers.tail _ _
  | unbox _ _ => exact Covers.tail _ _
  | asc _ _ => exact Covers.tail _ _

/-- `atomize` adds no capture binder. -/
theorem atomize_capNames {s : Sig} (nv : NameEnv s) (t : ATm s) :
    (atomize nv t).names.capNames = nv.capNames := by
  cases t with
  | path p => cases p with | var _ => rfl
  | _ => rfl

/-! ## Capture sets -/

/-- Resolve a capture atom.  A plain name takes the innermost binder of
either kind, the receiver of `x.C` a term binder. -/
def resolveCapAtom {s : Sig} (Λ : LabelTable) (nv : NameEnv s) : SCapAtom → Option (CapAtom s)
  | .name x =>
      match nv.find? x with
      | some ⟨.var, i⟩ => some (.var i)
      | some ⟨.cap, κ⟩ => some (.cvar κ)
      | none => none
  | .sel x C => do
      let i ← nv.findVar? x
      let l ← labelTyp? Λ C
      pure (.sel i l)
  | .any => some .any

/-- Resolve a capture set, atom by atom. -/
def resolveCap {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (c : SCap) : Option (CaptureSet s) :=
  match c with
  | [] => some []
  | a :: c => do
      let a' ← resolveCapAtom Λ nv a
      let c' ← resolveCap Λ nv c
      pure (a' :: c')
termination_by structural c

/-! ## Types -/

/-- The shape of a phrase at a type-member bound or a type definition: a
phrase written `S ^ C` is boxed, any other phrase stands for its shape. -/
def asBound {s : Sig} (T : SType) (T' : Ty s) : Shape s :=
  match T with
  | .capt _ _ => .box T'
  | _ => T'.shape

/-- The shape of a phrase at any other shape position: a phrase written
`S ^ C` fails, any other phrase stands for its shape. -/
def asShape? {s : Sig} (T : SType) (T' : Ty s) : Option (Shape s) :=
  match T with
  | .capt _ _ => none
  | _ => some T'.shape

/-- A surface phrase read as a type.  A bare shape is pure, `S ^ C` carries
`C`.  Each recursive call is on a direct subphrase, and the shape reading of a
subphrase is `asBound` or `asShape?`, which do not recurse. -/
def resolveT {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (T : SType) : Option (Ty s) :=
  match T with
  | .top => some (.capt [] .top)
  | .bot => some (.capt [] .bot)
  | .typ A S T => do
      let l ← labelTyp? Λ A
      let S' ← resolveT Λ nv S
      let T' ← resolveT Λ nv T
      pure (.capt [] (.typ l (asBound S S') (asBound T T')))
  | .fld a T => do
      let l ← labelTrm? Λ a
      let T' ← resolveT Λ nv T
      pure (.capt [] (.fld l T'))
  | .cap C lo hi => do
      let l ← labelTyp? Λ C
      let lo' ← resolveCap Λ nv lo
      let hi' ← resolveCap Λ nv hi
      pure (.capt [] (.cap l lo' hi'))
  | .sel x A => do
      let i ← nv.findVar? x
      let l ← labelTyp? Λ A
      pure (.capt [] (.sel (.var i) l))
  | .mu x T => do
      let T' ← resolveT Λ (nv.cons x) T
      let S ← asShape? T T'
      pure (.capt [] (.mu S))
  | .all x S T => do
      let S' ← resolveT Λ nv S
      let T' ← resolveT Λ (nv.cons x) T
      pure (.capt [] (.all S' T'))
  | .and S T => do
      let S' ← resolveT Λ nv S
      let T' ← resolveT Λ nv T
      let S'' ← asShape? S S'
      let T'' ← asShape? T T'
      pure (.capt [] (.and S'' T''))
  | .box T => do
      let T' ← resolveT Λ nv T
      pure (.capt [] (.box T'))
  | .capt S C => do
      let S' ← resolveT Λ nv S
      let S'' ← asShape? S S'
      let C' ← resolveCap Λ nv C
      pure (.capt C' S'')
termination_by structural T

/-- An annotation at a `let` or an ascription: tested by the frozen
`Ty.anyOk` and expanded at the platform set `P`. -/
def resolveTy {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (P : CaptureSet s) (T : SType) :
    Option (Ty s) := do
  let T' ← resolveT Λ nv T
  if T'.anyOk then pure (T'.expand P) else none

/-- A function's domain: tested by the arrow clause of the frozen
`Shape.anyOk`, no `any` in its own outer set, and expanded at `P`. -/
def resolveDom {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (P : CaptureSet s) (T : SType) :
    Option (Ty s) := do
  let T' ← resolveT Λ nv T
  if CaptureSet.noAny T'.captureSet && T'.anyOk then pure (T'.expand P) else none

/-- The set an object's self shape reads `any` as: the object's own set
under the self binder, with the self. -/
def selfRead {s : Sig} (U : CaptureSet s) : CaptureSet (s,x) :=
  CaptureSet.weaken U ∪ [CapAtom.var .here]

/-- The self annotation of `ν(x : T. d)`: the self shape under the binder and
the object's own set outside it, if written.  It is tested and expanded as
the type `μ S ^ U` it stands for, at `P`, with `U` empty when not written. -/
def resolveSelf {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (P : CaptureSet s) (x : String)
    (T : SType) : Option (Shape (s,x) × Option (CaptureSet s)) := do
  let S' ← resolveT Λ (nv.cons x) T.selfShape
  let S ← asShape? T.selfShape S'
  let U ← (match T.selfSet with
    | none => some none
    | some U => (resolveCap Λ nv U).map some)
  let U' := U.map (fun C => CaptureSet.expand C P)
  if S.anyOk then pure (S.expand (selfRead (U'.getD [])), U') else none

/-! ## Terms -/

mutual
/-- Resolve a surface term under the platform set `P`, inserting `let`
bindings for the four direct style forms.  The result is in monadic normal
form by construction. -/
def resolveTm {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (P : CaptureSet s) (e : STm) :
    Option (ATm s) :=
  match e with
  | .var x => do
      let i ← nv.findVar? x
      pure (.path (.var i))
  | .lam x T t => do
      let T' ← resolveDom Λ nv P T
      let t' ← resolveTm Λ (nv.cons x) (CaptureSet.weaken P) t
      pure (.lam T' t')
  | .obj x T d => do
      let SU ← resolveSelf Λ nv P x T
      let d' ← resolveDefs Λ (nv.cons x) (CaptureSet.weaken P) d
      pure (.obj SU.1 SU.2 d')
  | .app t u => do
      let t₀ ← resolveTm Λ nv P t
      let a := atomize nv t₀
      let u₀ ← resolveTm Λ a.names (CaptureSet.rename P a.spine.rename) u
      let b := atomize a.names u₀
      pure ((a.spine.append b.spine).plug (.app (b.spine.rename.var a.var) b.var))
  | .proj t a => do
      let t₀ ← resolveTm Λ nv P t
      let c := atomize nv t₀
      let l ← labelTrm? Λ a
      pure (c.spine.plug (.proj c.var l))
  | .«let» x ann t u => do
      let ann' ← (match ann with
        | none => some none
        | some U => (resolveTy Λ nv P U).map some)
      let t' ← resolveTm Λ nv P t
      let u' ← resolveTm Λ (nv.cons x) (CaptureSet.weaken P) u
      pure (.let ann' t' u')
  | .box t => do
      let t₀ ← resolveTm Λ nv P t
      let c := atomize nv t₀
      pure (c.spine.plug (.box c.var))
  | .unbox C t => do
      let t₀ ← resolveTm Λ nv P t
      let c := atomize nv t₀
      let C' ← resolveCap Λ c.names C
      if CaptureSet.noAny C' then pure (c.spine.plug (.unbox C' c.var)) else none
  | .asc t T => do
      let t' ← resolveTm Λ nv P t
      let T' ← resolveTy Λ nv P T
      pure (.asc t' T')
termination_by structural e
/-- Resolve a surface definition list under the platform set `P`. -/
def resolveDefs {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (P : CaptureSet s) (d : SDefs) :
    Option (ADefs s) :=
  match d with
  | .typ A T => do
      let l ← labelTyp? Λ A
      let T' ← resolveT Λ nv T
      let S := asBound T T'
      if S.noAny then pure (.typ l S) else none
  | .trm a t => do
      let l ← labelTrm? Λ a
      let t' ← resolveTm Λ nv P t
      pure (.trm l t')
  | .and d e => do
      let d' ← resolveDefs Λ nv P d
      let e' ← resolveDefs Λ nv P e
      pure (.and d' e')
  | .cap C c => do
      let l ← labelTyp? Λ C
      let c' ← resolveCap Λ nv c
      if CaptureSet.noAny c' then pure (.cap l c') else none
termination_by structural d
end

/-- Resolve a surface term at a given environment and platform set, the
entry point for a term that sits under a context. -/
def resolveIn {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (P : CaptureSet s) (e : STm) :
    Option (ATm s) :=
  resolveTm Λ nv P e

/-- Resolve a closed program over a platform. -/
def resolveTop (Λ : LabelTable) (π : PlatformNames) (e : STm) : Option (ATm π.sig) :=
  resolveTm Λ π.names π.set e

/-! ## Totality

Resolution succeeds on a phrase whose free names are in scope at the kind
their position needs, whose labels are in the table, whose `any` atoms are
where the position test admits them (`AnyPlaced`), and whose written
capturing types sit where the resolver reads them (`CaptPlaced`).  The proof
is by structural recursion on the surface phrase.  Two facts about `resolveT`
carry it: it succeeds on such a phrase, and the type it returns passes the
frozen `any` tests whenever the phrase passes the surface ones
(`resolveT_any`).  In the direct style clauses the operand is resolved under
the environment `atomize` returns, and `atomize_names_covers` carries the
scoping across. -/

/-- A phrase not written `S ^ C` stands for its shape. -/
theorem asShape?_of_not_capt {s : Sig} {T : SType} (h : T.isCapt = false) (T' : Ty s) :
    asShape? T T' = some T'.shape := by
  cases T <;> simp_all [asShape?, SType.isCapt]

/-- A scoped and labelled capture set resolves. -/
theorem resolveCap_isSome : ∀ (c : SCap) {s : Sig} (Λ : LabelTable) (nv : NameEnv s),
    SCap.Scoped nv.capNames nv.names c = true → SCap.LabelsIn Λ c = true →
    (resolveCap Λ nv c).isSome = true
  | [], _, _, _, _, _ => rfl
  | .name x :: c, _, Λ, nv, hs, hl => by
      simp only [SCap.Scoped, SCap.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨⟨k, i⟩, hf⟩ := Option.isSome_iff_exists.mp (NameEnv.find?_isSome nv x hs.1)
      obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp (resolveCap_isSome c Λ nv hs.2 hl)
      cases k <;> simp [resolveCap, resolveCapAtom, hf, hc]
  | .sel x C :: c, _, Λ, nv, hs, hl => by
      simp only [SCap.Scoped, SCap.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (NameEnv.findVar?_isSome nv x hs.1)
      obtain ⟨l, hlC⟩ := Option.isSome_iff_exists.mp hl.1
      obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp (resolveCap_isSome c Λ nv hs.2 hl.2)
      simp [resolveCap, resolveCapAtom, hi, hlC, hc]
  | .any :: c, _, Λ, nv, hs, hl => by
      simp only [SCap.Scoped, SCap.LabelsIn] at hs hl
      obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp (resolveCap_isSome c Λ nv hs hl)
      simp [resolveCap, resolveCapAtom, hc]

/-- A resolved capture set holds an `any` only where the written one does. -/
theorem resolveCap_noAny : ∀ (c : SCap) {s : Sig} (Λ : LabelTable) (nv : NameEnv s)
    (c' : CaptureSet s), resolveCap Λ nv c = some c' → SCap.NoAny c = true →
    CaptureSet.noAny c' = true
  | [], _, _, _, c', h, _ => by
      simp [resolveCap] at h; subst h; rfl
  | .name x :: c, _, Λ, nv, c', h, ha => by
      simp only [SCap.NoAny] at ha
      simp only [resolveCap, resolveCapAtom, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨a, ha', c'', hc, rfl⟩ := h
      have := resolveCap_noAny c Λ nv c'' hc ha
      cases hf : nv.find? x with
      | none => simp [hf] at ha'
      | some p =>
        obtain ⟨k, i⟩ := p
        cases k <;> simp [hf] at ha' <;> subst ha' <;> simpa [CaptureSet.noAny] using this
  | .sel x C :: c, _, Λ, nv, c', h, ha => by
      simp only [SCap.NoAny] at ha
      simp only [resolveCap, resolveCapAtom, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨a, ⟨i, _, l, _, rfl⟩, c'', hc, rfl⟩ := h
      simpa [CaptureSet.noAny] using resolveCap_noAny c Λ nv c'' hc ha
  | .any :: c, _, _, _, _, _, ha => by simp [SCap.NoAny] at ha

/-- A scoped and labelled phrase whose capturing types are placed resolves
as a type. -/
theorem resolveT_isSome : ∀ (T : SType) {s : Sig} (Λ : LabelTable) (nv : NameEnv s),
    SType.Scoped nv.capNames nv.names T = true → SType.LabelsIn Λ T = true →
    SType.CaptPlaced T = true → (resolveT Λ nv T).isSome = true
  | .top, _, _, _, _, _, _ => rfl
  | .bot, _, _, _, _, _, _ => rfl
  | .typ A S T, _, Λ, nv, hs, hl, hc => by
      simp only [SType.Scoped, SType.LabelsIn, SType.CaptPlaced, Bool.and_eq_true] at hs hl hc
      obtain ⟨l, hA⟩ := Option.isSome_iff_exists.mp hl.1.1
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp (resolveT_isSome S Λ nv hs.1 hl.1.2 hc.1)
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp (resolveT_isSome T Λ nv hs.2 hl.2 hc.2)
      simp [resolveT, hA, hS, hT]
  | .fld a T, _, Λ, nv, hs, hl, hc => by
      simp only [SType.Scoped, SType.LabelsIn, SType.CaptPlaced, Bool.and_eq_true] at hs hl hc
      obtain ⟨l, ha⟩ := Option.isSome_iff_exists.mp hl.1
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp (resolveT_isSome T Λ nv hs hl.2 hc)
      simp [resolveT, ha, hT]
  | .cap C lo hi, _, Λ, nv, hs, hl, _ => by
      simp only [SType.Scoped, SType.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨l, hC⟩ := Option.isSome_iff_exists.mp hl.1.1
      obtain ⟨lo', hlo⟩ := Option.isSome_iff_exists.mp (resolveCap_isSome lo Λ nv hs.1 hl.1.2)
      obtain ⟨hi', hhi⟩ := Option.isSome_iff_exists.mp (resolveCap_isSome hi Λ nv hs.2 hl.2)
      simp [resolveT, hC, hlo, hhi]
  | .sel x A, _, Λ, nv, hs, hl, _ => by
      simp only [SType.Scoped, SType.LabelsIn] at hs hl
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (NameEnv.findVar?_isSome nv x hs)
      obtain ⟨l, hA⟩ := Option.isSome_iff_exists.mp hl
      simp [resolveT, hi, hA]
  | .mu x T, _, Λ, nv, hs, hl, hc => by
      simp only [SType.Scoped, SType.LabelsIn, SType.CaptPlaced, Bool.and_eq_true,
        Bool.not_eq_true'] at hs hl hc
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp
        (resolveT_isSome T Λ (nv.cons x) hs hl hc.2)
      simp [resolveT, hT, asShape?_of_not_capt hc.1]
  | .all x S T, _, Λ, nv, hs, hl, hc => by
      simp only [SType.Scoped, SType.LabelsIn, SType.CaptPlaced, Bool.and_eq_true] at hs hl hc
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp (resolveT_isSome S Λ nv hs.1 hl.1 hc.1)
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp
        (resolveT_isSome T Λ (nv.cons x) hs.2 hl.2 hc.2)
      simp [resolveT, hS, hT]
  | .and S T, _, Λ, nv, hs, hl, hc => by
      simp only [SType.Scoped, SType.LabelsIn, SType.CaptPlaced, Bool.and_eq_true,
        Bool.not_eq_true'] at hs hl hc
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp (resolveT_isSome S Λ nv hs.1 hl.1 hc.1.2)
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp (resolveT_isSome T Λ nv hs.2 hl.2 hc.2)
      simp [resolveT, hS, hT, asShape?_of_not_capt hc.1.1.1, asShape?_of_not_capt hc.1.1.2]
  | .box T, _, Λ, nv, hs, hl, hc => by
      simp only [SType.Scoped, SType.LabelsIn, SType.CaptPlaced] at hs hl hc
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp (resolveT_isSome T Λ nv hs hl hc)
      simp [resolveT, hT]
  | .capt S C, _, Λ, nv, hs, hl, hc => by
      simp only [SType.Scoped, SType.LabelsIn, SType.CaptPlaced, Bool.and_eq_true,
        Bool.not_eq_true'] at hs hl hc
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp (resolveT_isSome S Λ nv hs.1 hl.1 hc.2)
      obtain ⟨C', hC⟩ := Option.isSome_iff_exists.mp (resolveCap_isSome C Λ nv hs.2 hl.2)
      simp [resolveT, hS, hC, asShape?_of_not_capt hc.1]

/-- No `any` in the written outer set of a phrase, true when none is
written. -/
def SType.outerNoAny : SType → Bool
  | .capt _ C => SCap.NoAny C
  | _ => true

/-- A shape read at a bound holds no `any` when the type it is read from
holds none. -/
theorem asBound_noAny {s : Sig} (T : SType) {T' : Ty s} (h : T'.noAny = true) :
    (asBound T T').noAny = true := by
  cases T' with
  | capt C S =>
    cases T <;> simp_all [asBound, Ty.noAny, Shape.noAny, Ty.shape]

/-- The shape `asShape?` returns is the shape of the type. -/
theorem asShape?_some {s : Sig} {T : SType} {T' : Ty s} {S : Shape s}
    (h : asShape? T T' = some S) : S = T'.shape := by
  cases T <;> simp_all [asShape?]

/-- The shape of a type with no `any` holds no `any`. -/
theorem shape_noAny {s : Sig} {T' : Ty s} (h : T'.noAny = true) : T'.shape.noAny = true := by
  cases T' with
  | capt C S => simp_all [Ty.noAny, Ty.shape]

/-- The shape of a type that passes `Ty.anyOk` passes `Shape.anyOk`. -/
theorem shape_anyOk {s : Sig} {T' : Ty s} (h : T'.anyOk = true) : T'.shape.anyOk = true := by
  cases T' with
  | capt C S => simp_all [Ty.anyOk, Ty.shape]

/-- What a resolved type says about `any`, read off the written phrase: no
`any` in the outer set, none at all, and the frozen `Ty.anyOk`. -/
theorem resolveT_any : ∀ (T : SType) {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (T' : Ty s),
    resolveT Λ nv T = some T' →
    (T.outerNoAny = true → CaptureSet.noAny T'.captureSet = true) ∧
    (SType.NoAny T = true → T'.noAny = true) ∧
    (SType.AnyPlaced T = true → T'.anyOk = true)
  | .top, _, _, _, T', h => by
      simp only [resolveT, Option.some.injEq] at h; subst h; exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | .bot, _, _, _, T', h => by
      simp only [resolveT, Option.some.injEq] at h; subst h; exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | .typ A S T, _, Λ, nv, T', h => by
      simp only [resolveT, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨l, _, S', hS, T'', hT, rfl⟩ := h
      have iS := resolveT_any S Λ nv S' hS
      have iT := resolveT_any T Λ nv T'' hT
      refine ⟨fun _ => rfl, fun ha => ?_, fun ha => ?_⟩ <;>
      · simp only [SType.NoAny, SType.AnyPlaced, Bool.and_eq_true] at ha
        simp [Ty.noAny, Ty.anyOk, Shape.noAny, Shape.anyOk, CaptureSet.noAny,
          asBound_noAny S (iS.2.1 ha.1), asBound_noAny T (iT.2.1 ha.2)]
  | .fld a T, _, Λ, nv, T', h => by
      simp only [resolveT, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨l, _, T'', hT, rfl⟩ := h
      have iT := resolveT_any T Λ nv T'' hT
      refine ⟨fun _ => rfl, fun ha => ?_, fun ha => ?_⟩
      · simp only [SType.NoAny] at ha
        simp [Ty.noAny, Shape.noAny, CaptureSet.noAny, iT.2.1 ha]
      · simp only [SType.AnyPlaced] at ha
        simp [Ty.anyOk, Shape.anyOk, iT.2.2 ha]
  | .cap C lo hi, _, Λ, nv, T', h => by
      simp only [resolveT, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨l, _, lo', hlo, hi', hhi, rfl⟩ := h
      refine ⟨fun _ => rfl, fun ha => ?_, fun ha => ?_⟩
      · simp only [SType.NoAny, Bool.and_eq_true] at ha
        simp [Ty.noAny, Shape.noAny, CaptureSet.noAny, resolveCap_noAny lo Λ nv lo' hlo ha.1,
          resolveCap_noAny hi Λ nv hi' hhi ha.2]
      · simp only [SType.AnyPlaced] at ha
        simp [Ty.anyOk, Shape.anyOk, resolveCap_noAny lo Λ nv lo' hlo ha]
  | .sel x A, _, Λ, nv, T', h => by
      simp only [resolveT, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨i, _, l, _, rfl⟩ := h
      exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | .mu x T, _, Λ, nv, T', h => by
      simp only [resolveT, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨T'', hT, Sh, hSh, rfl⟩ := h
      have iT := resolveT_any T Λ (nv.cons x) T'' hT
      rw [asShape?_some hSh]
      refine ⟨fun _ => rfl, fun ha => ?_, fun ha => ?_⟩
      · simp only [SType.NoAny] at ha
        simp [Ty.noAny, Shape.noAny, CaptureSet.noAny, shape_noAny (iT.2.1 ha)]
      · simp only [SType.AnyPlaced] at ha
        simp [Ty.anyOk, Shape.anyOk, shape_anyOk (iT.2.2 ha)]
  | .all x S T, _, Λ, nv, T', h => by
      simp only [resolveT, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨S', hS, T'', hT, rfl⟩ := h
      have iS := resolveT_any S Λ nv S' hS
      have iT := resolveT_any T Λ (nv.cons x) T'' hT
      refine ⟨fun _ => rfl, fun ha => ?_, fun ha => ?_⟩
      · simp only [SType.NoAny, Bool.and_eq_true] at ha
        simp [Ty.noAny, Shape.noAny, CaptureSet.noAny, iS.2.1 ha.1, iT.2.1 ha.2]
      · simp only [SType.AnyPlaced, Bool.and_eq_true] at ha
        have hout : S.outerNoAny = true := by
          have := ha.1.1
          cases S <;> simp_all [SType.outerNoAny]
        cases S' with
        | capt C1 S1 =>
          have h1 := iS.1 hout
          have h2 := iS.2.2 ha.1.2
          simp only [Ty.captureSet, Ty.anyOk] at h1 h2
          simp [Ty.anyOk, Shape.anyOk, h1, h2, iT.2.2 ha.2]
  | .and S T, _, Λ, nv, T', h => by
      simp only [resolveT, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨S', hS, T'', hT, S₁, hS₁, T₁, hT₁, rfl⟩ := h
      have iS := resolveT_any S Λ nv S' hS
      have iT := resolveT_any T Λ nv T'' hT
      rw [asShape?_some hS₁, asShape?_some hT₁]
      refine ⟨fun _ => rfl, fun ha => ?_, fun ha => ?_⟩
      · simp only [SType.NoAny, Bool.and_eq_true] at ha
        simp [Ty.noAny, Shape.noAny, CaptureSet.noAny, shape_noAny (iS.2.1 ha.1),
          shape_noAny (iT.2.1 ha.2)]
      · simp only [SType.AnyPlaced, Bool.and_eq_true] at ha
        simp [Ty.anyOk, Shape.anyOk, shape_anyOk (iS.2.2 ha.1), shape_anyOk (iT.2.2 ha.2)]
  | .box T, _, Λ, nv, T', h => by
      simp only [resolveT, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨T'', hT, rfl⟩ := h
      have iT := resolveT_any T Λ nv T'' hT
      refine ⟨fun _ => rfl, fun ha => ?_, fun ha => ?_⟩
      · simp only [SType.NoAny] at ha
        simp [Ty.noAny, Shape.noAny, CaptureSet.noAny, iT.2.1 ha]
      · simp only [SType.AnyPlaced] at ha
        simp [Ty.anyOk, Shape.anyOk, iT.2.1 ha]
  | .capt S C, _, Λ, nv, T', h => by
      simp only [resolveT, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨S', hS, Sh, hSh, C', hC, rfl⟩ := h
      have iS := resolveT_any S Λ nv S' hS
      rw [asShape?_some hSh]
      refine ⟨fun ha => ?_, fun ha => ?_, fun ha => ?_⟩
      · simp only [SType.outerNoAny] at ha
        simpa [Ty.captureSet] using resolveCap_noAny C Λ nv C' hC ha
      · simp only [SType.NoAny, Bool.and_eq_true] at ha
        simp [Ty.noAny, resolveCap_noAny C Λ nv C' hC ha.1, shape_noAny (iS.2.1 ha.2)]
      · simp only [SType.AnyPlaced] at ha
        simp [Ty.anyOk, shape_anyOk (iS.2.2 ha)]

/-! ## The self annotation, read apart -/

/-- The labels of a self annotation, read apart. -/
theorem SType.selfShape_labelsIn (Λ : LabelTable) (T : SType) (h : SType.LabelsIn Λ T = true) :
    SType.LabelsIn Λ T.selfShape = true ∧
      ∀ U, T.selfSet = some U → SCap.LabelsIn Λ U = true := by
  cases T <;> simp_all [SType.selfShape, SType.selfSet, SType.LabelsIn]

/-- The `any` atoms of a self annotation's shape are placed. -/
theorem SType.selfShape_anyPlaced (T : SType) (h : SType.AnyPlaced T = true) :
    SType.AnyPlaced T.selfShape = true := by
  cases T <;> simp_all [SType.selfShape, SType.AnyPlaced]

/-- The shape of a placed self annotation is not itself written `S ^ C`. -/
theorem SType.selfShape_captPlaced (T : SType) (h : SType.CaptPlaced T = true) :
    T.selfShape.isCapt = false ∧ SType.CaptPlaced T.selfShape = true := by
  cases T <;> simp_all [SType.selfShape, SType.CaptPlaced, SType.isCapt]

/-! ## Totality of the annotation readers -/

/-- Totality of the reading of a `let` type or an ascription. -/
theorem resolveTy_isSome {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (P : CaptureSet s)
    (T : SType) (hs : SType.Scoped nv.capNames nv.names T = true)
    (hl : SType.LabelsIn Λ T = true) (ha : SType.AnyPlaced T = true)
    (hc : SType.CaptPlaced T = true) : (resolveTy Λ nv P T).isSome = true := by
  obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp (resolveT_isSome T Λ nv hs hl hc)
  simp [resolveTy, hT, (resolveT_any T Λ nv T' hT).2.2 ha]

/-- Totality of the reading of a function's domain. -/
theorem resolveDom_isSome {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (P : CaptureSet s)
    (T : SType) (hs : SType.Scoped nv.capNames nv.names T = true)
    (hl : SType.LabelsIn Λ T = true) (ho : T.outerNoAny = true)
    (ha : SType.AnyPlaced T = true)
    (hc : SType.CaptPlaced T = true) : (resolveDom Λ nv P T).isSome = true := by
  obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp (resolveT_isSome T Λ nv hs hl hc)
  have i := resolveT_any T Λ nv T' hT
  simp [resolveDom, hT, i.1 ho, i.2.2 ha]

/-- Totality of the reading of a self annotation. -/
theorem resolveSelf_isSome {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (P : CaptureSet s)
    (x : String) (T : SType) (hs : SType.SelfScoped nv.capNames nv.names x T = true)
    (hl : SType.LabelsIn Λ T = true) (ha : SType.AnyPlaced T = true)
    (hc : SType.CaptPlaced T = true) : (resolveSelf Λ nv P x T).isSome = true := by
  simp only [SType.SelfScoped, Bool.and_eq_true] at hs
  have hlS := SType.selfShape_labelsIn Λ T hl
  have hcS := SType.selfShape_captPlaced T hc
  obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp
    (resolveT_isSome T.selfShape Λ (nv.cons x) hs.1 hlS.1 hcS.2)
  have hok := shape_anyOk ((resolveT_any _ Λ (nv.cons x) S' hS).2.2
    (SType.selfShape_anyPlaced T ha))
  have hSh := asShape?_of_not_capt hcS.1 S'
  have hs2 := hs.2
  cases hU : T.selfSet with
  | none => simp [resolveSelf, hS, hSh, hU, hok]
  | some U =>
      rw [hU] at hs2
      obtain ⟨U', hU'⟩ := Option.isSome_iff_exists.mp
        (resolveCap_isSome U Λ nv hs2 (hlS.2 U hU))
      simp [resolveSelf, hS, hSh, hU, hU', hok]

/-- `atomize` keeps both lists of names in scope for the operand. -/
theorem STm.Scoped_atomize {s : Sig} (nv : NameEnv s) (t₀ : ATm s) (u : STm)
    (h : STm.Scoped nv.capNames nv.names u = true) :
    STm.Scoped (atomize nv t₀).names.capNames (atomize nv t₀).names.names u = true := by
  rw [atomize_capNames]
  exact STm.Scoped_covers _ u (atomize_names_covers nv t₀) h

/-- `atomize` keeps a capture set in scope. -/
theorem SCap.Scoped_atomize {s : Sig} (nv : NameEnv s) (t₀ : ATm s) (C : SCap)
    (h : SCap.Scoped nv.capNames nv.names C = true) :
    SCap.Scoped (atomize nv t₀).names.capNames (atomize nv t₀).names.names C = true := by
  rw [atomize_capNames]
  exact SCap.Scoped_covers _ C (atomize_names_covers nv t₀) h

mutual
/-- Totality of term resolution. -/
theorem resolveTm_isSome : ∀ {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (P : CaptureSet s)
    (e : STm), STm.Scoped nv.capNames nv.names e = true → STm.LabelsIn Λ e = true →
    STm.AnyPlaced e = true → STm.CaptPlaced e = true → (resolveTm Λ nv P e).isSome = true
  | _, Λ, nv, P, .var x, hs, _, _, _ => by
      simp only [STm.Scoped] at hs
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (NameEnv.findVar?_isSome nv x hs)
      simp [resolveTm, hi]
  | _, Λ, nv, P, .lam x T t, hs, hl, ha, hc => by
      simp only [STm.Scoped, STm.LabelsIn, STm.AnyPlaced, STm.CaptPlaced,
        Bool.and_eq_true] at hs hl ha hc
      have ho : T.outerNoAny = true := by
        have := ha.1.1
        cases T <;> simp_all [SType.outerNoAny]
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp
        (resolveDom_isSome Λ nv P T hs.1 hl.1 ho ha.1.2 hc.1)
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ (nv.cons x) (CaptureSet.weaken P) t hs.2 hl.2 ha.2 hc.2)
      simp [resolveTm, hT, ht]
  | _, Λ, nv, P, .obj x T d, hs, hl, ha, hc => by
      simp only [STm.Scoped, STm.LabelsIn, STm.AnyPlaced, STm.CaptPlaced,
        Bool.and_eq_true] at hs hl ha hc
      obtain ⟨SU, hSU⟩ := Option.isSome_iff_exists.mp
        (resolveSelf_isSome Λ nv P x T hs.1 hl.1 ha.1 hc.1)
      obtain ⟨d', hd⟩ := Option.isSome_iff_exists.mp
        (resolveDefs_isSome Λ (nv.cons x) (CaptureSet.weaken P) d hs.2 hl.2 ha.2 hc.2)
      simp [resolveTm, hSU, hd]
  | _, Λ, nv, P, .app t u, hs, hl, ha, hc => by
      simp only [STm.Scoped, STm.LabelsIn, STm.AnyPlaced, STm.CaptPlaced,
        Bool.and_eq_true] at hs hl ha hc
      obtain ⟨t₀, ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ nv P t hs.1 hl.1 ha.1 hc.1)
      obtain ⟨u₀, hu⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ (atomize nv t₀).names
          (CaptureSet.rename P (atomize nv t₀).spine.rename) u
          (STm.Scoped_atomize nv t₀ u hs.2) hl.2 ha.2 hc.2)
      simp [resolveTm, ht, hu]
  | _, Λ, nv, P, .proj t a, hs, hl, ha, hc => by
      simp only [STm.Scoped, STm.LabelsIn, STm.AnyPlaced, STm.CaptPlaced,
        Bool.and_eq_true] at hs hl ha hc
      obtain ⟨t₀, ht⟩ := Option.isSome_iff_exists.mp (resolveTm_isSome Λ nv P t hs hl.1 ha hc)
      obtain ⟨l, hla⟩ := Option.isSome_iff_exists.mp hl.2
      simp [resolveTm, ht, hla]
  | _, Λ, nv, P, .«let» x ann t u, hs, hl, ha, hc => by
      simp only [STm.Scoped, STm.LabelsIn, STm.AnyPlaced, STm.CaptPlaced,
        Bool.and_eq_true] at hs hl ha hc
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ nv P t hs.1.2 hl.1.2 ha.1.2 hc.1.2)
      obtain ⟨u', hu⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ (nv.cons x) (CaptureSet.weaken P) u hs.2 hl.2 ha.2 hc.2)
      cases ann with
      | none => simp [resolveTm, ht, hu]
      | some U =>
          obtain ⟨U', hU⟩ := Option.isSome_iff_exists.mp
            (resolveTy_isSome Λ nv P U hs.1.1 hl.1.1 ha.1.1 hc.1.1)
          simp [resolveTm, hU, ht, hu]
  | _, Λ, nv, P, .box t, hs, hl, ha, hc => by
      simp only [STm.Scoped, STm.LabelsIn, STm.AnyPlaced, STm.CaptPlaced] at hs hl ha hc
      obtain ⟨t₀, ht⟩ := Option.isSome_iff_exists.mp (resolveTm_isSome Λ nv P t hs hl ha hc)
      simp [resolveTm, ht]
  | _, Λ, nv, P, .unbox C t, hs, hl, ha, hc => by
      simp only [STm.Scoped, STm.LabelsIn, STm.AnyPlaced, STm.CaptPlaced,
        Bool.and_eq_true] at hs hl ha hc
      obtain ⟨t₀, ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ nv P t hs.2 hl.2 ha.2 hc)
      obtain ⟨C', hC⟩ := Option.isSome_iff_exists.mp
        (resolveCap_isSome C Λ (atomize nv t₀).names (SCap.Scoped_atomize nv t₀ C hs.1) hl.1)
      have hn := resolveCap_noAny C Λ _ C' hC ha.1
      simp [resolveTm, ht, hC, hn]
  | _, Λ, nv, P, .asc t T, hs, hl, ha, hc => by
      simp only [STm.Scoped, STm.LabelsIn, STm.AnyPlaced, STm.CaptPlaced,
        Bool.and_eq_true] at hs hl ha hc
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ nv P t hs.1 hl.1 ha.1 hc.1)
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp
        (resolveTy_isSome Λ nv P T hs.2 hl.2 ha.2 hc.2)
      simp [resolveTm, ht, hT]
/-- Totality of definition resolution. -/
theorem resolveDefs_isSome : ∀ {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (P : CaptureSet s)
    (d : SDefs), SDefs.Scoped nv.capNames nv.names d = true → SDefs.LabelsIn Λ d = true →
    SDefs.AnyPlaced d = true → SDefs.CaptPlaced d = true → (resolveDefs Λ nv P d).isSome = true
  | _, Λ, nv, P, .typ A T, hs, hl, ha, hc => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, SDefs.AnyPlaced, SDefs.CaptPlaced,
        Bool.and_eq_true] at hs hl ha hc
      obtain ⟨l, hA⟩ := Option.isSome_iff_exists.mp hl.1
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp (resolveT_isSome T Λ nv hs hl.2 hc)
      have hn := asBound_noAny T ((resolveT_any T Λ nv T' hT).2.1 ha)
      simp [resolveDefs, hA, hT, hn]
  | _, Λ, nv, P, .trm a t, hs, hl, ha, hc => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, SDefs.AnyPlaced, SDefs.CaptPlaced,
        Bool.and_eq_true] at hs hl ha hc
      obtain ⟨l, hla⟩ := Option.isSome_iff_exists.mp hl.1
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp (resolveTm_isSome Λ nv P t hs hl.2 ha hc)
      simp [resolveDefs, hla, ht]
  | _, Λ, nv, P, .and d e, hs, hl, ha, hc => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, SDefs.AnyPlaced, SDefs.CaptPlaced,
        Bool.and_eq_true] at hs hl ha hc
      obtain ⟨d', hd⟩ := Option.isSome_iff_exists.mp
        (resolveDefs_isSome Λ nv P d hs.1 hl.1 ha.1 hc.1)
      obtain ⟨e', he⟩ := Option.isSome_iff_exists.mp
        (resolveDefs_isSome Λ nv P e hs.2 hl.2 ha.2 hc.2)
      simp [resolveDefs, hd, he]
  | _, Λ, nv, P, .cap C c, hs, hl, ha, _ => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, SDefs.AnyPlaced, Bool.and_eq_true] at hs hl ha
      obtain ⟨l, hC⟩ := Option.isSome_iff_exists.mp hl.1
      obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (resolveCap_isSome c Λ nv hs hl.2)
      have hn := resolveCap_noAny c Λ nv c' hc' ha
      simp [resolveDefs, hC, hc', hn]
end

/-! ## No `any` in what the resolver emits -/

/-- No `any` in the bindings of a spine. -/
def Spine.NoAnyAnn {s s' : Sig} (sp : Spine s s') : Bool :=
  match sp with
  | .nil => true
  | .cons t sp => t.NoAnyAnn && sp.NoAnyAnn
termination_by structural sp

/-- Plugging keeps annotations free of `any`. -/
theorem Spine.plug_noAny : ∀ {s s' : Sig} (sp : Spine s s') (u : ATm s'),
    sp.NoAnyAnn = true → u.NoAnyAnn = true → (sp.plug u).NoAnyAnn = true
  | _, _, .nil, _, _, hu => hu
  | _, _, .cons t sp, u, hsp, hu => by
      simp only [Spine.NoAnyAnn, Bool.and_eq_true] at hsp
      simp [Spine.plug, ATm.NoAnyAnn, hsp.1, Spine.plug_noAny sp u hsp.2 hu]

/-- Appending keeps the bindings free of `any`. -/
theorem Spine.append_noAny : ∀ {s s' s'' : Sig} (sp : Spine s s') (sp' : Spine s' s''),
    sp.NoAnyAnn = true → sp'.NoAnyAnn = true → (sp.append sp').NoAnyAnn = true
  | _, _, _, .nil, _, _, h' => h'
  | _, _, _, .cons t sp, sp', h, h' => by
      simp only [Spine.NoAnyAnn, Bool.and_eq_true] at h
      simp [Spine.append, Spine.NoAnyAnn, h.1, Spine.append_noAny sp sp' h.2 h']

/-- The binding `atomize` inserts is the term it was given. -/
theorem atomize_noAny {s : Sig} (nv : NameEnv s) (t : ATm s) (h : t.NoAnyAnn = true) :
    (atomize nv t).spine.NoAnyAnn = true := by
  cases t with
  | path p => cases p with | var _ => rfl
  | _ => simpa [atomize, Spine.NoAnyAnn] using h

/-- A resolved `let` type or ascription holds no `any`. -/
theorem resolveTy_noAny {s : Sig} {Λ : LabelTable} {nv : NameEnv s} {P : CaptureSet s}
    {T : SType} {T' : Ty s} (hP : CaptureSet.noAny P = true)
    (h : resolveTy Λ nv P T = some T') : T'.noAny = true := by
  simp only [resolveTy, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨T'', _, h⟩ := h
  by_cases hok : T''.anyOk = true
  · simp only [hok, if_true, Option.pure_def, Option.some.injEq] at h
    subst h
    exact Captures.DotMNF.Ty.noAny_expand T'' P hok hP
  · simp [hok] at h

/-- A resolved domain holds no `any`. -/
theorem resolveDom_noAny {s : Sig} {Λ : LabelTable} {nv : NameEnv s} {P : CaptureSet s}
    {T : SType} {T' : Ty s} (hP : CaptureSet.noAny P = true)
    (h : resolveDom Λ nv P T = some T') : T'.noAny = true := by
  simp only [resolveDom, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨T'', _, h⟩ := h
  by_cases hok : (CaptureSet.noAny T''.captureSet && T''.anyOk) = true
  · simp only [hok, if_true, Option.pure_def, Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true] at hok
    exact Captures.DotMNF.Ty.noAny_expand T'' P hok.2 hP
  · simp [hok] at h

/-- A resolved self annotation and its set hold no `any`. -/
theorem resolveSelf_noAny {s : Sig} {Λ : LabelTable} {nv : NameEnv s} {P : CaptureSet s}
    {x : String} {T : SType} {SU : Shape (s,x) × Option (CaptureSet s)}
    (hP : CaptureSet.noAny P = true) (h : resolveSelf Λ nv P x T = some SU) :
    SU.1.noAny = true ∧ (match SU.2 with | none => true | some C => CaptureSet.noAny C) = true := by
  simp only [resolveSelf, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨S', _, Sh, _, U, _, h⟩ := h
  by_cases hok : Sh.anyOk = true
  · simp only [hok, if_true, Option.pure_def, Option.some.injEq] at h
    subst h
    have hU : CaptureSet.noAny ((U.map (fun C => CaptureSet.expand C P)).getD []) = true := by
      cases U with
      | none => rfl
      | some C => exact CaptureSet.noAny_expand hP C
    refine ⟨Captures.DotMNF.Shape.noAny_expand Sh _ hok (CaptureSet.noAny_self hU), ?_⟩
    cases U with
    | none => rfl
    | some C => exact CaptureSet.noAny_expand hP C
  · simp [hok] at h

mutual
/-- A resolved term holds no `any` in an annotation, a set or a type
definition. -/
theorem resolveTm_noAny : ∀ {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (P : CaptureSet s)
    (e : STm) (a : ATm s), CaptureSet.noAny P = true → resolveTm Λ nv P e = some a →
    a.NoAnyAnn = true
  | _, Λ, nv, P, .var x, a, _, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨i, _, rfl⟩ := h
      rfl
  | _, Λ, nv, P, .lam x T t, a, hP, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨T', hT, t', ht, rfl⟩ := h
      simp [ATm.NoAnyAnn, resolveDom_noAny hP hT,
        resolveTm_noAny Λ (nv.cons x) _ t t' (CaptureSet.noAny_weaken hP) ht]
  | _, Λ, nv, P, .obj x T d, a, hP, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨SU, hSU, d', hd, rfl⟩ := h
      have i := resolveSelf_noAny hP hSU
      have id := resolveDefs_noAny Λ (nv.cons x) _ d d' (CaptureSet.noAny_weaken hP) hd
      obtain ⟨S, U⟩ := SU
      cases U <;> simp_all [ATm.NoAnyAnn]
  | _, Λ, nv, P, .app t u, a, hP, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t₀, ht, u₀, hu, rfl⟩ := h
      have it := resolveTm_noAny Λ nv P t t₀ hP ht
      have iu := resolveTm_noAny Λ _ _ u u₀ (CaptureSet.noAny_rename hP _) hu
      exact Spine.plug_noAny _ _
        (Spine.append_noAny _ _ (atomize_noAny nv t₀ it) (atomize_noAny _ u₀ iu)) rfl
  | _, Λ, nv, P, .proj t a', a, hP, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t₀, ht, l, _, rfl⟩ := h
      exact Spine.plug_noAny _ _ (atomize_noAny nv t₀ (resolveTm_noAny Λ nv P t t₀ hP ht)) rfl
  | _, Λ, nv, P, .«let» x ann t u, a, hP, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ann', hann, t', ht, u', hu, rfl⟩ := h
      have it := resolveTm_noAny Λ nv P t t' hP ht
      have iu := resolveTm_noAny Λ (nv.cons x) _ u u' (CaptureSet.noAny_weaken hP) hu
      cases ann with
      | none =>
          simp only [Option.some.injEq] at hann
          subst hann
          simp [ATm.NoAnyAnn, it, iu]
      | some U =>
          simp only [Option.map_eq_some_iff] at hann
          obtain ⟨U', hU, rfl⟩ := hann
          simp [ATm.NoAnyAnn, it, iu, resolveTy_noAny hP hU]
  | _, Λ, nv, P, .box t, a, hP, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t₀, ht, rfl⟩ := h
      exact Spine.plug_noAny _ _ (atomize_noAny nv t₀ (resolveTm_noAny Λ nv P t t₀ hP ht)) rfl
  | _, Λ, nv, P, .unbox C t, a, hP, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨t₀, ht, C', _, h⟩ := h
      by_cases hn : CaptureSet.noAny C' = true
      · simp only [hn, if_true, Option.pure_def, Option.some.injEq] at h
        subst h
        exact Spine.plug_noAny _ _
          (atomize_noAny nv t₀ (resolveTm_noAny Λ nv P t t₀ hP ht)) hn
      · simp [hn] at h
  | _, Λ, nv, P, .asc t T, a, hP, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, T', hT, rfl⟩ := h
      simp [ATm.NoAnyAnn, resolveTm_noAny Λ nv P t t' hP ht, resolveTy_noAny hP hT]
/-- Resolved definitions hold no `any`. -/
theorem resolveDefs_noAny : ∀ {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (P : CaptureSet s)
    (d : SDefs) (a : ADefs s), CaptureSet.noAny P = true → resolveDefs Λ nv P d = some a →
    a.NoAnyAnn = true
  | _, Λ, nv, P, .typ A T, a, _, h => by
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨l, _, T', _, h⟩ := h
      by_cases hn : (asBound T T').noAny = true
      · simp only [hn, if_true, Option.pure_def, Option.some.injEq] at h
        subst h
        exact hn
      · simp [hn] at h
  | _, Λ, nv, P, .trm a' t, a, hP, h => by
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨l, _, t', ht, rfl⟩ := h
      exact resolveTm_noAny Λ nv P t t' hP ht
  | _, Λ, nv, P, .and d e, a, hP, h => by
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨d', hd, e', he, rfl⟩ := h
      simp [ADefs.NoAnyAnn, resolveDefs_noAny Λ nv P d d' hP hd,
        resolveDefs_noAny Λ nv P e e' hP he]
  | _, Λ, nv, P, .cap C c, a, _, h => by
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨l, _, c', _, h⟩ := h
      by_cases hn : CaptureSet.noAny c' = true
      · simp only [hn, if_true, Option.pure_def, Option.some.injEq] at h
        subst h
        exact hn
      · simp [hn] at h
end

/-- Every annotation the resolver emits holds no `any`, given a platform set
that holds none.  The expansion step is the frozen `Ty.noAny_expand`. -/
theorem resolve_noAny {s : Sig} {Λ : LabelTable} {nv : NameEnv s} {P : CaptureSet s} {e : STm}
    {a : ATm s} (hP : CaptureSet.noAny P = true) (h : resolveTm Λ nv P e = some a) :
    ATm.NoAnyAnn a = true :=
  resolveTm_noAny Λ nv P e a hP h

/-! ## Platform sets hold no `any`

`resolve_noAny` asks the platform set to hold no `any`.  Every platform built
by `PlatformNames.ofList` does. -/

/-- Pushing capabilities keeps a platform set free of `any`. -/
theorem PlatformNames.pushAll_set_noAny : ∀ (ys : List String) (π : PlatformNames),
    CaptureSet.noAny π.set = true → CaptureSet.noAny (π.pushAll ys).set = true
  | [], _, h => h
  | y :: ys, π, h => by
      apply PlatformNames.pushAll_set_noAny ys (π.push y)
      exact CaptureSet.noAny_append (CaptureSet.noAny_weaken h)
        (CaptureSet.noAny_cons_of_ne (by simp) CaptureSet.noAny_nil)

/-- The set of a platform built from names holds no `any`. -/
theorem PlatformNames.ofList_set_noAny (ys : List String) :
    CaptureSet.noAny (PlatformNames.ofList ys).set = true :=
  PlatformNames.pushAll_set_noAny ys _ rfl

/-! ## The two spine equations and the no insertion property -/

/-- Plugging into an appended spine is plugging twice. -/
theorem Spine.plug_append : ∀ {s s' s'' : Sig} (sp : Spine s s') (sp' : Spine s' s'')
    (u : ATm s''), (sp.append sp').plug u = sp.plug (sp'.plug u)
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .cons t sp, sp', u => by
      show ATm.let none t ((sp.append sp').plug u) = _
      rw [Spine.plug_append sp sp' u]
      rfl

/-- The weakening of an appended spine is the composite of the two. -/
theorem Spine.rename_append : ∀ {s s' s'' : Sig} (sp : Spine s s') (sp' : Spine s' s''),
    (sp.append sp').rename = Rename.comp sp.rename sp'.rename
  | _, _, _, .nil, sp' => Rename.funext' (fun _ => rfl)
  | _, _, _, .cons _ sp, sp' => by
      show Rename.comp Rename.succ ((sp.append sp').rename) = _
      rw [Spine.rename_append sp sp']
      exact Rename.funext' (fun _ => rfl)

/-- The no insertion property: a resolved term that is already a variable is
brought into variable position with no binding inserted. -/
theorem atomize_var {s : Sig} (nv : NameEnv s) (i : BVar s .var) :
    atomize nv (.path (.var i)) = ⟨s, .nil, nv, i⟩ := rfl

/-! ## The programs

Each program of `Notation.lean` is resolved over the platform `k1, k2`, the
version's `κ₁` and `κ₂`, with the labels of the version's examples, and its
erasure is compared with the version's own term by `decide`.  Resolution is
structural, so the kernel reduces it. -/

open Captures.DotMNF.Examples (C7tm C2tm S3tm S1tm S2tm S1TyAny S1Ty S2MkTyAny S2MkTy platSet
  k1 unitTy lA lB lT la lb lv)

/-- The labels of the version's examples (`DotMNF/Examples.lean`): the type
labels `A`, `B`, `T` and the capture member `C`, and the term labels. -/
def Λc : LabelTable :=
  [("A", .typ 0), ("B", .typ 1), ("T", .typ 2), ("C", .typ 3),
   ("a", .trm 0), ("b", .trm 1), ("v", .trm 2), ("elem", .trm 3), ("run", .trm 4),
   ("e1", .trm 5), ("e2", .trm 6), ("read", .trm 7), ("next", .trm 8)]

/-- The platform of the capture examples, `k1` outer and `k2` inner. -/
def πc : PlatformNames := PlatformNames.ofList ["k1", "k2"]

/-- The platform set is the version's `platSet`. -/
example : πc.set = platSet := by decide

/-! ### The capture examples -/

/-- C7 with its boxes and its unboxing written is the version's `C7tm`. -/
example : (resolveTop Λc πc C7src).map ATm.erase = some C7tm := by decide

/-- C2, its call `x.run u` in direct style, is the version's `C2tm`: the
inserted binding is the version's `let g = x.run in g u`. -/
example : (resolveTop Λc πc C2src).map ATm.erase = some C2tm := by decide

/-- S3, its member bound written at a capturing type and boxed by the
resolver, is the version's `S3tm`. -/
example : (resolveTop Λc πc S3src).map ATm.erase = some S3tm := by decide

/-- S1, `withFile` bound by an ascription at its `any` signature, is the
version's `S1tm`. -/
example : (resolveTop Λc πc S1src).map ATm.erase = some S1tm := by decide

/-- S2, `mk` bound by an ascription at its `any` signature, is the version's
`S2tm`. -/
example : (resolveTop Λc πc S2src).map ATm.erase = some S2tm := by decide

/-- C7 with no term level box has the skeleton of C7 with its boxes. -/
example : (resolveTop Λc πc C7nbSrc).map ATm.skel = (resolveTop Λc πc C7src).map ATm.skel := by
  decide

/-- S3 with no term level box has the skeleton of S3 with its boxes. -/
example : (resolveTop Λc πc S3nbSrc).map ATm.skel = (resolveTop Λc πc S3src).map ATm.skel := by
  decide

/-- The box free programs differ from the boxed ones: the boxes are what box
inference has to supply. -/
example : (resolveTop Λc πc C7nbSrc).map ATm.erase ≠ some C7tm := by decide

/-! ### The annotations of S1 and S2

The ascription that binds `withFile` and `mk` is resolved to the version's
written signature and expanded at the platform set, which reads the result
`any` as the arrow's own set with its binder. -/

/-- The type of the ascription a leading `let` binds. -/
def leadAsc {s : Sig} : ATm s → Option (Ty s)
  | .let _ (.asc _ T) _ => some T
  | _ => none

/-- The written type of a leading ascription, as a surface phrase. -/
def leadAscSrc : STm → Option SType
  | .«let» _ none (.asc _ T) _ => some T
  | _ => none

/-- The signature of `withFile` as written resolves to the version's
`S1TyAny`, `any` and all. -/
example : (leadAscSrc S1src).bind (resolveT Λc πc.names) = some (S1TyAny k1) := by decide

/-- The resolved annotation of `withFile` is the expansion of `S1TyAny` at
the platform set, which is the version's `S1Ty`. -/
example : (resolveTop Λc πc S1src).bind leadAsc = some ((S1TyAny k1).expand platSet) := by
  decide

example : (resolveTop Λc πc S1src).bind leadAsc = some (S1Ty k1) := by decide

/-- The signature of `mk` as written resolves to the version's `S2MkTyAny`. -/
example : (leadAscSrc S2src).bind (resolveT Λc πc.names) = some (S2MkTyAny k1) := by decide

/-- The resolved annotation of `mk` is the expansion of `S2MkTyAny` at the
platform set, which is the version's `S2MkTy`. -/
example : (resolveTop Λc πc S2src).bind leadAsc = some ((S2MkTyAny k1).expand platSet) := by
  decide

example : (resolveTop Λc πc S2src).bind leadAsc = some (S2MkTy k1) := by decide

/-- The second annotation of S2, the ascription of `un`, is `⊤`. -/
example : (resolveTop Λc πc S2src).bind
    (fun | .let _ _ (.let _ (.asc _ T) _) => some T | _ => none) = some unitTy := by decide

/-! ### Two programs that do not resolve -/

/-- `any` in the outer set of a function's domain is rejected, the arrow
clause of the version's `Shape.anyOk`. -/
example : (resolveTop Λc πc (cap% λ(x : ⊤ ^ {any}). x)).isNone = true := by decide

/-- A capturing type as an operand of `∧` is rejected: `^` binds looser than
`∧`, so the set belongs on the whole intersection. -/
example :
    (resolveTop Λc πc (cap% ν(z : ({a : ⊤} ^ {k1}) ∧ {b : ⊤}. {a = z} ∧ {b = z}))).isNone =
      true := by decide

/-- The same object with the set on the whole self annotation resolves, and
its set is the object's own. -/
example :
    (resolveTop Λc πc (cap% ν(z : {a : ⊤} ∧ {b : ⊤} ^ {k1}. {a = z} ∧ {b = z}))).map
        (fun | .obj _ U _ => U | _ => none) =
      some (some [CapAtom.cvar k1]) := by decide

/-- The totality theorem applies to the capture examples on the four decided
side conditions. -/
example : (resolveTop Λc πc S1src).isSome = true :=
  resolveTm_isSome Λc πc.names πc.set S1src (by decide) (by decide) (by decide) (by decide)

/-- And `resolve_noAny` says that what came out holds no `any`. -/
example : ∀ a, resolveTop Λc πc S2src = some a → a.NoAnyAnn = true :=
  fun _ h => resolve_noAny (PlatformNames.ofList_set_noAny _) h

/-! ### E1 to E10, the vanilla examples

The vanilla programs are the version's programs at pure types.  They are
resolved over the empty platform, and every type of the vanilla terms
becomes a shape at the empty set.  E1 to E9 are in monadic normal form, so
`atomize` inserts nothing.  E10 is a nested application in direct style and
is compared against its let expanded form. -/

/-- `⊤` as a pure type. -/
private abbrev pTop {s : Sig} : Ty s := .capt [] .top

/-- The term E1 resolves to. -/
def E1ann : ATm [] :=
  .lam (.capt [] (.typ lA .top .bot))
    (.let (some (.capt [] (.typ lB (.fld la pTop) (.fld la pTop))))
      (.path (.var .here)) (.path (.var .here)))

example : resolveTop Λc .empty E1src = some E1ann := by decide

/-- The totality theorem applies to E1. -/
example : (resolveTop Λc .empty E1src).isSome = true :=
  resolveTm_isSome Λc .nil [] E1src (by decide) (by decide) (by decide) (by decide)

/-- `∀(y : s.A) s.A` under the self binder. -/
private def E2AS : Shape ([],x) :=
  .all (.capt [] (.sel (.var .here) lA)) (.capt [] (.sel (.var (.there .here)) lA))

/-- The term E2 resolves to. -/
def E2ann : ATm [] :=
  .let none
    (.obj (.and (.typ lA E2AS E2AS) (.fld la (.capt [] E2AS))) none
      (.and (.typ lA E2AS)
        (.trm la (.lam (.capt [] (.sel (.var .here) lA)) (.path (.var .here))))))
    (.let none (.proj .here la) (.app .here .here))

example : resolveTop Λc .empty E2src = some E2ann := by decide

/-- The term E3 resolves to. -/
def E3ann : ATm [] :=
  .lam (.capt [] (.and (.typ lA .bot (.fld la pTop)) (.typ lA (.fld lb pTop) .top)))
    (.lam (.capt [] (.fld lb pTop))
      (.let (some (.capt [] (.fld la pTop))) (.path (.var .here)) (.path (.var .here))))

example : resolveTop Λc .empty E3src = some E3ann := by decide

/-- The term E4 resolves to. -/
def E4ann : ATm [] :=
  .lam (.capt [] (.typ lB (.typ lA .bot .top) (.typ lA (.fld la pTop) .top)))
    (.lam (.capt [] (.typ lA .bot .top))
      (.lam (.capt [] (.fld la pTop))
        (.let none (.lam (.capt [] (.sel (.var (.there .here)) lA)) (.path (.var .here)))
          (.app .here (.there .here)))))

example : resolveTop Λc .empty E4src = some E4ann := by decide

/-- The term E5 resolves to. -/
def E5ann : ATm [] :=
  .lam (.capt [] (.typ lA .top .top))
    (.let none
      (.lam (.capt [] (.typ lA .top .top))
        (.obj (.fld la (.capt [] (.sel (.var (.there .here)) lA))) none
          (.trm la (.path (.var (.there .here))))))
      (.let none (.app .here (.there .here)) (.proj .here la)))

example : resolveTop Λc .empty E5src = some E5ann := by decide

/-- The term E6 resolves to. -/
def E6ann : ATm [] :=
  .lam (.capt [] (.fld la pTop))
    (.obj (.and (.typ lT (.fld la pTop) (.fld la pTop)) (.fld lv (.capt [] (.sel (.var .here) lT))))
      none
      (.and (.typ lT (.fld la pTop)) (.trm lv (.path (.var (.there .here))))))

example : resolveTop Λc .empty E6src = some E6ann := by decide

/-- The term E7 resolves to. -/
def E7ann : ATm [] :=
  .obj (.and (.typ lA (.sel (.var .here) lB) (.sel (.var .here) lB))
          (.typ lB (.sel (.var .here) lA) (.sel (.var .here) lA)))
    none
    (.and (.typ lA (.sel (.var .here) lB)) (.typ lB (.sel (.var .here) lA)))

example : resolveTop Λc .empty E7src = some E7ann := by decide

/-- The term E8 resolves to. -/
def E8ann : ATm [] :=
  .lam (.capt [] (.typ lA .bot (.fld la pTop)))
    (.lam (.capt [] (.and (.sel (.var .here) lA) (.fld la pTop))) (.proj .here la))

example : resolveTop Λc .empty E8src = some E8ann := by decide

/-- The term E9 resolves to. -/
def E9ann : ATm [] :=
  .lam (.capt [] (.typ lA .bot (.fld la pTop)))
    (.lam (.capt [] (.sel (.var .here) lA)) (.proj .here la))

example : resolveTop Λc .empty E9src = some E9ann := by decide

/-- The let expanded form of E10, `λ(f). λ(g). let % = g f in f %`.  The
operand `g f` is not a variable, so `atomize` binds it. -/
def E10ann : ATm [] :=
  .lam pTop
    (.lam pTop
      (.let none (.app .here (.there .here))
        (.app (.there (.there .here)) .here)))

example : resolveTop Λc .empty E10src = some E10ann := by decide

/-- Erasure lands in the frozen syntax.  The inserted `let` is a `let` of
`DotMNF.Tm`, nothing more. -/
example : E10ann.erase =
    (Tm.val (.lam pTop (.val (.lam pTop
      (.let (.app .here (.there .here)) (.app (.there (.there .here)) .here)))))) := by decide

end CapturesFrontend
