import Coercions.CapturesCC.Frontend.Ann
import Coercions.CapturesCC.Frontend.Notation
import Coercions.CapturesCC.DotMNF.Examples

/-!
# Name resolution and let insertion for the CapturesCC front end

The functions of this module take a surface phrase to the annotated de Bruijn
syntax of `Ann.lean`: `resolveShape`, `resolveTy` and `resolveAns` for the
three sorts of type, `resolveTm` for a term and `resolveDefs` for a definition
list.  They are the only place where a surface name becomes an index.

## Names of two kinds

A signature has term binders and capture binders.  A name environment records
one surface name per binder, innermost first, with its kind.  A term name, the
receiver of a type selection `x.A` and the receiver of a capture member `x.C`
are looked up among the term binders only.  A plain name in a capture set takes
the innermost binder of either kind.  The platform capabilities are the
outermost capture binders, in the order given, so `["k1", "k2"]` gives `k1` at
`.there .here` and `k2` at `.here`.

## Binders the program does not write

The resolver inserts the binders the calculus has and no surface phrase
writes, so that the name environment stays in step with the signature.

- A lambda: the body root, then the arrow's own capture binder, then the
  parameter.  The domain is read under the arrow binder alone.
- An arrow type: its capture binder, which scopes over the domain, then the
  parameter, which with it scopes over the codomain.
- An object: the class root, then the self, over the definitions.  The self
  shape is read under the self alone.
- An existential answer `∃[c ⊑ C] T`: one capture binder over `T`.  The bound
  `C` is read outside it.
- A written unpacking `let ⟨c, x⟩ = t in u`: the witness binder, then the
  payload, over `u`.

A root and an anonymous arrow binder are named `"%"`, which no identifier of
the notation can equal.  So no surface name refers to a root, and `any` is the
only way to speak of one.  An arrow binder the program names, `∀[c]` or
`λ[c]`, is in scope under its name.

## The atoms `any` and `fresh`

The resolver turns `any` and `fresh` into `CapAtom.any` and `CapAtom.fresh`
and leaves them where the program wrote them.  The typer reads them, with
`Ty.expand`, `Ty.expandFresh` and `Ctx.reading`.  One placement is refused.  A
lambda domain holding `fresh` does not resolve, because the version reads a
domain by `Value.expand`, which reads `any` only, and its `FreshOk` keeps
`fresh` out of every parameter type.

## Let insertion

An explicit spine of bindings keeps the resolvers structural on the surface
phrase.  Application, projection, `□ t` and `C ⊸ t` atomize their operands.
The inserted binder is named `"%"`.  Every inserted binding is a plain `let`.
The typer decides whether a `let` unpacks an existential answer.

An unboxing written with the empty set, `{} ⊸ t`, leaves its set to the typer.
A nonempty set is kept as written.

This module imports `Notation.lean`, and Lean's token table is global.  So the
Greek nu that opens an object literal is a keyword here and cannot be a local
name.  The name environment is written `nv` for that reason.
-/

namespace CapturesCCFrontend

open CapturesCC.FCdot (Kind Sig BVar Rename Label)
open CapturesCC.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Tm Value Defs Platform)

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

/-- The name of a binder the program may leave anonymous: its written name,
or `"%"`, which no surface identifier equals. -/
def binderName (o : Option String) : String := o.getD "%"

/-! ## The platform

A platform is a prefix of capture binders.  `PlatformNames` carries the
signature, the version's evidence that it is a platform prefix, the names of
the capabilities and the platform's capture set, every capability once. -/

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

/-! ## Covering

The resolver reads a phrase under an environment that may hold more names than
the surface scoping asks for: the inserted binders and the binder `atomize`
adds.  So the totality proof needs scoping to survive larger lists of names. -/

/-- Every name of the first list is a name of the second. -/
def Covers (Γ Γ' : List String) : Prop :=
  ∀ z, Γ.contains z = true → Γ'.contains z = true

/-- Every list covers itself. -/
theorem Covers.rfl' (Γ : List String) : Covers Γ Γ := fun _ h => h

/-- A list is covered by itself with one more name in front. -/
theorem Covers.tail (Γ : List String) (y : String) : Covers Γ (y :: Γ) := by
  intro z hz
  simp only [List.contains_cons, hz, Bool.or_true]

/-- Covering is transitive. -/
theorem Covers.trans {Γ Γ' Γ'' : List String} (h : Covers Γ Γ') (h' : Covers Γ' Γ'') :
    Covers Γ Γ'' := fun z hz => h' z (h z hz)

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

/-- Covering survives an optional name in front of both lists. -/
theorem Covers.underOpt {Γ Γ' : List String} (h : Covers Γ Γ') (o : Option String) :
    Covers (optCons o Γ) (optCons o Γ') := by
  cases o with
  | none => exact h
  | some n => exact h.cons n

/-- The capture names of a surface arrow binder are covered by the resolver's,
the written name or `"%"`. -/
theorem Covers.binder (K : List String) (o : Option String) :
    Covers (optCons o K) (binderName o :: K) := by
  cases o with
  | none => exact Covers.tail K "%"
  | some n => exact Covers.rfl' _

/-- Scoping of a capture set survives larger lists of names. -/
theorem SCap.Scoped_covers : ∀ (c : SCap) {K K' Γ Γ' : List String},
    Covers K K' → Covers Γ Γ' → SCap.Scoped K Γ c = true → SCap.Scoped K' Γ' c = true
  | [], _, _, _, _, _, _, _ => rfl
  | .name x :: c, _, _, _, _, hK, hΓ, hs => by
      simp only [SCap.Scoped, Bool.and_eq_true, Bool.or_eq_true] at hs ⊢
      refine ⟨?_, SCap.Scoped_covers c hK hΓ hs.2⟩
      rcases hs.1 with h1 | h1
      · exact Or.inl (hΓ x h1)
      · exact Or.inr (hK x h1)
  | .sel x _ :: c, _, _, _, _, hK, hΓ, hs => by
      simp only [SCap.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨hΓ x hs.1, SCap.Scoped_covers c hK hΓ hs.2⟩
  | .any :: c, _, _, _, _, hK, hΓ, hs => SCap.Scoped_covers c hK hΓ hs
  | .fresh :: c, _, _, _, _, hK, hΓ, hs => SCap.Scoped_covers c hK hΓ hs

mutual
/-- Scoping of a shape survives larger lists of names. -/
theorem SShape.Scoped_covers : ∀ (S : SShape) {K K' Γ Γ' : List String},
    Covers K K' → Covers Γ Γ' → SShape.Scoped K Γ S = true → SShape.Scoped K' Γ' S = true
  | .top, _, _, _, _, _, _, _ => rfl
  | .bot, _, _, _, _, _, _, _ => rfl
  | .typ _ S T, _, _, _, _, hK, hΓ, hs => by
      simp only [SShape.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SShape.Scoped_covers S hK hΓ hs.1, SShape.Scoped_covers T hK hΓ hs.2⟩
  | .fld _ T, _, _, _, _, hK, hΓ, hs => SType.Scoped_covers T hK hΓ hs
  | .cap _ lo hi, _, _, _, _, hK, hΓ, hs => by
      simp only [SShape.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SCap.Scoped_covers lo hK hΓ hs.1, SCap.Scoped_covers hi hK hΓ hs.2⟩
  | .sel x _, _, _, _, _, _, hΓ, hs => hΓ x hs
  | .mu x S, _, _, _, _, hK, hΓ, hs => SShape.Scoped_covers S hK (hΓ.cons x) hs
  | .all κ x T U, _, _, _, _, hK, hΓ, hs => by
      simp only [SShape.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.Scoped_covers T (hK.underOpt κ) hΓ hs.1,
        SAns.Scoped_covers U (hK.underOpt κ) (hΓ.cons x) hs.2⟩
  | .and S T, _, _, _, _, hK, hΓ, hs => by
      simp only [SShape.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SShape.Scoped_covers S hK hΓ hs.1, SShape.Scoped_covers T hK hΓ hs.2⟩
  | .box T, _, _, _, _, hK, hΓ, hs => SType.Scoped_covers T hK hΓ hs
/-- Scoping of a type survives larger lists of names. -/
theorem SType.Scoped_covers : ∀ (T : SType) {K K' Γ Γ' : List String},
    Covers K K' → Covers Γ Γ' → SType.Scoped K Γ T = true → SType.Scoped K' Γ' T = true
  | .capt S C, _, _, _, _, hK, hΓ, hs => by
      simp only [SType.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SShape.Scoped_covers S hK hΓ hs.1, SCap.Scoped_covers C hK hΓ hs.2⟩
/-- Scoping of an answer survives larger lists of names. -/
theorem SAns.Scoped_covers : ∀ (U : SAns) {K K' Γ Γ' : List String},
    Covers K K' → Covers Γ Γ' → SAns.Scoped K Γ U = true → SAns.Scoped K' Γ' U = true
  | .ty T, _, _, _, _, hK, hΓ, hs => SType.Scoped_covers T hK hΓ hs
  | .ex κ C T, _, _, _, _, hK, hΓ, hs => by
      simp only [SAns.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SCap.Scoped_covers C hK hΓ hs.1, SType.Scoped_covers T (hK.cons κ) hΓ hs.2⟩
end

mutual
/-- Scoping of a term survives larger lists of names. -/
theorem STm.Scoped_covers : ∀ (e : STm) {K K' Γ Γ' : List String},
    Covers K K' → Covers Γ Γ' → STm.Scoped K Γ e = true → STm.Scoped K' Γ' e = true
  | .var x, _, _, _, _, _, hΓ, hs => hΓ x hs
  | .lam κ x T t, _, _, _, _, hK, hΓ, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.Scoped_covers T (hK.underOpt κ) hΓ hs.1,
        STm.Scoped_covers t (hK.underOpt κ) (hΓ.cons x) hs.2⟩
  | .obj x S d, _, _, _, _, hK, hΓ, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SShape.Scoped_covers S hK (hΓ.cons x) hs.1,
        SDefs.Scoped_covers d hK (hΓ.cons x) hs.2⟩
  | .app t u, _, _, _, _, hK, hΓ, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨STm.Scoped_covers t hK hΓ hs.1, STm.Scoped_covers u hK hΓ hs.2⟩
  | .proj t _, _, _, _, _, hK, hΓ, hs => STm.Scoped_covers t hK hΓ hs
  | .«let» x ann t u, _, _, _, _, hK, hΓ, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      refine ⟨⟨?_, STm.Scoped_covers t hK hΓ hs.1.2⟩, STm.Scoped_covers u hK (hΓ.cons x) hs.2⟩
      cases ann with
      | none => rfl
      | some U => exact SAns.Scoped_covers U hK hΓ hs.1.1
  | .letex κ x t u, _, _, _, _, hK, hΓ, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨STm.Scoped_covers t hK hΓ hs.1, STm.Scoped_covers u (hK.cons κ) (hΓ.cons x) hs.2⟩
  | .box t, _, _, _, _, hK, hΓ, hs => STm.Scoped_covers t hK hΓ hs
  | .unbox C t, _, _, _, _, hK, hΓ, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SCap.Scoped_covers C hK hΓ hs.1, STm.Scoped_covers t hK hΓ hs.2⟩
  | .asc t T, _, _, _, _, hK, hΓ, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨STm.Scoped_covers t hK hΓ hs.1, SType.Scoped_covers T hK hΓ hs.2⟩
/-- Scoping of a definition list survives larger lists of names. -/
theorem SDefs.Scoped_covers : ∀ (d : SDefs) {K K' Γ Γ' : List String},
    Covers K K' → Covers Γ Γ' → SDefs.Scoped K Γ d = true → SDefs.Scoped K' Γ' d = true
  | .typ _ S, _, _, _, _, hK, hΓ, hs => SShape.Scoped_covers S hK hΓ hs
  | .cap _ c, _, _, _, _, hK, hΓ, hs => SCap.Scoped_covers c hK hΓ hs
  | .trm _ t, _, _, _, _, hK, hΓ, hs => STm.Scoped_covers t hK hΓ hs
  | .and d e, _, _, _, _, hK, hΓ, hs => by
      simp only [SDefs.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SDefs.Scoped_covers d hK hΓ hs.1, SDefs.Scoped_covers e hK hΓ hs.2⟩
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
the weakening that moves a variable of `s` into `s'`. -/

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

/-- A resolved term in variable position: the inserted bindings, their
environment and the variable. -/
structure Atomic (s : Sig) where
  /-- The signature after the insertions. -/
  sig : Sig
  /-- The insertions. -/
  spine : Spine s sig
  /-- The environment at that signature. -/
  names : NameEnv sig
  /-- The variable standing for the term. -/
  var : BVar sig .var

/-- Bring a resolved term into variable position.  A variable needs nothing.
Anything else is bound by one `let`. -/
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
  | obj _ _ => exact Covers.tail _ _
  | app _ _ => exact Covers.tail _ _
  | proj _ _ => exact Covers.tail _ _
  | «let» _ _ _ => exact Covers.tail _ _
  | letex _ _ => exact Covers.tail _ _
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

/-- Resolve a capture atom.  A plain name takes the innermost binder of either
kind, the receiver of `x.C` a term binder. -/
def resolveCapAtom {s : Sig} (Λ : LabelTable) (nv : NameEnv s) : SAtom → Option (CapAtom s)
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
  | .fresh => some .fresh

/-- Resolve a capture set, atom by atom. -/
def resolveCap {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (c : SCap) : Option (CaptureSet s) :=
  match c with
  | [] => some []
  | a :: c => do
      let a' ← resolveCapAtom Λ nv a
      let c' ← resolveCap Λ nv c
      pure (a' :: c')
termination_by structural c

/-! ## Shapes, types and answers

An arrow opens its capture binder, under its written name or `"%"`, for the
domain, and the parameter on top of it for the codomain.  An existential opens
its binder for the type and reads its bound outside. -/

mutual
/-- Resolve a surface shape. -/
def resolveShape {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (S : SShape) : Option (Shape s) :=
  match S with
  | .top => some .top
  | .bot => some .bot
  | .typ A S T => do
      let l ← labelTyp? Λ A
      let S' ← resolveShape Λ nv S
      let T' ← resolveShape Λ nv T
      pure (.typ l S' T')
  | .fld a T => do
      let l ← labelTrm? Λ a
      let T' ← resolveTy Λ nv T
      pure (.fld l T')
  | .cap C lo hi => do
      let l ← labelTyp? Λ C
      let lo' ← resolveCap Λ nv lo
      let hi' ← resolveCap Λ nv hi
      pure (.cap l lo' hi')
  | .sel x A => do
      let i ← nv.findVar? x
      let l ← labelTyp? Λ A
      pure (.sel (.var i) l)
  | .mu x S => do
      let S' ← resolveShape Λ (nv.cons x) S
      pure (.mu S')
  | .all κ x T U => do
      let T' ← resolveTy Λ (nv.consC (binderName κ)) T
      let U' ← resolveAns Λ ((nv.consC (binderName κ)).cons x) U
      pure (.all T' U')
  | .and S T => do
      let S' ← resolveShape Λ nv S
      let T' ← resolveShape Λ nv T
      pure (.and S' T')
  | .box T => do
      let T' ← resolveTy Λ nv T
      pure (.box T')
termination_by structural S
/-- Resolve a surface capturing type. -/
def resolveTy {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (T : SType) : Option (Ty s) :=
  match T with
  | .capt S C => do
      let S' ← resolveShape Λ nv S
      let C' ← resolveCap Λ nv C
      pure (.capt C' S')
termination_by structural T
/-- Resolve a surface answer. -/
def resolveAns {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (U : SAns) : Option (ETy s) :=
  match U with
  | .ty T => do
      let T' ← resolveTy Λ nv T
      pure (.ty T')
  | .ex κ C T => do
      let C' ← resolveCap Λ nv C
      let T' ← resolveTy Λ (nv.consC κ) T
      pure (.ex C' T')
termination_by structural U
end

/-! ## Terms -/

/-- The set an unboxing keeps: none for the empty set, else the resolved set. -/
def unboxSet {s : Sig} (C : SCap) (C' : CaptureSet s) : Option (CaptureSet s) :=
  match C with
  | [] => none
  | _ => some C'

mutual
/-- Resolve a surface term, inserting the binders the program does not write
and `let` bindings for the four direct style forms. -/
def resolveTm {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (e : STm) : Option (ATm s) :=
  match e with
  | .var x => do
      let i ← nv.findVar? x
      pure (.path (.var i))
  | .lam κ x T t => do
      let T' ← resolveTy Λ (nv.consC (binderName κ)) T
      let t' ← resolveTm Λ (((nv.consC "%").consC (binderName κ)).cons x) t
      if T'.noFresh then pure (.lam T' t') else none
  | .obj x S d => do
      let S' ← resolveShape Λ (nv.cons x) S
      let d' ← resolveDefs Λ ((nv.consC "%").cons x) d
      pure (.obj S' d')
  | .app t u => do
      let t₀ ← resolveTm Λ nv t
      let a := atomize nv t₀
      let u₀ ← resolveTm Λ a.names u
      let b := atomize a.names u₀
      pure ((a.spine.append b.spine).plug (.app (b.spine.rename.var a.var) b.var))
  | .proj t a => do
      let t₀ ← resolveTm Λ nv t
      let c := atomize nv t₀
      let l ← labelTrm? Λ a
      pure (c.spine.plug (.proj c.var l))
  | .«let» x ann t u => do
      let ann' ← (match ann with
        | none => some none
        | some U => (resolveAns Λ nv U).map some)
      let t' ← resolveTm Λ nv t
      let u' ← resolveTm Λ (nv.cons x) u
      pure (.let ann' t' u')
  | .letex κ x t u => do
      let t' ← resolveTm Λ nv t
      let u' ← resolveTm Λ ((nv.consC κ).cons x) u
      pure (.letex t' u')
  | .box t => do
      let t₀ ← resolveTm Λ nv t
      let c := atomize nv t₀
      pure (c.spine.plug (.box c.var))
  | .unbox C t => do
      let t₀ ← resolveTm Λ nv t
      let c := atomize nv t₀
      let C' ← resolveCap Λ c.names C
      pure (c.spine.plug (.unbox (unboxSet C C') c.var))
  | .asc t T => do
      let t' ← resolveTm Λ nv t
      let T' ← resolveTy Λ nv T
      pure (.asc t' T')
termination_by structural e
/-- Resolve a surface definition list, under the class root and the self. -/
def resolveDefs {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (d : SDefs) : Option (ADefs s) :=
  match d with
  | .typ A S => do
      let l ← labelTyp? Λ A
      let S' ← resolveShape Λ nv S
      pure (.typ l S')
  | .cap C c => do
      let l ← labelTyp? Λ C
      let c' ← resolveCap Λ nv c
      pure (.cap l c')
  | .trm a t => do
      let l ← labelTrm? Λ a
      let t' ← resolveTm Λ nv t
      pure (.trm l t')
  | .and d e => do
      let d' ← resolveDefs Λ nv d
      let e' ← resolveDefs Λ nv e
      pure (.and d' e')
termination_by structural d
end

/-- Resolve a surface term at a given environment. -/
def resolveIn {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (e : STm) : Option (ATm s) :=
  resolveTm Λ nv e

/-- Resolve a closed program over a platform. -/
def resolveTop (Λ : LabelTable) (π : PlatformNames) (e : STm) : Option (ATm π.sig) :=
  resolveTm Λ π.names e

/-- Resolve a whole program, over the platform its header names. -/
def resolveProg (Λ : LabelTable) (p : SProg) :
    Option (ATm (PlatformNames.ofList p.platform).sig) :=
  resolveTop Λ (PlatformNames.ofList p.platform) p.body

/-! ## Surface side conditions about atoms

`Avoids a` says that the atom `a` occurs in no capture set of the phrase,
annotations included.  `FreshPlaced` says that no lambda domain of a term holds
`fresh`. -/

/-- The atom occurs in no position of the set. -/
def SCap.Avoids (a : SAtom) : SCap → Bool
  | [] => true
  | b :: c => (b != a) && SCap.Avoids a c

mutual
/-- The atom occurs in no capture set of the shape. -/
def SShape.Avoids (a : SAtom) (S : SShape) : Bool :=
  match S with
  | .top => true
  | .bot => true
  | .typ _ S T => SShape.Avoids a S && SShape.Avoids a T
  | .fld _ T => SType.Avoids a T
  | .cap _ lo hi => SCap.Avoids a lo && SCap.Avoids a hi
  | .sel _ _ => true
  | .mu _ S => SShape.Avoids a S
  | .all _ _ T U => SType.Avoids a T && SAns.Avoids a U
  | .and S T => SShape.Avoids a S && SShape.Avoids a T
  | .box T => SType.Avoids a T
termination_by structural S
/-- The atom occurs in no capture set of the type. -/
def SType.Avoids (a : SAtom) (T : SType) : Bool :=
  match T with
  | .capt S C => SShape.Avoids a S && SCap.Avoids a C
termination_by structural T
/-- The atom occurs in no capture set of the answer. -/
def SAns.Avoids (a : SAtom) (U : SAns) : Bool :=
  match U with
  | .ty T => SType.Avoids a T
  | .ex _ C T => SCap.Avoids a C && SType.Avoids a T
termination_by structural U
end

mutual
/-- The atom occurs in no annotation and no set of the term. -/
def STm.Avoids (a : SAtom) (e : STm) : Bool :=
  match e with
  | .var _ => true
  | .lam _ _ T t => SType.Avoids a T && STm.Avoids a t
  | .obj _ S d => SShape.Avoids a S && SDefs.Avoids a d
  | .app t u => STm.Avoids a t && STm.Avoids a u
  | .proj t _ => STm.Avoids a t
  | .«let» _ ann t u =>
      (match ann with | none => true | some U => SAns.Avoids a U)
        && STm.Avoids a t && STm.Avoids a u
  | .letex _ _ t u => STm.Avoids a t && STm.Avoids a u
  | .box t => STm.Avoids a t
  | .unbox C t => SCap.Avoids a C && STm.Avoids a t
  | .asc t T => STm.Avoids a t && SType.Avoids a T
termination_by structural e
/-- The atom occurs in no annotation and no set of the definitions. -/
def SDefs.Avoids (a : SAtom) (d : SDefs) : Bool :=
  match d with
  | .typ _ S => SShape.Avoids a S
  | .cap _ c => SCap.Avoids a c
  | .trm _ t => STm.Avoids a t
  | .and d e => SDefs.Avoids a d && SDefs.Avoids a e
termination_by structural d
end

mutual
/-- No lambda domain of the term holds `fresh`. -/
def STm.FreshPlaced (e : STm) : Bool :=
  match e with
  | .var _ => true
  | .lam _ _ T t => SType.Avoids .fresh T && STm.FreshPlaced t
  | .obj _ _ d => SDefs.FreshPlaced d
  | .app t u => STm.FreshPlaced t && STm.FreshPlaced u
  | .proj t _ => STm.FreshPlaced t
  | .«let» _ _ t u => STm.FreshPlaced t && STm.FreshPlaced u
  | .letex _ _ t u => STm.FreshPlaced t && STm.FreshPlaced u
  | .box t => STm.FreshPlaced t
  | .unbox _ t => STm.FreshPlaced t
  | .asc t _ => STm.FreshPlaced t
termination_by structural e
/-- No lambda domain of the definitions holds `fresh`. -/
def SDefs.FreshPlaced (d : SDefs) : Bool :=
  match d with
  | .typ _ _ => true
  | .cap _ _ => true
  | .trm _ t => STm.FreshPlaced t
  | .and d e => SDefs.FreshPlaced d && SDefs.FreshPlaced e
termination_by structural d
end

/-! ## Totality

Resolution succeeds on a phrase whose free names are in scope at the kind
their position needs, whose labels are in the table, and, for a term, whose
lambda domains hold no `fresh`.  The proof is by structural recursion.  The
inserted binders only add names, so the written scoping carries over by
covering. -/

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
  | .fresh :: c, _, Λ, nv, hs, hl => by
      simp only [SCap.Scoped, SCap.LabelsIn] at hs hl
      obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp (resolveCap_isSome c Λ nv hs hl)
      simp [resolveCap, resolveCapAtom, hc]

/-- An arrow's domain keeps its scoping under the binder the resolver opens. -/
theorem Scoped_arrowDom {s : Sig} (nv : NameEnv s) (κ : Option String) (T : SType)
    (h : SType.Scoped (optCons κ nv.capNames) nv.names T = true) :
    SType.Scoped (nv.consC (binderName κ)).capNames (nv.consC (binderName κ)).names T = true :=
  SType.Scoped_covers T (Covers.binder _ κ) (Covers.rfl' _) h

mutual
/-- A scoped and labelled shape resolves. -/
theorem resolveShape_isSome : ∀ (S : SShape) {s : Sig} (Λ : LabelTable) (nv : NameEnv s),
    SShape.Scoped nv.capNames nv.names S = true → SShape.LabelsIn Λ S = true →
    (resolveShape Λ nv S).isSome = true
  | .top, _, _, _, _, _ => rfl
  | .bot, _, _, _, _, _ => rfl
  | .typ A S T, _, Λ, nv, hs, hl => by
      simp only [SShape.Scoped, SShape.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨l, hA⟩ := Option.isSome_iff_exists.mp hl.1.1
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp (resolveShape_isSome S Λ nv hs.1 hl.1.2)
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp (resolveShape_isSome T Λ nv hs.2 hl.2)
      simp [resolveShape, hA, hS, hT]
  | .fld a T, _, Λ, nv, hs, hl => by
      simp only [SShape.Scoped, SShape.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨l, ha⟩ := Option.isSome_iff_exists.mp hl.1
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp (resolveTy_isSome T Λ nv hs hl.2)
      simp [resolveShape, ha, hT]
  | .cap C lo hi, _, Λ, nv, hs, hl => by
      simp only [SShape.Scoped, SShape.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨l, hC⟩ := Option.isSome_iff_exists.mp hl.1.1
      obtain ⟨lo', hlo⟩ := Option.isSome_iff_exists.mp (resolveCap_isSome lo Λ nv hs.1 hl.1.2)
      obtain ⟨hi', hhi⟩ := Option.isSome_iff_exists.mp (resolveCap_isSome hi Λ nv hs.2 hl.2)
      simp [resolveShape, hC, hlo, hhi]
  | .sel x A, _, Λ, nv, hs, hl => by
      simp only [SShape.Scoped, SShape.LabelsIn] at hs hl
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (NameEnv.findVar?_isSome nv x hs)
      obtain ⟨l, hA⟩ := Option.isSome_iff_exists.mp hl
      simp [resolveShape, hi, hA]
  | .mu x S, _, Λ, nv, hs, hl => by
      simp only [SShape.Scoped, SShape.LabelsIn] at hs hl
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp (resolveShape_isSome S Λ (nv.cons x) hs hl)
      simp [resolveShape, hS]
  | .all κ x T U, _, Λ, nv, hs, hl => by
      simp only [SShape.Scoped, SShape.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp
        (resolveTy_isSome T Λ (nv.consC (binderName κ)) (Scoped_arrowDom nv κ T hs.1) hl.1)
      obtain ⟨U', hU⟩ := Option.isSome_iff_exists.mp
        (resolveAns_isSome U Λ ((nv.consC (binderName κ)).cons x)
          (SAns.Scoped_covers U (Covers.binder _ κ) (Covers.rfl' _) hs.2) hl.2)
      simp [resolveShape, hT, hU]
  | .and S T, _, Λ, nv, hs, hl => by
      simp only [SShape.Scoped, SShape.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp (resolveShape_isSome S Λ nv hs.1 hl.1)
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp (resolveShape_isSome T Λ nv hs.2 hl.2)
      simp [resolveShape, hS, hT]
  | .box T, _, Λ, nv, hs, hl => by
      simp only [SShape.Scoped, SShape.LabelsIn] at hs hl
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp (resolveTy_isSome T Λ nv hs hl)
      simp [resolveShape, hT]
/-- A scoped and labelled capturing type resolves. -/
theorem resolveTy_isSome : ∀ (T : SType) {s : Sig} (Λ : LabelTable) (nv : NameEnv s),
    SType.Scoped nv.capNames nv.names T = true → SType.LabelsIn Λ T = true →
    (resolveTy Λ nv T).isSome = true
  | .capt S C, _, Λ, nv, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp (resolveShape_isSome S Λ nv hs.1 hl.1)
      obtain ⟨C', hC⟩ := Option.isSome_iff_exists.mp (resolveCap_isSome C Λ nv hs.2 hl.2)
      simp [resolveTy, hS, hC]
/-- A scoped and labelled answer resolves. -/
theorem resolveAns_isSome : ∀ (U : SAns) {s : Sig} (Λ : LabelTable) (nv : NameEnv s),
    SAns.Scoped nv.capNames nv.names U = true → SAns.LabelsIn Λ U = true →
    (resolveAns Λ nv U).isSome = true
  | .ty T, _, Λ, nv, hs, hl => by
      simp only [SAns.Scoped, SAns.LabelsIn] at hs hl
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp (resolveTy_isSome T Λ nv hs hl)
      simp [resolveAns, hT]
  | .ex κ C T, _, Λ, nv, hs, hl => by
      simp only [SAns.Scoped, SAns.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨C', hC⟩ := Option.isSome_iff_exists.mp (resolveCap_isSome C Λ nv hs.1 hl.1)
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp
        (resolveTy_isSome T Λ (nv.consC κ) hs.2 hl.2)
      simp [resolveAns, hC, hT]
end

/-! ## What a resolved type holds of `any` and `fresh`

A resolved phrase holds `any` or `fresh` only where the written one does. -/

/-- A resolved capture set holds `any` or `fresh` only where the written one
does. -/
theorem resolveCap_avoids : ∀ (c : SCap) {s : Sig} (Λ : LabelTable) (nv : NameEnv s)
    (c' : CaptureSet s), resolveCap Λ nv c = some c' →
    (SCap.Avoids .any c = true → CaptureSet.noAny c' = true) ∧
    (SCap.Avoids .fresh c = true → CaptureSet.noFresh c' = true)
  | [], _, _, _, c', h => by
      simp [resolveCap] at h; subst h; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | a :: c, _, Λ, nv, c', h => by
      simp only [resolveCap, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨a', ha', c'', hc, rfl⟩ := h
      have ih := resolveCap_avoids c Λ nv c'' hc
      cases a with
      | name x =>
          cases hf : nv.find? x with
          | none => simp [resolveCapAtom, hf] at ha'
          | some p =>
              obtain ⟨k, i⟩ := p
              cases k <;> simp [resolveCapAtom, hf] at ha' <;> subst ha' <;>
                simpa [SCap.Avoids, CaptureSet.noAny, CaptureSet.noFresh] using ih
      | sel x C =>
          simp only [resolveCapAtom, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.pure_def, Option.some.injEq] at ha'
          obtain ⟨i, _, l, _, rfl⟩ := ha'
          simpa [SCap.Avoids, CaptureSet.noAny, CaptureSet.noFresh] using ih
      | any =>
          simp only [resolveCapAtom, Option.some.injEq] at ha'
          subst ha'
          refine ⟨fun h => by simp [SCap.Avoids] at h, fun h => ?_⟩
          simp only [SCap.Avoids, Bool.and_eq_true] at h
          simpa [CaptureSet.noFresh] using ih.2 h.2
      | fresh =>
          simp only [resolveCapAtom, Option.some.injEq] at ha'
          subst ha'
          refine ⟨fun h => ?_, fun h => by simp [SCap.Avoids] at h⟩
          simp only [SCap.Avoids, Bool.and_eq_true] at h
          simpa [CaptureSet.noAny] using ih.1 h.2

mutual
/-- A resolved shape holds `any` or `fresh` only where the written one
does. -/
theorem resolveShape_avoids : ∀ (S : SShape) {s : Sig} (Λ : LabelTable) (nv : NameEnv s)
    (S' : Shape s), resolveShape Λ nv S = some S' →
    (SShape.Avoids .any S = true → S'.noAny = true) ∧
    (SShape.Avoids .fresh S = true → S'.noFresh = true)
  | .top, _, _, _, S', h => by
      simp only [resolveShape, Option.some.injEq] at h; subst h; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | .bot, _, _, _, S', h => by
      simp only [resolveShape, Option.some.injEq] at h; subst h; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | .typ A S T, _, Λ, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨l, _, S₁, hS, T₁, hT, rfl⟩ := h
      have iS := resolveShape_avoids S Λ nv S₁ hS
      have iT := resolveShape_avoids T Λ nv T₁ hT
      refine ⟨fun ha => ?_, fun ha => ?_⟩ <;>
      · simp only [SShape.Avoids, Bool.and_eq_true] at ha
        simp [Shape.noAny, Shape.noFresh, iS.1, iS.2, iT.1, iT.2, ha.1, ha.2]
  | .fld a T, _, Λ, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨l, _, T₁, hT, rfl⟩ := h
      have iT := resolveTy_avoids T Λ nv T₁ hT
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SShape.Avoids] at ha
        simp [Shape.noAny, iT.1 ha]
      · simp only [SShape.Avoids] at ha
        simp [Shape.noFresh, iT.2 ha]
  | .cap C lo hi, _, Λ, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨l, _, lo', hlo, hi', hhi, rfl⟩ := h
      have ilo := resolveCap_avoids lo Λ nv lo' hlo
      have ihi := resolveCap_avoids hi Λ nv hi' hhi
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SShape.Avoids, Bool.and_eq_true] at ha
        simp [Shape.noAny, ilo.1 ha.1, ihi.1 ha.2]
      · simp only [SShape.Avoids, Bool.and_eq_true] at ha
        simp [Shape.noFresh, ilo.2 ha.1, ihi.2 ha.2]
  | .sel x A, _, Λ, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨i, _, l, _, rfl⟩ := h
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  | .mu x S, _, Λ, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨S₁, hS, rfl⟩ := h
      have iS := resolveShape_avoids S Λ (nv.cons x) S₁ hS
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SShape.Avoids] at ha
        simp [Shape.noAny, iS.1 ha]
      · simp only [SShape.Avoids] at ha
        simp [Shape.noFresh, iS.2 ha]
  | .all κ x T U, _, Λ, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨T₁, hT, U₁, hU, rfl⟩ := h
      have iT := resolveTy_avoids T Λ _ T₁ hT
      have iU := resolveAns_avoids U Λ _ U₁ hU
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SShape.Avoids, Bool.and_eq_true] at ha
        simp [Shape.noAny, iT.1 ha.1, iU.1 ha.2]
      · simp only [SShape.Avoids, Bool.and_eq_true] at ha
        simp [Shape.noFresh, iT.2 ha.1, iU.2 ha.2]
  | .and S T, _, Λ, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨S₁, hS, T₁, hT, rfl⟩ := h
      have iS := resolveShape_avoids S Λ nv S₁ hS
      have iT := resolveShape_avoids T Λ nv T₁ hT
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SShape.Avoids, Bool.and_eq_true] at ha
        simp [Shape.noAny, iS.1 ha.1, iT.1 ha.2]
      · simp only [SShape.Avoids, Bool.and_eq_true] at ha
        simp [Shape.noFresh, iS.2 ha.1, iT.2 ha.2]
  | .box T, _, Λ, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨T₁, hT, rfl⟩ := h
      have iT := resolveTy_avoids T Λ nv T₁ hT
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SShape.Avoids] at ha
        simp [Shape.noAny, iT.1 ha]
      · simp only [SShape.Avoids] at ha
        simp [Shape.noFresh, iT.2 ha]
/-- A resolved type holds `any` or `fresh` only where the written one
does. -/
theorem resolveTy_avoids : ∀ (T : SType) {s : Sig} (Λ : LabelTable) (nv : NameEnv s)
    (T' : Ty s), resolveTy Λ nv T = some T' →
    (SType.Avoids .any T = true → T'.noAny = true) ∧
    (SType.Avoids .fresh T = true → T'.noFresh = true)
  | .capt S C, _, Λ, nv, T', h => by
      simp only [resolveTy, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨S₁, hS, C₁, hC, rfl⟩ := h
      have iS := resolveShape_avoids S Λ nv S₁ hS
      have iC := resolveCap_avoids C Λ nv C₁ hC
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SType.Avoids, Bool.and_eq_true] at ha
        simp [Ty.noAny, iS.1 ha.1, iC.1 ha.2]
      · simp only [SType.Avoids, Bool.and_eq_true] at ha
        simp [Ty.noFresh, iS.2 ha.1, iC.2 ha.2]
/-- A resolved answer holds `any` or `fresh` only where the written one
does. -/
theorem resolveAns_avoids : ∀ (U : SAns) {s : Sig} (Λ : LabelTable) (nv : NameEnv s)
    (U' : ETy s), resolveAns Λ nv U = some U' →
    (SAns.Avoids .any U = true → U'.noAny = true) ∧
    (SAns.Avoids .fresh U = true → U'.noFresh = true)
  | .ty T, _, Λ, nv, U', h => by
      simp only [resolveAns, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨T₁, hT, rfl⟩ := h
      have iT := resolveTy_avoids T Λ nv T₁ hT
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SAns.Avoids] at ha
        simp [ETy.noAny, iT.1 ha]
      · simp only [SAns.Avoids] at ha
        simp [ETy.noFresh, iT.2 ha]
  | .ex κ C T, _, Λ, nv, U', h => by
      simp only [resolveAns, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨C₁, hC, T₁, hT, rfl⟩ := h
      have iC := resolveCap_avoids C Λ nv C₁ hC
      have iT := resolveTy_avoids T Λ _ T₁ hT
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SAns.Avoids, Bool.and_eq_true] at ha
        simp [ETy.noAny, iC.1 ha.1, iT.1 ha.2]
      · simp only [SAns.Avoids, Bool.and_eq_true] at ha
        simp [ETy.noFresh, iC.2 ha.1, iT.2 ha.2]
end

/-! ## Totality of term resolution -/

/-- `atomize` keeps both lists of names in scope for the operand. -/
theorem STm.Scoped_atomize {s : Sig} (nv : NameEnv s) (t₀ : ATm s) (u : STm)
    (h : STm.Scoped nv.capNames nv.names u = true) :
    STm.Scoped (atomize nv t₀).names.capNames (atomize nv t₀).names.names u = true := by
  rw [atomize_capNames]
  exact STm.Scoped_covers u (Covers.rfl' _) (atomize_names_covers nv t₀) h

/-- `atomize` keeps a capture set in scope. -/
theorem SCap.Scoped_atomize {s : Sig} (nv : NameEnv s) (t₀ : ATm s) (C : SCap)
    (h : SCap.Scoped nv.capNames nv.names C = true) :
    SCap.Scoped (atomize nv t₀).names.capNames (atomize nv t₀).names.names C = true := by
  rw [atomize_capNames]
  exact SCap.Scoped_covers C (Covers.rfl' _) (atomize_names_covers nv t₀) h

/-- A lambda body keeps its scoping under the three binders the resolver
opens. -/
theorem Scoped_lamBody {s : Sig} (nv : NameEnv s) (κ : Option String) (x : String) (t : STm)
    (h : STm.Scoped (optCons κ nv.capNames) (x :: nv.names) t = true) :
    STm.Scoped (((nv.consC "%").consC (binderName κ)).cons x).capNames
      (((nv.consC "%").consC (binderName κ)).cons x).names t = true :=
  STm.Scoped_covers t ((Covers.binder _ κ).trans ((Covers.tail _ "%").cons _)) (Covers.rfl' _) h

/-- Object definitions keep their scoping under the class root and the
self. -/
theorem Scoped_objDefs {s : Sig} (nv : NameEnv s) (x : String) (d : SDefs)
    (h : SDefs.Scoped nv.capNames (x :: nv.names) d = true) :
    SDefs.Scoped ((nv.consC "%").cons x).capNames ((nv.consC "%").cons x).names d = true :=
  SDefs.Scoped_covers d (Covers.tail _ "%") (Covers.rfl' _) h

mutual
/-- Totality of term resolution. -/
theorem resolveTm_isSome : ∀ {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (e : STm),
    STm.Scoped nv.capNames nv.names e = true → STm.LabelsIn Λ e = true →
    STm.FreshPlaced e = true → (resolveTm Λ nv e).isSome = true
  | _, Λ, nv, .var x, hs, _, _ => by
      simp only [STm.Scoped] at hs
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (NameEnv.findVar?_isSome nv x hs)
      simp [resolveTm, hi]
  | _, Λ, nv, .lam κ x T t, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FreshPlaced, Bool.and_eq_true] at hs hl hf
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp
        (resolveTy_isSome T Λ (nv.consC (binderName κ)) (Scoped_arrowDom nv κ T hs.1) hl.1)
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ _ t (Scoped_lamBody nv κ x t hs.2) hl.2 hf.2)
      have hn := (resolveTy_avoids T Λ _ T' hT).2 hf.1
      simp [resolveTm, hT, ht, hn]
  | _, Λ, nv, .obj x S d, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FreshPlaced, Bool.and_eq_true] at hs hl hf
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp
        (resolveShape_isSome S Λ (nv.cons x) hs.1 hl.1)
      obtain ⟨d', hd⟩ := Option.isSome_iff_exists.mp
        (resolveDefs_isSome Λ _ d (Scoped_objDefs nv x d hs.2) hl.2 hf)
      simp [resolveTm, hS, hd]
  | _, Λ, nv, .app t u, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FreshPlaced, Bool.and_eq_true] at hs hl hf
      obtain ⟨t₀, ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ nv t hs.1 hl.1 hf.1)
      obtain ⟨u₀, hu⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ (atomize nv t₀).names u
          (STm.Scoped_atomize nv t₀ u hs.2) hl.2 hf.2)
      simp [resolveTm, ht, hu]
  | _, Λ, nv, .proj t a, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FreshPlaced, Bool.and_eq_true] at hs hl hf
      obtain ⟨t₀, ht⟩ := Option.isSome_iff_exists.mp (resolveTm_isSome Λ nv t hs hl.1 hf)
      obtain ⟨l, hla⟩ := Option.isSome_iff_exists.mp hl.2
      simp [resolveTm, ht, hla]
  | _, Λ, nv, .«let» x ann t u, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FreshPlaced, Bool.and_eq_true] at hs hl hf
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ nv t hs.1.2 hl.1.2 hf.1)
      obtain ⟨u', hu⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ (nv.cons x) u hs.2 hl.2 hf.2)
      cases ann with
      | none => simp [resolveTm, ht, hu]
      | some U =>
          obtain ⟨U', hU⟩ := Option.isSome_iff_exists.mp
            (resolveAns_isSome U Λ nv hs.1.1 hl.1.1)
          simp [resolveTm, hU, ht, hu]
  | _, Λ, nv, .letex κ x t u, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FreshPlaced, Bool.and_eq_true] at hs hl hf
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ nv t hs.1 hl.1 hf.1)
      obtain ⟨u', hu⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ ((nv.consC κ).cons x) u hs.2 hl.2 hf.2)
      simp [resolveTm, ht, hu]
  | _, Λ, nv, .box t, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FreshPlaced] at hs hl hf
      obtain ⟨t₀, ht⟩ := Option.isSome_iff_exists.mp (resolveTm_isSome Λ nv t hs hl hf)
      simp [resolveTm, ht]
  | _, Λ, nv, .unbox C t, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FreshPlaced, Bool.and_eq_true] at hs hl hf
      obtain ⟨t₀, ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ nv t hs.2 hl.2 hf)
      obtain ⟨C', hC⟩ := Option.isSome_iff_exists.mp
        (resolveCap_isSome C Λ (atomize nv t₀).names (SCap.Scoped_atomize nv t₀ C hs.1) hl.1)
      simp [resolveTm, ht, hC]
  | _, Λ, nv, .asc t T, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FreshPlaced, Bool.and_eq_true] at hs hl hf
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ nv t hs.1 hl.1 hf)
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp
        (resolveTy_isSome T Λ nv hs.2 hl.2)
      simp [resolveTm, ht, hT]
/-- Totality of definition resolution. -/
theorem resolveDefs_isSome : ∀ {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (d : SDefs),
    SDefs.Scoped nv.capNames nv.names d = true → SDefs.LabelsIn Λ d = true →
    SDefs.FreshPlaced d = true → (resolveDefs Λ nv d).isSome = true
  | _, Λ, nv, .typ A S, hs, hl, _ => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨l, hA⟩ := Option.isSome_iff_exists.mp hl.1
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp (resolveShape_isSome S Λ nv hs hl.2)
      simp [resolveDefs, hA, hS]
  | _, Λ, nv, .cap C c, hs, hl, _ => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, Bool.and_eq_true] at hs hl
      obtain ⟨l, hC⟩ := Option.isSome_iff_exists.mp hl.1
      obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (resolveCap_isSome c Λ nv hs hl.2)
      simp [resolveDefs, hC, hc']
  | _, Λ, nv, .trm a t, hs, hl, hf => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, SDefs.FreshPlaced, Bool.and_eq_true] at hs hl hf
      obtain ⟨l, hla⟩ := Option.isSome_iff_exists.mp hl.1
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp (resolveTm_isSome Λ nv t hs hl.2 hf)
      simp [resolveDefs, hla, ht]
  | _, Λ, nv, .and d e, hs, hl, hf => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, SDefs.FreshPlaced, Bool.and_eq_true] at hs hl hf
      obtain ⟨d', hd⟩ := Option.isSome_iff_exists.mp
        (resolveDefs_isSome Λ nv d hs.1 hl.1 hf.1)
      obtain ⟨e', he⟩ := Option.isSome_iff_exists.mp
        (resolveDefs_isSome Λ nv e hs.2 hl.2 hf.2)
      simp [resolveDefs, hd, he]
end

/-! ## No `any` of the resolver's own

The inserted binders and the bindings of the spine carry no annotation, so a
program that writes no `any` resolves to a term with none. -/

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

/-- The set an unboxing keeps holds no `any` when the resolved one holds
none. -/
theorem unboxSet_noAny {s : Sig} (C : SCap) {C' : CaptureSet s} (h : CaptureSet.noAny C' = true) :
    (match unboxSet C C' with | none => true | some C => CaptureSet.noAny C) = true := by
  cases C <;> simp [unboxSet, h]

mutual
/-- A resolved term holds `any` in an annotation, a set or a type definition
only where the written term does. -/
theorem resolveTm_noAny : ∀ {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (e : STm) (a : ATm s),
    STm.Avoids .any e = true → resolveTm Λ nv e = some a → a.NoAnyAnn = true
  | _, Λ, nv, .var x, a, _, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨i, _, rfl⟩ := h
      rfl
  | _, Λ, nv, .lam κ x T t, a, ha, h => by
      simp only [STm.Avoids, Bool.and_eq_true] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨T', hT, t', ht, h⟩ := h
      by_cases hn : T'.noFresh = true
      · simp only [hn, if_true, Option.pure_def, Option.some.injEq] at h
        subst h
        simp [ATm.NoAnyAnn, (resolveTy_avoids T Λ _ T' hT).1 ha.1,
          resolveTm_noAny Λ _ t t' ha.2 ht]
      · simp [hn] at h
  | _, Λ, nv, .obj x S d, a, ha, h => by
      simp only [STm.Avoids, Bool.and_eq_true] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨S', hS, d', hd, rfl⟩ := h
      simp [ATm.NoAnyAnn, (resolveShape_avoids S Λ _ S' hS).1 ha.1,
        resolveDefs_noAny Λ _ d d' ha.2 hd]
  | _, Λ, nv, .app t u, a, ha, h => by
      simp only [STm.Avoids, Bool.and_eq_true] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t₀, ht, u₀, hu, rfl⟩ := h
      have it := resolveTm_noAny Λ nv t t₀ ha.1 ht
      have iu := resolveTm_noAny Λ _ u u₀ ha.2 hu
      exact Spine.plug_noAny _ _
        (Spine.append_noAny _ _ (atomize_noAny nv t₀ it) (atomize_noAny _ u₀ iu)) rfl
  | _, Λ, nv, .proj t a', a, ha, h => by
      simp only [STm.Avoids] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t₀, ht, l, _, rfl⟩ := h
      exact Spine.plug_noAny _ _ (atomize_noAny nv t₀ (resolveTm_noAny Λ nv t t₀ ha ht)) rfl
  | _, Λ, nv, .«let» x ann t u, a, ha, h => by
      simp only [STm.Avoids, Bool.and_eq_true] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ann', hann, t', ht, u', hu, rfl⟩ := h
      have it := resolveTm_noAny Λ nv t t' ha.1.2 ht
      have iu := resolveTm_noAny Λ (nv.cons x) u u' ha.2 hu
      cases ann with
      | none =>
          simp only [Option.some.injEq] at hann
          subst hann
          simp [ATm.NoAnyAnn, it, iu]
      | some U =>
          simp only [Option.map_eq_some_iff] at hann
          obtain ⟨U', hU, rfl⟩ := hann
          simp [ATm.NoAnyAnn, it, iu, (resolveAns_avoids U Λ nv U' hU).1 ha.1.1]
  | _, Λ, nv, .letex κ x t u, a, ha, h => by
      simp only [STm.Avoids, Bool.and_eq_true] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, u', hu, rfl⟩ := h
      simp [ATm.NoAnyAnn, resolveTm_noAny Λ nv t t' ha.1 ht, resolveTm_noAny Λ _ u u' ha.2 hu]
  | _, Λ, nv, .box t, a, ha, h => by
      simp only [STm.Avoids] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t₀, ht, rfl⟩ := h
      exact Spine.plug_noAny _ _ (atomize_noAny nv t₀ (resolveTm_noAny Λ nv t t₀ ha ht)) rfl
  | _, Λ, nv, .unbox C t, a, ha, h => by
      simp only [STm.Avoids, Bool.and_eq_true] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t₀, ht, C', hC, rfl⟩ := h
      exact Spine.plug_noAny _ _
        (atomize_noAny nv t₀ (resolveTm_noAny Λ nv t t₀ ha.2 ht))
        (unboxSet_noAny C ((resolveCap_avoids C Λ _ C' hC).1 ha.1))
  | _, Λ, nv, .asc t T, a, ha, h => by
      simp only [STm.Avoids, Bool.and_eq_true] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, T', hT, rfl⟩ := h
      simp [ATm.NoAnyAnn, resolveTm_noAny Λ nv t t' ha.1 ht, (resolveTy_avoids T Λ nv T' hT).1 ha.2]
/-- Resolved definitions hold `any` only where the written ones do. -/
theorem resolveDefs_noAny : ∀ {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (d : SDefs)
    (a : ADefs s), SDefs.Avoids .any d = true → resolveDefs Λ nv d = some a →
    a.NoAnyAnn = true
  | _, Λ, nv, .typ A S, a, ha, h => by
      simp only [SDefs.Avoids] at ha
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨l, _, S', hS, rfl⟩ := h
      exact (resolveShape_avoids S Λ nv S' hS).1 ha
  | _, Λ, nv, .cap C c, a, ha, h => by
      simp only [SDefs.Avoids] at ha
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨l, _, c', hc, rfl⟩ := h
      exact (resolveCap_avoids c Λ nv c' hc).1 ha
  | _, Λ, nv, .trm a' t, a, ha, h => by
      simp only [SDefs.Avoids] at ha
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨l, _, t', ht, rfl⟩ := h
      exact resolveTm_noAny Λ nv t t' ha ht
  | _, Λ, nv, .and d e, a, ha, h => by
      simp only [SDefs.Avoids, Bool.and_eq_true] at ha
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨d', hd, e', he, rfl⟩ := h
      simp [ADefs.NoAnyAnn, resolveDefs_noAny Λ nv d d' ha.1 hd,
        resolveDefs_noAny Λ nv e e' ha.2 he]
end

/-- A program that writes no `any` resolves to a term with none in an
annotation, a set or a type definition. -/
theorem resolve_noAny {s : Sig} {Λ : LabelTable} {nv : NameEnv s} {e : STm} {a : ATm s}
    (he : STm.Avoids .any e = true) (h : resolveTm Λ nv e = some a) :
    ATm.NoAnyAnn a = true :=
  resolveTm_noAny Λ nv e a he h

/-! ## Spine equations -/

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

/-- A variable is already in variable position, so no binding is inserted. -/
theorem atomize_var {s : Sig} (nv : NameEnv s) (i : BVar s .var) :
    atomize nv (.path (.var i)) = ⟨s, .nil, nv, i⟩ := rfl

/-! ## The programs

The programs of `Notation.lean` are resolved with the labels of the version's
examples and compared by `decide` with hand-written annotated terms, or with
the version's own types and terms. -/

open CapturesCC.DotMNF.Examples (k1 k2 platSet fileS unitTy unitTm arrowS lread lC
  W2TyAny W2Ty Z1TyF Z1Ty S1TyAny)

/-- The labels of the version's examples (`DotMNF/Examples.lean`). -/
def Λc : LabelTable :=
  [("A", .typ 0), ("B", .typ 1), ("T", .typ 2), ("C", .typ 3),
   ("a", .trm 0), ("b", .trm 1), ("v", .trm 2), ("elem", .trm 3), ("run", .trm 4),
   ("e1", .trm 5), ("e2", .trm 6), ("read", .trm 7), ("next", .trm 8)]

/-- The platform `k1, k2`. -/
def πc : PlatformNames := PlatformNames.ofList ["k1", "k2"]

/-- The platform `fs, k2`, as in the version's `Z1` and `S1`. -/
def πz : PlatformNames := PlatformNames.ofList ["fs", "k2"]

/-- The platform set is the version's `platSet`. -/
example : πc.set = platSet := by decide

/-! ### The written types keep `any` and `fresh` -/

/-- `process` of W2 resolves to the version's `W2TyAny`. -/
example : resolveTy Λc πc.names W2src = some W2TyAny := by decide

/-- The version reads that `any` as the arrow's own binder (`W2_expand`). -/
example : (resolveTy Λc πc.names W2src).map (·.expand platSet) = some W2Ty := by decide

/-- `freshCell` of Z1 resolves to the version's `Z1TyF`. -/
example : resolveTy Λc πz.names Z1src = some (Z1TyF k1) := by decide

/-- The version reads that `fresh` as an existential (`Z1_expandFresh`). -/
example : (resolveTy Λc πz.names Z1src).map Ty.expandFresh = some (Z1Ty k1) := by decide

/-- `withFile` of S1 resolves to the version's `S1TyAny`. -/
example : resolveTy Λc πz.names S1src = some (S1TyAny k1) := by decide

/-! ### Lambdas -/

/-- `any` in a lambda domain is kept. -/
example :
    resolveTop Λc πc (cc% λ(x : ⊤ ^ {any}). x) =
      some (.lam (.capt [CapAtom.any] .top) (.path (.var .here))) := by decide

/-- `fresh` in a lambda domain does not resolve. -/
example : (resolveTop Λc πc (cc% λ(x : ⊤ ^ {fresh}). x)).isNone = true := by decide

/-- Nor does `fresh` deeper in a domain. -/
example :
    (resolveTop Λc πc (cc% λ(h : (∀(u : ⊤) ⊤ ^ {fresh}) ^ {k1}). h)).isNone = true := by
  decide

/-- A named arrow binder is the domain's `.here`.  In the body it sits between
the body root and the parameter. -/
example :
    resolveTop Λc πc (cc% λ[c](x : ⊤ ^ {c}). let y : ⊤ ^ {c} = x in y) =
      some (.lam (.capt [CapAtom.cvar .here] .top)
        (.let (some (.ty (.capt [CapAtom.cvar (.there .here)] .top)))
          (.path (.var .here)) (.path (.var .here)))) := by decide

/-- An anonymous arrow binder has no name the program can write. -/
example : (resolveTop Λc πc (cc% λ(x : ⊤ ^ {c}). x)).isNone = true := by decide

/-- A platform capability, read in a domain and in a body. -/
example :
    resolveTop Λc πc (cc% λ(x : ⊤ ^ {k1}). let y : ⊤ ^ {k1} = x in y) =
      some (.lam (.capt [CapAtom.cvar (.there k1)] .top)
        (.let (some (.ty (.capt [CapAtom.cvar (.there (.there (.there k1)))] .top)))
          (.path (.var .here)) (.path (.var .here)))) := by decide

/-! ### Objects: the class root -/

/-- The outer `y` is one step out in the self shape and two in the
definitions. -/
example :
    resolveTop Λc πc
        (cc% λ(y : ⊤). ν(z : {a : ⊤} ∧ {C^ : {}..{y}}. {a = y} ∧ {C^ = {y}})) =
      some (.lam unitTy
        (.obj (.and (.fld (.trm 0) unitTy) (.cap lC [] [CapAtom.var (.there .here)]))
          (.and (.trm (.trm 0) (.path (.var (.there (.there .here)))))
            (.cap lC [CapAtom.var (.there (.there .here))])))) := by decide

/-! ### Answers, unpacking and unboxing -/

/-- An existential `let` annotation. -/
example :
    resolveTop Λc πc (cc% λ(u : ⊤). let r : ∃[w ⊑ {u}] ⊤ ^ {w} = u in r) =
      some (.lam unitTy
        (.let (some (.ex [CapAtom.var .here] (.capt [CapAtom.cvar .here] .top)))
          (.path (.var .here)) (.path (.var .here)))) := by decide

/-- A written unpacking opens the witness binder, then the payload. -/
example :
    resolveTop Λc πc (cc% λ(fc : ⊤). let ⟨k, c⟩ = fc in {k} ⊸ c) =
      some (.lam unitTy
        (.letex (.path (.var .here)) (.unbox (some [CapAtom.cvar (.there .here)]) .here))) := by
  decide

/-- An unboxing written with the empty set leaves its set to the typer. -/
example :
    resolveTop Λc πc (cc% λ(e : □(⊤ ^ {k1})). {} ⊸ e) =
      some (.lam (.capt [] (.box (.capt [CapAtom.cvar (.there k1)] .top)))
        (.unbox none .here)) := by decide

/-! ### Let insertion

`λ(f : ⊤). λ(g : ⊤). f (g f)`.  The operand `g f` is not a variable, so
`atomize` binds it. -/

/-- The nested application with its inserted `let`. -/
def nestedAppAnn : ATm πc.sig :=
  .lam unitTy (.lam unitTy
    (.let none (.app .here (.there (.there (.there .here))))
      (.app (.there (.there (.there (.there .here)))) .here)))

example : resolveTop Λc πc (cc% λ(f : ⊤). λ(g : ⊤). f (g f)) = some nestedAppAnn := by decide

/-- Its skeleton counts the inserted binding as one `let`. -/
example :
    nestedAppAnn.skel = .lam (.lam (.let (.app 0 1) (.app 2 0))) := by decide

/-! ### W2, the call of a capture-parameter arrow

`p f` under the version's context `W2CallCtx`. -/

example :
    (resolveIn Λc ((πc.names.cons "p").cons "f") (cc% p f)).map ATm.erase =
      some (Tm.app (.there .here) .here) := by decide

/-! ### A capture parameter that is called

`P1src` names `unit`, a term variable bound around it.  Its domain keeps the
written `any`.  Under the version's `Tm.expand`, the domain is
`(∀(u : ⊤) ⊤) ^ {κ}`, with `κ` the arrow's own binder. -/

/-- The term `P1src` resolves to, under `unit`. -/
def P1ann : ATm (πc.sig,x) :=
  .lam (.capt [CapAtom.any] arrowS)
    (.let none (.path (.var (.there (.there (.there .here)))))
      (.app (.there .here) .here))

example : resolveIn Λc (πc.names.cons "unit") P1src = some P1ann := by decide

example :
    (resolveIn Λc (πc.names.cons "unit") P1src).map (fun a => a.erase.expand) =
      some (Tm.val (.lam (.capt [CapAtom.cvar .here] arrowS)
        (.let (.path (.var (.there (.there (.there .here))))) (.app (.there .here) .here)))) := by
  decide

/-! ### The escape

`EscSrc` resolves.  Its `let` keeps the written answer with every `any` in
place. -/

/-- The annotation of the escape's `let`. -/
def EscTy {s : Sig} : Ty s :=
  .capt [] (.all (.capt [CapAtom.any] fileS)
    (.ty (.capt [CapAtom.any] (.all unitTy (.ty (.capt [CapAtom.any] fileS))))))

/-- The term `EscSrc` resolves to. -/
def EscAnn : ATm πc.sig :=
  .lam unitTy
    (.let (some (.ty EscTy))
      (.lam (.capt [CapAtom.any] fileS)
        (.lam unitTy (.path (.var (.there (.there (.there .here)))))))
      (.path (.var .here)))

example : resolveTop Λc πc EscSrc = some EscAnn := by decide

/-- The totality theorem applies to the escape. -/
example : (resolveTop Λc πc EscSrc).isSome = true :=
  resolveTm_isSome Λc πc.names EscSrc (by decide) (by decide) (by decide)

/-! ### Z1, the caller of `freshCell`, and two calls in a row

The version types the caller's body at `Z1Ctx`, the platform with
`fc : freshCell` and `un : ⊤` on top (`Z1_caller`).  The body is resolved
there, and so is `let c1 = fc un in fc un`.  The resolver inserts a plain
`let`.  The typer makes it a `letex`, whose body is the `let`'s body renamed
past the witness binder.  That unpacking erases to the term the version types,
and its skeleton is the `let`'s. -/

/-- The names of `Z1Ctx`. -/
def z1Names : NameEnv (πz.sig,x,x) := (πz.names.cons "fc").cons "un"

/-- `λ(v : ⊤). v` under a scope. -/
private def idAnn {s : Sig} : ATm s := .lam unitTy (.path (.var .here))

/-- The caller's body, as resolved. -/
def Z1callerAnn : ATm (πz.sig,x,x) :=
  .let none (.app (.there .here) .here) (.let none (.path (.var .here)) idAnn)

example :
    resolveIn Λc z1Names (cc% let c = fc un in let w = c in λ(v : ⊤). v) = some Z1callerAnn := by
  decide

/-- The unpacking the typer makes of a `let`. -/
def letexOf {s : Sig} : ATm s → Option (ATm s)
  | .let _ t u => some (.letex t (u.rename (Rename.succ (k := .cap)).lift))
  | _ => none

/-- The unpacking erases to the term of the version's `Z1_caller`. -/
example :
    (letexOf Z1callerAnn).map ATm.erase =
      some (Tm.letex (.app (.there .here) .here) (.let (.path (.var .here)) unitTm)) := by decide

/-- It has the skeleton of the `let`, by `ATm.skel_rename_succLift`. -/
example : (letexOf Z1callerAnn).map ATm.skel = some Z1callerAnn.skel :=
  congrArg some (ATm.skel_letex_of_let _ _ _)

/-- `let c1 = fc un in fc un`, as resolved. -/
def Z1TailAnn : ATm (πz.sig,x,x) :=
  .let none (.app (.there .here) .here) (.app (.there (.there .here)) (.there .here))

example : resolveIn Λc z1Names Z1TailSrc = some Z1TailAnn := by decide

/-- Its unpacking erases to `letex ⟨c, c1⟩ = fc un in fc un`. -/
example :
    (letexOf Z1TailAnn).map ATm.erase =
      some (Tm.letex (.app (.there .here) .here)
        (.app (.there (.there (.there .here))) (.there (.there .here)))) := by decide

example : (letexOf Z1TailAnn).map ATm.skel = some Z1TailAnn.skel := by decide

/-! ### The caller as a closed program

`Z1callerSrc` binds `fc` by a lambda whose domain writes `fresh`, so it does
not resolve.  Written with the existential that `fresh` reads as, it does. -/

example : (resolveProg Λc Z1callerSrc).isNone = true := by decide

/-- The caller over the platform `fs, k2`, with `fc`'s domain written as the
version's `Z1Ty`. -/
def Z1callerExSrc : SProg :=
  ccProg% [fs, k2]
    λ(fc : (∀(u : ⊤) ∃[c ⊑ {fs, u}] μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {c}) ^ {fs}).
      λ(un : ⊤). let c = fc un in let w = c in λ(v : ⊤). v

/-- Its domain is `Z1Ty` past the arrow binder.  In the inner body, `fc` is
three binders out of `un`. -/
example :
    resolveProg Λc Z1callerExSrc =
      some (.lam (Z1Ty (.there k1))
        (.lam unitTy
          (.let none (.app (.there (.there (.there .here))) .here)
            (.let none (.path (.var .here)) idAnn)))) := by decide

/-! ### No `any` of the resolver's own -/

/-- A program that writes no `any` resolves to a term with none. -/
example : ∀ a, resolveTop Λc πc (cc% λ(f : ⊤). λ(g : ⊤). f (g f)) = some a →
    a.NoAnyAnn = true :=
  fun _ h => resolve_noAny (by decide) h

end CapturesCCFrontend
