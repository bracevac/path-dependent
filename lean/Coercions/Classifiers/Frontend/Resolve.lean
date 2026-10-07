import Coercions.Classifiers.Frontend.Ann
import Coercions.Classifiers.Frontend.Notation
import Coercions.Classifiers.DotMNF.Examples

/-!
# Name resolution and let insertion for the Classifiers front end

The functions of this module take a surface phrase to the annotated de Bruijn
syntax of `Ann.lean`: `resolveShape`, `resolveTy` and `resolveAns` for the
three sorts of type, `resolveTm` for a term and `resolveDefs` for a
definition list.  They are the only place where a surface name becomes an
index.

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
(`lean/Coercions/Classifiers/DotMNF/Examples.lean`).

## Binders the program does not write

The calculus has binders that no surface phrase writes.  The resolver
inserts them, so that the name environment stays in step with the
signature.

- A lambda: the body root, then the arrow's own capture binder, then the
  parameter.  The domain is read under the arrow binder alone.
- An arrow type: its capture binder, which scopes over the domain, then the
  parameter, which with it scopes over the codomain.
- An object: the class root, then the self, over the definitions.  The self
  shape is read under the self alone.
- An existential answer `∃[c ⊑ C] T`: one capture binder over `T`.  The
  bound `C` is read outside it.
- A written unpacking `let ⟨c, x⟩ = t in u`: the witness binder, then the
  payload, over `u`.

A root and an anonymous arrow binder are named `"%"`, which no identifier of
the notation can equal.  So no surface name ever refers to a root, and `any`
is the only way to speak of one, which is the compiler's discipline.  An
arrow binder the program names, `∀[c]` or `λ[c]`, is in scope under its
name.

## The atoms `any` and `fresh`

The resolver does not read `any` and `fresh`.  It turns them into the frozen
atoms `CapAtom.any` and `CapAtom.fresh` and leaves them where the program
wrote them.  What each one stands for is a function of the context the typer
builds, so the typer reads them, with the frozen `Ty.expand`,
`Ty.expandFresh` and `Ctx.reading`.  One placement is refused here.  A
lambda domain holding `fresh` does not resolve: the version reads a domain
by `Value.expand`, which reads `any` only, and its `FreshOk` keeps `fresh`
out of every parameter type.

## Classifiers

A program declares its classifiers by name.  `clsTableOf` numbers each
declaration as the next child of its parent, in declaration order, and of
the root when it extends nothing, so `IO, ThreadLocal, Control extends
ThreadLocal` gives exactly the version's `Cls.IO`, `Cls.ThreadLocal` and
`Cls.Control`.  A kind resolves by `resolveKind`: `only` to the union of
`Cls.only`, `except` to one holed subtree of the root, `∪` to the union
and `∩` to the version's intersection.  A kind mentions no binder, so it
needs no name environment.

A projected atom resolves through the version's smart constructor
`CapAtom.projBy`, which intersects with a projection already there instead
of nesting a second one.  So a projected set `{a, b}.only[K]`, which the
notation writes as a projection of each atom, resolves to the version's
`CaptureSet.proj` of the resolved set (`resolveCap_map_proj`), and no
resolved phrase holds a projection under a projection
(`resolve_noNestedProj`).  A kind-bounded member `{C^ : K}` resolves to
`Shape.capk` at the type label of `C`.  A platform binder declared at a
classifier resolves to `Platform.consCls`, a plain one to `Platform.cons`.
Either way it opens one capture binder.

## Let insertion

Let insertion uses an explicit spine of bindings, as the vanilla front end
does, which keeps the resolvers structural on the surface phrase.  The two
vanilla direct style forms, application and projection, atomize their
operands, and so do the two box forms, `□ t` and `C ⊸ t`.  The inserted
binder is named `"%"`.  Every inserted binding is a plain `let`.  Whether a
`let` unpacks an existential answer is decided by the typer, from the
answer of the bound term.

An unboxing written with the empty set, `{} ⊸ t`, leaves its set to the
typer.  With a nonempty set the set is kept as written.

This module imports `Notation.lean` for the programs at the end, and Lean's
token table is global.  So the Greek nu that opens an object literal is a
keyword here and cannot be a local name.  The name environment is written
`nv` below for that reason.

Nothing in this module is part of the metatheory.  No definition here lives
in a namespace of the version.
-/

namespace ClassifiersFrontend

open Classifiers.FCdot (Kind Sig BVar Rename Label)
open Classifiers.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Tm Value Defs Platform)
open Classifiers

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

/-! ## The classifier table and kinds

`clsTableOf` reads a program's declarations into a `ClsTable`.  The
classifiers a table holds are paths in an infinite tree, so a declaration
takes the next free child index of its parent and no two declarations of
one parent meet.  A parent must be declared before its children.  A name
declared twice keeps its first entry, which `clsFind?` returns. -/

/-- The number of entries of the table that are direct children of `p`. -/
def childCount (κt : ClsTable) (p : Cls.Classifier) : Nat :=
  (κt.filter fun e =>
    match e.2 with
    | .child _ q => decide (q = p)
    | .top => false).length

/-- Extend a table by declarations, in order.  Each declaration is the
next child of its parent, or of the root when it extends nothing.  `none`
when a parent is declared after its child or not at all. -/
def clsTableOf (κt : ClsTable) (ds : SClsDecls) : Option ClsTable :=
  match ds with
  | [] => some κt
  | (c, none) :: ds => clsTableOf (κt ++ [(c, .child (childCount κt .top) .top)]) ds
  | (c, some p) :: ds => do
      let q ← clsFind? κt p
      clsTableOf (κt ++ [(c, .child (childCount κt q) q)]) ds
termination_by structural ds

/-- Look up every name of a list, failing on the first one that is not in
the table. -/
def clsFindAll? (κt : ClsTable) (cs : List String) : Option (List Cls.Classifier) :=
  match cs with
  | [] => some []
  | c :: cs => do
      let x ← clsFind? κt c
      let xs ← clsFindAll? κt cs
      pure (x :: xs)
termination_by structural cs

/-- Resolve a kind.  `only[c₁, …]` is the union of the `Cls.only cᵢ`,
`except[c₁, …]` the root minus the subtrees of the `cᵢ`, so `except[]` is
`Cls.Kind.top`.  `∪` is the version's union, list append, and `∩` its
intersection. -/
def resolveKind (κt : ClsTable) (K : SKind) : Option Cls.Kind :=
  match K with
  | .only cs => (clsFindAll? κt cs).map fun l => l.flatMap Cls.only
  | .except cs => (clsFindAll? κt cs).map fun l => Cls.Kind.node .top l
  | .union K L => do
      let k ← resolveKind κt K
      let l ← resolveKind κt L
      pure (k ++ l)
  | .inter K L => do
      let k ← resolveKind κt K
      let l ← resolveKind κt L
      pure (k.interB l)
termination_by structural K

/-- A name the table holds is found. -/
theorem clsFindAll?_isSome (κt : ClsTable) : ∀ (cs : List String),
    (cs.all fun c => (clsFind? κt c).isSome) = true → (clsFindAll? κt cs).isSome = true
  | [], _ => rfl
  | c :: cs, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h.1
      obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp (clsFindAll?_isSome κt cs h.2)
      simp [clsFindAll?, hx, hxs]

/-- **Totality of kind resolution.**  A kind whose classifier names are all
in the table resolves. -/
theorem resolveKind_isSome (κt : ClsTable) (K : SKind) (h : SKind.ClassifiersIn κt K = true) :
    (resolveKind κt K).isSome = true := by
  induction K with
  | only cs =>
      simp only [SKind.ClassifiersIn] at h
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (clsFindAll?_isSome κt cs h)
      simp [resolveKind, hl]
  | except cs =>
      simp only [SKind.ClassifiersIn] at h
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (clsFindAll?_isSome κt cs h)
      simp [resolveKind, hl]
  | union K L ihK ihL =>
      simp only [SKind.ClassifiersIn, Bool.and_eq_true] at h
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (ihK h.1)
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (ihL h.2)
      simp [resolveKind, hk, hl]
  | inter K L ihK ihL =>
      simp only [SKind.ClassifiersIn, Bool.and_eq_true] at h
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (ihK h.1)
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (ihL h.2)
      simp [resolveKind, hk, hl]

/-! ## The classified platform

A platform binder declared at a classifier is the version's
`Platform.consCls`, a plain one its `Platform.cons`.  The signature, the
names and the platform's own set depend on the binder names alone, so they
are those of `PlatformNames.ofList`, and only the `Platform` itself reads
the table. -/

/-- The platform of a binder list over a given prefix, each binder one more
capture binder, the first one outermost.  `none` when a binder's
classifier is not in the table. -/
def platformFrom (κt : ClsTable) (π : PlatformNames) (P : Platform π.sig) (ps : SPlatform) :
    Option (Platform (π.pushAll (ps.map Prod.fst)).sig) :=
  match ps with
  | [] => some P
  | (y, none) :: ps => platformFrom κt (π.push y) (.cons P) ps
  | (y, some c) :: ps => do
      let cl ← clsFind? κt c
      platformFrom κt (π.push y) (.consCls P cl) ps
termination_by structural ps

/-- The platform of a program's binder list. -/
def resolvePlatform (κt : ClsTable) (ps : SPlatform) :
    Option (Platform (PlatformNames.ofList (ps.map Prod.fst)).sig) :=
  platformFrom κt PlatformNames.empty .nil ps

/-- A platform whose classifiers are all in the table resolves. -/
theorem platformFrom_isSome (κt : ClsTable) : ∀ (ps : SPlatform) (π : PlatformNames)
    (P : Platform π.sig), SPlatform.ClassifiersIn κt ps = true →
    (platformFrom κt π P ps).isSome = true
  | [], _, _, _ => rfl
  | (y, none) :: ps, π, P, h => by
      simp only [SPlatform.ClassifiersIn, List.all_cons, Bool.true_and] at h
      exact platformFrom_isSome κt ps (π.push y) (.cons P) h
  | (y, some c) :: ps, π, P, h => by
      simp only [SPlatform.ClassifiersIn, List.all_cons, Bool.and_eq_true] at h
      obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.mp h.1
      have ih := platformFrom_isSome κt ps (π.push y) (.consCls P cl) h.2
      simpa [platformFrom, hcl] using ih

/-- **Totality of platform resolution.** -/
theorem resolvePlatform_isSome (κt : ClsTable) (ps : SPlatform)
    (h : SPlatform.ClassifiersIn κt ps = true) : (resolvePlatform κt ps).isSome = true :=
  platformFrom_isSome κt ps _ _ h

/-! ## Covering, the monotonicity of scoping

The resolver reads a phrase under an environment that may hold more names
than the surface scoping asks for: the binders it inserts, `"%"` for a root
or an anonymous arrow binder, and the binder `atomize` adds.  So the
totality proof needs scoping to survive larger lists of names, of both
kinds. -/

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

/-- The capture names a surface arrow binder opens are covered by the ones
the resolver opens, written name or `"%"`. -/
theorem Covers.binder (K : List String) (o : Option String) :
    Covers (optCons o K) (binderName o :: K) := by
  cases o with
  | none => exact Covers.tail K "%"
  | some n => exact Covers.rfl' _

/-- Scoping of a capture atom survives larger lists of names. -/
theorem SAtom.Scoped_covers : ∀ (a : SAtom) {K K' Γ Γ' : List String},
    Covers K K' → Covers Γ Γ' → SAtom.Scoped K Γ a = true → SAtom.Scoped K' Γ' a = true
  | .name x, _, _, _, _, hK, hΓ, hs => by
      simp only [SAtom.Scoped, Bool.or_eq_true] at hs ⊢
      rcases hs with h1 | h1
      · exact Or.inl (hΓ x h1)
      · exact Or.inr (hK x h1)
  | .sel x _, _, _, _, _, _, hΓ, hs => hΓ x hs
  | .any, _, _, _, _, _, _, hs => hs
  | .fresh, _, _, _, _, _, _, hs => hs
  | .proj a _, _, _, _, _, hK, hΓ, hs => SAtom.Scoped_covers a hK hΓ hs

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
  | .proj a _ :: c, _, _, _, _, hK, hΓ, hs => by
      simp only [SCap.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SAtom.Scoped_covers a hK hΓ hs.1, SCap.Scoped_covers c hK hΓ hs.2⟩

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
  | .capk _ _, _, _, _, _, _, _, _ => rfl
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

/-- Resolve a capture atom.  A plain name takes the innermost binder of
either kind, the receiver of `x.C` a term binder.  `any` and `fresh` are
kept as the frozen atoms.  A projected atom resolves its base and its kind
and projects through the version's `CapAtom.projBy`, which intersects with
a projection already there. -/
def resolveCapAtom {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (a : SAtom) :
    Option (CapAtom s) :=
  match a with
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
  | .proj a K => do
      let a' ← resolveCapAtom Λ κt nv a
      let k ← resolveKind κt K
      pure (CapAtom.projBy k a')
termination_by structural a

/-- Resolve a capture set, atom by atom. -/
def resolveCap {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (c : SCap) :
    Option (CaptureSet s) :=
  match c with
  | [] => some []
  | a :: c => do
      let a' ← resolveCapAtom Λ κt nv a
      let c' ← resolveCap Λ κt nv c
      pure (a' :: c')
termination_by structural c

/-- **A projected set is the version's projection of the set.**  The
notation writes `{a, b}.only[K]` as the projection of each atom, and
resolution takes that to `CaptureSet.proj` of the resolved set. -/
theorem resolveCap_map_proj {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s)
    {K : SKind} {k : Cls.Kind} (hk : resolveKind κt K = some k) : ∀ (c : SCap),
    resolveCap Λ κt nv (c.map (SAtom.proj · K)) =
      (resolveCap Λ κt nv c).map (CaptureSet.proj · k)
  | [] => rfl
  | a :: c => by
      have ih := resolveCap_map_proj Λ κt nv hk c
      simp only [List.map_cons, resolveCap, resolveCapAtom, hk, ih]
      cases resolveCapAtom Λ κt nv a <;> cases resolveCap Λ κt nv c <;> rfl

/-! ## Shapes, types and answers

The three sorts of the surface are the three sorts of the calculus, so each
is read into its own.  An arrow opens its capture binder, under its written
name or `"%"`, for the domain, and the parameter on top of it for the
codomain.  An existential opens its binder for the type and reads its bound
outside.  A kind-bounded member reads its kind against the table. -/

mutual
/-- Resolve a surface shape. -/
def resolveShape {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (S : SShape) :
    Option (Shape s) :=
  match S with
  | .top => some .top
  | .bot => some .bot
  | .typ A S T => do
      let l ← labelTyp? Λ A
      let S' ← resolveShape Λ κt nv S
      let T' ← resolveShape Λ κt nv T
      pure (.typ l S' T')
  | .fld a T => do
      let l ← labelTrm? Λ a
      let T' ← resolveTy Λ κt nv T
      pure (.fld l T')
  | .cap C lo hi => do
      let l ← labelTyp? Λ C
      let lo' ← resolveCap Λ κt nv lo
      let hi' ← resolveCap Λ κt nv hi
      pure (.cap l lo' hi')
  | .capk C K => do
      let l ← labelTyp? Λ C
      let k ← resolveKind κt K
      pure (.capk l k)
  | .sel x A => do
      let i ← nv.findVar? x
      let l ← labelTyp? Λ A
      pure (.sel (.var i) l)
  | .mu x S => do
      let S' ← resolveShape Λ κt (nv.cons x) S
      pure (.mu S')
  | .all κ x T U => do
      let T' ← resolveTy Λ κt (nv.consC (binderName κ)) T
      let U' ← resolveAns Λ κt ((nv.consC (binderName κ)).cons x) U
      pure (.all T' U')
  | .and S T => do
      let S' ← resolveShape Λ κt nv S
      let T' ← resolveShape Λ κt nv T
      pure (.and S' T')
  | .box T => do
      let T' ← resolveTy Λ κt nv T
      pure (.box T')
termination_by structural S
/-- Resolve a surface capturing type. -/
def resolveTy {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (T : SType) :
    Option (Ty s) :=
  match T with
  | .capt S C => do
      let S' ← resolveShape Λ κt nv S
      let C' ← resolveCap Λ κt nv C
      pure (.capt C' S')
termination_by structural T
/-- Resolve a surface answer. -/
def resolveAns {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (U : SAns) :
    Option (ETy s) :=
  match U with
  | .ty T => do
      let T' ← resolveTy Λ κt nv T
      pure (.ty T')
  | .ex κ C T => do
      let C' ← resolveCap Λ κt nv C
      let T' ← resolveTy Λ κt (nv.consC κ) T
      pure (.ex C' T')
termination_by structural U
end

/-! ## Terms -/

/-- The set an unboxing keeps: none when the program writes the empty set,
which leaves it to the typer, else the resolved set. -/
def unboxSet {s : Sig} (C : SCap) (C' : CaptureSet s) : Option (CaptureSet s) :=
  match C with
  | [] => none
  | _ => some C'

mutual
/-- Resolve a surface term, inserting the binders the program does not
write and `let` bindings for the four direct style forms.  The result is in
monadic normal form by construction. -/
def resolveTm {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (e : STm) :
    Option (ATm s) :=
  match e with
  | .var x => do
      let i ← nv.findVar? x
      pure (.path (.var i))
  | .lam κ x T t => do
      let T' ← resolveTy Λ κt (nv.consC (binderName κ)) T
      let t' ← resolveTm Λ κt (((nv.consC "%").consC (binderName κ)).cons x) t
      if T'.noFresh then pure (.lam T' t') else none
  | .obj x S d => do
      let S' ← resolveShape Λ κt (nv.cons x) S
      let d' ← resolveDefs Λ κt ((nv.consC "%").cons x) d
      pure (.obj S' d')
  | .app t u => do
      let t₀ ← resolveTm Λ κt nv t
      let a := atomize nv t₀
      let u₀ ← resolveTm Λ κt a.names u
      let b := atomize a.names u₀
      pure ((a.spine.append b.spine).plug (.app (b.spine.rename.var a.var) b.var))
  | .proj t a => do
      let t₀ ← resolveTm Λ κt nv t
      let c := atomize nv t₀
      let l ← labelTrm? Λ a
      pure (c.spine.plug (.proj c.var l))
  | .«let» x ann t u => do
      let ann' ← (match ann with
        | none => some none
        | some U => (resolveAns Λ κt nv U).map some)
      let t' ← resolveTm Λ κt nv t
      let u' ← resolveTm Λ κt (nv.cons x) u
      pure (.let ann' t' u')
  | .letex κ x t u => do
      let t' ← resolveTm Λ κt nv t
      let u' ← resolveTm Λ κt ((nv.consC κ).cons x) u
      pure (.letex t' u')
  | .box t => do
      let t₀ ← resolveTm Λ κt nv t
      let c := atomize nv t₀
      pure (c.spine.plug (.box c.var))
  | .unbox C t => do
      let t₀ ← resolveTm Λ κt nv t
      let c := atomize nv t₀
      let C' ← resolveCap Λ κt c.names C
      pure (c.spine.plug (.unbox (unboxSet C C') c.var))
  | .asc t T => do
      let t' ← resolveTm Λ κt nv t
      let T' ← resolveTy Λ κt nv T
      pure (.asc t' T')
termination_by structural e
/-- Resolve a surface definition list.  The environment is the one the
definitions live in, under the class root and the self. -/
def resolveDefs {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (d : SDefs) :
    Option (ADefs s) :=
  match d with
  | .typ A S => do
      let l ← labelTyp? Λ A
      let S' ← resolveShape Λ κt nv S
      pure (.typ l S')
  | .cap C c => do
      let l ← labelTyp? Λ C
      let c' ← resolveCap Λ κt nv c
      pure (.cap l c')
  | .trm a t => do
      let l ← labelTrm? Λ a
      let t' ← resolveTm Λ κt nv t
      pure (.trm l t')
  | .and d e => do
      let d' ← resolveDefs Λ κt nv d
      let e' ← resolveDefs Λ κt nv e
      pure (.and d' e')
termination_by structural d
end

/-- Resolve a surface term at a given environment, the entry point for a
term that sits under a context. -/
def resolveIn {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s) (e : STm) :
    Option (ATm s) :=
  resolveTm Λ κt nv e

/-- Resolve a closed program over a platform. -/
def resolveTop (Λ : LabelTable) (κt : ClsTable) (π : PlatformNames) (e : STm) :
    Option (ATm π.sig) :=
  resolveTm Λ κt π.names e

/-! ## Whole programs

A program's header declares its classifiers, its platform binders, and
optionally the body's use set and kind.  The signature, names and set of
the platform are those of its binder names, `SProg.platNames`, so the
resolved body has a type fixed by the program alone. -/

/-- The platform names of a program: its binder names, the first one
outermost. -/
def SProg.platNames (p : SProg) : PlatformNames := PlatformNames.ofList (p.platform.map Prod.fst)

/-- A resolved program over the signature `s` of its platform: the
classifier table its declarations give, the classified platform, the
declared use set and kind when written, and the body. -/
structure ResolvedProg (s : Sig) where
  /-- The classifier table of the declarations. -/
  table : ClsTable
  /-- The platform, each binder at its classifier when one is written. -/
  plat : Platform s
  /-- The declared use set, read over the platform. -/
  uses : Option (CaptureSet s)
  /-- The declared kind. -/
  kind : Option Cls.Kind
  /-- The body. -/
  body : ATm s

/-- Resolve a whole program: the declarations into a table, the platform,
the declared use set and kind against that table, and the body over the
platform. -/
def resolveProg (Λ : LabelTable) (p : SProg) : Option (ResolvedProg p.platNames.sig) := do
  let κt ← clsTableOf [] p.classifiers
  let P ← resolvePlatform κt p.platform
  let uses ← (match p.uses with
    | none => some none
    | some C => (resolveCap Λ κt p.platNames.names C).map some)
  let kind ← (match p.kind with
    | none => some none
    | some K => (resolveKind κt K).map some)
  let body ← resolveTop Λ κt p.platNames p.body
  pure ⟨κt, P, uses, kind, body⟩

/-! ## Surface side conditions about atoms

`Avoids a` says that the atom `a` occurs in no capture set of the phrase,
annotations included, also not under a projection.  `FreshPlaced` says that
no lambda domain of a term holds `fresh`, the one placement the resolver
refuses. -/

/-- The atom under the projections of a surface atom. -/
def SAtom.base (a : SAtom) : SAtom :=
  match a with
  | .proj a _ => SAtom.base a
  | .name x => .name x
  | .sel x C => .sel x C
  | .any => .any
  | .fresh => .fresh
termination_by structural a

/-- The atom occurs in no position of the set, also not under a
projection. -/
def SCap.Avoids (a : SAtom) (c : SCap) : Bool :=
  match c with
  | [] => true
  | b :: c => (b.base != a) && SCap.Avoids a c
termination_by structural c

mutual
/-- The atom occurs in no capture set of the shape. -/
def SShape.Avoids (a : SAtom) (S : SShape) : Bool :=
  match S with
  | .top => true
  | .bot => true
  | .typ _ S T => SShape.Avoids a S && SShape.Avoids a T
  | .fld _ T => SType.Avoids a T
  | .cap _ lo hi => SCap.Avoids a lo && SCap.Avoids a hi
  | .capk _ _ => true
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
their position needs, whose labels and classifier names are in their
tables, and, for a term, whose lambda domains hold no `fresh`.  The proof
is by structural recursion on the surface phrase.  Every binder the
resolver inserts only adds names, so the written scoping carries over by
covering.  In the direct style clauses the operand is resolved under the
environment `atomize` returns, and `atomize_names_covers` carries the
scoping across.  Classifier names and labels do not depend on the
environment. -/

/-- Scoping of a nonempty capture set is scoping of its first atom and of
the rest. -/
theorem SCap.Scoped_cons (K Γ : List String) (a : SAtom) (c : SCap) :
    SCap.Scoped K Γ (a :: c) = (SAtom.Scoped K Γ a && SCap.Scoped K Γ c) := by
  cases a <;> rfl

/-- Labelling of a nonempty capture set is labelling of its first atom and
of the rest. -/
theorem SCap.LabelsIn_cons (Λ : LabelTable) (a : SAtom) (c : SCap) :
    SCap.LabelsIn Λ (a :: c) = (SAtom.LabelsIn Λ a && SCap.LabelsIn Λ c) := by
  cases a <;> rfl

/-- A scoped, labelled and classified capture atom resolves. -/
theorem resolveCapAtom_isSome : ∀ (a : SAtom) {s : Sig} (Λ : LabelTable) (κt : ClsTable)
    (nv : NameEnv s), SAtom.Scoped nv.capNames nv.names a = true → SAtom.LabelsIn Λ a = true →
    SAtom.ClassifiersIn κt a = true → (resolveCapAtom Λ κt nv a).isSome = true
  | .name x, _, _, _, nv, hs, _, _ => by
      simp only [SAtom.Scoped] at hs
      obtain ⟨⟨k, i⟩, hf⟩ := Option.isSome_iff_exists.mp (NameEnv.find?_isSome nv x hs)
      cases k <;> simp [resolveCapAtom, hf]
  | .sel x C, _, Λ, _, nv, hs, hl, _ => by
      simp only [SAtom.Scoped, SAtom.LabelsIn] at hs hl
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (NameEnv.findVar?_isSome nv x hs)
      obtain ⟨l, hlC⟩ := Option.isSome_iff_exists.mp hl
      simp [resolveCapAtom, hi, hlC]
  | .any, _, _, _, _, _, _, _ => rfl
  | .fresh, _, _, _, _, _, _, _ => rfl
  | .proj a K, _, Λ, κt, nv, hs, hl, hc => by
      simp only [SAtom.Scoped, SAtom.LabelsIn, SAtom.ClassifiersIn, Bool.and_eq_true] at hs hl hc
      obtain ⟨a', ha⟩ := Option.isSome_iff_exists.mp
        (resolveCapAtom_isSome a Λ κt nv hs hl hc.1)
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (resolveKind_isSome κt K hc.2)
      simp [resolveCapAtom, ha, hk]

/-- A scoped, labelled and classified capture set resolves. -/
theorem resolveCap_isSome : ∀ (c : SCap) {s : Sig} (Λ : LabelTable) (κt : ClsTable)
    (nv : NameEnv s), SCap.Scoped nv.capNames nv.names c = true → SCap.LabelsIn Λ c = true →
    SCap.ClassifiersIn κt c = true → (resolveCap Λ κt nv c).isSome = true
  | [], _, _, _, _, _, _, _ => rfl
  | a :: c, _, Λ, κt, nv, hs, hl, hc => by
      rw [SCap.Scoped_cons] at hs
      rw [SCap.LabelsIn_cons] at hl
      simp only [SCap.ClassifiersIn, List.all_cons, Bool.and_eq_true] at hs hl hc
      obtain ⟨a', ha⟩ := Option.isSome_iff_exists.mp
        (resolveCapAtom_isSome a Λ κt nv hs.1 hl.1 hc.1)
      obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp
        (resolveCap_isSome c Λ κt nv hs.2 hl.2 hc.2)
      simp [resolveCap, ha, hc']

/-- An arrow's domain, read under the binder the resolver opens, keeps the
scoping the surface asks of it. -/
theorem Scoped_arrowDom {s : Sig} (nv : NameEnv s) (κ : Option String) (T : SType)
    (h : SType.Scoped (optCons κ nv.capNames) nv.names T = true) :
    SType.Scoped (nv.consC (binderName κ)).capNames (nv.consC (binderName κ)).names T = true :=
  SType.Scoped_covers T (Covers.binder _ κ) (Covers.rfl' _) h

mutual
/-- A scoped, labelled and classified shape resolves. -/
theorem resolveShape_isSome : ∀ (S : SShape) {s : Sig} (Λ : LabelTable) (κt : ClsTable)
    (nv : NameEnv s), SShape.Scoped nv.capNames nv.names S = true →
    SShape.LabelsIn Λ S = true → SShape.ClassifiersIn κt S = true →
    (resolveShape Λ κt nv S).isSome = true
  | .top, _, _, _, _, _, _, _ => rfl
  | .bot, _, _, _, _, _, _, _ => rfl
  | .typ A S T, _, Λ, κt, nv, hs, hl, hc => by
      simp only [SShape.Scoped, SShape.LabelsIn, SShape.ClassifiersIn, Bool.and_eq_true]
        at hs hl hc
      obtain ⟨l, hA⟩ := Option.isSome_iff_exists.mp hl.1.1
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp
        (resolveShape_isSome S Λ κt nv hs.1 hl.1.2 hc.1)
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp
        (resolveShape_isSome T Λ κt nv hs.2 hl.2 hc.2)
      simp [resolveShape, hA, hS, hT]
  | .fld a T, _, Λ, κt, nv, hs, hl, hc => by
      simp only [SShape.Scoped, SShape.LabelsIn, SShape.ClassifiersIn, Bool.and_eq_true]
        at hs hl hc
      obtain ⟨l, ha⟩ := Option.isSome_iff_exists.mp hl.1
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp (resolveTy_isSome T Λ κt nv hs hl.2 hc)
      simp [resolveShape, ha, hT]
  | .cap C lo hi, _, Λ, κt, nv, hs, hl, hc => by
      simp only [SShape.Scoped, SShape.LabelsIn, SShape.ClassifiersIn, Bool.and_eq_true]
        at hs hl hc
      obtain ⟨l, hC⟩ := Option.isSome_iff_exists.mp hl.1.1
      obtain ⟨lo', hlo⟩ := Option.isSome_iff_exists.mp
        (resolveCap_isSome lo Λ κt nv hs.1 hl.1.2 hc.1)
      obtain ⟨hi', hhi⟩ := Option.isSome_iff_exists.mp
        (resolveCap_isSome hi Λ κt nv hs.2 hl.2 hc.2)
      simp [resolveShape, hC, hlo, hhi]
  | .capk C K, _, Λ, κt, _, _, hl, hc => by
      simp only [SShape.LabelsIn, SShape.ClassifiersIn] at hl hc
      obtain ⟨l, hC⟩ := Option.isSome_iff_exists.mp hl
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (resolveKind_isSome κt K hc)
      simp [resolveShape, hC, hk]
  | .sel x A, _, Λ, _, nv, hs, hl, _ => by
      simp only [SShape.Scoped, SShape.LabelsIn] at hs hl
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (NameEnv.findVar?_isSome nv x hs)
      obtain ⟨l, hA⟩ := Option.isSome_iff_exists.mp hl
      simp [resolveShape, hi, hA]
  | .mu x S, _, Λ, κt, nv, hs, hl, hc => by
      simp only [SShape.Scoped, SShape.LabelsIn, SShape.ClassifiersIn] at hs hl hc
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp
        (resolveShape_isSome S Λ κt (nv.cons x) hs hl hc)
      simp [resolveShape, hS]
  | .all κ x T U, _, Λ, κt, nv, hs, hl, hc => by
      simp only [SShape.Scoped, SShape.LabelsIn, SShape.ClassifiersIn, Bool.and_eq_true]
        at hs hl hc
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp
        (resolveTy_isSome T Λ κt (nv.consC (binderName κ)) (Scoped_arrowDom nv κ T hs.1) hl.1
          hc.1)
      obtain ⟨U', hU⟩ := Option.isSome_iff_exists.mp
        (resolveAns_isSome U Λ κt ((nv.consC (binderName κ)).cons x)
          (SAns.Scoped_covers U (Covers.binder _ κ) (Covers.rfl' _) hs.2) hl.2 hc.2)
      simp [resolveShape, hT, hU]
  | .and S T, _, Λ, κt, nv, hs, hl, hc => by
      simp only [SShape.Scoped, SShape.LabelsIn, SShape.ClassifiersIn, Bool.and_eq_true]
        at hs hl hc
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp
        (resolveShape_isSome S Λ κt nv hs.1 hl.1 hc.1)
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp
        (resolveShape_isSome T Λ κt nv hs.2 hl.2 hc.2)
      simp [resolveShape, hS, hT]
  | .box T, _, Λ, κt, nv, hs, hl, hc => by
      simp only [SShape.Scoped, SShape.LabelsIn, SShape.ClassifiersIn] at hs hl hc
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp (resolveTy_isSome T Λ κt nv hs hl hc)
      simp [resolveShape, hT]
/-- A scoped, labelled and classified capturing type resolves. -/
theorem resolveTy_isSome : ∀ (T : SType) {s : Sig} (Λ : LabelTable) (κt : ClsTable)
    (nv : NameEnv s), SType.Scoped nv.capNames nv.names T = true →
    SType.LabelsIn Λ T = true → SType.ClassifiersIn κt T = true →
    (resolveTy Λ κt nv T).isSome = true
  | .capt S C, _, Λ, κt, nv, hs, hl, hc => by
      simp only [SType.Scoped, SType.LabelsIn, SType.ClassifiersIn, Bool.and_eq_true]
        at hs hl hc
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp
        (resolveShape_isSome S Λ κt nv hs.1 hl.1 hc.1)
      obtain ⟨C', hC⟩ := Option.isSome_iff_exists.mp
        (resolveCap_isSome C Λ κt nv hs.2 hl.2 hc.2)
      simp [resolveTy, hS, hC]
/-- A scoped, labelled and classified answer resolves. -/
theorem resolveAns_isSome : ∀ (U : SAns) {s : Sig} (Λ : LabelTable) (κt : ClsTable)
    (nv : NameEnv s), SAns.Scoped nv.capNames nv.names U = true →
    SAns.LabelsIn Λ U = true → SAns.ClassifiersIn κt U = true →
    (resolveAns Λ κt nv U).isSome = true
  | .ty T, _, Λ, κt, nv, hs, hl, hc => by
      simp only [SAns.Scoped, SAns.LabelsIn, SAns.ClassifiersIn] at hs hl hc
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp (resolveTy_isSome T Λ κt nv hs hl hc)
      simp [resolveAns, hT]
  | .ex κ C T, _, Λ, κt, nv, hs, hl, hc => by
      simp only [SAns.Scoped, SAns.LabelsIn, SAns.ClassifiersIn, Bool.and_eq_true] at hs hl hc
      obtain ⟨C', hC⟩ := Option.isSome_iff_exists.mp
        (resolveCap_isSome C Λ κt nv hs.1 hl.1 hc.1)
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp
        (resolveTy_isSome T Λ κt (nv.consC κ) hs.2 hl.2 hc.2)
      simp [resolveAns, hC, hT]
end

/-! ## What a resolved type holds of `any` and `fresh`

The resolver turns `any` into `CapAtom.any`, `fresh` into `CapAtom.fresh`,
a projected atom into the projection of its base, and every other atom
into a variable atom.  So a resolved phrase holds one of the two, under
projections or not, only where the written one does. -/

/-- The smart projection keeps an `any` exactly where the atom has one. -/
theorem noAnyA_projBy {s : Sig} (φ : Cls.Kind) (a : CapAtom s) :
    (CapAtom.projBy φ a).noAnyA = a.noAnyA := by
  cases a <;> rfl

/-- The smart projection keeps a `fresh` exactly where the atom has one. -/
theorem noFreshA_projBy {s : Sig} (φ : Cls.Kind) (a : CapAtom s) :
    (CapAtom.projBy φ a).noFreshA = a.noFreshA := by
  cases a <;> rfl

/-- A resolved atom holds `any` or `fresh` only where the written one does,
under its projections. -/
theorem resolveCapAtom_avoids : ∀ (a : SAtom) {s : Sig} (Λ : LabelTable) (κt : ClsTable)
    (nv : NameEnv s) (a' : CapAtom s), resolveCapAtom Λ κt nv a = some a' →
    ((a.base != .any) = true → a'.noAnyA = true) ∧
    ((a.base != .fresh) = true → a'.noFreshA = true)
  | .name x, _, _, _, nv, a', h => by
      cases hf : nv.find? x with
      | none => simp [resolveCapAtom, hf] at h
      | some p =>
          obtain ⟨k, i⟩ := p
          cases k <;> simp [resolveCapAtom, hf] at h <;> subst h <;>
            exact ⟨fun _ => rfl, fun _ => rfl⟩
  | .sel x C, _, _, _, _, a', h => by
      simp only [resolveCapAtom, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨i, _, l, _, rfl⟩ := h
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  | .any, _, _, _, _, a', h => by
      simp only [resolveCapAtom, Option.some.injEq] at h
      subst h
      exact ⟨fun h => by simp [SAtom.base] at h, fun _ => rfl⟩
  | .fresh, _, _, _, _, a', h => by
      simp only [resolveCapAtom, Option.some.injEq] at h
      subst h
      exact ⟨fun _ => rfl, fun h => by simp [SAtom.base] at h⟩
  | .proj a K, _, Λ, κt, nv, a', h => by
      simp only [resolveCapAtom, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨b, hb, k, _, rfl⟩ := h
      have ih := resolveCapAtom_avoids a Λ κt nv b hb
      simp only [SAtom.base, noAnyA_projBy, noFreshA_projBy]
      exact ih

/-- A resolved capture set holds `any` or `fresh` only where the written one
does. -/
theorem resolveCap_avoids : ∀ (c : SCap) {s : Sig} (Λ : LabelTable) (κt : ClsTable)
    (nv : NameEnv s) (c' : CaptureSet s), resolveCap Λ κt nv c = some c' →
    (SCap.Avoids .any c = true → CaptureSet.noAny c' = true) ∧
    (SCap.Avoids .fresh c = true → CaptureSet.noFresh c' = true)
  | [], _, _, _, _, c', h => by
      simp [resolveCap] at h; subst h; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | a :: c, _, Λ, κt, nv, c', h => by
      simp only [resolveCap, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨a', ha', c'', hc, rfl⟩ := h
      have ia := resolveCapAtom_avoids a Λ κt nv a' ha'
      have ih := resolveCap_avoids c Λ κt nv c'' hc
      refine ⟨fun hA => ?_, fun hF => ?_⟩
      · simp only [SCap.Avoids, Bool.and_eq_true] at hA
        simp [CaptureSet.noAny, ia.1 hA.1, ih.1 hA.2]
      · simp only [SCap.Avoids, Bool.and_eq_true] at hF
        simp [CaptureSet.noFresh, ia.2 hF.1, ih.2 hF.2]

mutual
/-- A resolved shape holds `any` or `fresh` only where the written one
does. -/
theorem resolveShape_avoids : ∀ (S : SShape) {s : Sig} (Λ : LabelTable) (κt : ClsTable)
    (nv : NameEnv s) (S' : Shape s), resolveShape Λ κt nv S = some S' →
    (SShape.Avoids .any S = true → S'.noAny = true) ∧
    (SShape.Avoids .fresh S = true → S'.noFresh = true)
  | .top, _, _, _, _, S', h => by
      simp only [resolveShape, Option.some.injEq] at h; subst h; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | .bot, _, _, _, _, S', h => by
      simp only [resolveShape, Option.some.injEq] at h; subst h; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | .typ A S T, _, Λ, κt, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨l, _, S₁, hS, T₁, hT, rfl⟩ := h
      have iS := resolveShape_avoids S Λ κt nv S₁ hS
      have iT := resolveShape_avoids T Λ κt nv T₁ hT
      refine ⟨fun ha => ?_, fun ha => ?_⟩ <;>
      · simp only [SShape.Avoids, Bool.and_eq_true] at ha
        simp [Shape.noAny, Shape.noFresh, iS.1, iS.2, iT.1, iT.2, ha.1, ha.2]
  | .fld a T, _, Λ, κt, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨l, _, T₁, hT, rfl⟩ := h
      have iT := resolveTy_avoids T Λ κt nv T₁ hT
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SShape.Avoids] at ha
        simp [Shape.noAny, iT.1 ha]
      · simp only [SShape.Avoids] at ha
        simp [Shape.noFresh, iT.2 ha]
  | .cap C lo hi, _, Λ, κt, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨l, _, lo', hlo, hi', hhi, rfl⟩ := h
      have ilo := resolveCap_avoids lo Λ κt nv lo' hlo
      have ihi := resolveCap_avoids hi Λ κt nv hi' hhi
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SShape.Avoids, Bool.and_eq_true] at ha
        simp [Shape.noAny, ilo.1 ha.1, ihi.1 ha.2]
      · simp only [SShape.Avoids, Bool.and_eq_true] at ha
        simp [Shape.noFresh, ilo.2 ha.1, ihi.2 ha.2]
  | .capk C K, _, Λ, κt, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨l, _, k, _, rfl⟩ := h
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  | .sel x A, _, Λ, κt, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨i, _, l, _, rfl⟩ := h
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  | .mu x S, _, Λ, κt, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨S₁, hS, rfl⟩ := h
      have iS := resolveShape_avoids S Λ κt (nv.cons x) S₁ hS
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SShape.Avoids] at ha
        simp [Shape.noAny, iS.1 ha]
      · simp only [SShape.Avoids] at ha
        simp [Shape.noFresh, iS.2 ha]
  | .all κ x T U, _, Λ, κt, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨T₁, hT, U₁, hU, rfl⟩ := h
      have iT := resolveTy_avoids T Λ κt _ T₁ hT
      have iU := resolveAns_avoids U Λ κt _ U₁ hU
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SShape.Avoids, Bool.and_eq_true] at ha
        simp [Shape.noAny, iT.1 ha.1, iU.1 ha.2]
      · simp only [SShape.Avoids, Bool.and_eq_true] at ha
        simp [Shape.noFresh, iT.2 ha.1, iU.2 ha.2]
  | .and S T, _, Λ, κt, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨S₁, hS, T₁, hT, rfl⟩ := h
      have iS := resolveShape_avoids S Λ κt nv S₁ hS
      have iT := resolveShape_avoids T Λ κt nv T₁ hT
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SShape.Avoids, Bool.and_eq_true] at ha
        simp [Shape.noAny, iS.1 ha.1, iT.1 ha.2]
      · simp only [SShape.Avoids, Bool.and_eq_true] at ha
        simp [Shape.noFresh, iS.2 ha.1, iT.2 ha.2]
  | .box T, _, Λ, κt, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨T₁, hT, rfl⟩ := h
      have iT := resolveTy_avoids T Λ κt nv T₁ hT
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SShape.Avoids] at ha
        simp [Shape.noAny, iT.1 ha]
      · simp only [SShape.Avoids] at ha
        simp [Shape.noFresh, iT.2 ha]
/-- A resolved type holds `any` or `fresh` only where the written one
does. -/
theorem resolveTy_avoids : ∀ (T : SType) {s : Sig} (Λ : LabelTable) (κt : ClsTable)
    (nv : NameEnv s) (T' : Ty s), resolveTy Λ κt nv T = some T' →
    (SType.Avoids .any T = true → T'.noAny = true) ∧
    (SType.Avoids .fresh T = true → T'.noFresh = true)
  | .capt S C, _, Λ, κt, nv, T', h => by
      simp only [resolveTy, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨S₁, hS, C₁, hC, rfl⟩ := h
      have iS := resolveShape_avoids S Λ κt nv S₁ hS
      have iC := resolveCap_avoids C Λ κt nv C₁ hC
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SType.Avoids, Bool.and_eq_true] at ha
        simp [Ty.noAny, iS.1 ha.1, iC.1 ha.2]
      · simp only [SType.Avoids, Bool.and_eq_true] at ha
        simp [Ty.noFresh, iS.2 ha.1, iC.2 ha.2]
/-- A resolved answer holds `any` or `fresh` only where the written one
does. -/
theorem resolveAns_avoids : ∀ (U : SAns) {s : Sig} (Λ : LabelTable) (κt : ClsTable)
    (nv : NameEnv s) (U' : ETy s), resolveAns Λ κt nv U = some U' →
    (SAns.Avoids .any U = true → U'.noAny = true) ∧
    (SAns.Avoids .fresh U = true → U'.noFresh = true)
  | .ty T, _, Λ, κt, nv, U', h => by
      simp only [resolveAns, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨T₁, hT, rfl⟩ := h
      have iT := resolveTy_avoids T Λ κt nv T₁ hT
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · simp only [SAns.Avoids] at ha
        simp [ETy.noAny, iT.1 ha]
      · simp only [SAns.Avoids] at ha
        simp [ETy.noFresh, iT.2 ha]
  | .ex κ C T, _, Λ, κt, nv, U', h => by
      simp only [resolveAns, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨C₁, hC, T₁, hT, rfl⟩ := h
      have iC := resolveCap_avoids C Λ κt nv C₁ hC
      have iT := resolveTy_avoids T Λ κt _ T₁ hT
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

/-- A lambda body, read under the three binders the resolver opens, keeps
the scoping the surface asks of it. -/
theorem Scoped_lamBody {s : Sig} (nv : NameEnv s) (κ : Option String) (x : String) (t : STm)
    (h : STm.Scoped (optCons κ nv.capNames) (x :: nv.names) t = true) :
    STm.Scoped (((nv.consC "%").consC (binderName κ)).cons x).capNames
      (((nv.consC "%").consC (binderName κ)).cons x).names t = true :=
  STm.Scoped_covers t ((Covers.binder _ κ).trans ((Covers.tail _ "%").cons _)) (Covers.rfl' _) h

/-- Object definitions, read under the class root and the self, keep the
scoping the surface asks of them. -/
theorem Scoped_objDefs {s : Sig} (nv : NameEnv s) (x : String) (d : SDefs)
    (h : SDefs.Scoped nv.capNames (x :: nv.names) d = true) :
    SDefs.Scoped ((nv.consC "%").cons x).capNames ((nv.consC "%").cons x).names d = true :=
  SDefs.Scoped_covers d (Covers.tail _ "%") (Covers.rfl' _) h

mutual
/-- **Totality of term resolution.**  A term whose names are in scope,
whose labels and classifier names are in their tables, and whose lambda
domains hold no `fresh` resolves. -/
theorem resolveTm_isSome : ∀ {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s)
    (e : STm), STm.Scoped nv.capNames nv.names e = true → STm.LabelsIn Λ e = true →
    STm.ClassifiersIn κt e = true → STm.FreshPlaced e = true →
    (resolveTm Λ κt nv e).isSome = true
  | _, Λ, κt, nv, .var x, hs, _, _, _ => by
      simp only [STm.Scoped] at hs
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (NameEnv.findVar?_isSome nv x hs)
      simp [resolveTm, hi]
  | _, Λ, κt, nv, .lam κ x T t, hs, hl, hc, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.ClassifiersIn, STm.FreshPlaced,
        Bool.and_eq_true] at hs hl hc hf
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp
        (resolveTy_isSome T Λ κt (nv.consC (binderName κ)) (Scoped_arrowDom nv κ T hs.1) hl.1
          hc.1)
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ κt _ t (Scoped_lamBody nv κ x t hs.2) hl.2 hc.2 hf.2)
      have hn := (resolveTy_avoids T Λ κt _ T' hT).2 hf.1
      simp [resolveTm, hT, ht, hn]
  | _, Λ, κt, nv, .obj x S d, hs, hl, hc, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.ClassifiersIn, STm.FreshPlaced,
        Bool.and_eq_true] at hs hl hc hf
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp
        (resolveShape_isSome S Λ κt (nv.cons x) hs.1 hl.1 hc.1)
      obtain ⟨d', hd⟩ := Option.isSome_iff_exists.mp
        (resolveDefs_isSome Λ κt _ d (Scoped_objDefs nv x d hs.2) hl.2 hc.2 hf)
      simp [resolveTm, hS, hd]
  | _, Λ, κt, nv, .app t u, hs, hl, hc, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.ClassifiersIn, STm.FreshPlaced,
        Bool.and_eq_true] at hs hl hc hf
      obtain ⟨t₀, ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ κt nv t hs.1 hl.1 hc.1 hf.1)
      obtain ⟨u₀, hu⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ κt (atomize nv t₀).names u
          (STm.Scoped_atomize nv t₀ u hs.2) hl.2 hc.2 hf.2)
      simp [resolveTm, ht, hu]
  | _, Λ, κt, nv, .proj t a, hs, hl, hc, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.ClassifiersIn, STm.FreshPlaced,
        Bool.and_eq_true] at hs hl hc hf
      obtain ⟨t₀, ht⟩ := Option.isSome_iff_exists.mp (resolveTm_isSome Λ κt nv t hs hl.1 hc hf)
      obtain ⟨l, hla⟩ := Option.isSome_iff_exists.mp hl.2
      simp [resolveTm, ht, hla]
  | _, Λ, κt, nv, .«let» x ann t u, hs, hl, hc, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.ClassifiersIn, STm.FreshPlaced,
        Bool.and_eq_true] at hs hl hc hf
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ κt nv t hs.1.2 hl.1.2 hc.1.2 hf.1)
      obtain ⟨u', hu⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ κt (nv.cons x) u hs.2 hl.2 hc.2 hf.2)
      cases ann with
      | none => simp [resolveTm, ht, hu]
      | some U =>
          obtain ⟨U', hU⟩ := Option.isSome_iff_exists.mp
            (resolveAns_isSome U Λ κt nv hs.1.1 hl.1.1 hc.1.1)
          simp [resolveTm, hU, ht, hu]
  | _, Λ, κt, nv, .letex κ x t u, hs, hl, hc, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.ClassifiersIn, STm.FreshPlaced,
        Bool.and_eq_true] at hs hl hc hf
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ κt nv t hs.1 hl.1 hc.1 hf.1)
      obtain ⟨u', hu⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ κt ((nv.consC κ).cons x) u hs.2 hl.2 hc.2 hf.2)
      simp [resolveTm, ht, hu]
  | _, Λ, κt, nv, .box t, hs, hl, hc, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.ClassifiersIn, STm.FreshPlaced] at hs hl hc hf
      obtain ⟨t₀, ht⟩ := Option.isSome_iff_exists.mp (resolveTm_isSome Λ κt nv t hs hl hc hf)
      simp [resolveTm, ht]
  | _, Λ, κt, nv, .unbox C t, hs, hl, hc, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.ClassifiersIn, STm.FreshPlaced,
        Bool.and_eq_true] at hs hl hc hf
      obtain ⟨t₀, ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ κt nv t hs.2 hl.2 hc.2 hf)
      obtain ⟨C', hC⟩ := Option.isSome_iff_exists.mp
        (resolveCap_isSome C Λ κt (atomize nv t₀).names (SCap.Scoped_atomize nv t₀ C hs.1) hl.1
          hc.1)
      simp [resolveTm, ht, hC]
  | _, Λ, κt, nv, .asc t T, hs, hl, hc, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.ClassifiersIn, STm.FreshPlaced,
        Bool.and_eq_true] at hs hl hc hf
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ κt nv t hs.1 hl.1 hc.1 hf)
      obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp
        (resolveTy_isSome T Λ κt nv hs.2 hl.2 hc.2)
      simp [resolveTm, ht, hT]
/-- Totality of definition resolution. -/
theorem resolveDefs_isSome : ∀ {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s)
    (d : SDefs), SDefs.Scoped nv.capNames nv.names d = true → SDefs.LabelsIn Λ d = true →
    SDefs.ClassifiersIn κt d = true → SDefs.FreshPlaced d = true →
    (resolveDefs Λ κt nv d).isSome = true
  | _, Λ, κt, nv, .typ A S, hs, hl, hc, _ => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, SDefs.ClassifiersIn, Bool.and_eq_true] at hs hl hc
      obtain ⟨l, hA⟩ := Option.isSome_iff_exists.mp hl.1
      obtain ⟨S', hS⟩ := Option.isSome_iff_exists.mp (resolveShape_isSome S Λ κt nv hs hl.2 hc)
      simp [resolveDefs, hA, hS]
  | _, Λ, κt, nv, .cap C c, hs, hl, hc, _ => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, SDefs.ClassifiersIn, Bool.and_eq_true] at hs hl hc
      obtain ⟨l, hC⟩ := Option.isSome_iff_exists.mp hl.1
      obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (resolveCap_isSome c Λ κt nv hs hl.2 hc)
      simp [resolveDefs, hC, hc']
  | _, Λ, κt, nv, .trm a t, hs, hl, hc, hf => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, SDefs.ClassifiersIn, SDefs.FreshPlaced,
        Bool.and_eq_true] at hs hl hc hf
      obtain ⟨l, hla⟩ := Option.isSome_iff_exists.mp hl.1
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp
        (resolveTm_isSome Λ κt nv t hs hl.2 hc hf)
      simp [resolveDefs, hla, ht]
  | _, Λ, κt, nv, .and d e, hs, hl, hc, hf => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, SDefs.ClassifiersIn, SDefs.FreshPlaced,
        Bool.and_eq_true] at hs hl hc hf
      obtain ⟨d', hd⟩ := Option.isSome_iff_exists.mp
        (resolveDefs_isSome Λ κt nv d hs.1 hl.1 hc.1 hf.1)
      obtain ⟨e', he⟩ := Option.isSome_iff_exists.mp
        (resolveDefs_isSome Λ κt nv e hs.2 hl.2 hc.2 hf.2)
      simp [resolveDefs, hd, he]
end

/-! ## No `any` of the resolver's own

The resolver keeps every `any` the program writes and adds none: the binders
it inserts and the bindings of the spine carry no annotation of their own.
So a program that writes no `any` resolves to a term with none. -/

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
theorem resolveTm_noAny : ∀ {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s)
    (e : STm) (a : ATm s), STm.Avoids .any e = true → resolveTm Λ κt nv e = some a →
    a.NoAnyAnn = true
  | _, Λ, κt, nv, .var x, a, _, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨i, _, rfl⟩ := h
      rfl
  | _, Λ, κt, nv, .lam κ x T t, a, ha, h => by
      simp only [STm.Avoids, Bool.and_eq_true] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨T', hT, t', ht, h⟩ := h
      by_cases hn : T'.noFresh = true
      · simp only [hn, if_true, Option.pure_def, Option.some.injEq] at h
        subst h
        simp [ATm.NoAnyAnn, (resolveTy_avoids T Λ κt _ T' hT).1 ha.1,
          resolveTm_noAny Λ κt _ t t' ha.2 ht]
      · simp [hn] at h
  | _, Λ, κt, nv, .obj x S d, a, ha, h => by
      simp only [STm.Avoids, Bool.and_eq_true] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨S', hS, d', hd, rfl⟩ := h
      simp [ATm.NoAnyAnn, (resolveShape_avoids S Λ κt _ S' hS).1 ha.1,
        resolveDefs_noAny Λ κt _ d d' ha.2 hd]
  | _, Λ, κt, nv, .app t u, a, ha, h => by
      simp only [STm.Avoids, Bool.and_eq_true] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t₀, ht, u₀, hu, rfl⟩ := h
      have it := resolveTm_noAny Λ κt nv t t₀ ha.1 ht
      have iu := resolveTm_noAny Λ κt _ u u₀ ha.2 hu
      exact Spine.plug_noAny _ _
        (Spine.append_noAny _ _ (atomize_noAny nv t₀ it) (atomize_noAny _ u₀ iu)) rfl
  | _, Λ, κt, nv, .proj t a', a, ha, h => by
      simp only [STm.Avoids] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t₀, ht, l, _, rfl⟩ := h
      exact Spine.plug_noAny _ _ (atomize_noAny nv t₀ (resolveTm_noAny Λ κt nv t t₀ ha ht)) rfl
  | _, Λ, κt, nv, .«let» x ann t u, a, ha, h => by
      simp only [STm.Avoids, Bool.and_eq_true] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ann', hann, t', ht, u', hu, rfl⟩ := h
      have it := resolveTm_noAny Λ κt nv t t' ha.1.2 ht
      have iu := resolveTm_noAny Λ κt (nv.cons x) u u' ha.2 hu
      cases ann with
      | none =>
          simp only [Option.some.injEq] at hann
          subst hann
          simp [ATm.NoAnyAnn, it, iu]
      | some U =>
          simp only [Option.map_eq_some_iff] at hann
          obtain ⟨U', hU, rfl⟩ := hann
          simp [ATm.NoAnyAnn, it, iu, (resolveAns_avoids U Λ κt nv U' hU).1 ha.1.1]
  | _, Λ, κt, nv, .letex κ x t u, a, ha, h => by
      simp only [STm.Avoids, Bool.and_eq_true] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, u', hu, rfl⟩ := h
      simp [ATm.NoAnyAnn, resolveTm_noAny Λ κt nv t t' ha.1 ht,
        resolveTm_noAny Λ κt _ u u' ha.2 hu]
  | _, Λ, κt, nv, .box t, a, ha, h => by
      simp only [STm.Avoids] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t₀, ht, rfl⟩ := h
      exact Spine.plug_noAny _ _ (atomize_noAny nv t₀ (resolveTm_noAny Λ κt nv t t₀ ha ht)) rfl
  | _, Λ, κt, nv, .unbox C t, a, ha, h => by
      simp only [STm.Avoids, Bool.and_eq_true] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t₀, ht, C', hC, rfl⟩ := h
      exact Spine.plug_noAny _ _
        (atomize_noAny nv t₀ (resolveTm_noAny Λ κt nv t t₀ ha.2 ht))
        (unboxSet_noAny C ((resolveCap_avoids C Λ κt _ C' hC).1 ha.1))
  | _, Λ, κt, nv, .asc t T, a, ha, h => by
      simp only [STm.Avoids, Bool.and_eq_true] at ha
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, T', hT, rfl⟩ := h
      simp [ATm.NoAnyAnn, resolveTm_noAny Λ κt nv t t' ha.1 ht,
        (resolveTy_avoids T Λ κt nv T' hT).1 ha.2]
/-- Resolved definitions hold `any` only where the written ones do. -/
theorem resolveDefs_noAny : ∀ {s : Sig} (Λ : LabelTable) (κt : ClsTable) (nv : NameEnv s)
    (d : SDefs) (a : ADefs s), SDefs.Avoids .any d = true → resolveDefs Λ κt nv d = some a →
    a.NoAnyAnn = true
  | _, Λ, κt, nv, .typ A S, a, ha, h => by
      simp only [SDefs.Avoids] at ha
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨l, _, S', hS, rfl⟩ := h
      exact (resolveShape_avoids S Λ κt nv S' hS).1 ha
  | _, Λ, κt, nv, .cap C c, a, ha, h => by
      simp only [SDefs.Avoids] at ha
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨l, _, c', hc, rfl⟩ := h
      exact (resolveCap_avoids c Λ κt nv c' hc).1 ha
  | _, Λ, κt, nv, .trm a' t, a, ha, h => by
      simp only [SDefs.Avoids] at ha
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨l, _, t', ht, rfl⟩ := h
      exact resolveTm_noAny Λ κt nv t t' ha ht
  | _, Λ, κt, nv, .and d e, a, ha, h => by
      simp only [SDefs.Avoids, Bool.and_eq_true] at ha
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨d', hd, e', he, rfl⟩ := h
      simp [ADefs.NoAnyAnn, resolveDefs_noAny Λ κt nv d d' ha.1 hd,
        resolveDefs_noAny Λ κt nv e e' ha.2 he]
end

/-- The resolver adds no `any` of its own: a program that writes none
resolves to a term with none in an annotation, a set or a type
definition. -/
theorem resolve_noAny {s : Sig} {Λ : LabelTable} {κt : ClsTable} {nv : NameEnv s} {e : STm}
    {a : ATm s} (he : STm.Avoids .any e = true) (h : resolveTm Λ κt nv e = some a) :
    ATm.NoAnyAnn a = true :=
  resolveTm_noAny Λ κt nv e a he h

/-! ## No projection under a projection

The version allows a projection to nest, since renaming never normalises
one.  The resolver never builds such a nesting: a projected atom goes
through `CapAtom.projBy`, which intersects with a projection already at the
top.  The statement is about every capture atom of a resolved term,
annotations, sets and type definitions included.  `ATm.AllAtoms p` says
that every capture atom of the term satisfies the test `p`, and
`resolveTm_allAtoms` gives it for any test that every resolved atom
passes. -/

/-- An atom holds at most one projection, at its top. -/
def atomProjDepthLe1 {s : Sig} (a : CapAtom s) : Bool :=
  match a with
  | .proj (.proj _ _) _ => false
  | _ => true

mutual
/-- Every capture atom of the shape passes the test. -/
def shapeAtomsAll (p : {s : Sig} → CapAtom s → Bool) {s : Sig} (S : Shape s) : Bool :=
  match S with
  | .top => true
  | .bot => true
  | .typ _ S T => shapeAtomsAll p S && shapeAtomsAll p T
  | .fld _ T => tyAtomsAll p T
  | .cap _ lo hi => lo.all (fun a => p a) && hi.all (fun a => p a)
  | .capk _ _ => true
  | .sel _ _ => true
  | .mu S => shapeAtomsAll p S
  | .all T U => tyAtomsAll p T && etyAtomsAll p U
  | .and S T => shapeAtomsAll p S && shapeAtomsAll p T
  | .box T => tyAtomsAll p T
termination_by structural S
/-- Every capture atom of the type passes the test. -/
def tyAtomsAll (p : {s : Sig} → CapAtom s → Bool) {s : Sig} (T : Ty s) : Bool :=
  match T with
  | .capt C S => C.all (fun a => p a) && shapeAtomsAll p S
termination_by structural T
/-- Every capture atom of the answer passes the test. -/
def etyAtomsAll (p : {s : Sig} → CapAtom s → Bool) {s : Sig} (E : ETy s) : Bool :=
  match E with
  | .ty T => tyAtomsAll p T
  | .ex C T => C.all (fun a => p a) && tyAtomsAll p T
termination_by structural E
end

mutual
/-- Every capture atom of an annotation, a set or a type definition of the
term passes the test. -/
def ATm.AllAtoms (p : {s : Sig} → CapAtom s → Bool) {s : Sig} (t : ATm s) : Bool :=
  match t with
  | .path _ => true
  | .lam T t => tyAtomsAll p T && ATm.AllAtoms p t
  | .obj S d => shapeAtomsAll p S && ADefs.AllAtoms p d
  | .app _ _ => true
  | .proj _ _ => true
  | .let ann t u =>
      (match ann with | none => true | some E => etyAtomsAll p E)
        && ATm.AllAtoms p t && ATm.AllAtoms p u
  | .letex t u => ATm.AllAtoms p t && ATm.AllAtoms p u
  | .box _ => true
  | .unbox C _ => (match C with | none => true | some C => C.all (fun a => p a))
  | .asc t T => ATm.AllAtoms p t && tyAtomsAll p T
termination_by structural t
/-- Every capture atom of the definitions passes the test. -/
def ADefs.AllAtoms (p : {s : Sig} → CapAtom s → Bool) {s : Sig} (d : ADefs s) : Bool :=
  match d with
  | .typ _ S => shapeAtomsAll p S
  | .cap _ c => c.all (fun a => p a)
  | .trm _ t => ATm.AllAtoms p t
  | .and d e => ADefs.AllAtoms p d && ADefs.AllAtoms p e
termination_by structural d
end

/-- No capture atom of the term holds a projection under a projection. -/
def ATm.ProjDepthLe1 {s : Sig} (t : ATm s) : Bool := ATm.AllAtoms atomProjDepthLe1 t

/-- Every capture atom of the bindings of a spine passes the test. -/
def Spine.AllAtoms (p : {s : Sig} → CapAtom s → Bool) {s s' : Sig} (sp : Spine s s') : Bool :=
  match sp with
  | .nil => true
  | .cons t sp => ATm.AllAtoms p t && Spine.AllAtoms p sp
termination_by structural sp

/-- Plugging keeps every atom passing the test. -/
theorem Spine.plug_allAtoms (p : {s : Sig} → CapAtom s → Bool) : ∀ {s s' : Sig}
    (sp : Spine s s') (u : ATm s'), Spine.AllAtoms p sp = true → ATm.AllAtoms p u = true →
    ATm.AllAtoms p (sp.plug u) = true
  | _, _, .nil, _, _, hu => hu
  | _, _, .cons t sp, u, hsp, hu => by
      simp only [Spine.AllAtoms, Bool.and_eq_true] at hsp
      simp [Spine.plug, ATm.AllAtoms, hsp.1, Spine.plug_allAtoms p sp u hsp.2 hu]

/-- Appending keeps every atom of the bindings passing the test. -/
theorem Spine.append_allAtoms (p : {s : Sig} → CapAtom s → Bool) : ∀ {s s' s'' : Sig}
    (sp : Spine s s') (sp' : Spine s' s''), Spine.AllAtoms p sp = true →
    Spine.AllAtoms p sp' = true → Spine.AllAtoms p (sp.append sp') = true
  | _, _, _, .nil, _, _, h' => h'
  | _, _, _, .cons t sp, sp', h, h' => by
      simp only [Spine.AllAtoms, Bool.and_eq_true] at h
      simp [Spine.append, Spine.AllAtoms, h.1, Spine.append_allAtoms p sp sp' h.2 h']

/-- The binding `atomize` inserts is the term it was given. -/
theorem atomize_allAtoms (p : {s : Sig} → CapAtom s → Bool) {s : Sig} (nv : NameEnv s)
    (t : ATm s) (h : ATm.AllAtoms p t = true) : Spine.AllAtoms p (atomize nv t).spine = true := by
  cases t with
  | path q => cases q with | var _ => rfl
  | _ => simpa [atomize, Spine.AllAtoms] using h

section AllAtoms
variable (p : {s : Sig} → CapAtom s → Bool) (Λ : LabelTable) (κt : ClsTable)
  (hp : ∀ {s : Sig} (nv : NameEnv s) (a : SAtom) (a' : CapAtom s),
    resolveCapAtom Λ κt nv a = some a' → p a' = true)
include hp

/-- Every atom of a resolved capture set is a resolved atom. -/
theorem resolveCap_allAtoms : ∀ (c : SCap) {s : Sig} (nv : NameEnv s) (c' : CaptureSet s),
    resolveCap Λ κt nv c = some c' → c'.all (fun a => p a) = true
  | [], _, _, c', h => by
      simp [resolveCap] at h; subst h; rfl
  | a :: c, _, nv, c', h => by
      simp only [resolveCap, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨a', ha', c'', hc, rfl⟩ := h
      simp [hp nv a a' ha', resolveCap_allAtoms c nv c'' hc]

mutual
/-- Every atom of a resolved shape is a resolved atom. -/
theorem resolveShape_allAtoms : ∀ (S : SShape) {s : Sig} (nv : NameEnv s) (S' : Shape s),
    resolveShape Λ κt nv S = some S' → shapeAtomsAll p S' = true
  | .top, _, _, S', h => by
      simp only [resolveShape, Option.some.injEq] at h; subst h; rfl
  | .bot, _, _, S', h => by
      simp only [resolveShape, Option.some.injEq] at h; subst h; rfl
  | .typ A S T, _, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨l, _, S₁, hS, T₁, hT, rfl⟩ := h
      simp [shapeAtomsAll, resolveShape_allAtoms S nv S₁ hS, resolveShape_allAtoms T nv T₁ hT]
  | .fld a T, _, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨l, _, T₁, hT, rfl⟩ := h
      simp [shapeAtomsAll, resolveTy_allAtoms T nv T₁ hT]
  | .cap C lo hi, _, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨l, _, lo', hlo, hi', hhi, rfl⟩ := h
      simp only [shapeAtomsAll, resolveCap_allAtoms p Λ κt hp lo nv lo' hlo,
        resolveCap_allAtoms p Λ κt hp hi nv hi' hhi, Bool.and_self]
  | .capk C K, _, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨l, _, k, _, rfl⟩ := h
      rfl
  | .sel x A, _, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨i, _, l, _, rfl⟩ := h
      rfl
  | .mu x S, _, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨S₁, hS, rfl⟩ := h
      simp [shapeAtomsAll, resolveShape_allAtoms S _ S₁ hS]
  | .all κ x T U, _, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨T₁, hT, U₁, hU, rfl⟩ := h
      simp [shapeAtomsAll, resolveTy_allAtoms T _ T₁ hT, resolveAns_allAtoms U _ U₁ hU]
  | .and S T, _, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨S₁, hS, T₁, hT, rfl⟩ := h
      simp [shapeAtomsAll, resolveShape_allAtoms S nv S₁ hS, resolveShape_allAtoms T nv T₁ hT]
  | .box T, _, nv, S', h => by
      simp only [resolveShape, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨T₁, hT, rfl⟩ := h
      simp [shapeAtomsAll, resolveTy_allAtoms T nv T₁ hT]
/-- Every atom of a resolved type is a resolved atom. -/
theorem resolveTy_allAtoms : ∀ (T : SType) {s : Sig} (nv : NameEnv s) (T' : Ty s),
    resolveTy Λ κt nv T = some T' → tyAtomsAll p T' = true
  | .capt S C, _, nv, T', h => by
      simp only [resolveTy, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨S₁, hS, C₁, hC, rfl⟩ := h
      simp only [tyAtomsAll, resolveCap_allAtoms p Λ κt hp C nv C₁ hC,
        resolveShape_allAtoms S nv S₁ hS, Bool.and_self]
/-- Every atom of a resolved answer is a resolved atom. -/
theorem resolveAns_allAtoms : ∀ (U : SAns) {s : Sig} (nv : NameEnv s) (U' : ETy s),
    resolveAns Λ κt nv U = some U' → etyAtomsAll p U' = true
  | .ty T, _, nv, U', h => by
      simp only [resolveAns, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨T₁, hT, rfl⟩ := h
      simp [etyAtomsAll, resolveTy_allAtoms T nv T₁ hT]
  | .ex κ C T, _, nv, U', h => by
      simp only [resolveAns, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨C₁, hC, T₁, hT, rfl⟩ := h
      simp only [etyAtomsAll, resolveCap_allAtoms p Λ κt hp C nv C₁ hC,
        resolveTy_allAtoms T _ T₁ hT, Bool.and_self]
end

mutual
/-- Every atom of a resolved term is a resolved atom. -/
theorem resolveTm_allAtoms : ∀ {s : Sig} (nv : NameEnv s) (e : STm) (a : ATm s),
    resolveTm Λ κt nv e = some a → ATm.AllAtoms p a = true
  | _, nv, .var x, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨i, _, rfl⟩ := h
      rfl
  | _, nv, .lam κ x T t, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨T', hT, t', ht, h⟩ := h
      by_cases hn : T'.noFresh = true
      · simp only [hn, if_true, Option.pure_def, Option.some.injEq] at h
        subst h
        simp [ATm.AllAtoms, resolveTy_allAtoms p Λ κt hp T _ T' hT,
          resolveTm_allAtoms _ t t' ht]
      · simp [hn] at h
  | _, nv, .obj x S d, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨S', hS, d', hd, rfl⟩ := h
      simp [ATm.AllAtoms, resolveShape_allAtoms p Λ κt hp S _ S' hS,
        resolveDefs_allAtoms _ d d' hd]
  | _, nv, .app t u, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t₀, ht, u₀, hu, rfl⟩ := h
      exact Spine.plug_allAtoms p _ _
        (Spine.append_allAtoms p _ _ (atomize_allAtoms p nv t₀ (resolveTm_allAtoms nv t t₀ ht))
          (atomize_allAtoms p _ u₀ (resolveTm_allAtoms _ u u₀ hu))) rfl
  | _, nv, .proj t a', a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t₀, ht, l, _, rfl⟩ := h
      exact Spine.plug_allAtoms p _ _
        (atomize_allAtoms p nv t₀ (resolveTm_allAtoms nv t t₀ ht)) rfl
  | _, nv, .«let» x ann t u, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ann', hann, t', ht, u', hu, rfl⟩ := h
      have it := resolveTm_allAtoms nv t t' ht
      have iu := resolveTm_allAtoms (nv.cons x) u u' hu
      cases ann with
      | none =>
          simp only [Option.some.injEq] at hann
          subst hann
          simp [ATm.AllAtoms, it, iu]
      | some U =>
          simp only [Option.map_eq_some_iff] at hann
          obtain ⟨U', hU, rfl⟩ := hann
          simp [ATm.AllAtoms, it, iu, resolveAns_allAtoms p Λ κt hp U nv U' hU]
  | _, nv, .letex κ x t u, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, u', hu, rfl⟩ := h
      simp [ATm.AllAtoms, resolveTm_allAtoms nv t t' ht, resolveTm_allAtoms _ u u' hu]
  | _, nv, .box t, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t₀, ht, rfl⟩ := h
      exact Spine.plug_allAtoms p _ _
        (atomize_allAtoms p nv t₀ (resolveTm_allAtoms nv t t₀ ht)) rfl
  | _, nv, .unbox C t, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t₀, ht, C', hC, rfl⟩ := h
      refine Spine.plug_allAtoms p _ _
        (atomize_allAtoms p nv t₀ (resolveTm_allAtoms nv t t₀ ht)) ?_
      have hC' := resolveCap_allAtoms p Λ κt hp C _ C' hC
      cases C <;> simp [unboxSet, ATm.AllAtoms, hC']
  | _, nv, .asc t T, a, h => by
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, T', hT, rfl⟩ := h
      simp [ATm.AllAtoms, resolveTm_allAtoms nv t t' ht, resolveTy_allAtoms p Λ κt hp T nv T' hT]
/-- Every atom of resolved definitions is a resolved atom. -/
theorem resolveDefs_allAtoms : ∀ {s : Sig} (nv : NameEnv s) (d : SDefs) (a : ADefs s),
    resolveDefs Λ κt nv d = some a → ADefs.AllAtoms p a = true
  | _, nv, .typ A S, a, h => by
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨l, _, S', hS, rfl⟩ := h
      simp [ADefs.AllAtoms, resolveShape_allAtoms p Λ κt hp S nv S' hS]
  | _, nv, .cap C c, a, h => by
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨l, _, c', hc, rfl⟩ := h
      simp only [ADefs.AllAtoms, resolveCap_allAtoms p Λ κt hp c nv c' hc]
  | _, nv, .trm a' t, a, h => by
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨l, _, t', ht, rfl⟩ := h
      simp [ADefs.AllAtoms, resolveTm_allAtoms nv t t' ht]
  | _, nv, .and d e, a, h => by
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨d', hd, e', he, rfl⟩ := h
      simp [ADefs.AllAtoms, resolveDefs_allAtoms nv d d' hd, resolveDefs_allAtoms nv e e' he]
end

end AllAtoms

/-- The smart projection of an atom with at most one projection has at
most one projection. -/
theorem atomProjDepthLe1_projBy {s : Sig} (φ : Cls.Kind) (a : CapAtom s)
    (h : atomProjDepthLe1 a = true) : atomProjDepthLe1 (CapAtom.projBy φ a) = true := by
  cases a with
  | proj b ψ =>
      cases b with
      | proj _ _ => simp [atomProjDepthLe1] at h
      | _ => rfl
  | _ => rfl

/-- A resolved atom holds at most one projection. -/
theorem resolveCapAtom_projDepthLe1 : ∀ (a : SAtom) {s : Sig} (Λ : LabelTable) (κt : ClsTable)
    (nv : NameEnv s) (a' : CapAtom s), resolveCapAtom Λ κt nv a = some a' →
    atomProjDepthLe1 a' = true
  | .name x, _, _, _, nv, a', h => by
      cases hf : nv.find? x with
      | none => simp [resolveCapAtom, hf] at h
      | some q =>
          obtain ⟨k, i⟩ := q
          cases k <;> simp [resolveCapAtom, hf] at h <;> subst h <;> rfl
  | .sel x C, _, _, _, _, a', h => by
      simp only [resolveCapAtom, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨i, _, l, _, rfl⟩ := h
      rfl
  | .any, _, _, _, _, a', h => by
      simp only [resolveCapAtom, Option.some.injEq] at h
      subst h
      rfl
  | .fresh, _, _, _, _, a', h => by
      simp only [resolveCapAtom, Option.some.injEq] at h
      subst h
      rfl
  | .proj a K, _, Λ, κt, nv, a', h => by
      simp only [resolveCapAtom, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨b, hb, k, _, rfl⟩ := h
      exact atomProjDepthLe1_projBy k b (resolveCapAtom_projDepthLe1 a Λ κt nv b hb)

/-- **No nested projection.**  No capture atom of a resolved term, in an
annotation, a set or a type definition, holds a projection under a
projection. -/
theorem resolve_noNestedProj {s : Sig} {Λ : LabelTable} {κt : ClsTable} {nv : NameEnv s}
    {e : STm} {a : ATm s} (h : resolveTm Λ κt nv e = some a) : ATm.ProjDepthLe1 a = true :=
  resolveTm_allAtoms atomProjDepthLe1 Λ κt
    (fun nv a a' h => resolveCapAtom_projDepthLe1 a Λ κt nv a' h) nv e a h

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

The programs of `Notation.lean` are resolved with the labels of the
version's examples and compared with hand-written annotated terms, or with
the version's own types and terms, by `decide`.  Resolution is structural,
so the kernel reduces it.  The atoms `any` and `fresh` come out as
`CapAtom.any` and `CapAtom.fresh`, where the program wrote them. -/

open Classifiers.DotMNF.Examples (k1 k2 platSet fileS unitTy unitTm arrowS lread lC
  W2TyAny W2Ty Z1TyF Z1Ty S1TyAny)

/-- The labels of the version's examples (`DotMNF/Examples.lean`): the type
labels `A`, `B`, `T` and the capture member `C`, and the term labels. -/
def Λc : LabelTable :=
  [("A", .typ 0), ("B", .typ 1), ("T", .typ 2), ("C", .typ 3),
   ("a", .trm 0), ("b", .trm 1), ("v", .trm 2), ("elem", .trm 3), ("run", .trm 4),
   ("e1", .trm 5), ("e2", .trm 6), ("read", .trm 7), ("next", .trm 8)]

/-- The platform `k1, k2`, the version's `κ₁` and `κ₂`. -/
def πc : PlatformNames := PlatformNames.ofList ["k1", "k2"]

/-- The platform `fs, k2`: the file system is the version's `κ₁`, the one
its `Z1` and `S1` examples name. -/
def πz : PlatformNames := PlatformNames.ofList ["fs", "k2"]

/-- The platform set is the version's `platSet`. -/
example : πc.set = platSet := by decide

/-! ### The written types keep `any` and `fresh` -/

/-- `process` of W2 resolves to the version's `W2TyAny`, its parameter `any`
kept as the atom. -/
example : resolveTy Λc [] πc.names W2src = some W2TyAny := by decide

/-- The version reads that `any` as the arrow's own binder, at every reading
of the enclosing scope (`W2_expand`). -/
example : (resolveTy Λc [] πc.names W2src).map (·.expand platSet) = some W2Ty := by decide

/-- `freshCell` of Z1 resolves to the version's `Z1TyF`, its result
`fresh` kept as the atom. -/
example : resolveTy Λc [] πz.names Z1src = some (Z1TyF k1) := by decide

/-- The version reads that `fresh` as an existential (`Z1_expandFresh`). -/
example : (resolveTy Λc [] πz.names Z1src).map Ty.expandFresh = some (Z1Ty k1) := by decide

/-- `withFile` of S1 resolves to the version's `S1TyAny`: the capture
member's bound, the member selection `cp.C` and the result `any` at their
places. -/
example : resolveTy Λc [] πz.names S1src = some (S1TyAny k1) := by decide

/-! ### Lambdas: the inserted binders, `any` and `fresh` in a domain -/

/-- `any` in a lambda domain is kept.  The version reads it as the arrow's
own binder. -/
example :
    resolveTop Λc [] πc (cls% λ(x : ⊤ ^ {any}). x) =
      some (.lam (.capt [CapAtom.any] .top) (.path (.var .here))) := by decide

/-- `fresh` in a lambda domain does not resolve: the version keeps `fresh`
out of every parameter type. -/
example : (resolveTop Λc [] πc (cls% λ(x : ⊤ ^ {fresh}). x)).isNone = true := by decide

/-- Nor does `fresh` deeper in a domain. -/
example :
    (resolveTop Λc [] πc (cls% λ(h : (∀(u : ⊤) ⊤ ^ {fresh}) ^ {k1}). h)).isNone = true := by
  decide

/-- A named arrow binder is the domain's `.here` and, in the body, sits
between the body root and the parameter. -/
example :
    resolveTop Λc [] πc (cls% λ[c](x : ⊤ ^ {c}). let y : ⊤ ^ {c} = x in y) =
      some (.lam (.capt [CapAtom.cvar .here] .top)
        (.let (some (.ty (.capt [CapAtom.cvar (.there .here)] .top)))
          (.path (.var .here)) (.path (.var .here)))) := by decide

/-- An anonymous arrow binder has no name the program can write. -/
example : (resolveTop Λc [] πc (cls% λ(x : ⊤ ^ {c}). x)).isNone = true := by decide

/-- A platform capability, read in a domain and in a body: past the arrow
binder in the first, past the body root, the arrow binder and the
parameter in the second. -/
example :
    resolveTop Λc [] πc (cls% λ(x : ⊤ ^ {k1}). let y : ⊤ ^ {k1} = x in y) =
      some (.lam (.capt [CapAtom.cvar (.there k1)] .top)
        (.let (some (.ty (.capt [CapAtom.cvar (.there (.there (.there k1)))] .top)))
          (.path (.var .here)) (.path (.var .here)))) := by decide

/-! ### Objects: the class root -/

/-- The self shape is read under the self alone, the definitions under the
class root and the self, so the outer `y` is one step out in the shape and
two in the definitions. -/
example :
    resolveTop Λc [] πc
        (cls% λ(y : ⊤). ν(z : {a : ⊤} ∧ {C^ : {}..{y}}. {a = y} ∧ {C^ = {y}})) =
      some (.lam unitTy
        (.obj (.and (.fld (.trm 0) unitTy) (.cap lC [] [CapAtom.var (.there .here)]))
          (.and (.trm (.trm 0) (.path (.var (.there (.there .here)))))
            (.cap lC [CapAtom.var (.there (.there .here))])))) := by decide

/-! ### Answers, unpacking and unboxing -/

/-- An existential `let` annotation: its binder over the type, its bound
read outside. -/
example :
    resolveTop Λc [] πc (cls% λ(u : ⊤). let r : ∃[w ⊑ {u}] ⊤ ^ {w} = u in r) =
      some (.lam unitTy
        (.let (some (.ex [CapAtom.var .here] (.capt [CapAtom.cvar .here] .top)))
          (.path (.var .here)) (.path (.var .here)))) := by decide

/-- A written unpacking opens the witness binder, then the payload. -/
example :
    resolveTop Λc [] πc (cls% λ(fc : ⊤). let ⟨k, c⟩ = fc in {k} ⊸ c) =
      some (.lam unitTy
        (.letex (.path (.var .here)) (.unbox (some [CapAtom.cvar (.there .here)]) .here))) := by
  decide

/-- An unboxing written with the empty set leaves its set to the typer. -/
example :
    resolveTop Λc [] πc (cls% λ(e : □(⊤ ^ {k1})). {} ⊸ e) =
      some (.lam (.capt [] (.box (.capt [CapAtom.cvar (.there k1)] .top)))
        (.unbox none .here)) := by decide

/-! ### Let insertion

`λ(f : ⊤). λ(g : ⊤). f (g f)`.  The operand `g f` is not a variable, so
`atomize` binds it.  Between `f` and `g` sit the inner lambda's body root
and arrow binder. -/

/-- The let expanded form of the nested application. -/
def nestedAppAnn : ATm πc.sig :=
  .lam unitTy (.lam unitTy
    (.let none (.app .here (.there (.there (.there .here))))
      (.app (.there (.there (.there (.there .here)))) .here)))

example : resolveTop Λc [] πc (cls% λ(f : ⊤). λ(g : ⊤). f (g f)) = some nestedAppAnn := by decide

/-- Its skeleton is that of the two lambdas around the application, the
inserted binding counted as one `let`. -/
example :
    nestedAppAnn.skel = .lam (.lam (.let (.app 0 1) (.app 2 0))) := by decide

/-! ### W2, the call of a capture-parameter arrow

`p f` under `p : process, f : File ^ {κ₁}`, the context `W2CallCtx` of the
version. -/

example :
    (resolveIn Λc [] ((πc.names.cons "p").cons "f") (cls% p f)).map ATm.erase =
      some (Tm.app (.there .here) .here) := by decide

/-! ### A capture parameter that is called

`P1src` names `unit`, a term variable bound around it here.  Its domain keeps
the written `any`.  Erased and read by the version's `Tm.expand`, the domain
is `(∀(u : ⊤) ⊤) ^ {κ}`, with `κ` the arrow's own binder. -/

/-- The term `P1src` resolves to, under `unit`. -/
def P1ann : ATm (πc.sig,x) :=
  .lam (.capt [CapAtom.any] arrowS)
    (.let none (.path (.var (.there (.there (.there .here)))))
      (.app (.there .here) .here))

example : resolveIn Λc [] (πc.names.cons "unit") P1src = some P1ann := by decide

example :
    (resolveIn Λc [] (πc.names.cons "unit") P1src).map (fun a => a.erase.expand) =
      some (Tm.val (.lam (.capt [CapAtom.cvar .here] arrowS)
        (.let (.path (.var (.there (.there (.there .here))))) (.app (.there .here) .here)))) := by
  decide

/-! ### The escape

`EscSrc` resolves.  Its `let` keeps the written answer with every `any` in
place, for the typer to read at the scope it opens. -/

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

example : resolveTop Λc [] πc EscSrc = some EscAnn := by decide

/-- The totality theorem applies to the escape on the three decided side
conditions. -/
example : (resolveTop Λc [] πc EscSrc).isSome = true :=
  resolveTm_isSome Λc [] πc.names EscSrc (by decide) (by decide) (by decide) (by decide)

/-! ### Z1, the caller of `freshCell`, and two calls in a row

The version types the caller's body at `Z1Ctx`, the platform with
`fc : freshCell` and `un : ⊤` on top (`Z1_caller`).  It is resolved there,
through `resolveIn`, and so is `let c1 = fc un in fc un`, whose answer is the
second call's existential.  The resolver inserts a plain `let`.  The typer
makes it a `letex`, whose body is the `let`'s body renamed past the witness
binder.  That unpacking erases to the term the version types, and its
skeleton is the `let`'s. -/

/-- The names of `Z1Ctx`. -/
def z1Names : NameEnv (πz.sig,x,x) := (πz.names.cons "fc").cons "un"

/-- `λ(v : ⊤). v` under a scope. -/
private def idAnn {s : Sig} : ATm s := .lam unitTy (.path (.var .here))

/-- The caller's body, as resolved. -/
def Z1callerAnn : ATm (πz.sig,x,x) :=
  .let none (.app (.there .here) .here) (.let none (.path (.var .here)) idAnn)

example :
    resolveIn Λc [] z1Names (cls% let c = fc un in let w = c in λ(v : ⊤). v) = some Z1callerAnn := by
  decide

/-- The unpacking the typer makes of a `let`. -/
def letexOf {s : Sig} : ATm s → Option (ATm s)
  | .let _ t u => some (.letex t (u.rename (Rename.succ (k := .cap)).lift))
  | _ => none

/-- The unpacking erases to the term of the version's `Z1_caller`. -/
example :
    (letexOf Z1callerAnn).map ATm.erase =
      some (Tm.letex (.app (.there .here) .here) (.let (.path (.var .here)) unitTm)) := by decide

/-- And it has the skeleton of the `let`, by `ATm.skel_rename_succLift`. -/
example : (letexOf Z1callerAnn).map ATm.skel = some Z1callerAnn.skel :=
  congrArg some (ATm.skel_letex_of_let _ _ _)

/-- `let c1 = fc un in fc un`, as resolved. -/
def Z1TailAnn : ATm (πz.sig,x,x) :=
  .let none (.app (.there .here) .here) (.app (.there (.there .here)) (.there .here))

example : resolveIn Λc [] z1Names Z1TailSrc = some Z1TailAnn := by decide

/-- Its unpacking erases to `letex ⟨c, c1⟩ = fc un in fc un`, the second
call under the witness and the payload binders. -/
example :
    (letexOf Z1TailAnn).map ATm.erase =
      some (Tm.letex (.app (.there .here) .here)
        (.app (.there (.there (.there .here))) (.there (.there .here)))) := by decide

example : (letexOf Z1TailAnn).map ATm.skel = some Z1TailAnn.skel := by decide

/-! ### The caller as a closed program

`Z1callerSrc` binds `fc` by a lambda whose domain writes `fresh`, so it does
not resolve.  Written with the domain the version gives `fc`, the
existential that `fresh` reads as, it does. -/

example : (resolveProg Λc Z1callerSrc).isNone = true := by decide

/-- The caller over the platform `fs, k2`, `fc`'s domain written as the
version's `Z1Ty`. -/
def Z1callerExSrc : SProg :=
  clsProg% platform [fs, k2]
    λ(fc : (∀(u : ⊤) ∃[c ⊑ {fs, u}] μ(f. {read : (∀(v : ⊤) ⊤) ^ {f}}) ^ {c}) ^ {fs}).
      λ(un : ⊤). let c = fc un in let w = c in λ(v : ⊤). v

/-- Its domain is `Z1Ty` past the arrow binder, and its inner body is the
caller's body under the two lambdas: `fc` three binders out of `un`. -/
example :
    (resolveProg Λc Z1callerExSrc).map (·.body) =
      some (.lam (Z1Ty (.there k1))
        (.lam unitTy
          (.let none (.app (.there (.there (.there .here))) .here)
            (.let none (.path (.var .here)) idAnn)))) := by decide

/-! ### No `any` of the resolver's own -/

/-- A program that writes no `any` resolves to a term with none. -/
example : ∀ a, resolveTop Λc [] πc (cls% λ(f : ⊤). λ(g : ⊤). f (g f)) = some a →
    a.NoAnyAnn = true :=
  fun _ h => resolve_noAny (by decide) h

/-! ## Totality of program resolution -/

/-- **Totality of program resolution.**  A program resolves when its
declarations give a table, and its platform, declared use set, declared kind
and body meet the side conditions against that table: classifier names in
the table, the use set and the body scoped over the platform and
labelled, and no `fresh` in a lambda domain. -/
theorem resolveProg_isSome (Λ : LabelTable) (p : SProg) {κt : ClsTable}
    (hκ : clsTableOf [] p.classifiers = some κt)
    (hP : SPlatform.ClassifiersIn κt p.platform = true)
    (hu : ∀ C, p.uses = some C →
      SCap.Scoped p.platNames.names.capNames p.platNames.names.names C = true ∧
        SCap.LabelsIn Λ C = true ∧ SCap.ClassifiersIn κt C = true)
    (hk : ∀ K, p.kind = some K → SKind.ClassifiersIn κt K = true)
    (hs : STm.Scoped p.platNames.names.capNames p.platNames.names.names p.body = true)
    (hl : STm.LabelsIn Λ p.body = true) (hc : STm.ClassifiersIn κt p.body = true)
    (hf : STm.FreshPlaced p.body = true) :
    (resolveProg Λ p).isSome = true := by
  obtain ⟨P, hPl⟩ := Option.isSome_iff_exists.mp (resolvePlatform_isSome κt p.platform hP)
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
    (resolveTm_isSome Λ κt p.platNames.names p.body hs hl hc hf)
  have hu' : ∃ u, (match p.uses with
      | none => some none
      | some C => (resolveCap Λ κt p.platNames.names C).map some) = some u := by
    cases hU : p.uses with
    | none => exact ⟨none, rfl⟩
    | some C =>
        obtain ⟨h1, h2, h3⟩ := hu C hU
        obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.mp
          (resolveCap_isSome C Λ κt p.platNames.names h1 h2 h3)
        exact ⟨some c, by simp [hc']⟩
  have hk' : ∃ k, (match p.kind with
      | none => some none
      | some K => (resolveKind κt K).map some) = some k := by
    cases hK : p.kind with
    | none => exact ⟨none, rfl⟩
    | some K =>
        obtain ⟨k, hk''⟩ := Option.isSome_iff_exists.mp (resolveKind_isSome κt K (hk K hK))
        exact ⟨some k, by simp [hk'']⟩
  obtain ⟨u, hu''⟩ := hu'
  obtain ⟨k, hk''⟩ := hk'
  simp only [resolveProg, hκ, hPl, hu'', hk'', resolveTop, hb, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.isSome_some]

/-! ## The classifier examples

CE1 to CE3 of `Notation.lean` against the version's E1 to E3
(`lean/Coercions/Classifiers/DotMNF/Examples.lean`).  The three programs
declare the same classifiers, and declaration order gives the version's
own `Cls.IO`, `Cls.ThreadLocal` and `Cls.Control`.  Every comparison is by
`decide`, except those with the version's `Platform`.  It has no decidable
equality, so those are by `rfl`. -/

open Classifiers.DotMNF.Examples (lbody E1Plat E1ctl E1io E1Filt E1Cod E1TryTy E1tm
  E2PlatIO E2Filt E2TyAny E2tm E3Plat E3k1 E3k2 E3AbsTy E3ClientTy E3Uses E3tm)

/-- The classifier declarations of CE1 to CE3, `IO, ThreadLocal, Control
extends ThreadLocal`. -/
def exClsDecls : SClsDecls := [("IO", none), ("ThreadLocal", none), ("Control", some "ThreadLocal")]

example : CE1src.classifiers = exClsDecls := by decide
example : CE2src.classifiers = exClsDecls := by decide
example : CE3src.classifiers = exClsDecls := by decide

/-- **The table of the examples.**  `IO` and `ThreadLocal` are the first two
children of the root, `Control` the first child of `ThreadLocal`, exactly
the version's classifiers. -/
theorem clsTableOf_examples :
    clsTableOf [] exClsDecls =
      some [("IO", Cls.IO), ("ThreadLocal", Cls.ThreadLocal), ("Control", Cls.Control)] := by
  decide

/-- The table of the examples. -/
def exCls : ClsTable := [("IO", Cls.IO), ("ThreadLocal", Cls.ThreadLocal), ("Control", Cls.Control)]

/-- A parent declared after its child gives no table. -/
example : clsTableOf [] [("Control", some "ThreadLocal"), ("ThreadLocal", none)] = none := by
  decide

/-- The labels of the classifier examples: those of `Λc`, and `body`, the
field of E1's and E2's objects. -/
def Λk : LabelTable := Λc ++ [("body", lbody)]

/-! ### Kinds -/

/-- `except[]` excludes nothing, so it is `Cls.Kind.top`, the kind of every
classifier. -/
example : resolveKind exCls (clsKind% except[]) = some Cls.Kind.top := by decide

/-- `only[]` is the empty kind. -/
example : resolveKind exCls (clsKind% only[]) = some Cls.Kind.empty := by decide

example : resolveKind exCls (clsKind% only[Control]) = some (Cls.only Cls.Control) := by decide

example : resolveKind exCls (clsKind% except[ThreadLocal]) = some (Cls.except Cls.ThreadLocal) := by
  decide

/-- `∪` is the version's union. -/
example :
    resolveKind exCls (clsKind% only[IO] ∪ only[Control]) =
      some (Cls.only Cls.IO ++ Cls.only Cls.Control) := by decide

/-- `∩` writes a holed subtree, which neither `only` nor `except` writes
alone. -/
example :
    resolveKind exCls (clsKind% only[ThreadLocal] ∩ except[Control]) =
      some [⟨Cls.ThreadLocal, [Cls.Control]⟩] := by decide

/-- A kind naming an undeclared classifier does not resolve. -/
example : resolveKind exCls (clsKind% only[Undeclared]) = none := by decide

/-- The totality theorem on a kind with two names. -/
example : (resolveKind exCls (clsKind% only[IO, Control])).isSome = true :=
  resolveKind_isSome exCls _ (by decide)

/-! ### Platforms -/

/-- **CE1's platform is `E1Plat`**: `ctl` at `Control`, `io` at `IO`. -/
example : resolvePlatform exCls CE1src.platform = some E1Plat := rfl

/-- CE2's platform is `E2PlatIO`. -/
example : resolvePlatform exCls CE2src.platform = some E2PlatIO := rfl

/-- CE3's platform is `E3Plat`, two binders at `Control`. -/
example : resolvePlatform exCls CE3src.platform = some E3Plat := rfl

/-- A binder with no classifier is the version's `Platform.cons`. -/
example :
    resolvePlatform exCls [("k1", none), ("k2", some "IO")] =
      some ((Platform.nil.cons).consCls Cls.IO) := rfl

/-- A binder at an undeclared classifier does not resolve. -/
example : (resolvePlatform exCls [("k", some "Undeclared")]).isNone = true := by decide

/-- The names of E1's platform, `ctl` outermost. -/
def E1Names : NameEnv ([],c,c) := (NameEnv.nil.consC "ctl").consC "io"

example : CE1src.platNames.sig = ([],c,c) := by decide

/-! ### Projected atoms and sets -/

/-- **CE1's declared use set, `{ctl, io}.only[Control]`, is `E1Filt`**, the
version's projection of the platform set. -/
example : resolveCap Λk exCls E1Names (clsSet% {ctl, io}.only[Control]) = some E1Filt := by
  decide

/-- The same through `resolveCap_map_proj`, from the set before the
projection. -/
example :
    resolveCap Λk exCls E1Names (clsSet% {ctl, io}.only[Control]) =
      (resolveCap Λk exCls E1Names (clsSet% {ctl, io})).map
        (CaptureSet.proj · (Cls.only Cls.Control)) :=
  resolveCap_map_proj Λk exCls E1Names (by decide) _

/-- A projection of a projected atom intersects the two kinds, as
`CaptureSet.proj` does, and nests nothing. -/
example :
    resolveCap Λk exCls E1Names (clsSet% {ctl.except[IO]}.only[Control]) =
      some [CapAtom.proj (.cvar E1ctl) ((Cls.only Cls.Control).interB (Cls.except Cls.IO))] := by
  decide

/-- `any` under a projection stays the atom `any`, projected. -/
example :
    resolveCap Λk exCls E1Names (clsSet% {any.except[ThreadLocal]}) =
      some [CapAtom.proj .any (Cls.except Cls.ThreadLocal)] := by decide

/-- **The codomain of CE1's `f` is `E1Cod`**, the parameter projected at
`only[Control]`.  It is read under the platform, `b`, the arrow binder and
the parameter. -/
example :
    resolveAns Λk exCls (((E1Names.cons "b").consC "%").cons "body")
      (clsAns% μ(z. {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}) ^ {body.only[Control]}) =
      some (E1Cod (s := ([],c,c,x))) := by decide

/-- And the whole type of `f` is the version's `E1TryTy`. -/
example :
    resolveTy Λk exCls (E1Names.cons "b")
      (clsTy% (∀(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io})
          μ(z. {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}) ^ {body.only[Control]}) ^ {}) =
      some (E1TryTy (.there E1ctl) (.there E1io)) := by decide

/-- CE2's `f` keeps `any` under the filter, the version's `E2TyAny`. -/
example :
    resolveTy Λk exCls ((((NameEnv.nil.consC "tl").consC "ctl").consC "io").cons "b")
      (clsTy% (∀(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {any.except[ThreadLocal]})
          μ(z. {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}) ^ {body}) ^ {}) =
      some E2TyAny := by decide

/-! ### The kind-bounded member -/

/-- The names of E3's platform, `k1` outermost. -/
def E3Names : NameEnv ([],c,c) := (NameEnv.nil.consC "k1").consC "k2"

/-- **The parameter of CE3's `c` is `E3AbsTy`**: a kind-bounded member `C`
and a field `run` at `{z.C}`, at the platform's set. -/
example :
    resolveTy Λk exCls E3Names
      (clsTy% μ(z. {C^ : only[Control]} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}}) ^ {k1, k2}) =
      some (E3AbsTy E3k1 E3k2) := by decide

/-- And the whole type of `c` is the version's `E3ClientTy`. -/
example :
    resolveTy Λk exCls E3Names
      (clsTy% (∀(x : μ(z. {C^ : only[Control]} ∧ {run : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z.C}})
          ^ {k1, k2}) (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {x, x.C}) ^ {}) =
      some (E3ClientTy E3k1 E3k2) := by decide

/-- A kind-bounded member at an undeclared classifier does not resolve. -/
example :
    (resolveShape Λk exCls E3Names (clsShape% {C^ : only[Undeclared]})).isNone = true := by
  decide

/-! ### The three programs -/

/-- CE1 resolves to the version's platform, use set, kind and term. -/
example : (resolveProg Λk CE1src).map (·.table) = some exCls := by decide
example : (resolveProg Λk CE1src).map (·.plat) = some E1Plat := rfl
example : (resolveProg Λk CE1src).map (·.uses) = some (some E1Filt) := by decide
example : (resolveProg Λk CE1src).map (·.kind) = some (some (Cls.only Cls.Control)) := by decide

/-- **CE1 erases to the version's `E1tm`.** -/
example : (resolveProg Λk CE1src).map (·.body.erase) = some E1tm := by decide

/-- CE2 resolves to the version's platform, use set and kind. -/
example : (resolveProg Λk CE2src).map (·.plat) = some E2PlatIO := rfl
example : (resolveProg Λk CE2src).map (·.uses) = some (some E2Filt) := by decide
example :
    (resolveProg Λk CE2src).map (·.kind) = some (some (Cls.except Cls.ThreadLocal)) := by decide

/-- **CE2 erases to the version's `E2tm`** once the version reads the
domain's `any` as the arrow's own binder, under the same filter. -/
example : (resolveProg Λk CE2src).map (·.body.erase.expand) = some E2tm := by decide

/-- CE3 resolves to the version's platform, use set and kind. -/
example : (resolveProg Λk CE3src).map (·.plat) = some E3Plat := rfl
example : (resolveProg Λk CE3src).map (·.uses) = some (some E3Uses) := by decide
example : (resolveProg Λk CE3src).map (·.kind) = some (some (Cls.only Cls.Control)) := by decide

/-- **CE3 erases to the version's `E3tm`.** -/
example : (resolveProg Λk CE3src).map (·.body.erase) = some E3tm := by decide

/-- No resolved program holds a projection under a projection. -/
example : (resolveProg Λk CE1src).map (·.body.ProjDepthLe1) = some true := by decide

/-- The totality theorem applies to CE1 on its decided side conditions. -/
example : (resolveProg Λk CE1src).isSome = true :=
  resolveProg_isSome Λk CE1src clsTableOf_examples (by decide)
    (fun C h => by cases h; exact ⟨by decide, by decide, by decide⟩)
    (fun K h => by cases h; decide) (by decide) (by decide) (by decide) (by decide)

/-- And the term totality theorem to CE3's body. -/
example : (resolveTop Λk exCls CE3src.platNames CE3src.body).isSome = true :=
  resolveTm_isSome Λk exCls _ _ (by decide) (by decide) (by decide) (by decide)

end ClassifiersFrontend
