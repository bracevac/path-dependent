import Coercions.Paths.Frontend.Ann
import Coercions.Paths.Frontend.Notation
import Coercions.Paths.DotMNF.Examples

/-!
# Name resolution and let insertion

Four functions take a surface phrase to the annotated de Bruijn syntax of
`Ann.lean`, and they are the only place where a surface name becomes an
index.  `resolvePath` resolves a path, `resolveTy` a type, and `resolveTm` and
`resolveDefs` a term and a definition list.

Name environments are innermost binder first, one name per binder of the
signature, so shadowing is innermost wins by construction.  User names are
data in a `NameEnv`, never Lean identifiers, so Lean's macro hygiene never
touches them.

A surface path resolves its root by the name environment and every field step
by the label table, at the term sort.  A type label is read at the type sort.
The sort of a label is fixed by its position and never by its case.

Let insertion is written with an explicit spine of bindings rather than with a
continuation.  That is what keeps the resolvers structural on the surface
phrase, which in turn is what makes the checks at the end of this module reduce
in the kernel.  The inserted binder is named `"%"`, which no Lean identifier can
equal and which nothing ever looks up, so repeated insertions need no freshness
counter.

A path in term position is nested projections, and let insertion binds every
prefix.  So `x.a.b` resolves to `let % = x.a in %.b`.  The inserted binder is
opaque: it gets the type of `x.a`, not the singleton of the path `x.a`.  That
is what the version's monadic normal form gives a deep path in term position,
and it loses what a member of `x.a` says in terms of `x.a`.

Monadic normal form is by construction and needs no predicate: `ATm.app`,
`ATm.proj` and `ATm.path` take bare variables, exactly as
`Paths.DotMNF.Tm.app`, `Tm.proj` and `Tm.path` do.  What is stated below is
totality on scoped well labelled phrases, the two spine equations, and the no
insertion property.  No semantic relation between the surface program and the
term it resolves to is claimed here.  A direct style calculus with its own type
preservation theorem would be a separate development, not covered here.

This module imports `Notation.lean`, for the programs at the end, and Lean's
token table is global.  So the words `type`, `let`, `in` and the single letters
that `Notation.lean` made atoms, among them the Greek nu that opens an object
literal, are keywords here and none of them can be a local name.  The Greek nu
would be the natural name for a name environment, but it is already a keyword,
so it is written `nv` below instead.

Nothing in this module is part of the metatheory.  No definition here lives in
the `Paths.DotMNF` or `Paths.FCdot` namespaces.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Rename Label)
open Paths.DotMNF (Path Ty Tm Defs)

/-! ## Name environments -/

/-- One surface name per binder of the signature, innermost binder first. -/
inductive NameEnv : Sig → Type where
  /-- The empty environment. -/
  | nil : NameEnv []
  /-- One more binder, with its surface name. -/
  | cons : NameEnv s → String → NameEnv (s,x)

/-- The index of a name, innermost binder wins. -/
def NameEnv.find? : {s : Sig} → NameEnv s → String → Option (BVar s .var)
  | _, .nil, _ => none
  | _, .cons nv y, z => if z = y then some .here else (nv.find? z).map .there
termination_by structural _ nv => nv

/-- The names of the environment, innermost binder first. -/
def NameEnv.names : {s : Sig} → NameEnv s → List String
  | _, .nil => []
  | _, .cons nv y => y :: nv.names
termination_by structural _ nv => nv

/-! ## Covering, the monotonicity of scoping

The two direct style clauses of `resolveTm` resolve the operand under the
environment that `atomize` returns, which is the one it was given or that one
with a single inserted name on the front.  So the totality proof needs scoping
to survive a larger name list, and that is this section. -/

/-- Every name of the first list is a name of the second. -/
def Covers (Γ Γ' : List String) : Prop :=
  ∀ z, Γ.contains z = true → Γ'.contains z = true

theorem Covers.rfl' (Γ : List String) : Covers Γ Γ := fun _ h => h

theorem Covers.tail (Γ : List String) (y : String) : Covers Γ (y :: Γ) := by
  intro z hz
  simp only [List.contains_cons, hz, Bool.or_true]

theorem Covers.cons {Γ Γ' : List String} (h : Covers Γ Γ') (x : String) :
    Covers (x :: Γ) (x :: Γ') := by
  intro z hz
  simp only [List.contains_cons] at hz ⊢
  cases hzx : (z == x) with
  | true => simp
  | false =>
      simp only [hzx, Bool.false_or] at hz ⊢
      exact h z hz

/-- Scoping of a path survives a larger name list.  Only the root is asked. -/
theorem SPath.Scoped_covers : ∀ (p : SPath) {Γ Γ' : List String}, Covers Γ Γ' →
    SPath.Scoped Γ p = true → SPath.Scoped Γ' p = true
  | .var x, _, _, h, hs => h x hs
  | .sel p _, _, _, h, hs => SPath.Scoped_covers p h hs

/-- Scoping survives a larger name list. -/
theorem SType.Scoped_covers : ∀ (T : SType) {Γ Γ' : List String}, Covers Γ Γ' →
    SType.Scoped Γ T = true → SType.Scoped Γ' T = true
  | .top, _, _, _, _ => rfl
  | .bot, _, _, _, _ => rfl
  | .typ _ S T, _, _, h, hs => by
      simp only [SType.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.Scoped_covers S h hs.1, SType.Scoped_covers T h hs.2⟩
  | .fld _ T, _, _, h, hs => SType.Scoped_covers T h hs
  | .vfld _ T, _, _, h, hs => SType.Scoped_covers T h hs
  | .sngl p, _, _, h, hs => SPath.Scoped_covers p h hs
  | .sel p _, _, _, h, hs => SPath.Scoped_covers p h hs
  | .mu x T, _, _, h, hs => SType.Scoped_covers T (h.cons x) hs
  | .all x S T, _, _, h, hs => by
      simp only [SType.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.Scoped_covers S h hs.1, SType.Scoped_covers T (h.cons x) hs.2⟩
  | .and S T, _, _, h, hs => by
      simp only [SType.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.Scoped_covers S h hs.1, SType.Scoped_covers T h hs.2⟩

mutual
/-- Scoping of a term survives a larger name list. -/
theorem STm.Scoped_covers : ∀ (e : STm) {Γ Γ' : List String}, Covers Γ Γ' →
    STm.Scoped Γ e = true → STm.Scoped Γ' e = true
  | .var x, _, _, h, hs => h x hs
  | .lam x T t, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.Scoped_covers T h hs.1, STm.Scoped_covers t (h.cons x) hs.2⟩
  | .obj x T d, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.Scoped_covers T (h.cons x) hs.1, SDefs.Scoped_covers d (h.cons x) hs.2⟩
  | .app t u, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨STm.Scoped_covers t h hs.1, STm.Scoped_covers u h hs.2⟩
  | .proj t _, _, _, h, hs => STm.Scoped_covers t h hs
  | .«let» x ann t u, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      refine ⟨⟨?_, STm.Scoped_covers t h hs.1.2⟩, STm.Scoped_covers u (h.cons x) hs.2⟩
      cases ann with
      | none => rfl
      | some U => exact SType.Scoped_covers U h hs.1.1
/-- Scoping of a definition list survives a larger name list. -/
theorem SDefs.Scoped_covers : ∀ (d : SDefs) {Γ Γ' : List String}, Covers Γ Γ' →
    SDefs.Scoped Γ d = true → SDefs.Scoped Γ' d = true
  | .typ _ T, _, _, h, hs => SType.Scoped_covers T h hs
  | .trm _ t, _, _, h, hs => STm.Scoped_covers t h hs
  | .and d e, _, _, h, hs => by
      simp only [SDefs.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SDefs.Scoped_covers d h hs.1, SDefs.Scoped_covers e h hs.2⟩
end

/-- A name in the environment has an index. -/
theorem NameEnv.find?_isSome : ∀ {s : Sig} (nv : NameEnv s) (x : String),
    nv.names.contains x = true → (nv.find? x).isSome = true
  | _, .nil, _, h => by simp [NameEnv.names] at h
  | _, .cons nv y, x, h => by
      show (if x = y then some BVar.here else (nv.find? x).map .there).isSome = true
      by_cases hxy : x = y
      · simp [hxy]
      · rw [if_neg hxy]
        have hy : (x == y) = false := by simp [hxy]
        have h' : nv.names.contains x = true := by
          simp only [NameEnv.names, List.contains_cons, hy, Bool.false_or] at h
          exact h
        have hrec := NameEnv.find?_isSome nv x h'
        cases hf : nv.find? x with
        | none => rw [hf] at hrec; exact absurd hrec (by simp)
        | some i => simp

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
def Spine.plug : {s s' : Sig} → Spine s s' → ATm s' → ATm s
  | _, _, .nil, u => u
  | _, _, .cons t sp, u => .let none t (sp.plug u)
termination_by structural _ _ sp => sp

/-- The weakening a spine induces on its outer signature. -/
def Spine.rename : {s s' : Sig} → Spine s s' → Rename s s'
  | _, _, .nil => Rename.id
  | _, _, .cons _ sp => Rename.comp Rename.succ sp.rename
termination_by structural _ _ sp => sp

/-- Stack one spine under another. -/
def Spine.append : {s s' s'' : Sig} → Spine s s' → Spine s' s'' → Spine s s''
  | _, _, _, .nil, sp' => sp'
  | _, _, _, .cons t sp, sp' => .cons t (sp.append sp')
termination_by structural _ _ _ sp => sp

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
  | .path i => ⟨s, .nil, nv, i⟩
  | _ => ⟨(s,x), .cons t .nil, nv.cons "%", .here⟩

/-- `atomize` extends the environment by at most one name. -/
theorem atomize_names_covers {s : Sig} (nv : NameEnv s) (t : ATm s) :
    Covers nv.names (atomize nv t).names.names := by
  cases t with
  | path _ => exact Covers.rfl' _
  | lam _ _ => exact Covers.tail _ _
  | obj _ _ => exact Covers.tail _ _
  | app _ _ => exact Covers.tail _ _
  | proj _ _ => exact Covers.tail _ _
  | «let» _ _ _ => exact Covers.tail _ _

/-! ## The resolvers

Each is structural on the surface phrase.  The clause order matches
`SType.Scoped` and `SType.LabelsIn` conjunct for conjunct, so the totality
proofs take the conjunctions apart in the order the `Option`s are produced.

`ν(x : T. d)` resolves its annotation under the self binder, as `Defs (s,x)`
requires.  `let x : U = t in u` resolves `U` at the outer signature, matching
the `U.weaken` of the typing rule.  Evaluation order is left to right and
matches the machine's, since the two spines are appended in that order. -/

/-- Resolve a surface path: the root by the environment, every field step by
the table at the term sort. -/
def resolvePath {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (p : SPath) : Option (Path s) :=
  match p with
  | .var x => do
      let i ← nv.find? x
      pure (.var i)
  | .sel p a => do
      let p' ← resolvePath Λ nv p
      let l ← labelTrm? Λ a
      pure (.sel p' l)
termination_by structural p

/-- Resolve a surface type. -/
def resolveTy {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (T : SType) : Option (Ty s) :=
  match T with
  | .top => some .top
  | .bot => some .bot
  | .typ A S T => do
      let l ← labelTyp? Λ A
      let S' ← resolveTy Λ nv S
      let T' ← resolveTy Λ nv T
      pure (.typ l S' T')
  | .fld a T => do
      let l ← labelTrm? Λ a
      let T' ← resolveTy Λ nv T
      pure (.fld l T')
  | .vfld a T => do
      let l ← labelTrm? Λ a
      let T' ← resolveTy Λ nv T
      pure (.vfld l T')
  | .sngl p => do
      let p' ← resolvePath Λ nv p
      pure (.sngl p')
  | .sel p A => do
      let p' ← resolvePath Λ nv p
      let l ← labelTyp? Λ A
      pure (.sel p' l)
  | .mu x T => do
      let T' ← resolveTy Λ (nv.cons x) T
      pure (.mu T')
  | .all x S T => do
      let S' ← resolveTy Λ nv S
      let T' ← resolveTy Λ (nv.cons x) T
      pure (.all S' T')
  | .and S T => do
      let S' ← resolveTy Λ nv S
      let T' ← resolveTy Λ nv T
      pure (.and S' T')
termination_by structural T

mutual
/-- Resolve a surface term, inserting `let` bindings for the two direct style
forms.  The result is in monadic normal form by construction. -/
def resolveTm {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (e : STm) : Option (ATm s) :=
  match e with
  | .var x => do
      let i ← nv.find? x
      pure (.path i)
  | .lam x T t => do
      let T' ← resolveTy Λ nv T
      let t' ← resolveTm Λ (nv.cons x) t
      pure (.lam T' t')
  | .obj x T d => do
      let T' ← resolveTy Λ (nv.cons x) T
      let d' ← resolveDefs Λ (nv.cons x) d
      pure (.obj T' d')
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
        | some U => (resolveTy Λ nv U).map some)
      let t' ← resolveTm Λ nv t
      let u' ← resolveTm Λ (nv.cons x) u
      pure (.let ann' t' u')
termination_by structural e
/-- Resolve a surface definition list. -/
def resolveDefs {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (d : SDefs) : Option (ADefs s) :=
  match d with
  | .typ A T => do
      let l ← labelTyp? Λ A
      let T' ← resolveTy Λ nv T
      pure (.typ l T')
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

/-- Resolve a surface program under the names of a context, innermost first.
This is the entry point for a program the version types under a context. -/
def resolveIn {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (e : STm) : Option (ATm s) :=
  resolveTm Λ nv e

/-- Resolve a closed surface program. -/
def resolve (Λ : LabelTable) (e : STm) : Option (ATm []) := resolveIn Λ .nil e

/-! ## Totality

Resolution succeeds on a phrase whose free names are all in the environment and
whose labels are all in the table at the sort their position demands.  The
proof is by structural recursion on the surface phrase.  In the two direct
style clauses the operand is resolved under the environment `atomize` returns,
and `atomize_names_covers` is what carries the scoping hypothesis across. -/

/-- A scoped path whose field steps are term labels of the table resolves. -/
theorem resolvePath_isSome {s : Sig} (Λ : LabelTable) (nv : NameEnv s) : ∀ (p : SPath),
    SPath.Scoped nv.names p = true → SPath.LabelsIn Λ p = true →
    (resolvePath Λ nv p).isSome = true
  | .var x, hs, _ => by
      simp only [SPath.Scoped] at hs
      have h1 := NameEnv.find?_isSome nv x hs
      simp only [resolvePath]
      cases hx : nv.find? x with
      | none => rw [hx] at h1; simp at h1
      | some _ => rfl
  | .sel p a, hs, hl => by
      simp only [SPath.Scoped] at hs
      simp only [SPath.LabelsIn, Bool.and_eq_true] at hl
      have h1 := resolvePath_isSome Λ nv p hs hl.1
      simp only [resolvePath]
      cases hp : resolvePath Λ nv p with
      | none => rw [hp] at h1; simp at h1
      | some _ =>
        cases ha : labelTrm? Λ a with
        | none => rw [ha] at hl; simp at hl
        | some _ => rfl

/-- A scoped, well labelled type resolves. -/
theorem resolveTy_isSome : ∀ (T : SType) {s : Sig} (Λ : LabelTable) (nv : NameEnv s),
    SType.Scoped nv.names T = true → SType.LabelsIn Λ T = true →
    (resolveTy Λ nv T).isSome = true
  | .top, _, _, _, _, _ => rfl
  | .bot, _, _, _, _, _ => rfl
  | .typ A S T, _, Λ, nv, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolveTy_isSome S Λ nv hs.1 hl.1.2
      have h2 := resolveTy_isSome T Λ nv hs.2 hl.2
      simp only [resolveTy]
      cases hA : labelTyp? Λ A with
      | none => rw [hA] at hl; simp at hl
      | some _ =>
        cases hS : resolveTy Λ nv S with
        | none => rw [hS] at h1; simp at h1
        | some _ =>
          cases hT : resolveTy Λ nv T with
          | none => rw [hT] at h2; simp at h2
          | some _ => rfl
  | .fld a T, _, Λ, nv, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolveTy_isSome T Λ nv hs hl.2
      simp only [resolveTy]
      cases ha : labelTrm? Λ a with
      | none => rw [ha] at hl; simp at hl
      | some _ =>
        cases hT : resolveTy Λ nv T with
        | none => rw [hT] at h1; simp at h1
        | some _ => rfl
  | .vfld a T, _, Λ, nv, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolveTy_isSome T Λ nv hs hl.2
      simp only [resolveTy]
      cases ha : labelTrm? Λ a with
      | none => rw [ha] at hl; simp at hl
      | some _ =>
        cases hT : resolveTy Λ nv T with
        | none => rw [hT] at h1; simp at h1
        | some _ => rfl
  | .sngl p, _, Λ, nv, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn] at hs hl
      have h1 := resolvePath_isSome Λ nv p hs hl
      simp only [resolveTy]
      cases hp : resolvePath Λ nv p with
      | none => rw [hp] at h1; simp at h1
      | some _ => rfl
  | .sel p A, _, Λ, nv, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolvePath_isSome Λ nv p hs hl.1
      simp only [resolveTy]
      cases hp : resolvePath Λ nv p with
      | none => rw [hp] at h1; simp at h1
      | some _ =>
        cases hA : labelTyp? Λ A with
        | none => rw [hA] at hl; simp at hl
        | some _ => rfl
  | .mu x T, _, Λ, nv, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn] at hs hl
      have h1 := resolveTy_isSome T Λ (nv.cons x) hs hl
      simp only [resolveTy]
      cases hT : resolveTy Λ (nv.cons x) T with
      | none => rw [hT] at h1; simp at h1
      | some _ => rfl
  | .all x S T, _, Λ, nv, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolveTy_isSome S Λ nv hs.1 hl.1
      have h2 := resolveTy_isSome T Λ (nv.cons x) hs.2 hl.2
      simp only [resolveTy]
      cases hS : resolveTy Λ nv S with
      | none => rw [hS] at h1; simp at h1
      | some _ =>
        cases hT : resolveTy Λ (nv.cons x) T with
        | none => rw [hT] at h2; simp at h2
        | some _ => rfl
  | .and S T, _, Λ, nv, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolveTy_isSome S Λ nv hs.1 hl.1
      have h2 := resolveTy_isSome T Λ nv hs.2 hl.2
      simp only [resolveTy]
      cases hS : resolveTy Λ nv S with
      | none => rw [hS] at h1; simp at h1
      | some _ =>
        cases hT : resolveTy Λ nv T with
        | none => rw [hT] at h2; simp at h2
        | some _ => rfl

mutual
/-- A scoped, well labelled term resolves. -/
theorem resolveTm_isSome : ∀ (e : STm) {s : Sig} (Λ : LabelTable) (nv : NameEnv s),
    STm.Scoped nv.names e = true → STm.LabelsIn Λ e = true →
    (resolveTm Λ nv e).isSome = true
  | .var x, _, Λ, nv, hs, _ => by
      simp only [STm.Scoped] at hs
      have h1 := NameEnv.find?_isSome nv x hs
      simp only [resolveTm]
      cases hx : nv.find? x with
      | none => rw [hx] at h1; simp at h1
      | some _ => rfl
  | .lam x T t, _, Λ, nv, hs, hl => by
      simp only [STm.Scoped, STm.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolveTy_isSome T Λ nv hs.1 hl.1
      have h2 := resolveTm_isSome t Λ (nv.cons x) hs.2 hl.2
      simp only [resolveTm]
      cases hT : resolveTy Λ nv T with
      | none => rw [hT] at h1; simp at h1
      | some _ =>
        cases ht : resolveTm Λ (nv.cons x) t with
        | none => rw [ht] at h2; simp at h2
        | some _ => rfl
  | .obj x T d, _, Λ, nv, hs, hl => by
      simp only [STm.Scoped, STm.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolveTy_isSome T Λ (nv.cons x) hs.1 hl.1
      have h2 := resolveDefs_isSome d Λ (nv.cons x) hs.2 hl.2
      simp only [resolveTm]
      cases hT : resolveTy Λ (nv.cons x) T with
      | none => rw [hT] at h1; simp at h1
      | some _ =>
        cases hd : resolveDefs Λ (nv.cons x) d with
        | none => rw [hd] at h2; simp at h2
        | some _ => rfl
  | .app t u, _, Λ, nv, hs, hl => by
      simp only [STm.Scoped, STm.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolveTm_isSome t Λ nv hs.1 hl.1
      simp only [resolveTm]
      cases ht : resolveTm Λ nv t with
      | none => rw [ht] at h1; simp at h1
      | some t₀ =>
        have h2 := resolveTm_isSome u Λ (atomize nv t₀).names
          (STm.Scoped_covers u (atomize_names_covers nv t₀) hs.2) hl.2
        cases hu : resolveTm Λ (atomize nv t₀).names u with
        | none => rw [hu] at h2; simp at h2
        | some _ => simp [hu]
  | .proj t a, _, Λ, nv, hs, hl => by
      simp only [STm.Scoped, STm.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolveTm_isSome t Λ nv hs hl.1
      simp only [resolveTm]
      cases ht : resolveTm Λ nv t with
      | none => rw [ht] at h1; simp at h1
      | some _ =>
        cases ha : labelTrm? Λ a with
        | none => rw [ha] at hl; simp at hl
        | some _ => rfl
  | .«let» x ann t u, _, Λ, nv, hs, hl => by
      simp only [STm.Scoped, STm.LabelsIn, Bool.and_eq_true] at hs hl
      have h2 := resolveTm_isSome t Λ nv hs.1.2 hl.1.2
      have h3 := resolveTm_isSome u Λ (nv.cons x) hs.2 hl.2
      cases ann with
      | none =>
        simp only [resolveTm]
        cases ht : resolveTm Λ nv t with
        | none => rw [ht] at h2; simp at h2
        | some _ =>
          cases hu : resolveTm Λ (nv.cons x) u with
          | none => rw [hu] at h3; simp at h3
          | some _ => rfl
      | some U =>
        have h1 := resolveTy_isSome U Λ nv hs.1.1 hl.1.1
        simp only [resolveTm]
        cases hU : resolveTy Λ nv U with
        | none => rw [hU] at h1; simp at h1
        | some _ =>
          cases ht : resolveTm Λ nv t with
          | none => rw [ht] at h2; simp at h2
          | some _ =>
            cases hu : resolveTm Λ (nv.cons x) u with
            | none => rw [hu] at h3; simp at h3
            | some _ => rfl
/-- A scoped, well labelled definition list resolves. -/
theorem resolveDefs_isSome : ∀ (d : SDefs) {s : Sig} (Λ : LabelTable) (nv : NameEnv s),
    SDefs.Scoped nv.names d = true → SDefs.LabelsIn Λ d = true →
    (resolveDefs Λ nv d).isSome = true
  | .typ A T, _, Λ, nv, hs, hl => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolveTy_isSome T Λ nv hs hl.2
      simp only [resolveDefs]
      cases hA : labelTyp? Λ A with
      | none => rw [hA] at hl; simp at hl
      | some _ =>
        cases hT : resolveTy Λ nv T with
        | none => rw [hT] at h1; simp at h1
        | some _ => rfl
  | .trm a t, _, Λ, nv, hs, hl => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolveTm_isSome t Λ nv hs hl.2
      simp only [resolveDefs]
      cases ha : labelTrm? Λ a with
      | none => rw [ha] at hl; simp at hl
      | some _ =>
        cases ht : resolveTm Λ nv t with
        | none => rw [ht] at h1; simp at h1
        | some _ => rfl
  | .and d e, _, Λ, nv, hs, hl => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolveDefs_isSome d Λ nv hs.1 hl.1
      have h2 := resolveDefs_isSome e Λ nv hs.2 hl.2
      simp only [resolveDefs]
      cases hd : resolveDefs Λ nv d with
      | none => rw [hd] at h1; simp at h1
      | some _ =>
        cases he : resolveDefs Λ nv e with
        | none => rw [he] at h2; simp at h2
        | some _ => rfl
end

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
    atomize nv (.path i) = ⟨s, .nil, nv, i⟩ := rfl

/-! ## The version's programs

Every program of `Notation.lean` resolves, and its erasure is the term of the
version's own derivation in `lean/Coercions/Paths/DotMNF/Examples.lean`.  Each
comparison is a `decide`: resolution is structural, so the kernel reduces it.

The label table is written out.  The version gives two names one label in
places (`lC` and `X4_lType` are both `.typ 3`, `lf` and `X4_lnewTypeTop` are
both `.trm 4`), so a table interned from the program would not reproduce the
version's terms.  The label of gDOT Fig. 2 keeps its own name, `Type`, which
the notation writes `«Type»`. -/

open Paths.DotMNF.Examples

/-- The labels of `lean/Coercions/Paths/DotMNF/Examples.lean`, by the names
the programs below write. -/
def pathsTable : LabelTable :=
  [("A", lA), ("B", lB), ("T", lT), ("a", la), ("b", lb), ("v", lv),
   ("f", lf), ("c", lc), ("C", lC),
   ("Option", Fig2_lOption), ("types", Fig2_ltypes), ("tpe", Fig2_ltpe), ("id", Fig2_lid),
   ("newSymbol", Fig2_lnewSymbol), ("n", Fig2_ln),
   ("Type", X4_lType), ("TypeTop", X4_lTypeTop), ("TypeRef", X4_lTypeRef),
   ("Symbol", X4_lSymbol), ("newTypeTop", X4_lnewTypeTop), ("newTypeRef", X4_lnewTypeRef),
   ("symbols", X4_lsymbols), ("symb", X4_lsymb)]

/-- The term a derivation of the version is about. -/
def versionTerm {s : Sig} {Γ : Paths.DotMNF.Ctx s} {t : Tm s} {T : Ty s}
    (_ : Paths.DotMNF.HasTy Γ t T) : Tm s := t

/-! ### E1p, bad bounds at a path -/

example : (resolve pathsTable E1p_src).map ATm.erase = some (versionTerm E1p) := by decide

/-- The domain resolves to the version's `E1p_Dom`. -/
example : resolveTy pathsTable .nil (pdotTy% {val f : {A : ⊤..⊥}}) = some (E1p_Dom (s := [])) := by
  decide

/-- The totality theorem applies to E1p, on the two decided side conditions. -/
example : (resolveTm pathsTable .nil E1p_src).isSome = true :=
  resolveTm_isSome E1p_src pathsTable .nil (by decide) (by decide)

/-! ### X3, with `x` bound by a lambda

The version types X3 in the context `x : {val a : {val b : ⊤}}`.  Written
closed, the context entry becomes a lambda.  The direct-style `x.a.b` inserts
the `let` that X3 writes by hand, so both resolve to the same term. -/

example : (resolve pathsTable X3_src).map ATm.erase =
    some (.val (.lam X3_A (versionTerm X3))) := by decide

example : (resolve pathsTable X3d_src).map ATm.erase =
    some (.val (.lam X3_A (versionTerm X3))) := by decide

/-- The direct-style path and the hand written `let` resolve to one term. -/
example : resolve pathsTable X3d_src = resolve pathsTable X3_src := by decide

/-- X3 written open, under the version's own context: resolved at the name of
that context's one entry, it is the version's term. -/
example : (resolveIn pathsTable (.cons .nil "x") (pdot% let y = x.a in y.b)).map ATm.erase =
    some (versionTerm X3) := by decide

/-! ### E9, a singleton at a `let` -/

example : (resolve pathsTable E9_src).map ATm.erase = some (versionTerm E9) := by decide

/-! ### X1 -/

example : (resolve pathsTable X1_src).map ATm.erase =
    some (versionTerm (X1_lit (Γ := Paths.DotMNF.Ctx.nil))) := by decide

/-! ### E2p, a function at a path-keyed member, applied to itself -/

example : (resolve pathsTable E2p_src).map ATm.erase = some (versionTerm E2p) := by decide

/-! ### E11, a stable field beside a singleton field -/

example : (resolve pathsTable E11_src).map ATm.erase = some (versionTerm E11) := by decide

/-! ### The base programs E1 to E8, unchanged in the version -/

example : (resolve pathsTable E1_src).map ATm.erase = some (versionTerm E1) := by decide

example : (resolve pathsTable E2_src).map ATm.erase = some (versionTerm E2) := by decide

example : (resolve pathsTable E3_src).map ATm.erase = some (versionTerm E3) := by decide

example : (resolve pathsTable E4_src).map ATm.erase = some (versionTerm E4) := by decide

example : (resolve pathsTable E5_src).map ATm.erase = some (versionTerm E5) := by decide

/-- The version types E6 under `n : {a : ⊤}`.  Written closed, that entry is a
lambda's binder. -/
example : (resolve pathsTable E6_src).map ATm.erase =
    some (.val (.lam E6Int (versionTerm E6))) := by decide

example : (resolve pathsTable E7_src).map ATm.erase = some (versionTerm E7) := by decide

example : (resolve pathsTable E8_src).map ATm.erase = some (versionTerm E8) := by decide

/-! ### The hop pages E3p to E8p -/

example : (resolve pathsTable E3p_src).map ATm.erase = some (versionTerm E3p) := by decide

example : (resolve pathsTable E4p_src).map ATm.erase = some (versionTerm E4p) := by decide

example : (resolve pathsTable E5p_src).map ATm.erase = some (versionTerm E5p) := by decide

example : (resolve pathsTable E6p_src).map ATm.erase = some (versionTerm E6p) := by decide

example : (resolve pathsTable E7p_src).map ATm.erase = some (versionTerm E7p_lit) := by decide

example : (resolve pathsTable E8p_src).map ATm.erase = some (versionTerm E8p) := by decide

/-! ### X2, X4 written closed, P3e -/

example : (resolve pathsTable X2_src).map ATm.erase =
    some (versionTerm (X2_lit (Γ := Paths.DotMNF.Ctx.nil))) := by decide

/-- The version types X4 under `pcore : ⊤`.  Written closed, that entry is a
lambda's binder. -/
example : (resolve pathsTable X4_src).map ATm.erase =
    some (.val (.lam .top (versionTerm X4_lit0))) := by decide

/-- P3e's third member is the term label 2, which the table calls `v`. -/
example : (resolve pathsTable P3e_src).map ATm.erase = some (versionTerm P3e_lit) := by decide

/-! ### gDOT Fig. 2 and pDOT Fig. 1 -/

/-- The surface program resolves, and its erasure is the version's `Fig2_prog`. -/
example : (resolve pathsTable Fig2_src).map ATm.erase = some Fig2_prog := by decide

/-- The two nested literals carry exactly the bodies of the two stable fields
of `pcore`'s self type, which is the side condition of `DefsTy.trmObj`. -/
example : (match resolve pathsTable Fig2_src with
    | some (.let _ _ (.let _ (.obj T (.and (.trm _ (.obj Tt _)) (.trm _ (.obj Ty _)))) _)) =>
        decide (T = .and (.vfld Fig2_ltypes (.mu Tt)) (.vfld X4_lsymbols (.mu Ty)))
    | _ => false) = true := by decide

/-- The self annotation of `pcore` resolves to the version's `Fig2_pBody`. -/
example : (match resolve pathsTable Fig2_src with
    | some (.let _ _ (.let _ (.obj T _) _)) => decide (T = Fig2_pBody)
    | _ => false) = true := by decide

/-- Fig. 1 is Fig. 2 with `tpe : p.types.Type`, and its erasure is the
version's `Fig1_prog`. -/
example : (resolve pathsTable Fig1_src).map ATm.erase = some Fig1_prog := by decide

/-! ### Three programs of the restriction account

R1 and R2 reach a singleton's alias through a type member whose bounds are
singletons, which the version's subtyping relates.  R7 is the direct-style
path whose inserted binder is opaque.  Here the claim is only that all three
resolve.  Whether they type is the typer's question. -/

example : (resolve pathsTable R1_src).isSome = true := by decide

example : (resolve pathsTable R2_src).isSome = true := by decide

example : (resolve pathsTable R7_src).isSome = true := by decide

end PathsFrontend
