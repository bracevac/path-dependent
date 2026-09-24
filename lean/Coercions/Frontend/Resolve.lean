import Coercions.Frontend.Ann
import Coercions.Frontend.Notation

/-!
# Name resolution and let insertion

Stage F0.5 of `plan-5e-frontend-stages.md`.  Three functions take a surface
phrase to the annotated de Bruijn syntax of `Ann.lean`, and they are the only
place where a surface name becomes an index.

Name environments are innermost binder first, one name per binder of the
signature, so shadowing is innermost wins by construction.  User names are
data in a `NameEnv`, never Lean identifiers, so Lean's macro hygiene never
touches them.

Let insertion is written with an explicit spine of bindings rather than with a
continuation.  That is what keeps the three resolvers structural on the surface
phrase, which in turn is what makes the checks at the end of this module reduce
in the kernel.  The inserted binder is named `"%"`, which no Lean identifier can
equal and which nothing ever looks up, so repeated insertions need no freshness
counter.

Monadic normal form is by construction and needs no predicate: `ATm.app` and
`ATm.proj` take bare variables, exactly as `DotMNF.Tm.app` and `DotMNF.Tm.proj`
do.  What is stated below is totality on scoped well labelled programs, the two
spine equations, and the no insertion property.  No semantic relation between
the surface program and the term it resolves to is claimed here.  That is the
direct style calculus with its own type preservation theorem, parked by
`plan-5-extensions.md` §7 as a development of its own.

This module imports `Notation.lean`, for the ten example programs at the end,
and Lean's token table is global.  So the words `type`, `let`, `in` and the
single letters that `Notation.lean` made atoms, among them the Greek nu that
opens an object literal, are keywords here and none of them can be a local
name.  The plan writes the name environment `ν`.  It is written `nv` below,
for that reason and no other.

Nothing in this module is part of the metatheory.  No definition here lives in
the `DotMNF` or `FCdot` namespaces.
-/

namespace Frontend

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Path Ty Tm Defs)

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

/-- The names of the environment, innermost binder first. -/
def NameEnv.names : {s : Sig} → NameEnv s → List String
  | _, .nil => []
  | _, .cons nv y => y :: nv.names

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

/-- Scoping survives a larger name list. -/
theorem SType.Scoped_covers : ∀ (T : SType) {Γ Γ' : List String}, Covers Γ Γ' →
    SType.Scoped Γ T = true → SType.Scoped Γ' T = true
  | .top, _, _, _, _ => rfl
  | .bot, _, _, _, _ => rfl
  | .typ _ S T, _, _, h, hs => by
      simp only [SType.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.Scoped_covers S h hs.1, SType.Scoped_covers T h hs.2⟩
  | .fld _ T, _, _, h, hs => SType.Scoped_covers T h hs
  | .sel x _, _, _, h, hs => h x hs
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

/-- The weakening a spine induces on its outer signature. -/
def Spine.rename : {s s' : Sig} → Spine s s' → Rename s s'
  | _, _, .nil => Rename.id
  | _, _, .cons _ sp => Rename.comp Rename.succ sp.rename

/-- Stack one spine under another. -/
def Spine.append : {s s' s'' : Sig} → Spine s s' → Spine s' s'' → Spine s s''
  | _, _, _, .nil, sp' => sp'
  | _, _, _, .cons t sp, sp' => .cons t (sp.append sp')

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
and nothing is inserted; anything else is bound by one fresh `let`. -/
def atomize {s : Sig} (nv : NameEnv s) (t : ATm s) : Atomic s :=
  match t with
  | .path (.var i) => ⟨s, .nil, nv, i⟩
  | _ => ⟨(s,x), .cons t .nil, nv.cons "%", .here⟩

/-- `atomize` extends the environment by at most one name. -/
theorem atomize_names_covers {s : Sig} (nv : NameEnv s) (t : ATm s) :
    Covers nv.names (atomize nv t).names.names := by
  cases t with
  | path p => cases p with | var _ => exact Covers.rfl' _
  | lam _ _ => exact Covers.tail _ _
  | obj _ _ => exact Covers.tail _ _
  | app _ _ => exact Covers.tail _ _
  | proj _ _ => exact Covers.tail _ _
  | «let» _ _ _ => exact Covers.tail _ _

/-! ## The resolvers

Each of the three is structural on the surface phrase.  The clause order
matches `SType.Scoped` and `SType.LabelsIn` conjunct for conjunct, so the
totality proofs take the conjunctions apart in the order the `Option`s are
produced.

`ν(x : T. d)` resolves its annotation under the self binder, as `Defs (s,x)`
requires.  `let x : U = t in u` resolves `U` at the outer signature, matching
the `U.weaken` of the typing rule.  Evaluation order is left to right and
matches the machine's, since the two spines are appended in that order. -/

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
  | .sel x A => do
      let i ← nv.find? x
      let l ← labelTyp? Λ A
      pure (.sel (.var i) l)
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
      pure (.path (.var i))
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

/-- Resolve a closed surface program. -/
def resolve (Λ : LabelTable) (e : STm) : Option (ATm []) := resolveTm Λ .nil e

/-! ## Totality

Resolution succeeds on a phrase whose free names are all in the environment and
whose labels are all in the table.  The proof is by structural recursion on the
surface phrase.  In the two direct style clauses the operand is resolved under
the environment `atomize` returns, and `atomize_names_covers` is what carries
the scoping hypothesis across. -/

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
  | .sel x A, _, Λ, nv, hs, hl => by
      simp only [SType.Scoped, SType.LabelsIn] at hs hl
      have h1 := NameEnv.find?_isSome nv x hs
      simp only [resolveTy]
      cases hx : nv.find? x with
      | none => rw [hx] at h1; simp at h1
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
    atomize nv (.path (.var i)) = ⟨s, .nil, nv, i⟩ := rfl

/-! ## The ten programs of F3.3

The deliverable of F0.7.  Each program is written once in the surface notation
of `Notation.lean` and once as a hand written `ATm []`, and the two are compared
by `rfl`.  Resolution is structural, so the kernel reduces it and no compiled
evaluation is needed.

E1 to E9 are the vanilla examples of `lean/Coercions/DotMNF/Examples.lean`, all
of which are already in monadic normal form there, so `atomize` inserts nothing
and the resolved term is the hand written one on the nose.  That is
`atomize_var` at work.  E10 is the opposite case, a nested application in direct
style, and it is compared against its let expanded form.

The label table reproduces the one of the vanilla examples, so a later stage can
compare the erasures against the hand written `DotMNF.Tm`s there.

One correction to the plan's table of F3.3.  It prints E2's self type as
`{A : ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}`.  A type member declaration needs
two bounds, and the single bound form is the field declaration `{a : T}`, whose
name would then be looked up at the term sort and fail.  The vanilla file has
`.typ lA E2A E2A`, both bounds, so the surface program below writes both. -/

/-- Type label `A` of the vanilla examples. -/
private def lA : Label := .typ 0
/-- Type label `B` of the vanilla examples. -/
private def lB : Label := .typ 1
/-- Type label `T` of the vanilla examples. -/
private def lT : Label := .typ 2
/-- Term label `a` of the vanilla examples. -/
private def la : Label := .trm 0
/-- Term label `b` of the vanilla examples. -/
private def lb : Label := .trm 1
/-- Term label `v` of the vanilla examples. -/
private def lv : Label := .trm 2

/-- The label table of `lean/Coercions/DotMNF/Examples.lean`. -/
def exampleTable : LabelTable :=
  [("A", lA), ("B", lB), ("T", lT), ("a", la), ("b", lb), ("v", lv)]

/-! ### E1: bad bounds under a lambda -/

/-- `λ(x : {A : ⊤..⊥}). let y : {B : {a : ⊤}..{a : ⊤}} = x in y`. -/
def E1src : STm :=
  dot% λ(x : {A : ⊤..⊥}). let y : {B : {a : ⊤} .. {a : ⊤}} = x in y

/-- The term E1 resolves to. -/
def E1ann : ATm [] :=
  .lam (.typ lA .top .bot)
    (.let (some (.typ lB (.fld la .top) (.fld la .top)))
      (.path (.var .here)) (.path (.var .here)))

example : resolve exampleTable E1src = some E1ann := rfl

/-- The totality theorem applies to E1, on the two decided side conditions. -/
example : (resolveTm exampleTable .nil E1src).isSome = true :=
  resolveTm_isSome E1src exampleTable .nil (by decide) (by decide)

/-! ### E2: a recursive object with a self referential member -/

/-- `let x = ν(s : {A : E2A..E2A} ∧ {a : E2A}. {type A = E2A} ∧ {a = λ(y : s.A). y})
in let f = x.a in f f`, with `E2A` the type `∀(y : s.A) s.A`. -/
def E2src : STm :=
  dot% let x = ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}.
                  {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y})
       in let f = x.a in f f

/-- `∀(y : s.A) s.A` under the self binder. -/
private def E2A : Ty ([],x) :=
  .all (.sel (.var .here) lA) (.sel (.var (.there .here)) lA)

/-- The term E2 resolves to. -/
def E2ann : ATm [] :=
  .let none
    (.obj (.and (.typ lA E2A E2A) (.fld la E2A))
      (.and (.typ lA E2A)
        (.trm la (.lam (.sel (.var .here) lA) (.path (.var .here))))))
    (.let none (.proj .here la) (.app .here .here))

example : resolve exampleTable E2src = some E2ann := rfl

/-! ### E3: an intersection with a shared member -/

/-- `λ(x : {A : ⊥..{a : ⊤}} ∧ {A : {b : ⊤}..⊤}). λ(z : {b : ⊤}). let y : {a : ⊤} = z in y`. -/
def E3src : STm :=
  dot% λ(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}).
         λ(z : {b : ⊤}). let y : {a : ⊤} = z in y

/-- The term E3 resolves to. -/
def E3ann : ATm [] :=
  .lam (.and (.typ lA .bot (.fld la .top)) (.typ lA (.fld lb .top) .top))
    (.lam (.fld lb .top)
      (.let (some (.fld la .top)) (.path (.var .here)) (.path (.var .here))))

example : resolve exampleTable E3src = some E3ann := rfl

/-! ### E4: the counterexample of the paper's first section -/

/-- `λ(x : {B : {A : ⊥..⊤}..{A : {a : ⊤}..⊤}}). λ(w : {A : ⊥..⊤}). λ(n : {a : ⊤}).
let g = λ(y : w.A). y in g n`. -/
def E4src : STm :=
  dot% λ(x : {B : {A : ⊥ .. ⊤} .. {A : {a : ⊤} .. ⊤}}).
         λ(w : {A : ⊥ .. ⊤}). λ(n : {a : ⊤}). let g = λ(y : w.A). y in g n

/-- The term E4 resolves to. -/
def E4ann : ATm [] :=
  .lam (.typ lB (.typ lA .bot .top) (.typ lA (.fld la .top) .top))
    (.lam (.typ lA .bot .top)
      (.lam (.fld la .top)
        (.let none (.lam (.sel (.var (.there .here)) lA) (.path (.var .here)))
          (.app .here (.there .here)))))

example : resolve exampleTable E4src = some E4ann := rfl

/-! ### E5: an object returned from a function and selected after a `let` -/

/-- `λ(w : {A : ⊤..⊤}). let f = λ(v : {A : ⊤..⊤}). ν(z : {a : v.A}. {a = v})
in let o = f w in o.a`. -/
def E5src : STm :=
  dot% λ(w : {A : ⊤..⊤}).
         let f = λ(v : {A : ⊤..⊤}). ν(z : {a : v.A}. {a = v})
         in let o = f w in o.a

/-- The term E5 resolves to. -/
def E5ann : ATm [] :=
  .lam (.typ lA .top .top)
    (.let none
      (.lam (.typ lA .top .top)
        (.obj (.fld la (.sel (.var (.there .here)) lA))
          (.trm la (.path (.var (.there .here))))))
      (.let none (.app .here (.there .here)) (.proj .here la)))

example : resolve exampleTable E5src = some E5ann := rfl

/-! ### E6: a field typed at its own literal's member -/

/-- `λ(n : {a : ⊤}). ν(x : {T : {a : ⊤}..{a : ⊤}} ∧ {v : x.T}. {type T = {a : ⊤}} ∧ {v = n})`. -/
def E6src : STm :=
  dot% λ(n : {a : ⊤}).
         ν(x : {T : {a : ⊤} .. {a : ⊤}} ∧ {v : x.T}.
             {type T = {a : ⊤}} ∧ {v = n})

/-- The term E6 resolves to. -/
def E6ann : ATm [] :=
  .lam (.fld la .top)
    (.obj (.and (.typ lT (.fld la .top) (.fld la .top)) (.fld lv (.sel (.var .here) lT)))
      (.and (.typ lT (.fld la .top)) (.trm lv (.path (.var (.there .here))))))

example : resolve exampleTable E6src = some E6ann := rfl

/-! ### E7: two type members that name each other -/

/-- `ν(x : {A : x.B..x.B} ∧ {B : x.A..x.A}. {type A = x.B} ∧ {type B = x.A})`. -/
def E7src : STm :=
  dot% ν(x : {A : x.B .. x.B} ∧ {B : x.A .. x.A}.
           {type A = x.B} ∧ {type B = x.A})

/-- The term E7 resolves to. -/
def E7ann : ATm [] :=
  .obj (.and (.typ lA (.sel (.var .here) lB) (.sel (.var .here) lB))
          (.typ lB (.sel (.var .here) lA) (.sel (.var .here) lA)))
    (.and (.typ lA (.sel (.var .here) lB)) (.typ lB (.sel (.var .here) lA)))

example : resolve exampleTable E7src = some E7ann := rfl

/-! ### E8: the right view step -/

/-- `λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A ∧ {a : ⊤}). y.a`. -/
def E8src : STm :=
  dot% λ(x : {A : ⊥ .. {a : ⊤}}). λ(y : x.A ∧ {a : ⊤}). y.a

/-- The term E8 resolves to. -/
def E8ann : ATm [] :=
  .lam (.typ lA .bot (.fld la .top))
    (.lam (.and (.sel (.var .here) lA) (.fld la .top)) (.proj .here la))

example : resolve exampleTable E8src = some E8ann := rfl

/-! ### E9: the upper view step -/

/-- `λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A). y.a`. -/
def E9src : STm :=
  dot% λ(x : {A : ⊥ .. {a : ⊤}}). λ(y : x.A). y.a

/-- The term E9 resolves to. -/
def E9ann : ATm [] :=
  .lam (.typ lA .bot (.fld la .top))
    (.lam (.sel (.var .here) lA) (.proj .here la))

example : resolve exampleTable E9src = some E9ann := rfl

/-! ### E10: let insertion at a nested application

The only one of the ten that is not already in monadic normal form.  The operand
`g f` is not a variable, so `atomize` binds it to the inserted name `"%"`, which
is the innermost binder of the body.  Evaluation order is left to right: the
operator is atomized first, and being a variable it inserts nothing, so the one
inserted binding is the operand's. -/

/-- `λ(f : ⊤). λ(g : ⊤). f (g f)`. -/
def E10src : STm :=
  dot% λ(f : ⊤). λ(g : ⊤). f (g f)

/-- The let expanded form, `λ(f). λ(g). let % = g f in f %`. -/
def E10ann : ATm [] :=
  .lam .top
    (.lam .top
      (.let none (.app .here (.there .here))
        (.app (.there (.there .here)) .here)))

example : resolve exampleTable E10src = some E10ann := rfl

/-- The totality theorem applies to E10 as well, and E10 needs no label. -/
example : (resolveTm exampleTable .nil E10src).isSome = true :=
  resolveTm_isSome E10src exampleTable .nil (by decide) (by decide)

/-- Erasure drops the two annotations and lands in the frozen syntax.  The
inserted `let` is a `let` of `DotMNF.Tm`, nothing more. -/
example : E10ann.erase =
    (Tm.val (.lam .top (.val (.lam .top
      (.let (.app .here (.there .here)) (.app (.there (.there .here)) .here)))))) := rfl

end Frontend

