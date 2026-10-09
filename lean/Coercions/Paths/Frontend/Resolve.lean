import Coercions.Paths.Frontend.Ann
import Coercions.Paths.Frontend.Notation
import Coercions.Paths.DotMNF.Examples

/-!
# Name resolution and let insertion

`resolvePath`, `resolveTy`, `resolveTm` and `resolveDefs` take a surface phrase
to the partial terms of `Ann.lean`.  They are the only place where a name
becomes an index.  A slot the programmer left empty stays empty in the result,
for the elaborator to fill.  `resolveP` returns that partial term.  `resolve`
keeps only a program with every slot written, through `PTm.full?`, and gives
the annotated term the typer reads.

A `NameEnv` lists one name per binder, innermost first, so the innermost
binding wins.  A path resolves its root by the name environment and its field
steps by the label table at the term sort.  A type label is read at the type
sort.

Direct style terms become monadic normal form by let insertion.  The inserted
bindings form an explicit `Spine`, not a continuation, which keeps the
resolvers structural.  The inserted binder is named `"%"`, which nothing looks
up, so no freshness counter is needed.  A path `x.a.b` in term position
resolves to `let % = x.a in %.b`.  The binder `%` has the type of `x.a`, not
the singleton of the path.

`PTm.app`, `PTm.proj` and `PTm.path` take bare variables, so normal form needs
no predicate.  Each inserted `let` carries a tag that says where it sits: `arg`
at the operand of an application, `recv` at an operator or at the receiver of a
projection.  The module proves totality on scoped, well labelled phrases, the
two spine equations and the no insertion property.  It relates a surface
program to its resolved term only by the examples at the end.

`Notation.lean` is imported for those examples.  Its tokens are global, so
`type`, `let`, `in` and the Greek nu are keywords here.  The name environment is
written `nv` for that reason.

Nothing here belongs to the metatheory.
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

`resolveTm` resolves the operand of an application or projection under the
environment that `atomize` returns, which is the given one plus at most one
name.  The totality proof therefore needs scoping to survive a larger name
list. -/

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

/-- Scoping of a path survives a larger name list. -/
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

/-- Scoping of an optional type survives a larger name list. -/
theorem SType.ScopedOpt_covers : ∀ (T : Option SType) {Γ Γ' : List String}, Covers Γ Γ' →
    SType.ScopedOpt Γ T = true → SType.ScopedOpt Γ' T = true
  | none, _, _, _, _ => rfl
  | some T, _, _, h, hs => SType.Scoped_covers T h hs

mutual
/-- Scoping of a term survives a larger name list. -/
theorem STm.Scoped_covers : ∀ (e : STm) {Γ Γ' : List String}, Covers Γ Γ' →
    STm.Scoped Γ e = true → STm.Scoped Γ' e = true
  | .var x, _, _, h, hs => h x hs
  | .lam x T t, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.ScopedOpt_covers T h hs.1, STm.Scoped_covers t (h.cons x) hs.2⟩
  | .obj x T d, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.ScopedOpt_covers T (h.cons x) hs.1, SDefs.Scoped_covers d (h.cons x) hs.2⟩
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
  | .asc t T, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨STm.Scoped_covers t h hs.1, SType.Scoped_covers T h hs.2⟩
/-- Scoping of a definition list survives a larger name list. -/
theorem SDefs.Scoped_covers : ∀ (d : SDefs) {Γ Γ' : List String}, Covers Γ Γ' →
    SDefs.Scoped Γ d = true → SDefs.Scoped Γ' d = true
  | .typ _ T, _, _, h, hs => SType.Scoped_covers T h hs
  | .trm _ T t, _, _, h, hs => by
      simp only [SDefs.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.ScopedOpt_covers T h hs.1, STm.Scoped_covers t h hs.2⟩
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

A `Spine s s'` is a stack of `let` bindings that takes a term over `s'` to a
term over `s`.  `Spine.rename` moves a variable of `s` into `s'`.
`Rename.comp f g` is `g ∘ f`. -/

/-- A stack of inserted `let` bindings, each with the tag it is plugged
with. -/
inductive Spine : Sig → Sig → Type where
  /-- No binding. -/
  | nil : Spine s s
  /-- One binding, then the rest under it. -/
  | cons : LetTag → PTm s → Spine (s,x) s' → Spine s s'

/-- Wrap a term of the inner signature in the bindings of the spine. -/
def Spine.plug : {s s' : Sig} → Spine s s' → PTm s' → PTm s
  | _, _, .nil, u => u
  | _, _, .cons g t sp, u => .let g none t (sp.plug u)
termination_by structural _ _ sp => sp

/-- The weakening a spine induces on its outer signature. -/
def Spine.rename : {s s' : Sig} → Spine s s' → Rename s s'
  | _, _, .nil => Rename.id
  | _, _, .cons _ _ sp => Rename.comp Rename.succ sp.rename
termination_by structural _ _ sp => sp

/-- Stack one spine under another. -/
def Spine.append : {s s' s'' : Sig} → Spine s s' → Spine s' s'' → Spine s s''
  | _, _, _, .nil, sp' => sp'
  | _, _, _, .cons g t sp, sp' => .cons g t (sp.append sp')
termination_by structural _ _ _ sp => sp

/-- A term in variable position: the inserted bindings, the extended
environment and the variable that stands for the term. -/
structure Atomic (s : Sig) where
  /-- The signature after the insertions. -/
  sig : Sig
  /-- The insertions. -/
  spine : Spine s sig
  /-- The environment at that signature. -/
  names : NameEnv sig
  /-- The variable standing for the term. -/
  var : BVar sig .var

/-- A variable stays.  Any other term is bound by one fresh `let`, with the tag
`g` that says where the term sits. -/
def atomize {s : Sig} (g : LetTag) (nv : NameEnv s) (t : PTm s) : Atomic s :=
  match t with
  | .path i => ⟨s, .nil, nv, i⟩
  | _ => ⟨(s,x), .cons g t .nil, nv.cons "%", .here⟩

/-- `atomize` extends the environment by at most one name. -/
theorem atomize_names_covers {s : Sig} (g : LetTag) (nv : NameEnv s) (t : PTm s) :
    Covers nv.names (atomize g nv t).names.names := by
  cases t with
  | path _ => exact Covers.rfl' _
  | lam _ _ => exact Covers.tail _ _
  | obj _ _ => exact Covers.tail _ _
  | app _ _ => exact Covers.tail _ _
  | proj _ _ => exact Covers.tail _ _
  | «let» _ _ _ _ => exact Covers.tail _ _

/-! ## The resolvers

Each is structural on the surface phrase.  The clause order matches
`SType.Scoped` and `SType.LabelsIn`.

`ν(x : T. d)` resolves its annotation under the self binder.
`let x : U = t in u` resolves `U` at the outer signature.  Operands are
evaluated left to right, as the spines are appended in that order.

`(t : T)` resolves to `let % : T = t in %`, the same term a written
`let y : T = t in y` gives except for the tag.  It needs no form of its own in
`PTm`. -/

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

/-- Resolve an optional surface type.  An empty slot stays empty, and a
written type that does not resolve fails the whole. -/
def resolveTyOpt {s : Sig} (Λ : LabelTable) (nv : NameEnv s) :
    Option SType → Option (Option (Ty s))
  | none => some none
  | some T => (resolveTy Λ nv T).map some

mutual
/-- Resolve a surface term, inserting `let` bindings for the two direct style
forms.  The result is in monadic normal form by construction.  An empty slot of
the source is an empty slot of the result.  An inserted binding at an operand is
tagged `arg`, one at an operator or a receiver `recv`, and an ascription is a
`let` tagged `asc` whose body is its own binder. -/
def resolveTm {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (e : STm) : Option (PTm s) :=
  match e with
  | .var x => do
      let i ← nv.find? x
      pure (.path i)
  | .lam x T t => do
      let T' ← resolveTyOpt Λ nv T
      let t' ← resolveTm Λ (nv.cons x) t
      pure (.lam T' t')
  | .obj x T d => do
      let T' ← resolveTyOpt Λ (nv.cons x) T
      let d' ← resolveDefs Λ (nv.cons x) d
      pure (.obj T' d')
  | .app t u => do
      let t₀ ← resolveTm Λ nv t
      let a := atomize .recv nv t₀
      let u₀ ← resolveTm Λ a.names u
      let b := atomize .arg a.names u₀
      pure ((a.spine.append b.spine).plug (.app (b.spine.rename.var a.var) b.var))
  | .proj t a => do
      let t₀ ← resolveTm Λ nv t
      let c := atomize .recv nv t₀
      let l ← labelTrm? Λ a
      pure (c.spine.plug (.proj c.var l))
  | .«let» x ann t u => do
      let ann' ← resolveTyOpt Λ nv ann
      let t' ← resolveTm Λ nv t
      let u' ← resolveTm Λ (nv.cons x) u
      pure (.let .written ann' t' u')
  | .asc t T => do
      let t' ← resolveTm Λ nv t
      let T' ← resolveTy Λ nv T
      pure (.let .asc (some T') t' (.path .here))
termination_by structural e
/-- Resolve a surface definition list. -/
def resolveDefs {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (d : SDefs) : Option (PDefs s) :=
  match d with
  | .typ A T => do
      let l ← labelTyp? Λ A
      let T' ← resolveTy Λ nv T
      pure (.typ l T')
  | .trm a T t => do
      let l ← labelTrm? Λ a
      let T' ← resolveTyOpt Λ nv T
      let t' ← resolveTm Λ nv t
      pure (.trm l T' t')
  | .and d e => do
      let d' ← resolveDefs Λ nv d
      let e' ← resolveDefs Λ nv e
      pure (.and d' e')
termination_by structural d
end

/-- Resolve a program under the names of a context, innermost first, with every
slot written.  A program with an empty slot resolves to `none` here. -/
def resolveIn {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (e : STm) : Option (ATm s) :=
  (resolveTm Λ nv e).bind PTm.full?

/-- Resolve a closed surface program to a partial term. -/
def resolveP (Λ : LabelTable) (e : STm) : Option (PTm []) := resolveTm Λ .nil e

/-- Resolve a closed surface program with every slot written.  A program with an
empty slot resolves to `none` here, and to its partial term by `resolveP`. -/
def resolve (Λ : LabelTable) (e : STm) : Option (ATm []) := (resolveP Λ e).bind PTm.full?

/-- `resolve` is `resolveP` followed by `PTm.full?`. -/
theorem resolve_eq (Λ : LabelTable) (e : STm) : resolve Λ e = (resolveP Λ e).bind PTm.full? :=
  rfl

/-! ## Totality

Resolution succeeds on a phrase whose free names are in the environment and
whose labels are in the table at the right sort.  In the two direct style
clauses, `atomize_names_covers` carries the scoping hypothesis across. -/

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

/-- An optional type resolves on the same side conditions.  An empty slot always
does. -/
theorem resolveTyOpt_isSome (T : Option SType) {s : Sig} (Λ : LabelTable) (nv : NameEnv s) :
    SType.ScopedOpt nv.names T = true → SType.LabelsInOpt Λ T = true →
    (resolveTyOpt Λ nv T).isSome = true := by
  intro hs hl
  cases T with
  | none => rfl
  | some T =>
    have h1 := resolveTy_isSome T Λ nv hs hl
    simp only [resolveTyOpt]
    cases hT : resolveTy Λ nv T with
    | none => rw [hT] at h1; simp at h1
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
      have h1 := resolveTyOpt_isSome T Λ nv hs.1 hl.1
      have h2 := resolveTm_isSome t Λ (nv.cons x) hs.2 hl.2
      simp only [resolveTm]
      cases hT : resolveTyOpt Λ nv T with
      | none => rw [hT] at h1; simp at h1
      | some _ =>
        cases ht : resolveTm Λ (nv.cons x) t with
        | none => rw [ht] at h2; simp at h2
        | some _ => rfl
  | .obj x T d, _, Λ, nv, hs, hl => by
      simp only [STm.Scoped, STm.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolveTyOpt_isSome T Λ (nv.cons x) hs.1 hl.1
      have h2 := resolveDefs_isSome d Λ (nv.cons x) hs.2 hl.2
      simp only [resolveTm]
      cases hT : resolveTyOpt Λ (nv.cons x) T with
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
        have h2 := resolveTm_isSome u Λ (atomize .recv nv t₀).names
          (STm.Scoped_covers u (atomize_names_covers .recv nv t₀) hs.2) hl.2
        cases hu : resolveTm Λ (atomize .recv nv t₀).names u with
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
        simp only [resolveTm, resolveTyOpt]
        cases ht : resolveTm Λ nv t with
        | none => rw [ht] at h2; simp at h2
        | some _ =>
          cases hu : resolveTm Λ (nv.cons x) u with
          | none => rw [hu] at h3; simp at h3
          | some _ => rfl
      | some U =>
        have h1 := resolveTy_isSome U Λ nv hs.1.1 hl.1.1
        simp only [resolveTm, resolveTyOpt]
        cases hU : resolveTy Λ nv U with
        | none => rw [hU] at h1; simp at h1
        | some _ =>
          cases ht : resolveTm Λ nv t with
          | none => rw [ht] at h2; simp at h2
          | some _ =>
            cases hu : resolveTm Λ (nv.cons x) u with
            | none => rw [hu] at h3; simp at h3
            | some _ => rfl
  | .asc t T, _, Λ, nv, hs, hl => by
      simp only [STm.Scoped, STm.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolveTm_isSome t Λ nv hs.1 hl.1
      have h2 := resolveTy_isSome T Λ nv hs.2 hl.2
      simp only [resolveTm]
      cases ht : resolveTm Λ nv t with
      | none => rw [ht] at h1; simp at h1
      | some _ =>
        cases hT : resolveTy Λ nv T with
        | none => rw [hT] at h2; simp at h2
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
  | .trm a T t, _, Λ, nv, hs, hl => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, Bool.and_eq_true] at hs hl
      have h1 := resolveTyOpt_isSome T Λ nv hs.1 hl.1.2
      have h2 := resolveTm_isSome t Λ nv hs.2 hl.2
      simp only [resolveDefs]
      cases ha : labelTrm? Λ a with
      | none => rw [ha] at hl; simp at hl
      | some _ =>
        cases hT : resolveTyOpt Λ nv T with
        | none => rw [hT] at h1; simp at h1
        | some _ =>
          cases ht : resolveTm Λ nv t with
          | none => rw [ht] at h2; simp at h2
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
    (u : PTm s''), (sp.append sp').plug u = sp.plug (sp'.plug u)
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .cons g t sp, sp', u => by
      show PTm.let g none t ((sp.append sp').plug u) = _
      rw [Spine.plug_append sp sp' u]
      rfl

/-- The weakening of an appended spine is the composite of the two. -/
theorem Spine.rename_append : ∀ {s s' s'' : Sig} (sp : Spine s s') (sp' : Spine s' s''),
    (sp.append sp').rename = Rename.comp sp.rename sp'.rename
  | _, _, _, .nil, sp' => Rename.funext' (fun _ => rfl)
  | _, _, _, .cons _ _ sp, sp' => by
      show Rename.comp Rename.succ ((sp.append sp').rename) = _
      rw [Spine.rename_append sp sp']
      exact Rename.funext' (fun _ => rfl)

/-- No insertion: a variable is not bound again. -/
theorem atomize_var {s : Sig} (g : LetTag) (nv : NameEnv s) (i : BVar s .var) :
    atomize g nv (.path i) = ⟨s, .nil, nv, i⟩ := rfl

/-! ## The version's programs

Every program of `Notation.lean` resolves, and its erasure is the term of the
version's derivation in `lean/Coercions/Paths/DotMNF/Examples.lean`.  Each
check is a `decide`.

The label table is written out because the version gives two names one label in
places (`lC` and `X4_lType` are both `.typ 3`).  The label of gDOT Fig. 2 is
named `Type`, written `«Type»` in the notation. -/

open Paths.DotMNF.Examples

/-- The labels of the version's examples, by the names the programs write. -/
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

/-- Totality applies to E1p. -/
example : (resolveTm pathsTable .nil E1p_src).isSome = true :=
  resolveTm_isSome E1p_src pathsTable .nil (by decide) (by decide)

/-! ### X3, with `x` bound by a lambda

The version types X3 in the context `x : {val a : {val b : ⊤}}`.  Written
closed, that entry becomes a lambda.  The direct-style `x.a.b` inserts the
`let` that X3 writes by hand. -/

example : (resolve pathsTable X3_src).map ATm.erase =
    some (.val (.lam X3_A (versionTerm X3))) := by decide

example : (resolve pathsTable X3d_src).map ATm.erase =
    some (.val (.lam X3_A (versionTerm X3))) := by decide

/-- The direct-style path and the hand written `let` resolve to one term. -/
example : resolve pathsTable X3d_src = resolve pathsTable X3_src := by decide

/-- X3 written open, resolved under the name of its one context entry. -/
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
lambda. -/
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
lambda. -/
example : (resolve pathsTable X4_src).map ATm.erase =
    some (.val (.lam .top (versionTerm X4_lit0))) := by decide

/-- P3e's third member is the term label 2, named `v` in the table. -/
example : (resolve pathsTable P3e_src).map ATm.erase = some (versionTerm P3e_lit) := by decide

/-! ### gDOT Fig. 2 and pDOT Fig. 1 -/

/-- The program resolves to the version's `Fig2_prog`. -/
example : (resolve pathsTable Fig2_src).map ATm.erase = some Fig2_prog := by decide

/-- The two nested literals carry the bodies of the two stable fields of
`pcore`'s self type, as `DefsTy.trmObj` requires. -/
example : (match resolve pathsTable Fig2_src with
    | some (.let _ _ (.let _ (.obj T (.and (.trm _ (.obj Tt _)) (.trm _ (.obj Ty _)))) _)) =>
        decide (T = .and (.vfld Fig2_ltypes (.mu Tt)) (.vfld X4_lsymbols (.mu Ty)))
    | _ => false) = true := by decide

/-- The self annotation of `pcore` resolves to the version's `Fig2_pBody`. -/
example : (match resolve pathsTable Fig2_src with
    | some (.let _ _ (.let _ (.obj T _) _)) => decide (T = Fig2_pBody)
    | _ => false) = true := by decide

/-- Fig. 1 is Fig. 2 with `tpe : p.types.Type`.  It resolves to `Fig1_prog`. -/
example : (resolve pathsTable Fig1_src).map ATm.erase = some Fig1_prog := by decide

/-! ### R1, R2 and R7

R1 and R2 reach a singleton's alias through a type member whose bounds are
singletons.  R7 is the direct-style path whose inserted binder is opaque.  Here
they only resolve.  Typing them is the typer's question. -/

example : (resolve pathsTable R1_src).isSome = true := by decide

example : (resolve pathsTable R2_src).isSome = true := by decide

example : (resolve pathsTable R7_src).isSome = true := by decide

/-! ## Partial programs

A program with an empty slot resolves by `resolveP` to a partial term with that
slot empty, and `resolve` returns `none` on it.  The checks below show the empty
slots and the tags.  Then each example program loses some of its annotations:
the erased source resolves to the resolved written program with the same
annotations erased by `PTm.eraseDoms`, `PTm.eraseSelf` or `PTm.eraseArgs`. -/

example : resolveP pathsTable (pdot% λx. x) = some (.lam none (.path .here)) := rfl

example : resolve pathsTable (pdot% λx. x) = none := rfl

/-- The body of `λx.` takes a path, which stays one projection off the
variable. -/
example : resolveP pathsTable (pdot% λx. x.a) = some (.lam none (.proj .here la)) := rfl

/-- A lambda passed as an argument is bound by an `arg` binding. -/
example : resolveP pathsTable (pdot% λ(f : ⊤). f (λx. x)) =
    some (.lam (some .top)
      (.let .arg none (.lam none (.path .here)) (.app (.there .here) .here))) := rfl

/-- An operator that is not a variable is bound by a `recv` binding. -/
example : resolveP pathsTable (pdot% λ(f : ⊤). λ(x : ⊤). f x x) =
    some (.lam (some .top) (.lam (some .top)
      (.let .recv none (.app (.there .here) .here) (.app .here (.there .here))))) := rfl

/-- The prefix of a path in term position is bound by a `recv` binding. -/
example : (resolveP pathsTable X3d_src).map PTm.eraseDoms =
    some (.lam none (.let .recv none (.proj .here la) (.proj .here lb))) := rfl

/-- The ascription is a `let` at its type whose body is the binder. -/
example : resolveP pathsTable (pdot% λ(y : ⊤). (λx. x : ∀(z : ⊤) ⊤)) =
    some (.lam (some .top)
      (.let .asc (some (.all .top .top)) (.lam none (.path .here)) (.path .here))) := rfl

/-- An ascription at a singleton type names the path's root. -/
example : resolveP pathsTable (pdot% λ(y : ⊤). (y : y.type)) =
    some (.lam (some .top)
      (.let .asc (some (.sngl (.var .here))) (.path .here) (.path .here))) := rfl

example : resolveP pathsTable (pdot% ν(x. {a : ⊤ = x})) =
    some (.obj none (.trm la (some .top) (.path .here))) := rfl

/-- A literal without a self type nested in another one. -/
example : resolveP pathsTable (pdot% ν(x. {c = ν(y. {type A = ⊤})})) =
    some (.obj none (.trm lc none (.obj none (.typ lA .top)))) := rfl

/-- A written field type resolves under the self binder, so it may name a path
off the self. -/
example : resolveP pathsTable (pdot% ν(x. {type A = ⊤} ∧ {a : x.A = x})) =
    some (.obj none (.and (.typ lA .top) (.trm la (some (.sel (.var .here) lA)) (.path .here)))) :=
  rfl

/-- A field type under a written self type resolves.  The elaborator compares
it with the self type's field at that label. -/
example : (resolveP pathsTable (pdot% ν(s : {a : ⊤}. {a : ⊤ = s}))).isSome = true := rfl

/-- E2 with the lambda domain erased. -/
def E2_srcD : STm :=
  pdot% let x = ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}.
                  {type A = ∀(y : s.A) s.A} ∧ {a = λy. y})
        in let f = x.a in f f

/-- E2 with the self type erased. -/
def E2_srcS : STm :=
  pdot% let x = ν(s. {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y}) in let f = x.a in f f

/-- E5 with the self type erased. -/
def E5_srcS : STm :=
  pdot% λ(w : {A : ⊤..⊤}). let f = λ(v : {A : ⊤..⊤}). ν(z. {a = v}) in let o = f w in o.a

/-- E6 with the self type erased. -/
def E6_srcS : STm := pdot% λ(n : {a : ⊤}). ν(x. {type T = {a : ⊤}} ∧ {v = n})

/-- E7 with the self type erased. -/
def E7_srcS : STm := pdot% ν(x. {type A = x.B} ∧ {type B = x.A})

/-- E8 with both lambda domains erased. -/
def E8_srcD : STm := pdot% λx. λy. y.a

/-- E9 with the lambda domain erased. -/
def E9_srcD : STm :=
  pdot% let q = ν(q : {B : {b : ⊤}..{b : ⊤}}. {type B = {b : ⊤}}) in
        let x = ν(x : {a : q.type}. {a = q}) in
        let y = x.a in
        λz. let w = z in w

/-- X1 with both self types erased. -/
def X1_srcS : STm := pdot% ν(z. {c = ν(w. {type A = z.B})} ∧ {type B = z.c.A})

/-- E11 with every self type erased. -/
def E11_srcS : STm :=
  pdot% let z = ν(z. {type C = ⊤}) in ν(x. {a = ν(w. {type A = ⊤})} ∧ {b = z})

/-- A callback whose formal names a singleton, its domain written. -/
def K1s_src : STm :=
  pdot% λ(w : ⊤). λ(k : ∀(h : ∀(x : w.type) ⊤) ⊤). k (λ(y : w.type). y)

/-- The same callback with its domain erased. -/
def K1s_srcA : STm := pdot% λ(w : ⊤). λ(k : ∀(h : ∀(x : w.type) ⊤) ⊤). k (λy. y)

/-- A callback whose formal names a path through a stable field. -/
def K1p_src : STm :=
  pdot% λ(m : {val c : μ(z. {A : ⊤ .. ⊤})}). λ(k : ∀(h : ∀(x : m.c.A) ⊤) ⊤). k (λ(y : m.c.A). y)

/-- The same callback with its domain erased. -/
def K1p_srcA : STm :=
  pdot% λ(m : {val c : μ(z. {A : ⊤ .. ⊤})}). λ(k : ∀(h : ∀(x : m.c.A) ⊤) ⊤). k (λy. y)

/-- A callee with two function types whose formals have one parameter type. -/
def K2_src : STm :=
  pdot% λ(g : (∀(h : ∀(x : ⊤) ⊤) ⊤) ∧ (∀(h : ∀(x : ⊤) {a : ⊤}) ⊤)). g (λ(x : ⊤). x)

/-- The same call with the argument's domain erased. -/
def K2_srcA : STm :=
  pdot% λ(g : (∀(h : ∀(x : ⊤) ⊤) ⊤) ∧ (∀(h : ∀(x : ⊤) {a : ⊤}) ⊤)). g (λx. x)

/-- A callee with two function types whose formals have two parameter types. -/
def K3_src : STm :=
  pdot% λ(g : (∀(h : ∀(x : ⊤) ⊤) ⊤) ∧ (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤)). g (λ(x : ⊤). x)

/-- The same call with the argument's domain erased. -/
def K3_srcA : STm :=
  pdot% λ(g : (∀(h : ∀(x : ⊤) ⊤) ⊤) ∧ (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤)). g (λx. x)

example : (resolveP pathsTable E2_src).map PTm.eraseDoms = resolveP pathsTable E2_srcD := rfl

example : (resolveP pathsTable E2_src).map PTm.eraseSelf = resolveP pathsTable E2_srcS := rfl

example : (resolveP pathsTable E5_src).map PTm.eraseSelf = resolveP pathsTable E5_srcS := rfl

example : (resolveP pathsTable E6_src).map PTm.eraseSelf = resolveP pathsTable E6_srcS := rfl

example : (resolveP pathsTable E7_src).map PTm.eraseSelf = resolveP pathsTable E7_srcS := rfl

example : (resolveP pathsTable E8_src).map PTm.eraseDoms = resolveP pathsTable E8_srcD := rfl

example : (resolveP pathsTable E9_src).map PTm.eraseDoms = resolveP pathsTable E9_srcD := rfl

example : (resolveP pathsTable X1_src).map PTm.eraseSelf = resolveP pathsTable X1_srcS := rfl

example : (resolveP pathsTable E11_src).map PTm.eraseSelf = resolveP pathsTable E11_srcS := rfl

example : (resolveP pathsTable K1s_src).map PTm.eraseArgs = resolveP pathsTable K1s_srcA := rfl

example : (resolveP pathsTable K1p_src).map PTm.eraseArgs = resolveP pathsTable K1p_srcA := rfl

example : (resolveP pathsTable K2_src).map PTm.eraseArgs = resolveP pathsTable K2_srcA := rfl

example : (resolveP pathsTable K3_src).map PTm.eraseArgs = resolveP pathsTable K3_srcA := rfl

/-- E2 binds its lambda with a `let` and passes none, so erasing the domains of
arguments leaves it as it is. -/
example : (resolveP pathsTable E2_src).map PTm.eraseArgs = resolveP pathsTable E2_src := rfl

/-- The written E2 is full, so `resolve` gives the annotated term above.  The
erased ones are not full. -/
example : (resolveP pathsTable E2_srcD).bind PTm.full? = none := rfl

example : (resolveP pathsTable E2_srcS).bind PTm.full? = none := rfl

/-- The written callbacks are full, and `resolve` sees no empty slot. -/
example : (resolve pathsTable K1s_src).isSome = true := rfl

example : resolve pathsTable K1s_srcA = none := rfl

end PathsFrontend
