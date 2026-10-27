import Coercions.PDot.Frontend.Ann
import Coercions.PDot.Frontend.Surface

/-!
# Name resolution for pDOT

`resolvePath`, `resolveTy`, `resolveTm` and `resolveDefs` take a surface phrase
to the partial terms of `Ann.lean`.  They are the only place where a name
becomes an index.  A slot the programmer left empty stays empty, for the
elaborator to fill.  `resolveP` returns that partial term.  `resolve` keeps
only a program with every slot written, through `PTm.full?`.

A `NameEnv` lists one name per binder, innermost first, and the aliases of
module paths (plan XI D-12).  The innermost binding wins.  A binder answers its
variable, and an alias answers its path.  A path resolves its root by the
environment and its field steps by the label table at the term sort.  A type
label is read at the type sort.

Paths are terms (plan XI D-4).  A selection on a path resolves to a longer
path, and an application keeps its path operands.  An operand that is no path
is bound by one inserted `let`, tagged `arg` at the operand of an application
and `recv` at an operator or a receiver.  The inserted bindings form an
explicit `Spine`, which keeps the resolvers structural.  The inserted binder is
named `"%"`, which nothing looks up.

The module proves totality on scoped, well labelled phrases whose fields have a
right shape, the two spine equations, and the no insertion property: a phrase
whose operands are paths resolves with no inserted `let`.

Nothing here belongs to the metatheory.
-/

namespace PDotFrontend

open Paths.FCdot (Sig BVar Kind Label Rename Path)
open PDot.Source (Ty Dec)

/-! ## Name environments -/

/-- The surface names of the binders of a signature, innermost first, with the
aliases of module paths. -/
inductive NameEnv : Sig → Type where
  /-- The empty environment. -/
  | nil : NameEnv []
  /-- One more binder, with its surface name. -/
  | cons : NameEnv s → String → NameEnv (s,x)
  /-- A name that stands for a path, with no binder (plan XI D-12). -/
  | alias : NameEnv s → String → Path s → NameEnv s

/-- The path a name stands for, innermost binding first.  A binder gives its
variable, an alias its path. -/
def NameEnv.find? : {s : Sig} → NameEnv s → String → Option (Path s)
  | _, .nil, _ => none
  | _, .cons nv y, z => if z = y then some (.var .here) else (nv.find? z).map (·.rename Rename.succ)
  | _, .alias nv y p, z => if z = y then some p else nv.find? z
termination_by structural _ nv => nv

/-- The names of the environment, innermost first, aliases included. -/
def NameEnv.names : {s : Sig} → NameEnv s → List String
  | _, .nil => []
  | _, .cons nv y => y :: nv.names
  | _, .alias nv y _ => y :: nv.names
termination_by structural _ nv => nv

/-! ## Covering, the monotonicity of scoping

`resolveTm` resolves the operand of an application under the environment that
`atomize` returns, which is the given one plus at most one name.  The totality
proof therefore needs scoping to survive a larger name list. -/

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

/-- Scoping of a type survives a larger name list. -/
theorem SType.Scoped_covers : ∀ (T : SType) {Γ Γ' : List String}, Covers Γ Γ' →
    SType.Scoped Γ T = true → SType.Scoped Γ' T = true
  | .top, _, _, _, _ => rfl
  | .bot, _, _, _, _ => rfl
  | .typ _ S T, _, _, h, hs => by
      simp only [SType.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SType.Scoped_covers S h hs.1, SType.Scoped_covers T h hs.2⟩
  | .fld _ T, _, _, h, hs => SType.Scoped_covers T h hs
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
  | .proj t _, _, _, h, hs => by
      simp only [STm.Scoped] at hs ⊢
      exact STm.Scoped_covers t h hs
  | .«let» x ann t u, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨⟨SType.ScopedOpt_covers ann h hs.1.1, STm.Scoped_covers t h hs.1.2⟩,
        STm.Scoped_covers u (h.cons x) hs.2⟩
  | .asc t T, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨STm.Scoped_covers t h hs.1, SType.Scoped_covers T h hs.2⟩
  | .alias x p u, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SPath.Scoped_covers p h hs.1, STm.Scoped_covers u (h.cons x) hs.2⟩
  | .bind _ x t u, _, _, h, hs => by
      simp only [STm.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨STm.Scoped_covers t h hs.1, STm.Scoped_covers u (h.cons x) hs.2⟩
/-- Scoping of definitions survives a larger name list. -/
theorem SDefs.Scoped_covers : ∀ (d : SDefs) {Γ Γ' : List String}, Covers Γ Γ' →
    SDefs.Scoped Γ d = true → SDefs.Scoped Γ' d = true
  | .nil, _, _, _, _ => by simp only [SDefs.Scoped]
  | .typ ds _ T, _, _, h, hs => by
      simp only [SDefs.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨SDefs.Scoped_covers ds h hs.1, SType.Scoped_covers T h hs.2⟩
  | .trm ds _ T t, _, _, h, hs => by
      simp only [SDefs.Scoped, Bool.and_eq_true] at hs ⊢
      exact ⟨⟨SDefs.Scoped_covers ds h hs.1.1, SType.ScopedOpt_covers T h hs.1.2⟩,
        STm.Scoped_covers t h hs.2⟩
end

/-- A name in the environment resolves. -/
theorem NameEnv.find?_isSome : ∀ {s : Sig} (nv : NameEnv s) (x : String),
    nv.names.contains x = true → (nv.find? x).isSome = true
  | _, .nil, _, h => by simp [NameEnv.names] at h
  | _, .cons nv y, x, h => by
      show (if x = y then some (Path.var .here) else (nv.find? x).map (·.rename Rename.succ)).isSome = true
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
        | some _ => simp
  | _, .alias nv y p, x, h => by
      show (if x = y then some p else nv.find? x).isSome = true
      by_cases hxy : x = y
      · simp [hxy]
      · rw [if_neg hxy]
        have hy : (x == y) = false := by simp [hxy]
        have h' : nv.names.contains x = true := by
          simp only [NameEnv.names, List.contains_cons, hy, Bool.false_or] at h
          exact h
        exact NameEnv.find?_isSome nv x h'

/-! ## The spine of inserted bindings

A `Spine s s'` is a stack of `let` bindings that takes a term over `s'` to a
term over `s`.  `Spine.rename` moves a variable of `s` into `s'`.
`Rename.comp f g` is `g ∘ f`. -/

/-- A stack of inserted `let` bindings, each with its tag. -/
inductive Spine : Sig → Sig → Type where
  /-- No binding. -/
  | nil : Spine s s
  /-- One binding, then the rest under it. -/
  | cons : LetTag → PTm s → Spine (s,x) s' → Spine s s'

/-- Wrap a term of the inner signature in the bindings of the spine. -/
def Spine.plug : {s s' : Sig} → Spine s s' → PTm s' → PTm s
  | _, _, .nil, u => u
  | _, _, .cons g t sp, u => .«let» g none t (sp.plug u)
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

/-- A term in path position: the inserted bindings, the environment after them,
and the path that stands for the term. -/
structure Atomic (s : Sig) where
  /-- The signature after the insertions. -/
  sig : Sig
  /-- The insertions. -/
  spine : Spine s sig
  /-- The environment at that signature. -/
  names : NameEnv sig
  /-- The path standing for the term. -/
  path : Path sig

/-- A path stays.  Any other term is bound by one `let` with the tag `g`. -/
def atomize {s : Sig} (g : LetTag) (nv : NameEnv s) (t : PTm s) : Atomic s :=
  match t with
  | .path p => ⟨s, .nil, nv, p⟩
  | _ => ⟨(s,x), .cons g t .nil, nv.cons "%", .var .here⟩

/-- `atomize` extends the environment by at most one name. -/
theorem atomize_names_covers {s : Sig} (g : LetTag) (nv : NameEnv s) (t : PTm s) :
    Covers nv.names (atomize g nv t).names.names := by
  cases t with
  | path _ => exact Covers.rfl' _
  | app _ _ => exact Covers.tail _ _
  | lam _ _ => exact Covers.tail _ _
  | new _ _ => exact Covers.tail _ _
  | «let» _ _ _ _ => exact Covers.tail _ _

/-- No insertion: a path is not bound again. -/
theorem atomize_path {s : Sig} (g : LetTag) (nv : NameEnv s) (p : Path s) :
    atomize g nv (.path p) = ⟨s, .nil, nv, p⟩ := rfl

/-! ## The resolvers

Each is structural on the surface phrase.  `ν(x : T) {d}` resolves its self
type and its definitions under the self binder.  `let x : U = t in u` resolves
`U` at the outer signature.  Operands resolve left to right. -/

/-- Resolve a surface path: the root by the environment, every field step by
the table at the term sort. -/
def resolvePath {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (p : SPath) : Option (Path s) :=
  match p with
  | .var x => nv.find? x
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
      pure (.rcd (.typ l S' T'))
  | .fld a T => do
      let l ← labelTrm? Λ a
      let T' ← resolveTy Λ nv T
      pure (.rcd (.trm l T'))
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

/-- Resolve an optional surface type.  An empty slot stays empty, and a written
type that does not resolve fails the whole. -/
def resolveTyOpt {s : Sig} (Λ : LabelTable) (nv : NameEnv s) :
    Option SType → Option (Option (Ty s))
  | none => some none
  | some T => (resolveTy Λ nv T).map some

/-- The tag of a `bind`: `widen` for a widened `val`, `recv` for an unstable
prefix. -/
def SBind.tag : SBind → LetTag
  | .widen => .widen
  | .unstable => .recv

mutual
/-- Resolve a surface term.  A selection on a path is a longer path.  An operand
that is no path is bound by one inserted `let`.  An ascription is a `let`
tagged `asc` whose body is its own binder.  An alias resolves its path and
stands for it in the body. -/
def resolveTm {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (e : STm) : Option (PTm s) :=
  match e with
  | .var x => (nv.find? x).map PTm.path
  | .lam x T t => do
      let T' ← resolveTyOpt Λ nv T
      let t' ← resolveTm Λ (nv.cons x) t
      pure (.lam T' t')
  | .obj x T d => do
      let T' ← resolveTyOpt Λ (nv.cons x) T
      let d' ← resolveDefs Λ (nv.cons x) d
      pure (.new T' d')
  | .app t u => do
      let t₀ ← resolveTm Λ nv t
      let a := atomize .recv nv t₀
      let u₀ ← resolveTm Λ a.names u
      let b := atomize .arg a.names u₀
      pure ((a.spine.append b.spine).plug (.app (a.path.rename b.spine.rename) b.path))
  | .proj t a => do
      let t₀ ← resolveTm Λ nv t
      let c := atomize .recv nv t₀
      let l ← labelTrm? Λ a
      pure (c.spine.plug (.path (c.path.sel l)))
  | .«let» x ann t u => do
      let ann' ← resolveTyOpt Λ nv ann
      let t' ← resolveTm Λ nv t
      let u' ← resolveTm Λ (nv.cons x) u
      pure (.«let» .written ann' t' u')
  | .asc t T => do
      let t' ← resolveTm Λ nv t
      let T' ← resolveTy Λ nv T
      pure (.«let» .asc (some T') t' (.path (.var .here)))
  | .alias x p u => do
      let p' ← resolvePath Λ nv p
      resolveTm Λ (nv.alias x p') u
  | .bind k x t u => do
      let t' ← resolveTm Λ nv t
      let u' ← resolveTm Λ (nv.cons x) u
      pure (.«let» k.tag none t' u')
termination_by structural e
/-- Resolve surface definitions.  A field holding a lambda is `PDef.lam`, one
holding a literal `PDef.new`, one holding a path `PDef.path`.  A written type
on a path field is dropped, after `FieldsOk` checked it.  A written type on a
literal field, and any other right side, gives `none`. -/
def resolveDefs {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (d : SDefs) : Option (PDefs s) :=
  match d with
  | .nil => some .nil
  | .typ ds A T => do
      let ds' ← resolveDefs Λ nv ds
      let l ← labelTyp? Λ A
      let T' ← resolveTy Λ nv T
      pure (.cons ds' (.typ l T'))
  | .trm ds a T (.lam y D b) => do
      let ds' ← resolveDefs Λ nv ds
      let l ← labelTrm? Λ a
      let T' ← resolveTyOpt Λ nv T
      let D' ← resolveTyOpt Λ nv D
      let b' ← resolveTm Λ (nv.cons y) b
      pure (.cons ds' (.lam l T' D' b'))
  | .trm ds a T (.obj y S e) => do
      let ds' ← resolveDefs Λ nv ds
      let l ← labelTrm? Λ a
      match T with
      | some _ => none
      | none =>
        let S' ← resolveTyOpt Λ (nv.cons y) S
        let e' ← resolveDefs Λ (nv.cons y) e
        pure (.cons ds' (.new l S' e'))
  | .trm ds a _ t => do
      let ds' ← resolveDefs Λ nv ds
      let l ← labelTrm? Λ a
      let p ← t.toPath?
      let p' ← resolvePath Λ nv p
      pure (.cons ds' (.path l p'))
termination_by structural d
end

/-- Resolve a program under the names of a context, with every slot written. -/
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


/-! ## Paths in term position -/

/-- A term that is a path has a surface path. -/
theorem STm.isPath_toPath? : ∀ (t : STm), t.isPath = true → ∃ p, t.toPath? = some p
  | .var x, _ => ⟨.var x, rfl⟩
  | .proj t a, h => by
      have ⟨p, hp⟩ := STm.isPath_toPath? t h
      exact ⟨p.sel a, by simp [STm.toPath?, hp]⟩

/-- The surface path of a scoped term is scoped. -/
theorem STm.toPath?_Scoped : ∀ (t : STm) {Γ : List String} {p : SPath}, t.toPath? = some p →
    STm.Scoped Γ t = true → SPath.Scoped Γ p = true
  | .var x, _, _, hp, hs => by
      simp only [STm.toPath?, Option.some.injEq] at hp
      subst hp
      simpa [STm.Scoped, SPath.Scoped] using hs
  | .proj t a, _, _, hp, hs => by
      simp only [STm.toPath?] at hp
      cases hq : t.toPath? with
      | none => rw [hq] at hp; simp at hp
      | some q =>
        rw [hq] at hp
        simp only [Option.map_some, Option.some.injEq] at hp
        subst hp
        simp only [STm.Scoped] at hs
        simp only [SPath.Scoped]
        exact STm.toPath?_Scoped t hq hs

/-- The surface path of a well labelled term is well labelled. -/
theorem STm.toPath?_LabelsIn : ∀ (t : STm) {Λ : LabelTable} {p : SPath}, t.toPath? = some p →
    STm.LabelsIn Λ t = true → SPath.LabelsIn Λ p = true
  | .var x, _, _, hp, _ => by
      simp only [STm.toPath?, Option.some.injEq] at hp
      subst hp
      rfl
  | .proj t a, _, _, hp, hl => by
      simp only [STm.toPath?] at hp
      cases hq : t.toPath? with
      | none => rw [hq] at hp; simp at hp
      | some q =>
        rw [hq] at hp
        simp only [Option.map_some, Option.some.injEq] at hp
        subst hp
        simp only [STm.LabelsIn, Bool.and_eq_true] at hl
        simp only [SPath.LabelsIn, Bool.and_eq_true]
        exact ⟨STm.toPath?_LabelsIn t hq hl.1, hl.2⟩

/-- A field that is no lambda and no literal, with a right shape, holds a
path. -/
theorem fieldShape_path (T : Option SType) (t : STm)
    (hlam : ∀ y D b, t ≠ .lam y D b) (hobj : ∀ y S e, t ≠ .obj y S e) :
    fieldShape T t = true → ∃ p, t.toPath? = some p := by
  intro h
  cases T with
  | none =>
    cases t with
    | lam y D b => exact absurd rfl (hlam y D b)
    | obj y S e => exact absurd rfl (hobj y S e)
    | _ => exact STm.isPath_toPath? _ (by simpa [fieldShape] using h)
  | some U =>
    cases t with
    | lam y D b => exact absurd rfl (hlam y D b)
    | obj y S e => exact absurd rfl (hobj y S e)
    | _ =>
      simp only [fieldShape] at h
      split at h
      · exact ⟨_, by assumption⟩
      · simp at h

/-! ## Totality

Resolution succeeds on a phrase whose free names are in the environment, whose
labels are in the table at the right sort, and whose fields have a right shape.
In the two clauses that atomize, `atomize_names_covers` carries the scoping
hypothesis across. -/

/-- A scoped path whose field steps are term labels of the table resolves. -/
theorem resolvePath_isSome {s : Sig} (Λ : LabelTable) (nv : NameEnv s) : ∀ (p : SPath),
    SPath.Scoped nv.names p = true → SPath.LabelsIn Λ p = true →
    (resolvePath Λ nv p).isSome = true
  | .var x, hs, _ => by
      simp only [SPath.Scoped] at hs
      simp only [resolvePath]
      exact NameEnv.find?_isSome nv x hs
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

/-- The clause of a path field.  The clauses of a lambda field and a literal
field come first, so this one holds for a right side that is neither. -/
theorem resolveDefs_trm_path {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (ds : SDefs) (a : String)
    (T : Option SType) (t : STm)
    (hlam : ∀ y D b, t ≠ .lam y D b) (hobj : ∀ y S e, t ≠ .obj y S e) :
    resolveDefs Λ nv (.trm ds a T t) = (do
      let ds' ← resolveDefs Λ nv ds
      let l ← labelTrm? Λ a
      let p ← t.toPath?
      let p' ← resolvePath Λ nv p
      pure (.cons ds' (.path l p'))) := by
  cases t with
  | lam y D b => exact absurd rfl (hlam y D b)
  | obj y S e => exact absurd rfl (hobj y S e)
  | _ => simp only [resolveDefs]

mutual
/-- A scoped, well labelled term whose fields have a right shape resolves. -/
theorem resolveTm_isSome : ∀ (e : STm) {s : Sig} (Λ : LabelTable) (nv : NameEnv s),
    STm.Scoped nv.names e = true → STm.LabelsIn Λ e = true → STm.FieldsOk e = true →
    (resolveTm Λ nv e).isSome = true
  | .var x, _, Λ, nv, hs, _, _ => by
      simp only [STm.Scoped] at hs
      simp only [resolveTm, Option.isSome_map]
      exact NameEnv.find?_isSome nv x hs
  | .lam x T t, _, Λ, nv, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FieldsOk, Bool.and_eq_true] at hs hl hf
      have h1 := resolveTyOpt_isSome T Λ nv hs.1 hl.1
      have h2 := resolveTm_isSome t Λ (nv.cons x) hs.2 hl.2 hf
      simp only [resolveTm]
      cases hT : resolveTyOpt Λ nv T with
      | none => rw [hT] at h1; simp at h1
      | some _ =>
        cases ht : resolveTm Λ (nv.cons x) t with
        | none => rw [ht] at h2; simp at h2
        | some _ => rfl
  | .obj x T d, _, Λ, nv, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FieldsOk, Bool.and_eq_true] at hs hl hf
      have h1 := resolveTyOpt_isSome T Λ (nv.cons x) hs.1 hl.1
      have h2 := resolveDefs_isSome d Λ (nv.cons x) hs.2 hl.2 hf
      simp only [resolveTm]
      cases hT : resolveTyOpt Λ (nv.cons x) T with
      | none => rw [hT] at h1; simp at h1
      | some _ =>
        cases hd : resolveDefs Λ (nv.cons x) d with
        | none => rw [hd] at h2; simp at h2
        | some _ => rfl
  | .app t u, _, Λ, nv, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FieldsOk, Bool.and_eq_true] at hs hl hf
      have h1 := resolveTm_isSome t Λ nv hs.1 hl.1 hf.1
      simp only [resolveTm]
      cases ht : resolveTm Λ nv t with
      | none => rw [ht] at h1; simp at h1
      | some t₀ =>
        have h2 := resolveTm_isSome u Λ (atomize .recv nv t₀).names
          (STm.Scoped_covers u (atomize_names_covers .recv nv t₀) hs.2) hl.2 hf.2
        cases hu : resolveTm Λ (atomize .recv nv t₀).names u with
        | none => rw [hu] at h2; simp at h2
        | some _ => simp [hu]
  | .proj t a, _, Λ, nv, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FieldsOk, Bool.and_eq_true] at hs hl hf
      have h1 := resolveTm_isSome t Λ nv hs hl.1 hf
      simp only [resolveTm]
      cases ht : resolveTm Λ nv t with
      | none => rw [ht] at h1; simp at h1
      | some _ =>
        cases ha : labelTrm? Λ a with
        | none => rw [ha] at hl; simp at hl
        | some _ => rfl
  | .«let» x ann t u, _, Λ, nv, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FieldsOk, Bool.and_eq_true] at hs hl hf
      have h1 := resolveTyOpt_isSome ann Λ nv hs.1.1 hl.1.1
      have h2 := resolveTm_isSome t Λ nv hs.1.2 hl.1.2 hf.1
      have h3 := resolveTm_isSome u Λ (nv.cons x) hs.2 hl.2 hf.2
      simp only [resolveTm]
      cases hA : resolveTyOpt Λ nv ann with
      | none => rw [hA] at h1; simp at h1
      | some _ =>
        cases ht : resolveTm Λ nv t with
        | none => rw [ht] at h2; simp at h2
        | some _ =>
          cases hu : resolveTm Λ (nv.cons x) u with
          | none => rw [hu] at h3; simp at h3
          | some _ => rfl
  | .asc t T, _, Λ, nv, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FieldsOk, Bool.and_eq_true] at hs hl hf
      have h1 := resolveTm_isSome t Λ nv hs.1 hl.1 hf
      have h2 := resolveTy_isSome T Λ nv hs.2 hl.2
      simp only [resolveTm]
      cases ht : resolveTm Λ nv t with
      | none => rw [ht] at h1; simp at h1
      | some _ =>
        cases hT : resolveTy Λ nv T with
        | none => rw [hT] at h2; simp at h2
        | some _ => rfl
  | .alias x p u, _, Λ, nv, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FieldsOk, Bool.and_eq_true] at hs hl hf
      have h1 := resolvePath_isSome Λ nv p hs.1 hl.1
      simp only [resolveTm]
      cases hp : resolvePath Λ nv p with
      | none => rw [hp] at h1; simp at h1
      | some p' =>
        exact resolveTm_isSome u Λ (nv.alias x p') hs.2 hl.2 hf
  | .bind k x t u, _, Λ, nv, hs, hl, hf => by
      simp only [STm.Scoped, STm.LabelsIn, STm.FieldsOk, Bool.and_eq_true] at hs hl hf
      have h1 := resolveTm_isSome t Λ nv hs.1 hl.1 hf.1
      have h2 := resolveTm_isSome u Λ (nv.cons x) hs.2 hl.2 hf.2
      simp only [resolveTm]
      cases ht : resolveTm Λ nv t with
      | none => rw [ht] at h1; simp at h1
      | some _ =>
        cases hu : resolveTm Λ (nv.cons x) u with
        | none => rw [hu] at h2; simp at h2
        | some _ => rfl
/-- Scoped, well labelled definitions whose fields have a right shape
resolve. -/
theorem resolveDefs_isSome : ∀ (d : SDefs) {s : Sig} (Λ : LabelTable) (nv : NameEnv s),
    SDefs.Scoped nv.names d = true → SDefs.LabelsIn Λ d = true → SDefs.FieldsOk d = true →
    (resolveDefs Λ nv d).isSome = true
  | .nil, _, _, _, _, _, _ => by simp only [resolveDefs, Option.isSome_some]
  | .typ ds A T, _, Λ, nv, hs, hl, hf => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, SDefs.FieldsOk, Bool.and_eq_true] at hs hl hf
      have h0 := resolveDefs_isSome ds Λ nv hs.1 hl.1.1 hf
      have h1 := resolveTy_isSome T Λ nv hs.2 hl.2
      simp only [resolveDefs]
      cases hd : resolveDefs Λ nv ds with
      | none => rw [hd] at h0; simp at h0
      | some _ =>
        cases hA : labelTyp? Λ A with
        | none => rw [hA] at hl; simp at hl
        | some _ =>
          cases hT : resolveTy Λ nv T with
          | none => rw [hT] at h1; simp at h1
          | some _ => rfl
  | .trm ds a T t, _, Λ, nv, hs, hl, hf => by
      simp only [SDefs.Scoped, SDefs.LabelsIn, SDefs.FieldsOk, Bool.and_eq_true] at hs hl hf
      have h0 := resolveDefs_isSome ds Λ nv hs.1.1 hl.1.1.1 hf.1.1
      have ha : (labelTrm? Λ a).isSome = true := hl.1.1.2
      match t, hs, hl, hf with
      | .lam y D b, hs, hl, hf =>
        simp only [STm.Scoped, STm.LabelsIn, STm.FieldsOk, Bool.and_eq_true] at hs hl hf
        have h1 := resolveTyOpt_isSome T Λ nv hs.1.2 hl.1.2
        have h2 := resolveTyOpt_isSome D Λ nv hs.2.1 hl.2.1
        have h3 := resolveTm_isSome b Λ (nv.cons y) hs.2.2 hl.2.2 hf.1.2
        simp only [resolveDefs]
        cases hd : resolveDefs Λ nv ds with
        | none => rw [hd] at h0; simp at h0
        | some _ =>
          cases ha' : labelTrm? Λ a with
          | none => rw [ha'] at ha; simp at ha
          | some _ =>
            cases hT : resolveTyOpt Λ nv T with
            | none => rw [hT] at h1; simp at h1
            | some _ =>
              cases hD : resolveTyOpt Λ nv D with
              | none => rw [hD] at h2; simp at h2
              | some _ =>
                cases hb : resolveTm Λ (nv.cons y) b with
                | none => rw [hb] at h3; simp at h3
                | some _ => rfl
      | .obj y S e, hs, hl, hf =>
        simp only [STm.Scoped, STm.LabelsIn, STm.FieldsOk, Bool.and_eq_true] at hs hl hf
        have h2 := resolveTyOpt_isSome S Λ (nv.cons y) hs.2.1 hl.2.1
        have h3 := resolveDefs_isSome e Λ (nv.cons y) hs.2.2 hl.2.2 hf.1.2
        cases T with
        | some U => simp [fieldShape, STm.toPath?] at hf
        | none =>
          simp only [resolveDefs]
          cases hd : resolveDefs Λ nv ds with
          | none => rw [hd] at h0; simp at h0
          | some _ =>
            cases ha' : labelTrm? Λ a with
            | none => rw [ha'] at ha; simp at ha
            | some _ =>
              cases hS : resolveTyOpt Λ (nv.cons y) S with
              | none => rw [hS] at h2; simp at h2
              | some _ =>
                cases he : resolveDefs Λ (nv.cons y) e with
                | none => rw [he] at h3; simp at h3
                | some _ => rfl
      | .var x, hs, hl, hf =>
        have hlam : ∀ y D b, STm.var x ≠ .lam y D b := fun _ _ _ h => STm.noConfusion h
        have hobj : ∀ y S e, STm.var x ≠ .obj y S e := fun _ _ _ h => STm.noConfusion h
        have hp : (STm.var x).toPath? = some (.var x) := rfl
        have h1 := resolvePath_isSome Λ nv (.var x)
          (STm.toPath?_Scoped _ hp hs.2) (STm.toPath?_LabelsIn _ hp hl.2)
        rw [resolveDefs_trm_path Λ nv ds a T _ hlam hobj, hp]
        cases hd : resolveDefs Λ nv ds with
        | none => rw [hd] at h0; simp at h0
        | some _ =>
          cases ha' : labelTrm? Λ a with
          | none => rw [ha'] at ha; simp at ha
          | some _ =>
            cases hq : resolvePath Λ nv (.var x) with
            | none => rw [hq] at h1; simp at h1
            | some _ => simp [hq]
      | .proj t' a', hs, hl, hf =>
        have hlam : ∀ y D b, STm.proj t' a' ≠ .lam y D b := fun _ _ _ h => STm.noConfusion h
        have hobj : ∀ y S e, STm.proj t' a' ≠ .obj y S e := fun _ _ _ h => STm.noConfusion h
        have ⟨p, hp⟩ := fieldShape_path T _ hlam hobj hf.2
        have h1 := resolvePath_isSome Λ nv p
          (STm.toPath?_Scoped _ hp hs.2) (STm.toPath?_LabelsIn _ hp hl.2)
        rw [resolveDefs_trm_path Λ nv ds a T _ hlam hobj, hp]
        cases hd : resolveDefs Λ nv ds with
        | none => rw [hd] at h0; simp at h0
        | some _ =>
          cases ha' : labelTrm? Λ a with
          | none => rw [ha'] at ha; simp at ha
          | some _ =>
            cases hq : resolvePath Λ nv p with
            | none => rw [hq] at h1; simp at h1
            | some _ => simp [hq]
      | .app _ _, _, _, hf => cases T <;> simp [fieldShape, STm.isPath, STm.toPath?] at hf
      | .«let» _ _ _ _, _, _, hf => cases T <;> simp [fieldShape, STm.isPath, STm.toPath?] at hf
      | .asc _ _, _, _, hf => cases T <;> simp [fieldShape, STm.isPath, STm.toPath?] at hf
      | .alias _ _ _, _, _, hf => cases T <;> simp [fieldShape, STm.isPath, STm.toPath?] at hf
      | .bind _ _ _ _, _, _, hf => cases T <;> simp [fieldShape, STm.isPath, STm.toPath?] at hf
end

/-! ## The two spine equations -/

/-- Plugging into an appended spine is plugging twice. -/
theorem Spine.plug_append : ∀ {s s' s'' : Sig} (sp : Spine s s') (sp' : Spine s' s'')
    (u : PTm s''), (sp.append sp').plug u = sp.plug (sp'.plug u)
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .cons g t sp, sp', u => by
      show PTm.«let» g none t ((sp.append sp').plug u) = _
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

/-! ## No insertion on path operands

A term in path position resolves to a path, so `atomize` binds nothing.  Under
`PathOperands` every operand and receiver is in path position, and no `bind`
occurs, so no `let` tagged `arg` or `recv` is made. -/

/-- A term that is a path resolves to a path. -/
theorem resolveTm_path : ∀ (e : STm) {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (p : PTm s),
    e.isPath = true → resolveTm Λ nv e = some p → ∃ q, p = .path q
  | .var x, _, Λ, nv, p, _, h => by
      simp only [resolveTm, Option.map_eq_some_iff] at h
      obtain ⟨q, _, rfl⟩ := h
      exact ⟨q, rfl⟩
  | .proj t a, _, Λ, nv, p, hp, h => by
      simp only [STm.isPath] at hp
      simp only [resolveTm] at h
      cases ht : resolveTm Λ nv t with
      | none => simp [ht] at h
      | some t₀ =>
        obtain ⟨q, rfl⟩ := resolveTm_path t Λ nv t₀ hp ht
        cases hl : labelTrm? Λ a with
        | none => simp [ht, hl] at h
        | some l =>
          simp only [ht, hl, atomize, Spine.plug, Option.bind_eq_bind, Option.bind_some,
            Option.pure_def, Option.some.injEq] at h
          exact ⟨q.sel l, h.symm⟩
  | .lam .., _, _, _, _, hp, _ => by simp [STm.isPath] at hp
  | .obj .., _, _, _, _, hp, _ => by simp [STm.isPath] at hp
  | .app .., _, _, _, _, hp, _ => by simp [STm.isPath] at hp
  | .«let» .., _, _, _, _, hp, _ => by simp [STm.isPath] at hp
  | .asc .., _, _, _, _, hp, _ => by simp [STm.isPath] at hp
  | .alias .., _, _, _, _, hp, _ => by simp [STm.isPath] at hp
  | .bind .., _, _, _, _, hp, _ => by simp [STm.isPath] at hp

mutual
/-- A term whose operands are paths resolves with no inserted `let`. -/
theorem resolve_noInsert : ∀ (e : STm) {s : Sig} (Λ : LabelTable) (nv : NameEnv s) (p : PTm s),
    STm.PathOperands e = true → resolveTm Λ nv e = some p → p.inserted = 0
  | .var x, _, Λ, nv, p, _, h => by
      simp only [resolveTm, Option.map_eq_some_iff] at h
      obtain ⟨q, _, rfl⟩ := h
      rfl
  | .lam x T t, _, Λ, nv, p, ho, h => by
      simp only [STm.PathOperands] at ho
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨T', _, t', ht, rfl⟩ := h
      simp only [PTm.inserted]
      exact resolve_noInsert t Λ (nv.cons x) t' ho ht
  | .obj x T d, _, Λ, nv, p, ho, h => by
      simp only [STm.PathOperands] at ho
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨T', _, d', hd, rfl⟩ := h
      simp only [PTm.inserted]
      exact resolveDefs_noInsert d Λ (nv.cons x) d' ho hd
  | .app t u, _, Λ, nv, p, ho, h => by
      simp only [STm.PathOperands, Bool.and_eq_true] at ho
      simp only [resolveTm] at h
      cases ht : resolveTm Λ nv t with
      | none => simp [ht] at h
      | some t₀ =>
        obtain ⟨q, rfl⟩ := resolveTm_path t Λ nv t₀ ho.1.1.1 ht
        cases hu : resolveTm Λ nv u with
        | none => simp [ht, atomize, hu] at h
        | some u₀ =>
          obtain ⟨q', rfl⟩ := resolveTm_path u Λ nv u₀ ho.1.1.2 hu
          simp only [ht, hu, atomize, Spine.append, Spine.plug, Option.bind_eq_bind,
            Option.bind_some, Option.pure_def, Option.some.injEq] at h
          subst h
          rfl
  | .proj t a, _, Λ, nv, p, ho, h => by
      simp only [STm.PathOperands, Bool.and_eq_true] at ho
      have ⟨q, hq⟩ := resolveTm_path (.proj t a) Λ nv p (by simpa [STm.isPath] using ho.1) h
      subst hq
      rfl
  | .«let» x ann t u, _, Λ, nv, p, ho, h => by
      simp only [STm.PathOperands, Bool.and_eq_true] at ho
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, t', ht, u', hu, rfl⟩ := h
      simp only [PTm.inserted, LetTag.counts]
      rw [resolve_noInsert t Λ nv t' ho.1 ht, resolve_noInsert u Λ (nv.cons x) u' ho.2 hu]
  | .asc t T, _, Λ, nv, p, ho, h => by
      simp only [STm.PathOperands] at ho
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨t', ht, _, _, rfl⟩ := h
      simp only [PTm.inserted, LetTag.counts]
      rw [resolve_noInsert t Λ nv t' ho ht]
  | .alias x q u, _, Λ, nv, p, ho, h => by
      simp only [STm.PathOperands] at ho
      simp only [resolveTm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨q', _, hu⟩ := h
      exact resolve_noInsert u Λ (nv.alias x q') p ho hu
  | .bind .., _, _, _, _, ho, _ => by simp [STm.PathOperands] at ho
/-- Definitions whose operands are paths resolve with no inserted `let`. -/
theorem resolveDefs_noInsert : ∀ (d : SDefs) {s : Sig} (Λ : LabelTable) (nv : NameEnv s)
    (ds : PDefs s), SDefs.PathOperands d = true → resolveDefs Λ nv d = some ds → ds.inserted = 0
  | .nil, _, Λ, nv, ds, _, h => by
      simp only [resolveDefs, Option.some.injEq] at h
      subst h
      rfl
  | .typ d A T, _, Λ, nv, ds, ho, h => by
      simp only [SDefs.PathOperands] at ho
      simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨d', hd, _, _, _, _, rfl⟩ := h
      simp only [PDefs.inserted, PDef.inserted]
      rw [resolveDefs_noInsert d Λ nv d' ho hd]
  | .trm d a T t, _, Λ, nv, ds, ho, h => by
      simp only [SDefs.PathOperands, Bool.and_eq_true] at ho
      match t, ho, h with
      | .lam y D b, ho, h =>
        simp only [STm.PathOperands] at ho
        simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨d', hd, _, _, _, _, _, _, b', hb, rfl⟩ := h
        simp only [PDefs.inserted, PDef.inserted]
        rw [resolveDefs_noInsert d Λ nv d' ho.1 hd, resolve_noInsert b Λ (nv.cons y) b' ho.2 hb]
      | .obj y S e, ho, h =>
        simp only [STm.PathOperands] at ho
        cases T with
        | some _ =>
          simp [resolveDefs] at h
        | none =>
          simp only [resolveDefs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
            Option.some.injEq] at h
          obtain ⟨d', hd, _, _, _, _, e', he, rfl⟩ := h
          simp only [PDefs.inserted, PDef.inserted]
          rw [resolveDefs_noInsert d Λ nv d' ho.1 hd, resolveDefs_noInsert e Λ (nv.cons y) e' ho.2 he]
      | .var x, ho, h =>
        rw [resolveDefs_trm_path Λ nv d a T _ (fun _ _ _ h => STm.noConfusion h)
          (fun _ _ _ h => STm.noConfusion h)] at h
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨d', hd, _, _, _, _, _, _, rfl⟩ := h
        simp only [PDefs.inserted, PDef.inserted]
        rw [resolveDefs_noInsert d Λ nv d' ho.1 hd]
      | .proj t' a', ho, h =>
        rw [resolveDefs_trm_path Λ nv d a T _ (fun _ _ _ h => STm.noConfusion h)
          (fun _ _ _ h => STm.noConfusion h)] at h
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨d', hd, _, _, _, _, _, _, rfl⟩ := h
        simp only [PDefs.inserted, PDef.inserted]
        rw [resolveDefs_noInsert d Λ nv d' ho.1 hd]
      | .app t' u', ho, h =>
        rw [resolveDefs_trm_path Λ nv d a T _ (fun _ _ _ h => STm.noConfusion h)
          (fun _ _ _ h => STm.noConfusion h)] at h
        simp [STm.toPath?] at h
      | .«let» _ _ _ _, ho, h =>
        rw [resolveDefs_trm_path Λ nv d a T _ (fun _ _ _ h => STm.noConfusion h)
          (fun _ _ _ h => STm.noConfusion h)] at h
        simp [STm.toPath?] at h
      | .asc _ _, ho, h =>
        rw [resolveDefs_trm_path Λ nv d a T _ (fun _ _ _ h => STm.noConfusion h)
          (fun _ _ _ h => STm.noConfusion h)] at h
        simp [STm.toPath?] at h
      | .alias _ _ _, ho, h =>
        rw [resolveDefs_trm_path Λ nv d a T _ (fun _ _ _ h => STm.noConfusion h)
          (fun _ _ _ h => STm.noConfusion h)] at h
        simp [STm.toPath?] at h
      | .bind _ _ _ _, ho, h =>
        rw [resolveDefs_trm_path Λ nv d a T _ (fun _ _ _ h => STm.noConfusion h)
          (fun _ _ _ h => STm.noConfusion h)] at h
        simp [STm.toPath?] at h
end

/-! ## Tests

Terms and expected values are written by constructors in prefix form, under the
table `Λab` unless a test names another. -/

section Tests

/-- The table of the tests. -/
private def Λab : LabelTable := [("a", .trm 0), ("b", .trm 1)]

/-- `x.a.b` under `[x]` is one path, with no `let` (plan XI D-4). -/
example : resolveTm Λab (NameEnv.nil.cons "x") (.proj (.proj (.var "x") "a") "b") =
    some (.path (.sel (.sel (.var .here) (.trm 0)) (.trm 1))) := by decide

example : ((resolveTm Λab (NameEnv.nil.cons "x") (.proj (.proj (.var "x") "a") "b")).map
    PTm.inserted) = some 0 := by decide

/-- `f x.a` under `[f, x]` keeps both operands. -/
example : resolveTm Λab ((NameEnv.nil.cons "f").cons "x") (.app (.var "f") (.proj (.var "x") "a")) =
    some (.app (.var (.there .here)) (.sel (.var .here) (.trm 0))) := by decide

/-- `f (g x)` under `[f, g, x]` binds the operand by one `let` tagged `arg`. -/
example : resolveTm Λab (((NameEnv.nil.cons "f").cons "g").cons "x")
    (.app (.var "f") (.app (.var "g") (.var "x"))) =
    some (.«let» .arg none (.app (.var (.there .here)) (.var .here))
      (.app (.var (.there (.there (.there .here)))) (.var .here))) := by decide

example : ((resolveTm Λab (((NameEnv.nil.cons "f").cons "g").cons "x")
    (.app (.var "f") (.app (.var "g") (.var "x")))).map PTm.inserted) = some 1 := by decide

/-- `(x : ⊤)` under `[x]` is a `let` tagged `asc` whose body is its binder. -/
example : resolveTm Λab (NameEnv.nil.cons "x") (.asc (.var "x") .top) =
    some (.«let» .asc (some .top) (.path (.var .here)) (.path (.var .here))) := by decide

/-- `alias y x.a (y.b)` under `[x]` is the path `x.a.b`. -/
example : resolveTm Λab (NameEnv.nil.cons "x") (.alias "y" (.sel (.var "x") "a") (.proj (.var "y") "b")) =
    some (.path (.sel (.sel (.var .here) (.trm 0)) (.trm 1))) := by decide

/-- Under `[x, z]` the alias path is weakened past `z`. -/
example : resolveTm Λab ((NameEnv.nil.cons "x").cons "z")
    (.alias "y" (.sel (.var "x") "a") (.proj (.var "y") "b")) =
    some (.path (.sel (.sel (.var (.there .here)) (.trm 0)) (.trm 1))) := by decide

/-- `bind .unstable u x.a (u.b)` under `[x]` is a `let` tagged `recv`. -/
example : resolveTm Λab (NameEnv.nil.cons "x") (.bind .unstable "u" (.proj (.var "x") "a") (.proj (.var "u") "b")) =
    some (.«let» .recv none (.path (.sel (.var .here) (.trm 0))) (.path (.sel (.var .here) (.trm 1)))) := by
  decide

/-- `bind .widen` gives a `let` tagged `widen`. -/
example : resolveTm Λab (NameEnv.nil.cons "x") (.bind .widen "u" (.proj (.var "x") "a") (.var "u")) =
    some (.«let» .widen none (.path (.sel (.var .here) (.trm 0))) (.path (.var .here))) := by decide

/-- The table of the literal test. -/
private def Λlit : LabelTable :=
  [("a", .trm 0), ("b", .trm 1), ("f", .trm 2), ("c", .trm 3), ("A", .typ 0)]

/-- `ν(s) {a = s.b, f = λ(y : ⊤). y, c = ν(t) {type A = ⊤}}`. -/
private def litTest : STm :=
  .obj "s" none
    (.trm (.trm (.trm .nil "a" none (.proj (.var "s") "b"))
      "f" none (.lam "y" (some .top) (.var "y")))
      "c" none (.obj "t" none (.typ .nil "A" .top)))

/-- Its three fields resolve to `PDef.path`, `PDef.lam`, `PDef.new`, in order. -/
example : resolveTm Λlit .nil litTest =
    some (.new none
      (.cons (.cons (.cons .nil (.path (.trm 0) (.sel (.var .here) (.trm 1))))
        (.lam (.trm 2) none (some .top) (.path (.var .here))))
        (.new (.trm 3) none (.cons .nil (.typ (.typ 0) .top))))) := by decide

/-- `ν(s) {a = f x}` resolves to `none`: an application is no field. -/
example : resolveTm Λab .nil (.obj "s" none (.trm .nil "a" none (.app (.var "f") (.var "x")))) =
    none := by decide

/-- A written type on a literal field resolves to `none`. -/
example : resolveTm Λlit .nil
    (.obj "s" none (.trm .nil "c" (some .top) (.obj "t" none (.typ .nil "A" .top)))) = none := by
  decide

/-- A written type on a path field is dropped. -/
example : resolveTm Λab .nil
    (.obj "s" none (.trm .nil "a" (some (.sngl (.sel (.var "s") "b"))) (.proj (.var "s") "b"))) =
    some (.new none (.cons .nil (.path (.trm 0) (.sel (.var .here) (.trm 1))))) := by decide

/-- A written declared type of a lambda field is kept, and `resolve` refuses it. -/
example : resolveTm Λlit .nil
    (.obj "s" none (.trm .nil "f" (some (.all "z" .top .top)) (.lam "y" (some .top) (.var "y")))) =
    some (.new none (.cons .nil (.lam (.trm 2) (some (.all .top .top)) (some .top) (.path (.var .here))))) := by
  decide

/-- An empty domain stays empty in `resolveP`, and `resolve` gives `none`. -/
example : resolveP Λab (.lam "x" none (.var "x")) = some (.lam none (.path (.var .here))) := by decide

example : resolve Λab (.lam "x" none (.var "x")) = none := by decide

example : resolve Λab (.lam "x" (some .top) (.var "x")) =
    some (.lam .top (.path (.var .here))) := by decide

/-- Totality applies to the literal test. -/
example : (resolveTm Λlit .nil litTest).isSome = true :=
  resolveTm_isSome litTest Λlit .nil (by decide) (by decide) (by decide)

end Tests

end PDotFrontend
