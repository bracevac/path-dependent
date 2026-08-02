import LambdaPHistory.RuntimeConversion

/-!
Binder-scoped path equivalence.

`Path.RuntimeEq` is indexed by a concrete store.  Reusing it naively below a
binder is unsound: the freshly bound variable is not a location in that
store, so it must not acquire a co-resolution equation.  This file separates
the generic algebra from the store-specific relation.

Given any equivalence and path congruence `E` on `Path n`, `Path.ScopedLift E`
is its least congruence one scope deeper.  Old equations are weakened, while
the new variable has only the explicit reflexive seed.  The main theorem says
that opening two lifted-equivalent templates with `E`-equivalent actual paths
produces `E`-equivalent paths.
-/

namespace LambdaPHistory

/-- The elementary interface required of a path equivalence. -/
structure Path.IsEquivCongr {n : Nat}
    (E : Path n -> Path n -> Prop) : Prop where
  refl : ∀ p, E p p
  symm : ∀ {p q}, E p q -> E q p
  trans : ∀ {p q r}, E p q -> E q r -> E p r
  fst : ∀ {p q}, E p q -> E p.fst q.fst
  sel : ∀ {p q}, E p q -> ∀ a, E (p.sel a) (q.sel a)

namespace Path.IsEquivCongr

/-- Pointwise-equivalent substitutions give equivalent instances of one
path template. -/
theorem subst
    {E : Path m -> Path m -> Prop}
    {ρ₁ ρ₂ : PathSubst n m}
    (hE : Path.IsEquivCongr E)
    (hρ : ∀ x, E (ρ₁ x) (ρ₂ x)) (p : Path n) :
    E (p.subst ρ₁) (p.subst ρ₂) := by
  induction p with
  | var x => exact hρ x
  | fst p ih => exact hE.fst ih
  | sel p a ih => exact hE.sel ih a

/-- Equivalent paths remain equivalent in an arbitrary one-hole path
context. -/
theorem open_context
    {E : Path n -> Path n -> Prop}
    (hE : Path.IsEquivCongr E) (h : E p q) (r : Path (n + 1)) :
    E (r.open p) (r.open q) := by
  apply hE.subst (p := r)
  intro x
  refine Fin.cases ?_ (fun y => ?_) x
  · exact h
  · exact hE.refl (.var y)

end Path.IsEquivCongr

/-- Lift an ambient path equivalence through one binder.

There is deliberately no constructor that consults a larger store, and no
constructor relating the fresh variable to an old path. -/
inductive Path.ScopedLift {n : Nat}
    (E : Path n -> Path n -> Prop) : Path (n + 1) -> Path (n + 1) -> Prop where
| bound : Path.ScopedLift E (.var 0) (.var 0)
| old : E p q -> Path.ScopedLift E p.weaken q.weaken
| symm : Path.ScopedLift E p q -> Path.ScopedLift E q p
| trans :
    Path.ScopedLift E p q ->
    Path.ScopedLift E q r ->
    Path.ScopedLift E p r
| fst : Path.ScopedLift E p q -> Path.ScopedLift E p.fst q.fst
| sel : Path.ScopedLift E p q -> Path.ScopedLift E (p.sel a) (q.sel a)

namespace Path.ScopedLift

/-- A morphism of ambient path relations lifts together with an extended
renaming.  This is the renaming analogue of `subst_same` used by runtime
store extension. -/
theorem rename
    {E₁ : Path n -> Path n -> Prop}
    {E₂ : Path m -> Path m -> Prop}
    {f : FinFun n m}
    (hmap : ∀ {p q}, E₁ p q -> E₂ (p.rename f) (q.rename f))
    (h : Path.ScopedLift E₁ p q) :
    Path.ScopedLift E₂ (p.rename f.ext) (q.rename f.ext) := by
  induction h with
  | bound => exact .bound
  | @old p q hpq =>
      simpa only [Path.weaken_rename] using
        (Path.ScopedLift.old (hmap hpq))
  | symm hpq ih => exact .symm ih
  | trans hpq hqr ih₁ ih₂ => exact .trans ih₁ ih₂
  | fst hpq ih => exact .fst ih
  | sel hpq ih => exact .sel ih

/-- Reflexivity is derived structurally.  At the fresh variable it can only
start from `bound`; at an old variable it starts from ambient reflexivity. -/
theorem refl
    {E : Path n -> Path n -> Prop}
    (hE : Path.IsEquivCongr E) (p : Path (n + 1)) :
    Path.ScopedLift E p p := by
  induction p with
  | var x =>
      refine Fin.cases ?_ (fun y => ?_) x
      · exact .bound
      · simpa [Path.weaken, Path.rename] using
          (Path.ScopedLift.old (hE.refl (Path.var y)))
  | fst p ih => exact .fst ih
  | sel p a ih => exact .sel ih

/-- The scoped lift is itself an equivalence and path congruence. -/
theorem isEquivCongr
    {E : Path n -> Path n -> Prop}
    (hE : Path.IsEquivCongr E) :
    Path.IsEquivCongr (Path.ScopedLift E) where
  refl := Path.ScopedLift.refl hE
  symm := Path.ScopedLift.symm
  trans := Path.ScopedLift.trans
  fst := Path.ScopedLift.fst
  sel h a := Path.ScopedLift.sel (a := a) h

/-- Substituting opening substitutions into lifted-equivalent templates is
sound when the two actual paths are ambient-equivalent. -/
theorem subst_openAt
    {E : Path n -> Path n -> Prop}
    (hE : Path.IsEquivCongr E)
    (h : Path.ScopedLift E p q) :
    ∀ {r s : Path n}, E r s ->
      E (p.subst (PathSubst.openAt r))
        (q.subst (PathSubst.openAt s)) := by
  induction h with
  | bound =>
      intro r s hrs
      exact hrs
  | @old p q hpq =>
      intro r s hrs
      change E (p.weaken.open r) (q.weaken.open s)
      simpa only [Path.weaken_open] using hpq
  | symm hpq ih =>
      intro r s hrs
      exact hE.symm (ih (hE.symm hrs))
  | trans hpq hqt ih₁ ih₂ =>
      intro r s hrs
      exact hE.trans (ih₁ hrs) (ih₂ (hE.refl s))
  | fst hpq ih =>
      intro r s hrs
      exact hE.fst (ih hrs)
  | sel hpq ih =>
      intro r s hrs
      exact hE.sel (ih hrs) _

/-- Opening form of `subst_openAt`. -/
theorem open_paths
    {E : Path n -> Path n -> Prop}
    (hE : Path.IsEquivCongr E)
    (h : Path.ScopedLift E p q)
    (hrs : E r s) : E (p.open r) (q.open s) := by
  simpa only [Path.open] using h.subst_openAt hE hrs

private theorem Path.weaken_ne_bound (p : Path n) :
    p.weaken ≠ Path.var (0 : Fin (n + 1)) := by
  cases p with
  | var x =>
      intro h
      cases h
  | fst p =>
      intro h
      cases h
  | sel p a =>
      intro h
      cases h

/-- The fresh variable cannot become equivalent to any distinct path.  This
is the formal no-co-resolution property of the lift. -/
theorem bound_only
    {E : Path n -> Path n -> Prop}
    (h : Path.ScopedLift E p q) :
    (p = Path.var 0 -> q = Path.var 0) ∧
      (q = Path.var 0 -> p = Path.var 0) := by
  induction h with
  | bound => exact ⟨id, id⟩
  | old hpq =>
      exact ⟨
        fun hp => (Path.weaken_ne_bound _ hp).elim,
        fun hq => (Path.weaken_ne_bound _ hq).elim⟩
  | symm hpq ih => exact ⟨ih.2, ih.1⟩
  | trans hpq hqr ih₁ ih₂ =>
      exact ⟨fun hp => ih₂.1 (ih₁.1 hp),
        fun hr => ih₁.2 (ih₂.2 hr)⟩
  | fst hpq ih =>
      constructor
      · intro hp
        cases hp
      · intro hq
        cases hq
  | sel hpq ih =>
      constructor
      · intro hp
        cases hp
      · intro hq
        cases hq

theorem bound_left
    {E : Path n -> Path n -> Prop}
    (h : Path.ScopedLift E (Path.var 0) q) : q = Path.var 0 :=
  h.bound_only.1 rfl

theorem bound_right
    {E : Path n -> Path n -> Prop}
    (h : Path.ScopedLift E p (Path.var 0)) : p = Path.var 0 :=
  h.bound_only.2 rfl

end Path.ScopedLift

/-! ## Runtime specialization -/

/-- Store-indexed runtime equality supplies the generic equivalence and
congruence interface. -/
theorem Path.RuntimeEq.isEquivCongr (sigma : Store n) :
    Path.IsEquivCongr (Path.RuntimeEq sigma) where
  refl := fun _ => Path.RuntimeEq.refl
  symm := fun h => Path.RuntimeEq.symm h
  trans := fun h₁ h₂ => Path.RuntimeEq.trans h₁ h₂
  fst h := by
    simpa [Path.open, Path.subst] using
      (Path.RuntimeEq.congr h (Path.fst (Path.var 0)))
  sel h a := by
    simpa [Path.open, Path.subst] using
      (Path.RuntimeEq.congr h (Path.sel (Path.var 0) a))

/-- Runtime equality lifted through a binder without extending the store. -/
abbrev Path.ScopedRuntimeEq (sigma : Store n) :
    Path (n + 1) -> Path (n + 1) -> Prop :=
  Path.ScopedLift (Path.RuntimeEq sigma)

/-- Opening scoped runtime-equivalent templates by runtime-equivalent actual
paths is sound in the original store. -/
theorem Path.ScopedRuntimeEq.open
    (h : Path.ScopedRuntimeEq sigma p q)
    (hrs : Path.RuntimeEq sigma r s) :
    Path.RuntimeEq sigma (p.open r) (q.open s) :=
  Path.ScopedLift.open_paths (Path.RuntimeEq.isEquivCongr sigma) h hrs

end LambdaPHistory
