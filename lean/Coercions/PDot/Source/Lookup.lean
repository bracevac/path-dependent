import Coercions.PDot.Source.Binding

/-!
# Lookup of paths in a store

Path lookup of pDOT, as `Lookup.v:17-46` of the Coq formalization states it.  `LStep γ r r'` is
`γ ⊢ r ⤳ r'`, Coq's `lookup_step`, three constructors.  `Lookups γ r r'` is its reflexive transitive
closure `⤳*`, Coq's `star (lookup_step γ)` (`Sequences.v:19-23`).

Coq states `lookup_var` with the premise `binds x v γ`.  A store here binds every variable of its
signature, so `Store.get` is total and the rule reads `γ.get x` in its conclusion.  `LStep.var_of_get`
states the rule with Coq's premise.  Coq's `defs_has ds {a := t}` is `ds.get a = some {a = r}`, the
newest definition at the label (`get_def`, `Definitions.v:203-209`).  `r⟨p⟩` opens the right-hand side
at the path `p`, which is Coq's `open_defrhs_p p t`.

`CyclicPath γ p` is Coq's `cyclic_path` (`Safety.v:409`), an infinite lookup sequence from `p`, here as
a function from the naturals.  `PathSafe γ p` has no Coq row.  It is the predicate of `PDot.safety`:
every lookup sequence from `p` ends in a value or can take one more step.

The theorems are Coq's `lookup_step_func`, `lookup_val_inv`, `lookup_irred` and `lookup_func`.  Two
examples close the file.  `E12_lookup` is the worked lookup of the paper, written out step by step.
`C4_source` shows that `lookup_sel_v` opens a field at the location it was found under, not at the
written prefix.

Binders are named in comments only.  `.here` is the newest variable of a signature.
-/

namespace PDot.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## The rules (`Lookup.v:17-46`) -/

/-- `γ ⊢ r ⤳ r'`, Coq's `lookup_step` (`Lookup.v:17`). -/
inductive LStep (γ : Store s) : Rhs s → Rhs s → Prop where
  -- :22  γ.get x = v  ⟹  γ ⊢ defp x ⤳ defv v
  | lookup_var : LStep γ (.defp (.var x)) (.defv (γ.get x))
  -- :29  γ ⊢ defp p ⤳ defp q  ⟹  γ ⊢ defp p.a ⤳ defp q.a
  | lookup_sel_p : LStep γ (.defp p) (.defp q) → LStep γ (.defp (p.sel a)) (.defp (q.sel a))
  -- :36  γ ⊢ defp p ⤳ defv ν(z : T) ds,  ds.get a = some {a = r}  ⟹  γ ⊢ defp p.a ⤳ r⟨p⟩
  | lookup_sel_v : LStep γ (.defp p) (.defv (.new T ds)) → ds.get a = some (.trm a r) →
      LStep γ (.defp (p.sel a)) (r.substPath p)

/-- `γ ⊢ r ⤳* r'`, the reflexive transitive closure of `LStep` (`Lookup.v:44`). -/
inductive Lookups (γ : Store s) : Rhs s → Rhs s → Prop where     -- ⤳*
  -- star_refl:  γ ⊢ r ⤳* r
  | refl : Lookups γ r r
  -- star_step:  γ ⊢ r ⤳ r',  γ ⊢ r' ⤳* r''  ⟹  γ ⊢ r ⤳* r''
  | step : LStep γ r r' → Lookups γ r' r'' → Lookups γ r r''

/-- An infinite lookup sequence from `p`, Coq's `cyclic_path γ p := infseq (lookup_step γ) (defp p)`
(`Safety.v:409`), in the function form of `infseq_with_function` (`Sequences.v:95-96`). -/
def CyclicPath (γ : Store s) (p : Path s) : Prop := ∃ f : Nat → Rhs s, f 0 = .defp p ∧ ∀ n, LStep γ (f n) (f (n+1))

/-- Every lookup sequence from `p` ends in a value or steps once more.  No Coq row.  It is the
predicate of `PDot.safety` and takes the place of the conclusion of `path_safety`
(`Safety.v:442-447`). -/
def PathSafe (γ : Store s) (p : Path s) : Prop :=
  ∀ r, Lookups γ (.defp p) r → (∃ v, r = .defv v) ∨ ∃ r', LStep γ r r'

/-! ## The rules in Coq's form, and forward forms for derivations -/

/-- `lookup_var` with Coq's premise `binds x v γ` (`Lookup.v:22-24`). -/
theorem LStep.var_of_get {γ : Store s} {x : BVar s .var} {v : Val s} (h : γ.get x = v) :
    LStep γ (.defp (.var x)) (.defv v) :=
  h ▸ LStep.lookup_var

/-- `lookup_sel_v` with its opened right-hand side named, so a derivation can be written forward. -/
theorem LStep.sel_v {γ : Store s} {p : Path s} {T : Ty (s,x)} {ds : Defs (s,x)} {a : Label}
    {r : Rhs (s,x)} {r' : Rhs s} (h : LStep γ (.defp p) (.defv (.new T ds)))
    (hg : ds.get a = some (.trm a r)) (e : r.substPath p = r') : LStep γ (.defp (p.sel a)) r' :=
  e ▸ LStep.lookup_sel_v h hg

theorem Lookups.single {γ : Store s} {r r' : Rhs s} (h : LStep γ r r') : Lookups γ r r' :=
  .step h .refl

theorem Lookups.trans {γ : Store s} {r r' r'' : Rhs s} :
    Lookups γ r r' → Lookups γ r' r'' → Lookups γ r r'' := by
  intro h₁ h₂
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

/-! ## Determinism (`Lookup.v:104-147`) -/

/-- No lookup step leaves a value, `lookup_irred` (`Lookup.v:127`). -/
theorem LStep.irred {γ : Store s} {v : Val s} {r : Rhs s} : ¬ LStep γ (.defv v) r :=
  fun h => nomatch h

/-- Lookup is a function, `lookup_step_func` (`Lookup.v:112`).  At `lookup_sel_v` the two field
reads agree because `Defs.get` returns one definition. -/
theorem LStep.det : LStep γ r r₁ → LStep γ r r₂ → r₁ = r₂ := by
  intro h₁
  induction h₁ generalizing r₂ with
  | lookup_var =>
      intro h₂
      cases h₂
      rfl
  | lookup_sel_p _ ih =>
      intro h₂
      cases h₂ with
      | lookup_sel_p h =>
          cases ih h
          rfl
      | lookup_sel_v h _ => cases ih h
  | lookup_sel_v _ hg ih =>
      intro h₂
      cases h₂ with
      | lookup_sel_p h => cases ih h
      | lookup_sel_v h hg' =>
          cases ih h
          rw [hg] at hg'
          cases hg'
          rfl

/-- A value looks up only to itself, `lookup_val_inv` (`Lookup.v:104`). -/
theorem Lookups.from_val : Lookups γ (.defv v) r → r = .defv v
  | .refl => rfl
  | .step h _ => absurd h LStep.irred

theorem Lookups.val_unique_of_eq {γ : Store s} {r r₁ : Rhs s} {v₂ : Val s} :
    Lookups γ r r₁ → ∀ v₁, r₁ = .defv v₁ → Lookups γ r (.defv v₂) → v₁ = v₂ := by
  intro h₁
  induction h₁ with
  | refl =>
      intro v₁ e h₂
      subst e
      cases Lookups.from_val h₂
      rfl
  | step h₁ _ ih =>
      intro v₁ e h₂
      cases h₂ with
      | refl => exact absurd h₁ LStep.irred
      | step h₂ rest =>
          cases LStep.det h₁ h₂
          exact ih v₁ e rest

/-- Two lookups of one start to values agree, `lookup_func` (`Lookup.v:134`).  Coq states it for a
path.  It holds for every start. -/
theorem Lookups.val_unique : Lookups γ r (.defv v₁) → Lookups γ r (.defv v₂) → v₁ = v₂ :=
  fun h₁ h₂ => Lookups.val_unique_of_eq h₁ v₁ rfl h₂

/-! ## E12: the worked lookup of the paper (`calculus.tex:284-305`)

`γ12 = (y ↦ ν(y'){b = ν(y''){c = λ(z : ⊤) z}}), (x ↦ ν(x){a = y.b})`.  The chain is
`x.a.c ⤳ y.b.c ⤳ λ(z : ⊤) z`.  The literals carry annotations, which lookup does not read:
`{b : μ(y''. {c : ∀(z : ⊤) ⊤})}` for `y` and `{a : (y.b).type}` for `x`. -/

abbrev e12_a : Label := .trm 0
abbrev e12_b : Label := .trm 1
abbrev e12_c : Label := .trm 2

/-- `ν(y' : {b : μ(y''. {c : ∀(z : ⊤) ⊤})}) {b = ν(y'' : {c : ∀(z : ⊤) ⊤}) {c = λ(z : ⊤) z}}`, at the
empty signature. -/
abbrev vy12 : Val ([] : Sig) :=
  .new (.rcd (.trm e12_b (.mu (.rcd (.trm e12_c (.all .top .top))))))
    (.cons .nil (.trm e12_b (.defv (.new (.rcd (.trm e12_c (.all .top .top)))
      (.cons .nil (.trm e12_c (.defv (.lam .top (.path (.var .here))))))))))

/-- `ν(x : {a : (y.b).type}) {a = y.b}`, at the signature `[y]`.  In the body `.here` is `x` and
`.there .here` is `y`. -/
abbrev vx12 : Val (([] : Sig),x) :=
  .new (.rcd (.trm e12_a (.sngl (.sel (.var (.there .here)) e12_b))))
    (.cons .nil (.trm e12_a (.defp (.sel (.var (.there .here)) e12_b))))

/-- `y ↦ vy12`, then `x ↦ vx12`.  `x` is `.here`, `y` is `.there .here`. -/
abbrev γ12 : Store ((([] : Sig),x),x) := (Store.nil.cons vy12).cons vx12
abbrev x12 : Path ((([] : Sig),x),x) := .var .here
abbrev y12 : Path ((([] : Sig),x),x) := .var (.there .here)
/-- `λ(z : ⊤) z`. -/
abbrev lam12 : Val ((([] : Sig),x),x) := .lam .top (.path (.var .here))
/-- `ν(y'' : {c : ∀(z : ⊤) ⊤}) {c = λ(z : ⊤) z}`, at the signature `[y, x]`. -/
abbrev vyb12 : Val ((([] : Sig),x),x) :=
  .new (.rcd (.trm e12_c (.all .top .top))) (.cons .nil (.trm e12_c (.defv (.lam .top (.path (.var .here))))))

-- γ ⊢ x ⤳ ν(x){a = y.b}
theorem E12_x : LStep γ12 (.defp x12) (.defv vx12.weaken) := .lookup_var
-- γ ⊢ x.a ⤳ y.b
theorem E12_xa : LStep γ12 (.defp (x12.sel e12_a)) (.defp (y12.sel e12_b)) := .sel_v E12_x rfl rfl
-- γ ⊢ x.a.c ⤳ y.b.c
theorem E12_xac : LStep γ12 (.defp ((x12.sel e12_a).sel e12_c)) (.defp ((y12.sel e12_b).sel e12_c)) :=
  .lookup_sel_p E12_xa
-- γ ⊢ y ⤳ ν(y'){b = ν(y''){c = λ(z : ⊤) z}}
theorem E12_y : LStep γ12 (.defp y12) (.defv vy12.weaken.weaken) := .lookup_var
-- γ ⊢ y.b ⤳ ν(y''){c = λ(z : ⊤) z}
theorem E12_yb : LStep γ12 (.defp (y12.sel e12_b)) (.defv vyb12) := .sel_v E12_y rfl rfl
-- γ ⊢ y.b.c ⤳ λ(z : ⊤) z
theorem E12_ybc : LStep γ12 (.defp ((y12.sel e12_b).sel e12_c)) (.defv lam12) := .sel_v E12_yb rfl rfl

/-- `γ12 ⊢ x.a.c ⤳* λ(z : ⊤) z`, by `x.a.c ⤳ y.b.c ⤳ λ(z : ⊤) z`. -/
theorem E12_lookup : Lookups γ12 (.defp ((x12.sel e12_a).sel e12_c)) (.defv lam12) :=
  .step E12_xac (.step E12_ybc .refl)

/-! ## C4: the source opens a field at its location (`refute-d1.md:171-190`)

`γC4 = (y ↦ ν(w){f = λ(u : ⊤) w}), (x ↦ ν(v){b = y})`.  The path `x.b` aliases `y`.  So
`x.b.f ⤳ y.f ⤳ λ(u : ⊤) y`.  The field `f` is opened at `y`, where it was found.  Opened at the
written prefix `x.b` it would be `λ(u : ⊤) x.b`, which is another value. -/

abbrev c4_b : Label := .trm 1
abbrev c4_f : Label := .trm 3

/-- `ν(w : {f : ∀(u : ⊤) ⊤}) {f = λ(u : ⊤) w}`, at the empty signature.  In the body of the lambda
`.here` is `u` and `.there .here` is `w`. -/
abbrev vyC4 : Val ([] : Sig) :=
  .new (.rcd (.trm c4_f (.all .top .top)))
    (.cons .nil (.trm c4_f (.defv (.lam .top (.path (.var (.there .here)))))))

/-- `ν(v : {b : y.type}) {b = y}`, at the signature `[y]`.  In the body `.here` is `v` and
`.there .here` is `y`. -/
abbrev vxC4 : Val (([] : Sig),x) :=
  .new (.rcd (.trm c4_b (.sngl (.var (.there .here)))))
    (.cons .nil (.trm c4_b (.defp (.var (.there .here)))))

/-- `y ↦ vyC4`, then `x ↦ vxC4`.  `x` is `.here`, `y` is `.there .here`. -/
abbrev γC4 : Store ((([] : Sig),x),x) := (Store.nil.cons vyC4).cons vxC4
abbrev xC4 : Path ((([] : Sig),x),x) := .var .here
abbrev yC4 : Path ((([] : Sig),x),x) := .var (.there .here)
/-- `λ(u : ⊤) y`, the field opened at the location `y`. -/
abbrev lamAtY : Val ((([] : Sig),x),x) := .lam .top (.path yC4.weaken)
/-- `λ(u : ⊤) x.b`, the field opened at the written prefix `x.b`. -/
abbrev lamAtXb : Val ((([] : Sig),x),x) := .lam .top (.path (xC4.sel c4_b).weaken)

-- γ ⊢ x.b ⤳ y
theorem C4_xb : LStep γC4 (.defp (xC4.sel c4_b)) (.defp yC4) := .sel_v .lookup_var rfl rfl
-- γ ⊢ x.b.f ⤳ y.f
theorem C4_xbf : LStep γC4 (.defp ((xC4.sel c4_b).sel c4_f)) (.defp (yC4.sel c4_f)) := .lookup_sel_p C4_xb
-- γ ⊢ y.f ⤳ λ(u : ⊤) y
theorem C4_yf : LStep γC4 (.defp (yC4.sel c4_f)) (.defv lamAtY) := .sel_v .lookup_var rfl rfl

/-- `γC4 ⊢ x.b.f ⤳* λ(u : ⊤) y`, and that lambda is not `λ(u : ⊤) x.b`. -/
theorem C4_source : Lookups γC4 (.defp ((xC4.sel c4_b).sel c4_f)) (.defv lamAtY) ∧ lamAtY ≠ lamAtXb :=
  ⟨.step C4_xbf (.step C4_yf .refl), by decide⟩

end PDot.Source
