import Coercions.Nominal.Source.Lookup

/-!
# Reduction, normal forms, extended reduction

Reduction of pDOT, as `Reduction.v:11-46` and `Safety.v:468-483` of the Coq formalization state it.

* `Red c c' ρ` is `c ⟼ c'`, Coq's `red` (`Reduction.v:11-35`), 4 constructors.  A configuration is
  `⟨s, γ, t⟩`, a store and a term over one signature.  Coq's `red_let_val` allocates the value at a
  fresh name `x # γ`.  Here the fresh name is the new innermost variable of the signature, and `ρ` is
  the renaming of the step's store, `Rename.id` or `Rename.succ`.  `red_let_tgt` weakens the
  continuation of the `let` by the variable its step adds, `t.rename ρ.lift`.
* `NormForm t` is Coq's `norm_form` (`Reduction.v:44-46`), 2 constructors.
* `ExtRed c c'` is `c ↠ c'`, Coq's `extended_red` (`Safety.v:468-475`), 2 constructors.  It adds one
  lookup step on a path to reduction.

`Step c c'` forgets the renaming, and `Reds` is its reflexive transitive closure, Coq's `⟼*`
(`Reduction.v:39`).  `Diverges` and `Diverges'` are Coq's `diverges` (`Safety.v:408`) and `diverges'`
(`Safety.v:483`), an infinite sequence of steps, here as a function from the naturals.

There is no projection rule.  `path p` is a normal form whatever `p` is.  The one rule that reads the
store is `red_app`, through the closure `⤳*` of lookup.

Binders are named in comments only.  `.here` is the newest variable of a signature.
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-- A right-hand side as a term, Coq's `deftrm` (`CanonicalForms.v:20-24`). -/
def Rhs.toTm : Rhs s → Tm s
  | .defp p => .path p                           -- (defp p).toTm = path p
  | .defv v => .val v                            -- (defv v).toTm = val v

/-! ## Reduction (`Reduction.v:11-46`) -/

/-- `c ⟼[ρ] c'`, Coq's `red` (`Reduction.v:11`).  `ρ` renames the store of `c` into the store of
`c'`. -/
inductive Red : (c c' : Conf) → Rename c.s c'.s → Prop where
  -- :16  γ ⊢ defp q ⤳* defv λ(z : T) t  ⟹  ⟨s, γ, app q p⟩ ⟼[id] ⟨s, γ, t⟨p⟩⟩
  | red_app {s : Sig} {γ : Store s} {q p : Path s} {T : Ty s} {t : Tm (s,x)} :
      Lookups γ (.defp q) (.defv (.lam T t)) → Red ⟨s, γ, .app q p⟩ ⟨s, γ, t.substPath p⟩ Rename.id
  -- :21  ⟨s, γ, let z = val v in t⟩ ⟼[succ] ⟨(s,z), (γ, z ↦ v), t⟩
  | red_let_val : Red ⟨s, γ, .lett (.val v) t⟩ ⟨(s,x), γ.cons v, t⟩ Rename.succ
  -- :26  ⟨s, γ, let z = path p in t⟩ ⟼[id] ⟨s, γ, t⟨p⟩⟩
  | red_let_path : Red ⟨s, γ, .lett (.path p) t⟩ ⟨s, γ, t.substPath p⟩ Rename.id
  -- :32  ⟨s, γ, t₀⟩ ⟼[ρ] ⟨s', γ', t₀'⟩  ⟹  ⟨s, γ, let z = t₀ in t⟩ ⟼[ρ] ⟨s', γ', let z = t₀' in t.rename ρ.lift⟩
  | red_let_tgt : Red ⟨s, γ, t₀⟩ ⟨s', γ', t₀'⟩ ρ → Red ⟨s, γ, .lett t₀ t⟩ ⟨s', γ', .lett t₀' (t.rename ρ.lift)⟩ ρ

/-- Paths and values are normal forms, Coq's `norm_form` (`Reduction.v:44`). -/
inductive NormForm : Tm s → Prop where
  -- :45  NormForm (path p)
  | nf_path : NormForm (.path p)
  -- :46  NormForm (val v)
  | nf_val : NormForm (.val v)

/-- One reduction step, its store renaming forgotten. -/
def Step (c c' : Conf) : Prop := ∃ ρ, Red c c' ρ

/-- `c ⟼* c'`, Coq's `star red` (`Reduction.v:39`). -/
inductive Reds : Conf → Conf → Prop where
  -- star_refl:  c ⟼* c
  | refl : Reds c c
  -- star_step:  c ⟼ c',  c' ⟼* c''  ⟹  c ⟼* c''
  | step : Step c c' → Reds c' c'' → Reds c c''

/-! ## Extended reduction (`Safety.v:468-483`) -/

/-- `c ↠ c'`, Coq's `extended_red` (`Safety.v:468`). -/
inductive ExtRed : Conf → Conf → Prop where
  -- :469  c ⟼ c'  ⟹  c ↠ c'
  | er_red : Step c c' → ExtRed c c'
  -- :472  γ ⊢ defp p ⤳ r  ⟹  ⟨s, γ, path p⟩ ↠ ⟨s, γ, r.toTm⟩
  | er_lookup {s : Sig} {γ : Store s} {p : Path s} {r : Rhs s} :
      LStep γ (.defp p) r → ExtRed ⟨s, γ, .path p⟩ ⟨s, γ, r.toTm⟩

/-- An infinite reduction sequence from `c`, Coq's `diverges := infseq red` (`Safety.v:408`). -/
def Diverges (c : Conf) : Prop := ∃ f : Nat → Conf, f 0 = c ∧ ∀ n, Step (f n) (f (n+1))

/-- An infinite extended reduction sequence from `c`, Coq's `diverges' := infseq extended_red`
(`Safety.v:483`). -/
def Diverges' (c : Conf) : Prop := ∃ f : Nat → Conf, f 0 = c ∧ ∀ n, ExtRed (f n) (f (n+1))

/-! ## Determinism and normal forms -/

/-- Reduction is a function.  The configuration and the store renaming of a step are fixed by the
configuration it starts from.  At `red_app` the two lookups agree by `Lookups.val_unique`. -/
theorem Red.det : Red c c₁ ρ₁ → Red c c₂ ρ₂ → c₁ = c₂ ∧ HEq ρ₁ ρ₂ := by
  intro h₁
  induction h₁ generalizing c₂ with
  | red_app hl =>
      intro h₂
      cases h₂ with
      | red_app hl' =>
          cases Lookups.val_unique hl hl'
          exact ⟨rfl, HEq.rfl⟩
  | red_let_val =>
      intro h₂
      cases h₂ with
      | red_let_val => exact ⟨rfl, HEq.rfl⟩
      | red_let_tgt h => cases h
  | red_let_path =>
      intro h₂
      cases h₂ with
      | red_let_path => exact ⟨rfl, HEq.rfl⟩
      | red_let_tgt h => cases h
  | red_let_tgt h ih =>
      intro h₂
      cases h₂ with
      | red_let_val => cases h
      | red_let_path => cases h
      | red_let_tgt h' =>
          obtain ⟨e, he⟩ := ih h'
          cases e
          cases he
          exact ⟨rfl, HEq.rfl⟩

/-- A normal form does not reduce. -/
theorem NormForm.no_red : NormForm c.tm → ¬ Red c c' ρ := by
  intro hn hr
  cases hr <;> cases hn

end Nominal.Source
