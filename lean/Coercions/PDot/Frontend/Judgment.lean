import Coercions.PDot.Frontend.Ann
import Coercions.PDot.Frontend.Decide

/-!
# The annotated judgment

The judgment `AHasTy` of the pDOT front end over the annotated terms `ATm`.
This is plan XI (`plan-11-pdot-frontends.md`), its part "The annotated
judgment (D-14)" and the "Reuse" row `Judgment`.  There is no model in the
Paths front end.  Substitution follows `PDot/Source/Binding.lean` and the
rules follow `PDot/Source/Typing.lean`.

- `AHasTy`, `ADefTy` and `ADefsTy` are one mutual block of `Type`-valued
  families.  There is one rule per former of `ATm`, `ADef` and `ADefs`, and
  one rule `asub` for subtyping.  A `let` with a written type binds at that
  type (`aletS`), and a `let` without one binds at the type of its right side
  (`aletN`).  The rule `adnew` types the opened definitions, as `ty_def_new`
  does.
- `AHasTy.erase` gives the `PDot.Source` derivation of the erased term, and
  `ADefTy.erase` and `ADefsTy.erase` do so for definitions.  The cast of
  `adnew` crosses `ADefs.erase_substPath`.
- `ATm.size` counts the constructors of `ATm`, `ADef` and `ADefs`.  It is the
  index of the typer, and substitution keeps it (`ATm.size_subst`).

Nothing here is metatheory.  Every recursive definition is structural, so it
reduces in the kernel and `decide +kernel` runs it.
-/

namespace PDotFrontend

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)
open PDot.Source (Ty Dec Tm Val Def Defs Rhs Ctx HasTy DefTy DefsTy Sub)

/-! ## Substitution on annotated terms -/

mutual
/-- Substitution of paths in an annotated term.  A written type of a `let` is
substituted, and the body under a binder by `σ.lift`. -/
def ATm.subst : {s₁ s₂ : Sig} → ATm s₁ → PathSubst s₁ s₂ → ATm s₂
  | _, _, .path p, σ => .path (p.subst σ)
  | _, _, .app p q, σ => .app (p.subst σ) (q.subst σ)
  | _, _, .lam S t, σ => .lam (S.subst σ) (t.subst σ.lift)
  | _, _, .new T ds, σ => .new (T.subst σ.lift) (ds.subst σ.lift)
  | _, _, .«let» g W t u, σ => .«let» g (W.map (·.subst σ)) (t.subst σ) (u.subst σ.lift)
termination_by structural _ _ t => t
/-- Substitution of paths in an annotated definition. -/
def ADef.subst : {s₁ s₂ : Sig} → ADef s₁ → PathSubst s₁ s₂ → ADef s₂
  | _, _, .typ A T, σ => .typ A (T.subst σ)
  | _, _, .path a p, σ => .path a (p.subst σ)
  | _, _, .lam a S t, σ => .lam a (S.subst σ) (t.subst σ.lift)
  | _, _, .new a T ds, σ => .new a (T.subst σ.lift) (ds.subst σ.lift)
termination_by structural _ _ d => d
/-- Substitution of paths in annotated definitions. -/
def ADefs.subst : {s₁ s₂ : Sig} → ADefs s₁ → PathSubst s₁ s₂ → ADefs s₂
  | _, _, .nil, _ => .nil
  | _, _, .cons ds d, σ => .cons (ds.subst σ) (d.subst σ)
termination_by structural _ _ ds => ds
end

/-- The path `p` for the newest variable of an annotated term. -/
def ATm.substPath (t : ATm (s,x)) (p : Path s) : ATm s := t.subst (PathSubst.one p)
/-- The path `p` for the newest variable of an annotated definition. -/
def ADef.substPath (d : ADef (s,x)) (p : Path s) : ADef s := d.subst (PathSubst.one p)
/-- The path `p` for the newest variable of annotated definitions. -/
def ADefs.substPath (ds : ADefs (s,x)) (p : Path s) : ADefs s := ds.subst (PathSubst.one p)

mutual
/-- Erasure commutes with substitution. -/
theorem ATm.erase_subst : ∀ {s₁ s₂ : Sig} (t : ATm s₁) (σ : PathSubst s₁ s₂),
    (t.subst σ).erase = t.erase.subst σ
  | _, _, .path p, σ => by simp only [ATm.subst, ATm.erase, Tm.subst]
  | _, _, .app p q, σ => by simp only [ATm.subst, ATm.erase, Tm.subst]
  | _, _, .lam S t, σ => by
      simp only [ATm.subst, ATm.erase, Tm.subst, Val.subst, ATm.erase_subst t σ.lift]
  | _, _, .new T ds, σ => by
      simp only [ATm.subst, ATm.erase, Tm.subst, Val.subst, ADefs.erase_subst ds σ.lift]
  | _, _, .«let» g W t u, σ => by
      simp only [ATm.subst, ATm.erase, Tm.subst, ATm.erase_subst t σ, ATm.erase_subst u σ.lift]
/-- Erasure of a definition commutes with substitution. -/
theorem ADef.erase_subst : ∀ {s₁ s₂ : Sig} (d : ADef s₁) (σ : PathSubst s₁ s₂),
    (d.subst σ).erase = d.erase.subst σ
  | _, _, .typ A T, σ => by simp only [ADef.subst, ADef.erase, Def.subst]
  | _, _, .path a p, σ => by simp only [ADef.subst, ADef.erase, Def.subst, Rhs.subst]
  | _, _, .lam a S t, σ => by
      simp only [ADef.subst, ADef.erase, Def.subst, Rhs.subst, Val.subst, ATm.erase_subst t σ.lift]
  | _, _, .new a T ds, σ => by
      simp only [ADef.subst, ADef.erase, Def.subst, Rhs.subst, Val.subst, ADefs.erase_subst ds σ.lift]
/-- Erasure of definitions commutes with substitution. -/
theorem ADefs.erase_subst : ∀ {s₁ s₂ : Sig} (ds : ADefs s₁) (σ : PathSubst s₁ s₂),
    (ds.subst σ).erase = ds.erase.subst σ
  | _, _, .nil, σ => by simp only [ADefs.subst, ADefs.erase, Defs.subst]
  | _, _, .cons ds d, σ => by
      simp only [ADefs.subst, ADefs.erase, Defs.subst, ADefs.erase_subst ds σ, ADef.erase_subst d σ]
end

/-- Erasure of definitions commutes with opening at a path. -/
theorem ADefs.erase_substPath (ds : ADefs (s,x)) (p : Path s) :
    (ds.substPath p).erase = ds.erase.substPath p :=
  ADefs.erase_subst ds (PathSubst.one p)

/-- Erasure commutes with opening at a path. -/
theorem ATm.erase_substPath (t : ATm (s,x)) (p : Path s) :
    (t.substPath p).erase = t.erase.substPath p :=
  ATm.erase_subst t (PathSubst.one p)

/-! ## The judgment and its erasure -/

mutual
/-- The annotated judgment, one rule per former of `ATm` and the rule `asub`. -/
inductive AHasTy : Ctx s → ATm s → Ty s → Type where
  | apath : HasTy Γ (.path p) T → AHasTy Γ (.path p) T
  | aapp : HasTy Γ (.app p q) T → AHasTy Γ (.app p q) T
  | alam : AHasTy (Γ.cons S) t U → AHasTy Γ (.lam S t) (.all S U)
  | anew : ADefsTy (Γ.consSelf T) (.var .here) ds T → AHasTy Γ (.new T ds) (.mu T)
  | aletN : AHasTy Γ t T → AHasTy (Γ.cons T) u U.weaken → AHasTy Γ (.«let» g none t u) U
  | aletS : AHasTy Γ t W → AHasTy (Γ.cons W) u U.weaken → AHasTy Γ (.«let» g (some W) t u) U
  | asub : AHasTy Γ a T → Sub Γ T U → AHasTy Γ a U
/-- The annotated judgment of a definition at the receiver `r`. -/
inductive ADefTy : Ctx s → Path s → ADef s → Dec s → Type where
  | adtyp : ADefTy Γ r (.typ A T) (.typ A T T)
  | adpath : HasTy Γ (.path q) T → ADefTy Γ r (.path b q) (.trm b (.sngl q))
  | adlam : AHasTy Γ (.lam S t) (.all U V) → ADefTy Γ r (.lam b S t) (.trm b (.all U V))
  | adnew : (Ty.mu T).tight = true →
      ADefsTy Γ (r.sel b) (ds.substPath (r.sel b)) (T.substPath (r.sel b)) →
      ADefTy Γ r (.new b T ds) (.trm b (.mu T))
/-- The annotated judgment of definitions at the receiver `r`. -/
inductive ADefsTy : Ctx s → Path s → ADefs s → Ty s → Type where
  | adone : ADefTy Γ r d D → ADefsTy Γ r (.cons .nil d) (.rcd D)
  | adcons : ADefsTy Γ r ds T → ADefTy Γ r d D → ds.erase.hasnt d.erase.label →
      ADefsTy Γ r (.cons ds d) (.and T (.rcd D))
end

mutual
/-- The `PDot.Source` derivation of the erased term. -/
def AHasTy.erase : {s : Sig} → {Γ : Ctx s} → {a : ATm s} → {T : Ty s} →
    AHasTy Γ a T → HasTy Γ a.erase T
  | _, _, _, _, .apath d => d
  | _, _, _, _, .aapp d => d
  | _, _, _, _, .alam d => .ty_all_intro d.erase
  | _, _, _, _, .anew d => .ty_new_intro d.erase
  | _, _, _, _, .aletN d₁ d₂ => .ty_let d₁.erase d₂.erase
  | _, _, _, _, .aletS d₁ d₂ => .ty_let d₁.erase d₂.erase
  | _, _, _, _, .asub d e => .ty_sub d.erase e
termination_by structural _ _ _ _ d => d
/-- The `PDot.Source` derivation of the erased definition. -/
def ADefTy.erase : {s : Sig} → {Γ : Ctx s} → {r : Path s} → {d : ADef s} → {D : Dec s} →
    ADefTy Γ r d D → DefTy Γ r d.erase D
  | _, _, _, _, _, .adtyp => .ty_def_typ
  | _, _, _, _, _, .adpath d => .ty_def_path d
  | _, _, _, _, _, .adlam d => .ty_def_all d.erase
  | _, _, _, _, _, .adnew (ds := ds) (r := r) (b := b) h d =>
      .ty_def_new h (ADefs.erase_substPath ds (r.sel b) ▸ d.erase)
termination_by structural _ _ _ _ _ d => d
/-- The `PDot.Source` derivation of the erased definitions. -/
def ADefsTy.erase : {s : Sig} → {Γ : Ctx s} → {r : Path s} → {ds : ADefs s} → {T : Ty s} →
    ADefsTy Γ r ds T → DefsTy Γ r ds.erase T
  | _, _, _, _, _, .adone d => .ty_defs_one d.erase
  | _, _, _, _, _, .adcons d₁ d₂ h => .ty_defs_cons d₁.erase d₂.erase h
termination_by structural _ _ _ _ _ d => d
end

/-! ## The size, the typer's index -/

mutual
/-- The number of constructors of `ATm`, `ADef` and `ADefs` in a term. -/
def ATm.size : {s : Sig} → ATm s → Nat
  | _, .path _ => 1
  | _, .app _ _ => 1
  | _, .lam _ t => t.size + 1
  | _, .new _ ds => ds.size + 1
  | _, .«let» _ _ t u => t.size + u.size + 1
termination_by structural _ t => t
/-- The number of constructors in a definition. -/
def ADef.size : {s : Sig} → ADef s → Nat
  | _, .typ _ _ => 1
  | _, .path _ _ => 1
  | _, .lam _ _ t => t.size + 1
  | _, .new _ _ ds => ds.size + 1
termination_by structural _ d => d
/-- The number of constructors in definitions. -/
def ADefs.size : {s : Sig} → ADefs s → Nat
  | _, .nil => 1
  | _, .cons ds d => ds.size + d.size + 1
termination_by structural _ ds => ds
end

mutual
/-- Substitution keeps the size. -/
theorem ATm.size_subst : ∀ {s₁ s₂ : Sig} (t : ATm s₁) (σ : PathSubst s₁ s₂), (t.subst σ).size = t.size
  | _, _, .path _, _ => rfl
  | _, _, .app _ _, _ => rfl
  | _, _, .lam _ t, σ => by simp only [ATm.subst, ATm.size, ATm.size_subst t σ.lift]
  | _, _, .new _ ds, σ => by simp only [ATm.subst, ATm.size, ADefs.size_subst ds σ.lift]
  | _, _, .«let» _ _ t u, σ => by simp only [ATm.subst, ATm.size, ATm.size_subst t σ, ATm.size_subst u σ.lift]
/-- Substitution keeps the size of a definition. -/
theorem ADef.size_subst : ∀ {s₁ s₂ : Sig} (d : ADef s₁) (σ : PathSubst s₁ s₂), (d.subst σ).size = d.size
  | _, _, .typ _ _, _ => rfl
  | _, _, .path _ _, _ => rfl
  | _, _, .lam _ _ t, σ => by simp only [ADef.subst, ADef.size, ATm.size_subst t σ.lift]
  | _, _, .new _ _ ds, σ => by simp only [ADef.subst, ADef.size, ADefs.size_subst ds σ.lift]
/-- Substitution keeps the size of definitions. -/
theorem ADefs.size_subst : ∀ {s₁ s₂ : Sig} (ds : ADefs s₁) (σ : PathSubst s₁ s₂), (ds.subst σ).size = ds.size
  | _, _, .nil, _ => rfl
  | _, _, .cons ds d, σ => by simp only [ADefs.subst, ADefs.size, ADefs.size_subst ds σ, ADef.size_subst d σ]
end

/-! ## Tests

E13 through the judgment, a nested literal through `adnew`, two definitions
through `adcons` with `hasnt` decided, an ascription through `aletS` and
`asub`, the erasures, two sizes. -/

section Tests

open PDot.Source (e13_T e13_a) in
/-- E13 through the judgment, closed. -/
def e13A : ATm [] := .new e13_T (.cons .nil (.path e13_a (.sel (.var .here) e13_a)))

open PDot.Source (e13_T e13_a) in
/-- The derivation of E13 at its type. -/
def E13A_d : AHasTy .nil e13A (.mu e13_T) :=
  .anew (.adone (.adpath (.ty_new_elim (.ty_var rfl))))

example : e13A.erase = .val PDot.Source.e13_lit := by decide

/-- A type label of the tests. -/
abbrev jA : Label := .typ 0
/-- A term label of the tests. -/
abbrev jb : Label := .trm 0
/-- A second term label of the tests. -/
abbrev jc : Label := .trm 1

/-- `ν(x : {b : μ(y. {A : ⊤..⊤})}) {b = ν(y : {A : ⊤..⊤}) {A = ⊤}}`. -/
def nestA : ATm [] :=
  .new (.rcd (.trm jb (.mu (.rcd (.typ jA .top .top)))))
    (.cons .nil (.new jb (.rcd (.typ jA .top .top)) (.cons .nil (.typ jA .top))))

/-- The nested literal through `adnew`. -/
def nestA_d : AHasTy .nil nestA (.mu (.rcd (.trm jb (.mu (.rcd (.typ jA .top .top)))))) :=
  .anew (.adone (.adnew rfl (.adone .adtyp)))

example : Nonempty (HasTy .nil nestA.erase (.mu (.rcd (.trm jb (.mu (.rcd (.typ jA .top .top))))))) :=
  ⟨nestA_d.erase⟩

/-- `ν(x : {A : ⊤..⊤} ∧ {c : x.type}) {A = ⊤, c = x}`. -/
def twoA : ATm [] :=
  .new (.and (.rcd (.typ jA .top .top)) (.rcd (.trm jc (.sngl (.var .here)))))
    (.cons (.cons .nil (.typ jA .top)) (.path jc (.var .here)))

/-- Two definitions through `adcons`, with `hasnt` decided. -/
def twoA_d : AHasTy .nil twoA (.mu (.and (.rcd (.typ jA .top .top)) (.rcd (.trm jc (.sngl (.var .here)))))) :=
  .anew (.adcons (.adone .adtyp) (.adpath (.ty_var rfl)) (by decide))

example : twoA.erase = .val (.new (.and (.rcd (.typ jA .top .top)) (.rcd (.trm jc (.sngl (.var .here)))))
    (.cons (.cons .nil (.typ jA .top)) (.trm jc (.defp (.var .here))))) := by decide

/-- `let y : ⊤ = λ(z : ⊤). z in y`, through `aletS` and `asub`. -/
def letA : ATm [] := .«let» .asc (some .top) (.lam .top (.path (.var .here))) (.path (.var .here))
/-- The ascription at `⊤`. -/
def letA_d : AHasTy .nil letA .top :=
  .aletS (.asub (.alam (.apath (.ty_var rfl))) .subtyp_top) (.apath (.ty_var rfl))

example : letA.erase = .lett (.val (.lam .top (.path (.var .here)))) (.path (.var .here)) := by decide
example : nestA.size = 7 := by decide
example : (ADefs.substPath (.cons .nil (.typ jA (.sel (.var .here) jA))) (.var .here : Path ([],x))).size = 3 := by decide

end Tests

end PDotFrontend
