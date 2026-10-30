import Coercions.Nominal.Source.Repl
import Coercions.Nominal.Source.Examples
import Coercions.Nominal.FCn.Checker

/-!
# The decided side conditions

Decision procedures for the side conditions of the pDOT typer.  This is plan XI
(`plan-11-pdot-frontends.md`), its "Reuse" row `Decide`, its parts "Shape",
"Avoidance", replacement, and "Terms and definitions".  The model is
`lean/Coercions/Paths/Frontend/Decide.lean`.  The module decides four things.

- Equality of contexts, `DecidableEq` for `Nominal.Source.Ctx`.  The cut of a run
  tests a context against its pending goals (`Frontend/Fuel.lean`), so the
  equality runs in the kernel.  `ctxDecEq` names the instance.
- Strengthening, the inverse of `Ty.weaken`: `Ty.unweaken` with
  `Ty.unweaken_iff`.  Avoidance uses it to take a type past a bound variable.
  It reuses the partial renaming of the target (`PDot/FCp/Checker.lean`), and
  only the traversal of `Ty` and `Dec` is written here.
- Replacement found: `Repl.find?` builds a `Repl` derivation, and
  `Repl.find?_isSome` says it answers exactly when the library's decider
  `Ty.isRepl` does.
- Labels a block lacks: `Defs.hasnt?`, with a `Decidable` instance for
  `Defs.hasnt` through it.

`Ty.tight` (`PDot/Source/Repl.lean`) is already a Boolean and is reused as it
is.  Callers write `Ty.unweaken T`, not `T.unweaken`, since field notation on
a `Nominal.Source.Ty` looks only in the namespace `Nominal.Source.Ty`.

Every recursive definition is structural, so it reduces in the kernel and
`decide +kernel` runs it.
-/

namespace NominalFrontend

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)
open Nominal.Source (Ty Dec Ctx Defs Def Repl ReplDec)
open Nominal.FCn (PRename)

/-! ## Equality of contexts -/

/-! The derived instance lands in `NominalFrontend`, so the no-well-founded check of the
library sweeps it. -/
deriving instance DecidableEq for Nominal.Source.Ctx

/-- The derived equality of contexts, named for the axiom probe. -/
def ctxDecEq {s : Sig} (G H : Ctx s) : Decidable (G = H) := inferInstance

/-! ## Strengthening

`Ty.unrename T f` reads `T` back through the partial renaming `f`, one case per
constructor of `Ty` and `Dec`.  Under the binder of `μ` and of the codomain of
`∀` it lifts `f`. -/

mutual
/-- Read a type back through a partial renaming. -/
def Ty.unrename : Ty s₁ → PRename s₁ s₂ → Option (Ty s₂)
  | .top, _ => some .top
  | .bot, _ => some .bot
  | .rcd D, f => (Dec.unrename D f).map .rcd
  | .and T U, f => match Ty.unrename T f, Ty.unrename U f with
    | some T', some U' => some (.and T' U')
    | _, _ => none
  | .sel p A, f => (Nominal.FCn.Path.unrename p f).map (.sel · A)
  | .mu T, f => (Ty.unrename T f.lift).map .mu                      -- under z of μ(z. T)
  | .all S T, f => match Ty.unrename S f, Ty.unrename T f.lift with  -- T under z of ∀(z : S) T
    | some S', some T' => some (.all S' T')
    | _, _ => none
  | .sngl p, f => (Nominal.FCn.Path.unrename p f).map .sngl
/-- Read a declaration back through a partial renaming. -/
def Dec.unrename : Dec s₁ → PRename s₁ s₂ → Option (Dec s₂)
  | .typ A S U, f => match Ty.unrename S f, Ty.unrename U f with
    | some S', some U' => some (.typ A S' U')
    | _, _ => none
  | .trm a T, f => (Ty.unrename T f).map (.trm a)
end

/-- The `U` with `U↑ = T`, if any. -/
def Ty.unweaken (T : Ty (s,x)) : Option (Ty s) := Ty.unrename T PRename.unsucc

mutual
theorem Ty.unrename_rename {f : PRename s₁ s₂} {ρ : Rename s₂ s₁} (h : f.Inverts ρ) :
    ∀ (T : Ty s₂), Ty.unrename (T.rename ρ) f = some T
  | .top => rfl
  | .bot => rfl
  | .rcd D => by simp only [Ty.rename, Ty.unrename, Dec.unrename_rename h D]; rfl
  | .and T U => by simp only [Ty.rename, Ty.unrename, Ty.unrename_rename h T, Ty.unrename_rename h U]
  | .sel p A => by
      simp only [Ty.rename, Ty.unrename, Nominal.FCn.Path.unrename_rename h p]; rfl
  | .mu T => by simp only [Ty.rename, Ty.unrename, Ty.unrename_rename h.lift T]; rfl
  | .all S T => by simp only [Ty.rename, Ty.unrename, Ty.unrename_rename h S, Ty.unrename_rename h.lift T]
  | .sngl p => by
      simp only [Ty.rename, Ty.unrename, Nominal.FCn.Path.unrename_rename h p]; rfl
theorem Dec.unrename_rename {f : PRename s₁ s₂} {ρ : Rename s₂ s₁} (h : f.Inverts ρ) :
    ∀ (D : Dec s₂), Dec.unrename (D.rename ρ) f = some D
  | .typ A S U => by simp only [Dec.rename, Dec.unrename, Ty.unrename_rename h S, Ty.unrename_rename h U]
  | .trm a T => by simp only [Dec.rename, Dec.unrename, Ty.unrename_rename h T]; rfl
end

mutual
theorem Ty.eq_rename_of_unrename {f : PRename s₁ s₂} {ρ : Rename s₂ s₁} (h : f.Inverts ρ) :
    ∀ (T : Ty s₁) (U : Ty s₂), Ty.unrename T f = some U → T = U.rename ρ
  | .top, _, e => by cases e; rfl
  | .bot, _, e => by cases e; rfl
  | .rcd D, _, e => by
      obtain ⟨D', hD, rfl⟩ := Option.map_eq_some_iff.1 e
      simp only [Ty.rename]; rw [Dec.eq_rename_of_unrename h D D' hD]
  | .and T U, _, e => by
      simp only [Ty.unrename] at e
      split at e
      next T' U' hT hU =>
        cases e; simp only [Ty.rename]
        rw [Ty.eq_rename_of_unrename h T T' hT, Ty.eq_rename_of_unrename h U U' hU]
      next => cases e
  | .sel p A, _, e => by
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 e
      simp only [Ty.rename]; rw [Nominal.FCn.Path.eq_rename_of_unrename h p q hq]
  | .mu T, _, e => by
      obtain ⟨T', hT, rfl⟩ := Option.map_eq_some_iff.1 e
      simp only [Ty.rename]; rw [Ty.eq_rename_of_unrename h.lift T T' hT]
  | .all S T, _, e => by
      simp only [Ty.unrename] at e
      split at e
      next S' T' hS hT =>
        cases e; simp only [Ty.rename]
        rw [Ty.eq_rename_of_unrename h S S' hS, Ty.eq_rename_of_unrename h.lift T T' hT]
      next => cases e
  | .sngl p, _, e => by
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 e
      simp only [Ty.rename]; rw [Nominal.FCn.Path.eq_rename_of_unrename h p q hq]
theorem Dec.eq_rename_of_unrename {f : PRename s₁ s₂} {ρ : Rename s₂ s₁} (h : f.Inverts ρ) :
    ∀ (D : Dec s₁) (D' : Dec s₂), Dec.unrename D f = some D' → D = D'.rename ρ
  | .typ A S U, _, e => by
      simp only [Dec.unrename] at e
      split at e
      next S' U' hS hU =>
        cases e; simp only [Dec.rename]
        rw [Ty.eq_rename_of_unrename h S S' hS, Ty.eq_rename_of_unrename h U U' hU]
      next => cases e
  | .trm a T, _, e => by
      obtain ⟨T', hT, rfl⟩ := Option.map_eq_some_iff.1 e
      simp only [Dec.rename]; rw [Ty.eq_rename_of_unrename h T T' hT]
end

theorem Ty.unweaken_iff {T : Ty (s,x)} {U : Ty s} : Ty.unweaken T = some U ↔ T = U.weaken :=
  ⟨Ty.eq_rename_of_unrename Nominal.FCn.PRename.unsucc_inverts T U,
   fun e => e ▸ Ty.unrename_rename Nominal.FCn.PRename.unsucc_inverts U⟩
/-! ## Replacement found

`suffix?` reads `l = p.nomExt bs` and `r = q.nomExt bs` off `Path.nomDropPrefix`.
`Repl.find?` has one case per constructor pair of `Ty.isRepl`
(`PDot/Source/Repl.lean`), in the same order, and returns the derivation. -/

/-- `rpath` at a path written as an extension. -/
def replSel {p q l r : Path s} {A : Label} {bs : List Label} (hl : l = p.nomExt bs) (hr : r = q.nomExt bs) :
    Repl p q (.sel l A) (.sel r A) := by
  subst hl hr
  exact .rpath
/-- `rsngl` at a path written as an extension. -/
def replSngl {p q l r : Path s} {bs : List Label} (hl : l = p.nomExt bs) (hr : r = q.nomExt bs) :
    Repl p q (.sngl l) (.sngl r) := by
  subst hl hr
  exact .rsngl

/-- The field list `bs` with `l = p.nomExt bs` and `r = q.nomExt bs`. -/
def suffix? (p q l r : Path s) : Option ((bs : List Label) ×' (l = p.nomExt bs ∧ r = q.nomExt bs)) :=
  match hl : p.nomDropPrefix l with
  | none => none
  | some bs =>
    match hr : q.nomDropPrefix r with
    | none => none
    | some cs =>
      if hbc : bs = cs then
        some ⟨bs, Nominal.Source.Path.eq_ext_of_dropPrefix p l bs hl,
          hbc ▸ Nominal.Source.Path.eq_ext_of_dropPrefix q r cs hr⟩
      else none

theorem suffix?_isSome (p q l r : Path s) :
    (suffix? p q l r).isSome = p.nomSameSuffix q l r := by
  unfold suffix? Paths.FCdot.Path.nomSameSuffix
  split <;> rename_i hl
  · simp only [hl]; rfl
  · split <;> rename_i hr
    · simp only [hl, hr]; rfl
    · simp only [hl, hr]
      split <;> simp_all

mutual
/-- A derivation of `Repl p q T T'`, if one exists. -/
def Repl.find? (p q : Path s) : (T T' : Ty s) → Option (Repl p q T T')
  | .rcd D, .rcd D' => (ReplDec.find? p q D D').map .rrcd                                   -- rrcd
  | .and T U, .and T' U' =>
      (if hU : U = U' then (Repl.find? p q T T').map (fun r => hU ▸ .rand1 r) else none).or   -- rand1
        (if hT : T = T' then (Repl.find? p q U U').map (fun r => hT ▸ .rand2 r) else none)    -- rand2
  | .sel l A, .sel r A' =>
      if hA : A = A' then (suffix? p q l r).map (fun e => hA ▸ replSel e.2.1 e.2.2) else none  -- rpath
  | .mu T, .mu T' => (Repl.find? p.weaken q.weaken T T').map .rbnd                          -- rbnd, under z
  | .all S U, .all S' U' =>
      (if hU : U = U' then (Repl.find? p q S S').map (fun r => hU ▸ .rall1 r) else none).or   -- rall1
        (if hS : S = S' then (Repl.find? p.weaken q.weaken U U').map (fun r => hS ▸ .rall2 r) else none)  -- rall2, under z
  | .sngl l, .sngl r => (suffix? p q l r).map (fun e => replSngl e.2.1 e.2.2)               -- rsngl
  | _, _ => none
/-- A derivation of `ReplDec p q D D'`, if one exists. -/
def ReplDec.find? (p q : Path s) : (D D' : Dec s) → Option (ReplDec p q D D')
  | .typ A S U, .typ A' S' U' =>
      if hA : A = A' then
        (if hU : U = U' then (Repl.find? p q S S').map (fun r => hA ▸ hU ▸ .rdtyp1 r) else none).or   -- rdtyp1
          (if hS : S = S' then (Repl.find? p q U U').map (fun r => hA ▸ hS ▸ .rdtyp2 r) else none)    -- rdtyp2
      else none
  | .trm a T, .trm a' T' =>
      if ha : a = a' then (Repl.find? p q T T').map (fun r => ha ▸ .rdtrm r) else none            -- rdtrm
  | _, _ => none
end

mutual
theorem Repl.find?_isSome : ∀ {s : Sig} (p q : Path s) (T T' : Ty s),
    (Repl.find? p q T T').isSome = Ty.isRepl p q T T'
  | _, p, q, .rcd D, .rcd D' => by
      simp only [Repl.find?, Ty.isRepl, Option.isSome_map, ReplDec.find?_isSome p q D D']
  | _, p, q, .and T U, .and T' U' => by
      simp only [Repl.find?, Ty.isRepl, Option.isSome_or]
      by_cases hU : U = U' <;> by_cases hT : T = T' <;>
        simp [hU, hT, Repl.find?_isSome p q T T', Repl.find?_isSome p q U U']
  | _, p, q, .sel l A, .sel r A' => by
      simp only [Repl.find?, Ty.isRepl]
      by_cases hA : A = A' <;> simp [hA, suffix?_isSome]
  | _, p, q, .mu T, .mu T' => by
      simp only [Repl.find?, Ty.isRepl, Option.isSome_map, Repl.find?_isSome p.weaken q.weaken T T']
  | _, p, q, .all S U, .all S' U' => by
      simp only [Repl.find?, Ty.isRepl, Option.isSome_or]
      by_cases hU : U = U' <;> by_cases hS : S = S' <;>
        simp [hU, hS, Repl.find?_isSome p q S S', Repl.find?_isSome p.weaken q.weaken U U']
  | _, p, q, .sngl l, .sngl r => by
      simp only [Repl.find?, Ty.isRepl, Option.isSome_map, suffix?_isSome]
  | _, _, _, .top, T' => by cases T' <;> rfl
  | _, _, _, .bot, T' => by cases T' <;> rfl
  | _, _, _, .rcd _, .top => rfl
  | _, _, _, .rcd _, .bot => rfl
  | _, _, _, .rcd _, .and _ _ => rfl
  | _, _, _, .rcd _, .sel _ _ => rfl
  | _, _, _, .rcd _, .mu _ => rfl
  | _, _, _, .rcd _, .all _ _ => rfl
  | _, _, _, .rcd _, .sngl _ => rfl
  | _, _, _, .and _ _, .top => rfl
  | _, _, _, .and _ _, .bot => rfl
  | _, _, _, .and _ _, .rcd _ => rfl
  | _, _, _, .and _ _, .sel _ _ => rfl
  | _, _, _, .and _ _, .mu _ => rfl
  | _, _, _, .and _ _, .all _ _ => rfl
  | _, _, _, .and _ _, .sngl _ => rfl
  | _, _, _, .sel _ _, .top => rfl
  | _, _, _, .sel _ _, .bot => rfl
  | _, _, _, .sel _ _, .rcd _ => rfl
  | _, _, _, .sel _ _, .and _ _ => rfl
  | _, _, _, .sel _ _, .mu _ => rfl
  | _, _, _, .sel _ _, .all _ _ => rfl
  | _, _, _, .sel _ _, .sngl _ => rfl
  | _, _, _, .mu _, .top => rfl
  | _, _, _, .mu _, .bot => rfl
  | _, _, _, .mu _, .rcd _ => rfl
  | _, _, _, .mu _, .and _ _ => rfl
  | _, _, _, .mu _, .sel _ _ => rfl
  | _, _, _, .mu _, .all _ _ => rfl
  | _, _, _, .mu _, .sngl _ => rfl
  | _, _, _, .all _ _, .top => rfl
  | _, _, _, .all _ _, .bot => rfl
  | _, _, _, .all _ _, .rcd _ => rfl
  | _, _, _, .all _ _, .and _ _ => rfl
  | _, _, _, .all _ _, .sel _ _ => rfl
  | _, _, _, .all _ _, .mu _ => rfl
  | _, _, _, .all _ _, .sngl _ => rfl
  | _, _, _, .sngl _, .top => rfl
  | _, _, _, .sngl _, .bot => rfl
  | _, _, _, .sngl _, .rcd _ => rfl
  | _, _, _, .sngl _, .and _ _ => rfl
  | _, _, _, .sngl _, .sel _ _ => rfl
  | _, _, _, .sngl _, .mu _ => rfl
  | _, _, _, .sngl _, .all _ _ => rfl
theorem ReplDec.find?_isSome : ∀ {s : Sig} (p q : Path s) (D D' : Dec s),
    (ReplDec.find? p q D D').isSome = Dec.isRepl p q D D'
  | _, p, q, .typ A S U, .typ A' S' U' => by
      simp only [ReplDec.find?, Dec.isRepl]
      by_cases hA : A = A'
      · subst hA
        by_cases hU : U = U' <;> by_cases hS : S = S' <;>
          simp [hU, hS, Option.isSome_or, Repl.find?_isSome p q S S', Repl.find?_isSome p q U U']
      · simp [hA]
  | _, p, q, .trm a T, .trm a' T' => by
      simp only [ReplDec.find?, Dec.isRepl]
      by_cases ha : a = a' <;> simp [ha, Repl.find?_isSome p q T T']
  | _, _, _, .typ _ _ _, .trm _ _ => rfl
  | _, _, _, .trm _ _, .typ _ _ _ => rfl
end

theorem Repl.find?_iff {p q : Path s} {T T' : Ty s} :
    (Repl.find? p q T T').isSome = true ↔ Nonempty (Repl p q T T') := by
  rw [Repl.find?_isSome]
  exact Nominal.Source.Ty.isRepl_iff
/-! ## Labels a block lacks

`Defs.hasnt` is a `Prop` (`PDot/Source/Syntax.lean`).  It is decided through
`Option.isNone`, so no decision runs the derived equality of `Def`. -/

/-- The block `ds` has no definition with label `l`. -/
def Defs.hasnt? (ds : Defs s) (l : Label) : Bool := (ds.get l).isNone

theorem Defs.hasnt?_iff (ds : Defs s) (l : Label) : Defs.hasnt? ds l = true ↔ ds.hasnt l := by
  unfold Defs.hasnt? Nominal.Source.Defs.hasnt
  cases ds.get l <;> simp

instance instDecidableHasnt (ds : Defs s) (l : Label) : Decidable (ds.hasnt l) :=
  decidable_of_iff _ (Defs.hasnt?_iff ds l)

/-! ## Tests

The fifth test is a `μ` whose body mentions the variable being dropped.  The
sixth is a `μ` whose body mentions only its own binder.  The third `Repl` test
replaces two occurrences at once, which `Repl` refuses.  The last one replaces
under `μ` by `rbnd`. -/

section Tests
open Nominal.Source (e10_p e10_q e10_ty)
example : (Ctx.nil.cons (Ty.top : Ty [])) = Ctx.nil.cons .top := by decide +kernel
example : (Ctx.nil.cons (Ty.top : Ty [])) ≠ Ctx.nil.cons .bot := by decide +kernel
example : Ty.unweaken (s := []) (Ty.weaken (Ty.rcd (Dec.trm (.trm 0) .top))) = some (Ty.rcd (Dec.trm (.trm 0) .top)) := by decide +kernel
example : Ty.unweaken (s := []) (Ty.sel (.var .here) (.typ 0)) = none := by decide +kernel
example : Ty.unweaken (s := []) (Ty.mu (Ty.sel (.var (.there .here)) (.typ 0))) = none := by decide +kernel
example : Ty.unweaken (s := []) (Ty.mu (Ty.sel (.var .here) (.typ 0))) = some (Ty.mu (Ty.sel (.var .here) (.typ 0))) := by decide +kernel
example : (Nominal.Source.Defs.nil : Defs []).hasnt (.trm 0) := by decide
example : ¬ ((Nominal.Source.Defs.nil.cons (.typ (.typ 0) .top) : Defs []).hasnt (.typ 0)) := by decide
example : (Repl.find? e10_p e10_q (e10_ty e10_p e10_p) (e10_ty e10_p e10_q)).isSome = true := by decide +kernel
example : (Repl.find? e10_p e10_q (e10_ty e10_p e10_p) (e10_ty e10_q e10_p)).isSome = true := by decide +kernel
example : (Repl.find? e10_p e10_q (e10_ty e10_p e10_p) (e10_ty e10_q e10_q)).isSome = false := by decide +kernel
example : (Repl.find? (s := ([],x),x) (.var .here) (.var (.there .here))
    (.sel ((Path.var .here).sel (.trm 0)) (.typ 0)) (.sel ((Path.var (.there .here)).sel (.trm 0)) (.typ 0))).isSome = true := by decide +kernel
example : (Repl.find? (s := ([],x),x) (.var .here) (.var (.there .here))
    (.mu (.rcd (.trm (.trm 0) (.sngl (.var (.there .here))))))
    (.mu (.rcd (.trm (.trm 0) (.sngl (.var (.there (.there .here)))))))).isSome = true := by decide +kernel
end Tests

end NominalFrontend
