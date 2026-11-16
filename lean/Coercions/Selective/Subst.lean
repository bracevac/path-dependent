import Coercions.Selective.Complete

/-!
# Re-annotation under substitution, through DOT-MNF

`HTy.subst_atom`: if `t` is typed under `z : S`, and an atom `b : V` with
`V ≤₀ S` is substituted for `z` (by its root), then the renamed erased
program has an `H` annotation at the substituted type.

The proof goes through the translation, not through a local repair of the
evidence:

1. `HasTy.retype`: DOT-MNF typing is preserved by a *typed renaming*
   (`Ctx.Retypes`), a renaming whose image of every variable is typed in the
   target context at the renamed declared type.  This is the standard
   variable-substitution lemma of DOT-MNF; selections are retyped through
   their receiver's typing, which `HasTy.sub` supplies.
2. `elaboration_typed` takes the `H` derivation to DOT-MNF, `HasTy.retype`
   substitutes, and `elaboration_complete` builds a new annotation of the
   substituted erased program.

So the re-annotation is the fully explicit one of the converse translation (every
inclusion written as evidence, every implicit step `refl`; not minimized), not the original
annotation with the substituted variable's steps repaired in place.  The
lemma holds for inner binders as well (`HTy.retype`), since the typed
renaming lifts under binders.
-/

namespace Selective

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ctx Ty Path HasTy Sub DefsTy)

/-- A typed renaming: every variable of `Γ` goes to a variable that `Δ` types
at the renamed declared type. -/
def _root_.DotMNF.Ctx.Retypes {s1 s2 : Sig} (Γ : Ctx s1) (Δ : Ctx s2) (ρ : Rename s1 s2) : Type :=
  ∀ y, HasTy Δ (.path (.var (ρ.var y))) ((Γ.lookup y).rename ρ)

def _root_.DotMNF.Ctx.Retypes.cons {s1 s2 : Sig} {Γ : Ctx s1} {Δ : Ctx s2} {ρ : Rename s1 s2}
    (h : Γ.Retypes Δ ρ) (S : Ty s1) : (Γ.cons S).Retypes (Δ.cons (S.rename ρ)) ρ.lift
  | .here => by
      show HasTy _ (.path (.var .here)) (S.weaken.rename ρ.lift)
      rw [DotMNF.Ty.weaken_rename]; exact .var
  | .there y => by
      show HasTy _ (.path (.var (.there (ρ.var y)))) ((Γ.lookup y).weaken.rename ρ.lift)
      rw [DotMNF.Ty.weaken_rename]; exact (h y).weaken _

def _root_.DotMNF.Ctx.Retypes.consSelf {s1 s2 : Sig} {Γ : Ctx s1} {Δ : Ctx s2} {ρ : Rename s1 s2}
    (h : Γ.Retypes Δ ρ) (d : DotMNF.Defs (s1,x)) (T : Ty (s1,x)) :
    (Γ.consSelf d T).Retypes (Δ.consSelf (d.rename ρ.lift) (T.rename ρ.lift)) ρ.lift
  | .here => by
      show HasTy _ (.path (.var .here)) ((Ty.mu T).weaken.rename ρ.lift)
      rw [DotMNF.Ty.weaken_rename]; exact .var
  | .there y => by
      show HasTy _ (.path (.var (.there (ρ.var y)))) ((Γ.lookup y).weaken.rename ρ.lift)
      rw [DotMNF.Ty.weaken_rename]; exact (h y).weakenSelf _ _

mutual

def _root_.DotMNF.Sub.retype {s1 s2 : Sig} {Γ : Ctx s1} {S T : Ty s1} (h : Sub Γ S T)
    {Δ : Ctx s2} (ρ : Rename s1 s2) (hρ : Γ.Retypes Δ ρ) :
    Sub Δ (S.rename ρ) (T.rename ρ) :=
  match h with
  | .top => .top
  | .bot => .bot
  | .refl => .refl
  | .trans h1 h2 => .trans (h1.retype ρ hρ) (h2.retype ρ hρ)
  | .and1 => .and1
  | .and2 => .and2
  | .and h1 h2 => .and (h1.retype ρ hρ) (h2.retype ρ hρ)
  | .fld h => .fld (h.retype ρ hρ)
  | .typ h1 h2 => .typ (h1.retype ρ hρ) (h2.retype ρ hρ)
  | .selUpper h => .selUpper (h.retype ρ hρ)
  | .selLower h => .selLower (h.retype ρ hρ)
  | .all h1 h2 => .all (h1.retype ρ hρ) (h2.retype ρ.lift (hρ.cons _))

def _root_.DotMNF.HasTy.retype {s1 s2 : Sig} {Γ : Ctx s1} {t : DotMNF.Tm s1} {T : Ty s1} (h : HasTy Γ t T)
    {Δ : Ctx s2} (ρ : Rename s1 s2) (hρ : Γ.Retypes Δ ρ) :
    HasTy Δ (t.rename ρ) (T.rename ρ) :=
  match h with
  | .var (x := x) => hρ x
  | .lam h => .lam (h.retype ρ.lift (hρ.cons _))
  | .app h1 h2 => by
      rw [DotMNF.Ty.substVar_rename]
      exact .app (h1.retype ρ hρ) (h2.retype ρ hρ)
  | .obj h hd => .obj (h.retype ρ.lift (hρ.consSelf _ _)) (hd.rename ρ.lift)
  | .proj h => .proj (h.retype ρ hρ)
  | .let h1 h2 => by
      apply HasTy.let (h1.retype ρ hρ)
      simpa only [DotMNF.Ty.weaken_rename] using h2.retype ρ.lift (hρ.cons _)
  | .recI h => by
      apply HasTy.recI
      simpa only [DotMNF.Ty.substVar_rename] using h.retype ρ hρ
  | .recE h => by
      rw [DotMNF.Ty.substVar_rename]
      exact .recE (h.retype ρ hρ)
  | .andI h1 h2 => .andI (h1.retype ρ hρ) (h2.retype ρ hρ)
  | .sub h1 h2 => .sub (h1.retype ρ hρ) (h2.retype ρ hρ)

def _root_.DotMNF.DefsTy.retype {s1 s2 : Sig} {Γ : Ctx s1} {d : DotMNF.Defs s1} {T : Ty s1} (h : DefsTy Γ d T)
    {Δ : Ctx s2} (ρ : Rename s1 s2) (hρ : Γ.Retypes Δ ρ) :
    DefsTy Δ (d.rename ρ) (T.rename ρ) :=
  match h with
  | .typ => .typ
  | .trm h => .trm (h.retype ρ hρ)
  | .and h1 h2 => .and (h1.retype ρ hρ) (h2.retype ρ hρ)

end

/-- Substituting a variable `y : S` for the newest binder `z : S` is a typed renaming. -/
def _root_.DotMNF.Ctx.Retypes.subst {s : Sig} {Γ : Ctx s} {S : Ty s} {y : BVar s .var}
    (hy : HasTy Γ (.path (.var y)) S) : (Γ.cons S).Retypes Γ (Rename.subst y)
  | .here => by
      show HasTy Γ (.path (.var y)) (S.weaken.substVar y)
      rw [DotMNF.Ty.weaken_substVar]; exact hy
  | .there w => by
      show HasTy Γ (.path (.var w)) ((Γ.lookup w).weaken.substVar y)
      rw [DotMNF.Ty.weaken_substVar]; exact .var

/-- `H` typing is preserved by a typed renaming, up to re-annotation. -/
theorem HTy.retype {s1 s2 : Sig} {Γ : Ctx s1} {t : HTm s1} {T : Ty s1} (h : HTy Γ t T)
    {Δ : Ctx s2} (ρ : Rename s1 s2) (hρ : Γ.Retypes Δ ρ) :
    ∃ t' : HTm s2, t'.erase = t.erase.rename ρ ∧ HTy Δ t' (T.rename ρ) := by
  obtain ⟨d⟩ := elaboration_typed h
  exact elaboration_complete (d.retype ρ hρ)

/-- **Re-annotation under substitution of an atom** (stretch S1). -/
theorem HTy.subst_atom {s : Sig} {Γ : Ctx s} {S : Ty s} {t : HTm (s,x)} {T : Ty (s,x)} {b : Atom s}
    {V : Ty s} (ht : HTy (Γ.cons S) t T) (hb : ATy Γ b V) (hp : Prim Γ V S) :
    ∃ t' : HTm s, t'.erase = t.erase.rename (Rename.subst b.root) ∧ HTy Γ t' (T.substVar b.root) := by
  obtain ⟨db⟩ := ATy.sound hb
  obtain ⟨dp⟩ := primitive_sound hp
  exact HTy.retype ht (Rename.subst b.root) (DotMNF.Ctx.Retypes.subst (.sub db dp))

/-- The core of S1 for evidence: a primitive step under `z : S` becomes a
certificate after `z := root b`. -/
theorem Prim.subst_atom {s : Sig} {Γ : Ctx s} {S : Ty s} {T1 T2 : Ty (s,x)} {b : Atom s} {V : Ty s}
    (h : Prim (Γ.cons S) T1 T2) (hb : ATy Γ b V) (hp : Prim Γ V S) :
    ∃ c : Cert s, CTy Γ c (T1.substVar b.root) (T2.substVar b.root) := by
  obtain ⟨d⟩ := primitive_sound h
  obtain ⟨db⟩ := ATy.sound hb
  obtain ⟨dp⟩ := primitive_sound hp
  exact cert_complete (d.retype (Rename.subst b.root) (DotMNF.Ctx.Retypes.subst (.sub db dp)))

/-- Likewise for a certificate. -/
theorem CTy.subst_atom {s : Sig} {Γ : Ctx s} {S : Ty s} {c : Cert (s,x)} {T1 T2 : Ty (s,x)} {b : Atom s}
    {V : Ty s} (h : CTy (Γ.cons S) c T1 T2) (hb : ATy Γ b V) (hp : Prim Γ V S) :
    ∃ c' : Cert s, CTy Γ c' (T1.substVar b.root) (T2.substVar b.root) := by
  obtain ⟨d⟩ := CTy.sound h
  obtain ⟨db⟩ := ATy.sound hb
  obtain ⟨dp⟩ := primitive_sound hp
  exact cert_complete (d.retype (Rename.subst b.root) (DotMNF.Ctx.Retypes.subst (.sub db dp)))

end Selective
