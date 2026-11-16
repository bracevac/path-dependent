import Coercions.Selective.Check

/-!
# Renaming and weakening of evidence and annotated terms

Every judgment of `H` is preserved by a renaming `ρ` that preserves context
lookup (`Γ.Renames Δ ρ`), with the evidence renamed along.  The root of a
renamed atom is the renamed root (`Atom.root_rename`), so the `unfold`,
`fold`, `app` and `proj` cases instantiate at the right variable
(`DotMNF.Ty.substVar_rename`, as `Exp.rename` does).  Weakening is the
instance `ρ = Rename.succ`.

Renaming is not substitution of an atom for a variable; re-annotation under
substitution (`HTy.subst_atom`) is in `Subst.lean`.
-/

namespace Selective

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ctx Ty Path)

theorem FExp.rename {s1 s2 : Sig} {x : BVar s1 .var} {V : Ty s1} {a : Label} {T : Ty s1} :
    FExp x V a T → (ρ : Rename s1 s2) → FExp (ρ.var x) (V.rename ρ) a (T.rename ρ)
  | .fld, _ => .fld
  | .andL e, ρ => .andL (e.rename ρ)
  | .andR e, ρ => .andR (e.rename ρ)
  | .mu e, ρ => .mu (by
      have := e.rename ρ
      rwa [DotMNF.Ty.substVar_rename] at this)

mutual
theorem ATy.rename {s1 s2 : Sig} {Γ : Ctx s1} {a : Atom s1} {T : Ty s1} (h : ATy Γ a T)
    {Δ : Ctx s2} (ρ : Rename s1 s2) (hρ : Γ.Renames Δ ρ) :
    ATy Δ (a.rename ρ) (T.rename ρ) :=
  match h with
  | .var (x := x) => by rw [← hρ x]; exact .var
  | .cast ha hc => .cast (ha.rename ρ hρ) (hc.rename ρ hρ)
  | .unfold (a := a) ha => by
      have h1 := ATy.unfold (ha.rename ρ hρ)
      rw [Atom.root_rename, ← DotMNF.Ty.substVar_rename] at h1
      exact h1
  | .fold (a := a) ha => by
      have h1 := ha.rename ρ hρ
      rw [DotMNF.Ty.substVar_rename, ← Atom.root_rename] at h1
      exact .fold h1
  | .both ha hb hr => .both (ha.rename ρ hρ) (hb.rename ρ hρ) (by simp [hr])
theorem CTy.rename {s1 s2 : Sig} {Γ : Ctx s1} {c : Cert s1} {S T : Ty s1} (h : CTy Γ c S T)
    {Δ : Ctx s2} (ρ : Rename s1 s2) (hρ : Γ.Renames Δ ρ) :
    CTy Δ (c.rename ρ) (S.rename ρ) (T.rename ρ) :=
  match h with
  | .step p => .step (p.rename ρ hρ)
  | .seq h1 h2 => .seq (h1.rename ρ hρ) (h2.rename ρ hρ)
  | .pos hk => .pos (hk.rename ρ hρ)
theorem PTy.rename {s1 s2 : Sig} {Γ : Ctx s1} {k : Pos s1} {S T : Ty s1} (h : PTy Γ k S T)
    {Δ : Ctx s2} (ρ : Rename s1 s2) (hρ : Γ.Renames Δ ρ) :
    PTy Δ (k.rename ρ) (S.rename ρ) (T.rename ρ) :=
  match h with
  | .selU (a := a) ha he => by
      have h1 := PTy.selU (ha.rename ρ hρ) (by rw [Atom.root_rename]; exact he.rename ρ)
      rw [Atom.root_rename] at h1
      exact h1
  | .selL (a := a) ha he => by
      have h1 := PTy.selL (ha.rename ρ hρ) (by rw [Atom.root_rename]; exact he.rename ρ)
      rw [Atom.root_rename] at h1
      exact h1
  | .fld hk => .fld (hk.rename ρ hρ)
  | .typL hk => .typL (hk.rename ρ hρ)
  | .typU hk => .typU (hk.rename ρ hρ)
  | .allD hk => .allD (hk.rename ρ hρ)
  | .allC hk => .allC (hk.rename ρ.lift (hρ.cons _))
  | .andL hk => .andL (hk.rename ρ hρ)
  | .andR hk => .andR (hk.rename ρ hρ)
end

mutual
theorem HTy.rename {s1 s2 : Sig} {Γ : Ctx s1} {t : HTm s1} {T : Ty s1} (h : HTy Γ t T)
    {Δ : Ctx s2} (ρ : Rename s1 s2) (hρ : Γ.Renames Δ ρ) :
    HTy Δ (t.rename ρ) (T.rename ρ) :=
  match h with
  | .atom ha => .atom (ha.rename ρ hρ)
  | .lam ht => .lam (ht.rename ρ.lift (hρ.cons _))
  | .app (b := b) ha hb hp => by
      have h1 := HTy.app (ha.rename ρ hρ) (hb.rename ρ hρ) (hp.rename ρ hρ)
      rw [Atom.root_rename, ← DotMNF.Ty.substVar_rename] at h1
      exact h1
  | .obj (d := d) (T := T) hd hdist => by
      have h1 := hd.rename ρ.lift (hρ.consSelf d.erase T)
      rw [← HDefs.erase_rename] at h1
      exact .obj h1 (by rw [HDefs.erase_rename]; exact hdist.rename ρ.lift)
  | .proj ha hf => .proj (ha.rename ρ hρ) (by rw [Atom.root_rename]; exact hf.rename ρ)
  | .let h1 h2 => by
      have h2' := h2.rename ρ.lift (hρ.cons _)
      rw [DotMNF.Ty.weaken_rename] at h2'
      exact .let (h1.rename ρ hρ) h2'
  | .cast ht hp hc => .cast (ht.rename ρ hρ) (hp.rename ρ hρ) (hc.rename ρ hρ)
theorem HDefsTy.rename {s1 s2 : Sig} {Γ : Ctx s1} {d : HDefs s1} {T : Ty s1} (h : HDefsTy Γ d T)
    {Δ : Ctx s2} (ρ : Rename s1 s2) (hρ : Γ.Renames Δ ρ) :
    HDefsTy Δ (d.rename ρ) (T.rename ρ) :=
  match h with
  | .typ => .typ
  | .trm ht => .trm (ht.rename ρ hρ)
  | .and h1 h2 => .and (h1.rename ρ hρ) (h2.rename ρ hρ)
end

/-! ## Weakening -/

theorem ATy.weaken {s : Sig} {Γ : Ctx s} {a : Atom s} {T : Ty s} (h : ATy Γ a T) (V : Ty s) :
    ATy (Γ.cons V) (a.rename Rename.succ) T.weaken :=
  h.rename Rename.succ (fun _ => rfl)

theorem CTy.weaken {s : Sig} {Γ : Ctx s} {c : Cert s} {S T : Ty s} (h : CTy Γ c S T) (V : Ty s) :
    CTy (Γ.cons V) (c.rename Rename.succ) S.weaken T.weaken :=
  h.rename Rename.succ (fun _ => rfl)

theorem HTy.weaken {s : Sig} {Γ : Ctx s} {t : HTm s} {T : Ty s} (h : HTy Γ t T) (V : Ty s) :
    HTy (Γ.cons V) (t.rename Rename.succ) T.weaken :=
  h.rename Rename.succ (fun _ => rfl)

end Selective
