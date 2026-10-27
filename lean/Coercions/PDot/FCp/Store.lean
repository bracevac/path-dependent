import Coercions.PDot.FCp.Typing

/-!
# FCp stores and store typing (plan T.3, "Stores")

A store holds one value per variable, the newest last.  `Store.get` weakens what it reads, as
`Ctx.ty` does.  A typed store binds a lambda opaque at its function type and a literal transparent
at its object type, with the block of the literal under the binder.  The store variable is the
literal's own self in de Bruijn, so the block is the one `VA-Obj` used.

`Store.Typed.get_shape` is the plan's (I1) with the last conjunct of refute-d3's S2: a store
variable holds a lambda and has no block, or holds a literal and carries the block of that literal
with its self read as the variable (decision D14 of the groups file).
-/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

def Store.get : Store s → BVar s .var → Value s
  | .cons _ v, .here => v.weaken                            -- (σ, x ↦ v).get x = v↑
  | .cons σ _, .there y => (σ.get y).weaken                 -- (σ, x ↦ v).get y↑ = (σ.get y)↑
inductive Store.Typed : Store s → Ctx s → Prop where        -- ⊢ σ : Γ
  -- ST-Nil
  | nil : Store.Typed .nil .nil
  -- ST-Lam      binders σ Γ S, z of t T
  | lam : Store.Typed σ Γ → Value.HasType Γ (.lam S t) (.pi S T) → Store.Typed (σ.cons (.lam S t)) (Γ.cons (.opaque (.pi S T)))
  -- ST-Obj      binders σ Γ, z of ds, w of Tel, the store variable the literal's own self
  | obj : Store.Typed σ Γ → Value.HasType Γ (.obj Tel ds) (.mu Tel) → Store.Typed (σ.cons (.obj Tel ds)) (Γ.cons (.transparent (.mu Tel) ds.block))

/-- Reading the self of a literal as a variable, then weakening, is weakening under the self and
then reading it as the weakened variable. -/
theorem Rename.subst_comp_succ (y : BVar s .var) :
    (Rename.subst y).comp (Rename.succ (k := .var)) =
      (Rename.succ (k := .var)).lift.comp (Rename.subst (BVar.there y)) :=
  Rename.funext' (fun x => by cases x <;> rfl)

/-- Weakening under the self of a literal, then reading the self as the newest variable, is the
identity. -/
theorem Rename.succ_lift_comp_subst_here :
    (Rename.succ (k := .var)).lift.comp (Rename.subst (BVar.here (s := s) (k := .var))) = Rename.id :=
  Rename.funext' (fun x => by cases x <;> rfl)

theorem Store.Typed.get_shape {σ : Store s} {Γ : Ctx s} (h : Store.Typed σ Γ) (x : BVar s .var) :
    (∃ S t T, σ.get x = .lam S t ∧ Γ.ty x = .pi S T ∧ Γ.blockAt x = none) ∨
    (∃ Tel ds, σ.get x = .obj Tel ds ∧ Γ.ty x = .mu Tel ∧ Γ.blockAt x = some (ds.rename (Rename.subst x)).block) := by
  induction h with
  | nil => nomatch x
  | @lam s σ Γ S t T _ _ ih =>
      cases x with
      | here => exact .inl ⟨_, _, _, rfl, rfl, rfl⟩
      | there y =>
          rcases ih y with ⟨S', t', T', e1, e2, e3⟩ | ⟨Tel, ds, e1, e2, e3⟩
          · refine .inl ⟨S'.rename Rename.succ, t'.rename Rename.succ.lift, T'.rename Rename.succ.lift, ?_, ?_, ?_⟩
            · show (σ.get y).weaken = _; rw [e1]; rfl
            · show (Γ.ty y).weaken = _; rw [e2]; rfl
            · show (Γ.blockAt y).map _ = _; rw [e3]; rfl
          · refine .inr ⟨Tel.rename Rename.succ.lift, ds.rename Rename.succ.lift, ?_, ?_, ?_⟩
            · show (σ.get y).weaken = _; rw [e1]; rfl
            · show (Γ.ty y).weaken = _; rw [e2]; rfl
            · show (Γ.blockAt y).map _ = _
              rw [e3]
              show some ((ds.rename (Rename.subst y)).block.rename Rename.succ) = _
              rw [Defs.block_rename, Defs.rename_rename, Defs.rename_rename, Rename.subst_comp_succ]
  | @obj s σ Γ Tel ds _ _ ih =>
      cases x with
      | here =>
          refine .inr ⟨_, _, rfl, rfl, ?_⟩
          show some ds.block = some (((ds.rename Rename.succ.lift).rename (Rename.subst .here))).block
          rw [Defs.rename_rename, Rename.succ_lift_comp_subst_here, Defs.rename_id]
      | there y =>
          rcases ih y with ⟨S', t', T', e1, e2, e3⟩ | ⟨Tel', ds', e1, e2, e3⟩
          · refine .inl ⟨S'.rename Rename.succ, t'.rename Rename.succ.lift, T'.rename Rename.succ.lift, ?_, ?_, ?_⟩
            · show (σ.get y).weaken = _; rw [e1]; rfl
            · show (Γ.ty y).weaken = _; rw [e2]; rfl
            · show (Γ.blockAt y).map _ = _; rw [e3]; rfl
          · refine .inr ⟨Tel'.rename Rename.succ.lift, ds'.rename Rename.succ.lift, ?_, ?_, ?_⟩
            · show (σ.get y).weaken = _; rw [e1]; rfl
            · show (Γ.ty y).weaken = _; rw [e2]; rfl
            · show (Γ.blockAt y).map _ = _
              rw [e3]
              show some ((ds'.rename (Rename.subst y)).block.rename Rename.succ) = _
              rw [Defs.block_rename, Defs.rename_rename, Defs.rename_rename, Rename.subst_comp_succ]

end PDot.FCp
