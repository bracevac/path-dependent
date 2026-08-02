import LambdaP.Original.Renaming
import LambdaP.Original.Store

/-!
Syntax-directed typing for values and stores.

The ordinary term judgment includes subsumption, so it does not expose the
outer shape of a stored value's type.  `Tm.PreciseTy` records the type given
directly by the value introduction rule.  `Store.PreciseTy` then relates a
store to the context formed from exactly those types.
-/

namespace LambdaP.Original

/-- The type assigned directly by a value-introduction rule. -/
inductive Tm.PreciseTy : Ctx n -> Tm n -> LambdaP.Original.Ty n -> Prop where
| abs :
    Tm.Ty (Γ.snoc S) t T ->
    Tau.Wf Γ (Tau.ty S) ->
    Tm.PreciseTy Γ (Tm.abs S t) (Ty.Fun S T)
| pair :
    Ctx.Binds Γ y S ->
    Ctx.Binds Γ z T ->
    Tm.PreciseTy Γ (Tm.pair y a (Def.val z))
      (Ty.Pair (Ty.Single (Path.var y)) a
        (Tau.ty (Ty.Single (Path.var z).weaken)))
| tpair :
    Ctx.Binds Γ y S ->
    Tau.Wf Γ (Tau.ty T) ->
    Tm.PreciseTy Γ (Tm.pair y A (Def.type T))
      (Ty.Pair (Ty.Single (Path.var y)) A (Tau.intv T T).weaken)

/-- Precisely typed terms are values. -/
theorem Tm.PreciseTy.isValue (h : Tm.PreciseTy Γ v T) : v.IsValue := by
  cases h <;> constructor

/-- A precise derivation is also an ordinary typing derivation. -/
theorem Tm.PreciseTy.toTy (h : Tm.PreciseTy Γ v T) : Tm.Ty Γ v T := by
  cases h with
  | abs ht hwf => exact Tm.Ty.abs ht hwf
  | pair hy hz => exact Tm.Ty.pair hy hz
  | tpair hy hwf => exact Tm.Ty.tpair hy hwf

/-- Precise value typing is stable under every context-respecting renaming. -/
theorem Tm.PreciseTy.rename {n : Nat} {Γ : Ctx n} {v : Tm n}
    {T : LambdaP.Original.Ty n} (h : Tm.PreciseTy Γ v T) :
    ∀ {m} {f : FinFun n m} {Δ : Ctx m},
      Renaming Γ f Δ -> Tm.PreciseTy Δ (v.rename f) (T.rename f) := by
  cases h with
  | abs ht hwf =>
      intro m f Δ ρ
      simpa [Tm.rename, Ty.rename] using
        Tm.PreciseTy.abs (ht.rename (Renaming.ext ρ)) (hwf.rename ρ)
  | pair hy hz =>
      intro m f Δ ρ
      simpa [Tm.rename, Def.rename, Ty.rename, Tau.rename, Path.rename,
        Path.weaken_rename] using
        Tm.PreciseTy.pair (ρ hy) (ρ hz)
  | tpair hy hwf =>
      intro m f Δ ρ
      simpa only [Tm.rename, Def.rename, LambdaP.Original.Ty.rename,
        Tau.rename, Path.rename, ← Tau.weaken_rename] using
        Tm.PreciseTy.tpair (ρ hy) (hwf.rename ρ)

/-- Weakening is the special case of precise renaming used by store growth. -/
theorem Tm.PreciseTy.weaken (h : Tm.PreciseTy Γ v T) :
    Tm.PreciseTy (Γ.snoc S) v.weaken T.weaken := by
  simpa [Tm.weaken, Ty.weaken] using h.rename (Renaming.weaken (S := S))

/-- Executable lookup for an intrinsically scoped context. -/
def Ctx.lookup : (Γ : Ctx n) -> Fin n -> Ty n
| .nil, x => Fin.elim0 x
| .snoc Γ T, x =>
    Fin.cases T.weaken (fun y => (Ctx.lookup Γ y).weaken) x

theorem Ctx.Binds.lookup_eq (h : Ctx.Binds Γ x T) : Ctx.lookup Γ x = T := by
  induction h with
  | here => rfl
  | there _ ih => simpa [Ctx.lookup] using congrArg Ty.weaken ih

/-- Context lookup is functional. -/
theorem Ctx.Binds.unique
    (h₁ : Ctx.Binds Γ x T₁) (h₂ : Ctx.Binds Γ x T₂) : T₁ = T₂ := by
  exact h₁.lookup_eq.symm.trans h₂.lookup_eq

/-- A store and context built in lockstep from precise value types. -/
inductive Store.PreciseTy : Ctx n -> Store n -> Prop where
| empty : Store.PreciseTy Ctx.nil (Store.empty : Store 0)
| val :
    Store.PreciseTy Γ σ ->
    Tm.PreciseTy Γ v T ->
    (vv : v.IsValue) ->
    Store.PreciseTy (Γ.snoc T) (Store.val σ v vv)

/-- A precisely typed store is ordinarily well typed. -/
theorem Store.PreciseTy.toTy (h : Store.PreciseTy Γ σ) : Store.Ty Γ σ := by
  induction h with
  | empty => exact Store.Ty.empty
  | val _ hv _ ih => exact Store.Ty.val ih hv.toTy

/-- Inverting a store lookup recovers the exact corresponding context type. -/
theorem Store.PreciseTy.of_store_binds
    (hσ : Store.PreciseTy Γ σ) (hb : Store.Binds σ x v) :
    ∃ T, Ctx.Binds Γ x T ∧ Tm.PreciseTy Γ v T := by
  induction hσ with
  | empty => exact Fin.elim0 x
  | val hσ hv vv ih =>
      cases hb with
      | here =>
          exact ⟨_, Ctx.Binds.here, hv.weaken⟩
      | there hb =>
          obtain ⟨U, hU, hp⟩ := ih hb
          exact ⟨U.weaken, Ctx.Binds.there hU, hp.weaken⟩

/-- Conversely, each context lookup has a matching precisely typed value. -/
theorem Store.PreciseTy.of_ctx_binds
    (hσ : Store.PreciseTy Γ σ) (hb : Ctx.Binds Γ x T) :
    ∃ v, Store.Binds σ x v ∧ Tm.PreciseTy Γ v T := by
  induction hσ with
  | empty => exact Fin.elim0 x
  | val hσ hv vv ih =>
      cases hb with
      | here =>
          exact ⟨_, Store.Binds.here, hv.weaken⟩
      | there hb =>
          obtain ⟨u, hu, hp⟩ := ih hb
          exact ⟨u.weaken, Store.Binds.there hu, hp.weaken⟩

/-- If both lookups are supplied, their shared precise type is forced. -/
theorem Store.PreciseTy.lookup
    (hσ : Store.PreciseTy Γ σ)
    (hs : Store.Binds σ x v) (hc : Ctx.Binds Γ x T) :
    Tm.PreciseTy Γ v T := by
  obtain ⟨U, hU, hv⟩ := hσ.of_store_binds hs
  cases hU.unique hc
  exact hv

end LambdaP.Original
