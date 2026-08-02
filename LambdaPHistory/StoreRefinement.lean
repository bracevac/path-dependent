import LambdaPHistory.ValueInversion

/-!
A proof-only refinement of the historical public store typing.

`Store.Ty` records only the public type placed in the context.  Subsumption
can hide the introduction form of the stored value, so `Store.RefinedTy`
also retains its precise introduction type and the subtyping derivation from
that precise type to the public one.  Neither the source judgments nor the
machine state are changed.
-/

namespace LambdaPHistory

/-- A store typing enriched with the precise introduction type of each cell.
`P` is precise, while `T` is the public type recorded in the context. -/
inductive Store.RefinedTy : Ctx n -> Store n -> Prop where
| empty : Store.RefinedTy Ctx.nil (Store.empty : Store 0)
| val :
    Store.RefinedTy Γ σ ->
    Tm.PreciseTy Γ v P ->
    Tm.Ty Γ v T ->
    Tau.Sub Γ (Tau.ty P) (Tau.ty T) ->
    (vv : v.IsValue) ->
    Store.RefinedTy (Γ.snoc T) (Store.val σ v vv)

/-- Every historical public store typing admits the enriched proof data. -/
theorem Store.Ty.toRefined (h : Store.Ty Γ σ) : Store.RefinedTy Γ σ := by
  induction h with
  | empty => exact .empty
  | val hσ ht ih =>
      obtain ⟨P, hp, hsub⟩ := ht.value_inversion (by assumption)
      exact Store.RefinedTy.val ih hp ht hsub (by assumption)

/-- Forgetting precise types recovers the historical public store typing. -/
theorem Store.RefinedTy.toTy (h : Store.RefinedTy Γ σ) : Store.Ty Γ σ := by
  induction h with
  | empty => exact .empty
  | val hσ hp ht hsub vv ih => exact Store.Ty.val ih ht

/-- Every aligned store/context index has a value, its public type, and its
precise type.  The old-cell branch weakens all four witnesses together. -/
theorem Store.RefinedTy.lookup_exists
    {n : Nat} {Γ : Ctx n} {σ : Store n}
    (h : Store.RefinedTy Γ σ) (x : Fin n) :
    ∃ v T P,
      Store.Binds σ x v ∧
      Ctx.Binds Γ x T ∧
      Tm.PreciseTy Γ v P ∧
      Tm.Ty Γ v T ∧
      Tau.Sub Γ (Tau.ty P) (Tau.ty T) := by
  induction h with
  | empty => exact Fin.elim0 x
  | val hσ hp ht hsub vv ih =>
      refine Fin.cases ?_ (fun y => ?_) x
      · exact ⟨_, _, _, Store.Binds.here, Ctx.Binds.here,
          hp.weaken, ht.weaken, hsub.weaken⟩
      · obtain ⟨u, U, Q, hu, hU, hq, hut, hQU⟩ := ih y
        exact ⟨u.weaken, U.weaken, Q.weaken,
          Store.Binds.there hu, Ctx.Binds.there hU,
          hq.weaken, hut.weaken, hQU.weaken⟩

/-- Inverting a runtime store lookup recovers the aligned public context type,
the precise introduction type, and their subtype relation. -/
theorem Store.RefinedTy.of_store_binds
    {n : Nat} {Γ : Ctx n} {σ : Store n} {x : Fin n} {v : Tm n}
    (h : Store.RefinedTy Γ σ) (hs : Store.Binds σ x v) :
    ∃ T P,
      Ctx.Binds Γ x T ∧
      Tm.PreciseTy Γ v P ∧
      Tm.Ty Γ v T ∧
      Tau.Sub Γ (Tau.ty P) (Tau.ty T) := by
  obtain ⟨u, T, P, hu, hT, hp, ht, hsub⟩ := h.lookup_exists x
  cases hu.unique hs
  exact ⟨T, P, hT, hp, ht, hsub⟩

/-- Inverting a public context lookup recovers the aligned stored value, its
precise introduction type, and the refinement to the public type. -/
theorem Store.RefinedTy.of_ctx_binds
    {n : Nat} {Γ : Ctx n} {σ : Store n} {x : Fin n}
    {T : LambdaPHistory.Ty n}
    (h : Store.RefinedTy Γ σ) (hc : Ctx.Binds Γ x T) :
    ∃ v P,
      Store.Binds σ x v ∧
      Tm.PreciseTy Γ v P ∧
      Tm.Ty Γ v T ∧
      Tau.Sub Γ (Tau.ty P) (Tau.ty T) := by
  obtain ⟨v, U, P, hv, hU, hp, ht, hsub⟩ := h.lookup_exists x
  cases hU.unique hc
  exact ⟨v, P, hv, hp, ht, hsub⟩

/-- With both aligned lookup derivations supplied, only the precise type is
hidden; this is the convenient inversion form for preservation proofs. -/
theorem Store.RefinedTy.lookup
    {n : Nat} {Γ : Ctx n} {σ : Store n} {x : Fin n} {v : Tm n}
    {T : LambdaPHistory.Ty n}
    (h : Store.RefinedTy Γ σ)
    (hs : Store.Binds σ x v) (hc : Ctx.Binds Γ x T) :
    ∃ P,
      Tm.PreciseTy Γ v P ∧
      Tm.Ty Γ v T ∧
      Tau.Sub Γ (Tau.ty P) (Tau.ty T) := by
  obtain ⟨U, P, hU, hp, ht, hsub⟩ := h.of_store_binds hs
  cases hU.unique hc
  exact ⟨P, hp, ht, hsub⟩

end LambdaPHistory
