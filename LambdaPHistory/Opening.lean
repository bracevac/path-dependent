import LambdaPHistory.Renaming

/-!
Exact variable opening for the original intrinsically scoped judgments.

This is the ordinary substitution lemma available without any alias
conversion: if the replacement variable has exactly the type assigned to the
newest binder, opening is just a context-respecting renaming.  Operational
beta reduction and `let` renaming generally know the replacement only at a
subtype of the binder type; keeping this exact lemma separate identifies the
additional conversion theorem those cases require.
-/

namespace LambdaPHistory

/-- Removing the newest context entry is a valid renaming when its image is
an existing variable with exactly the stored binder type. -/
theorem Renaming.open
    {n : Nat} {Γ : Ctx n} {S : Ty n} {x : Fin n}
    (hx : Ctx.Binds Γ x S) :
    Renaming (Γ.snoc S) (FinFun.openAt x) Γ := by
  intro y T hy
  cases hy with
  | here =>
      simpa only [FinFun.openAt_zero, Ty.weaken, Ty.rename_rename,
        FinFun.openAt_weaken, Ty.rename_id] using hx
  | there hy =>
      simpa only [FinFun.openAt_succ, Ty.weaken, Ty.rename_rename,
        FinFun.openAt_weaken, Ty.rename_id] using hy

/-- Exact opening preserves precise path typing. -/
theorem Path.Ty.open_var
    (h : Path.Ty (Γ.snoc S) p τ)
    (hx : Ctx.Binds Γ x S) :
    Path.Ty Γ (p.rename (FinFun.openAt x))
      (τ.rename (FinFun.openAt x)) :=
  h.rename (Renaming.open hx)

/-- Exact opening preserves generalized subtyping. -/
theorem Tau.Sub.open_var
    (h : Tau.Sub (Γ.snoc S) τ₁ τ₂)
    (hx : Ctx.Binds Γ x S) :
    Tau.Sub Γ (τ₁.rename (FinFun.openAt x))
      (τ₂.rename (FinFun.openAt x)) :=
  h.rename (Renaming.open hx)

/-- Exact opening preserves well-formedness. -/
theorem Tau.Wf.open_var
    (h : Tau.Wf (Γ.snoc S) τ)
    (hx : Ctx.Binds Γ x S) :
    Tau.Wf Γ (τ.rename (FinFun.openAt x)) :=
  h.rename (Renaming.open hx)

/-- Exact opening preserves term typing. -/
theorem Tm.Ty.open_var
    (h : Tm.Ty (Γ.snoc S) t T)
    (hx : Ctx.Binds Γ x S) :
    Tm.Ty Γ (t.open x) (T.rename (FinFun.openAt x)) := by
  simpa [Tm.open] using h.rename (Renaming.open hx)

/-- The common historical body shape `T.weaken` opens back to `T`. -/
theorem Tm.Ty.open_var_weaken
    (h : Tm.Ty (Γ.snoc S) t T.weaken)
    (hx : Ctx.Binds Γ x S) :
    Tm.Ty Γ (t.open x) T := by
  have hT : T.weaken.rename (FinFun.openAt x) = T := by
    rw [LambdaPHistory.Ty.weaken,
      LambdaPHistory.Ty.rename_rename,
      FinFun.openAt_weaken, LambdaPHistory.Ty.rename_id]
  rw [← hT]
  exact h.open_var hx

end LambdaPHistory
