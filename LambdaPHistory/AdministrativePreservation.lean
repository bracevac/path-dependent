import LambdaPHistory.Machine

/-!
Preservation for the three administrative transitions of the original
machine.  The computational path, application, and variable-opening cases are
deliberately left out: this file isolates the cases that require only typing
inversion plus continuation/store weakening.
-/

namespace LambdaPHistory

/-- A transition either preserves the current context or allocates one new
store cell and weakens the observable result type. -/
inductive Preserve : Ctx n -> State m -> LambdaPHistory.Ty n -> Prop where
| same :
    State.Ty Γ s T ->
    Preserve Γ s T
| extend :
    State.Ty (Γ.snoc S) s T.weaken ->
    Preserve Γ s T

/-! ## Typing inversion through trailing subsumption -/

/-- Induction-strengthened inversion for `let`, stated for an arbitrary term
plus an equality exposing its outer constructor. -/
theorem Tm.Ty.let_inv_of_eq
    {n : Nat} {Γ : Ctx n} {u : Tm n} {T : LambdaPHistory.Ty n}
    (h : Tm.Ty Γ u T) :
    ∀ {s : Tm n} {t : Tm (n + 1)}, u = Tm.let s t ->
      ∃ S, Tm.Ty Γ s S ∧ Tau.Wf Γ (Tau.ty T) ∧
        Tm.Ty (Γ.snoc S) t T.weaken := by
  induction h with
  | path _ =>
      intro s t he
      cases he
  | abs _ _ _ =>
      intro s t he
      cases he
  | app _ _ _ _ =>
      intro s t he
      cases he
  | pair _ _ =>
      intro s t he
      cases he
  | tpair _ _ =>
      intro s t he
      cases he
  | «let» hs hwf ht _ _ =>
      intro s t he
      cases he
      exact ⟨_, hs, hwf, ht⟩
  | typed _ _ _ =>
      intro s t he
      cases he
  | sub ht hsub hwf ih =>
      intro s t he
      obtain ⟨S, hs, _, hb⟩ := ih he
      exact ⟨S, hs, hwf,
        Tm.Ty.sub hb (hsub.weaken (S := S)) (hwf.weaken (S := S))⟩

/-- Invert a typed `let`.  Any subsumption above the introduction rule is
pushed into the body, so the body has exactly the type assigned to the whole
`let` after weakening. -/
theorem Tm.Ty.let_inv (h : Tm.Ty Γ (Tm.let s t) T) :
    ∃ S, Tm.Ty Γ s S ∧ Tau.Wf Γ (Tau.ty T) ∧
      Tm.Ty (Γ.snoc S) t T.weaken :=
  h.let_inv_of_eq rfl

/-- Induction-strengthened inversion for an ascription. -/
theorem Tm.Ty.typed_inv_of_eq
    {n : Nat} {Γ : Ctx n} {u : Tm n} {T : LambdaPHistory.Ty n}
    (h : Tm.Ty Γ u T) :
    ∀ {t : Tm n} {A : LambdaPHistory.Ty n}, u = Tm.typed t A ->
      Tm.Ty Γ t T ∧ Tau.Wf Γ (Tau.ty T) := by
  induction h with
  | path _ =>
      intro t A he
      cases he
  | abs _ _ _ =>
      intro t A he
      cases he
  | app _ _ _ _ =>
      intro t A he
      cases he
  | pair _ _ =>
      intro t A he
      cases he
  | tpair _ _ =>
      intro t A he
      cases he
  | «let» _ _ _ _ _ =>
      intro t A he
      cases he
  | typed ht hwf _ =>
      intro t A he
      cases he
      exact ⟨ht, hwf⟩
  | sub ht hsub hwf ih =>
      intro t A he
      obtain ⟨ht, _⟩ := ih he
      exact ⟨Tm.Ty.sub ht hsub hwf, hwf⟩

/-- Invert an ascription.  Trailing subsumption is transferred to the
ascribed term, yielding exactly the externally assigned result type. -/
theorem Tm.Ty.typed_inv (h : Tm.Ty Γ (Tm.typed t A) T) :
    Tm.Ty Γ t T ∧ Tau.Wf Γ (Tau.ty T) :=
  h.typed_inv_of_eq rfl

/-! ## Administrative preservation cases -/

theorem Preserve.let_push
    (h : State.Ty Γ ⟨σ, k, Tm.let s t⟩ T) :
    Preserve Γ ⟨σ, Tm.Frame.let t :: k, s⟩ T := by
  cases h with
  | ok hσ hk ht =>
      obtain ⟨S, hs, _, hb⟩ := ht.let_inv
      exact .same (.ok hσ (.cons hk (.let hb)) hs)

theorem Preserve.lift
    (hv : v.IsValue)
    (h : State.Ty Γ ⟨σ, Tm.Frame.let t :: k, v⟩ T) :
    Preserve Γ ⟨Store.val σ v hv, Tm.Cont.weaken k, t⟩ T := by
  cases h with
  | ok hσ hk hvty =>
      cases hk with
      | cons hk hf =>
          cases hf with
          | «let» hb =>
              exact .extend (.ok (.val hσ hvty) hk.weaken hb)

theorem Preserve.ascribe
    (h : State.Ty Γ ⟨σ, k, Tm.typed t A⟩ T) :
    Preserve Γ ⟨σ, k, t⟩ T := by
  cases h with
  | ok hσ hk ht =>
      exact .same (.ok hσ hk ht.typed_inv.1)

end LambdaPHistory
