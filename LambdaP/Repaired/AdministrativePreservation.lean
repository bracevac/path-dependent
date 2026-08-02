import LambdaP.Repaired.Machine

/-! Preservation for let-push, allocation, and ascription erasure. -/

namespace LambdaP.Repaired

inductive Preserve : Ctx n -> State m -> LambdaP.Repaired.Ty n -> Prop where
| same :
    State.Ty Gamma s T ->
    Preserve Gamma s T
| extend :
    State.Ty (Gamma.snoc S) s T.weaken ->
    Preserve Gamma s T

theorem Tm.Ty.let_inv_of_eq
    {n : Nat} {Gamma : Ctx n} {u : Tm n} {T : LambdaP.Repaired.Ty n}
    (h : Tm.Ty Gamma u T) :
    forall {s : Tm n} {t : Tm (n + 1)}, u = Tm.let s t ->
      exists S, Tm.Ty Gamma s S /\ Tau.Wf Gamma (Tau.ty T) /\
        Tm.Ty (Gamma.snoc S) t T.weaken := by
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

theorem Tm.Ty.let_inv (h : Tm.Ty Gamma (Tm.let s t) T) :
    exists S, Tm.Ty Gamma s S /\ Tau.Wf Gamma (Tau.ty T) /\
      Tm.Ty (Gamma.snoc S) t T.weaken :=
  h.let_inv_of_eq rfl

theorem Tm.Ty.typed_inv_of_eq
    {n : Nat} {Gamma : Ctx n} {u : Tm n} {T : LambdaP.Repaired.Ty n}
    (h : Tm.Ty Gamma u T) :
    forall {t : Tm n} {A : LambdaP.Repaired.Ty n}, u = Tm.typed t A ->
      Tm.Ty Gamma t T /\ Tau.Wf Gamma (Tau.ty T) := by
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

theorem Tm.Ty.typed_inv (h : Tm.Ty Gamma (Tm.typed t A) T) :
    Tm.Ty Gamma t T /\ Tau.Wf Gamma (Tau.ty T) :=
  h.typed_inv_of_eq rfl

theorem Preserve.let_push
    (h : State.Ty Gamma ⟨sigma, k, Tm.let s t⟩ T) :
    Preserve Gamma ⟨sigma, Tm.Frame.let t :: k, s⟩ T := by
  cases h with
  | ok hsigma hk ht =>
      obtain ⟨S, hs, _, hb⟩ := ht.let_inv
      exact .same (.ok hsigma (.cons hk (.let hb)) hs)

theorem Preserve.lift
    (hv : v.IsValue)
    (h : State.Ty Gamma ⟨sigma, Tm.Frame.let t :: k, v⟩ T) :
    Preserve Gamma ⟨Store.val sigma v hv, Tm.Cont.weaken k, t⟩ T := by
  cases h with
  | ok hsigma hk hvty =>
      cases hk with
      | cons hk hf =>
          cases hf with
          | «let» hb =>
              exact .extend (.ok (.val hsigma hvty) hk.weaken hb)

theorem Preserve.ascribe
    (h : State.Ty Gamma ⟨sigma, k, Tm.typed t A⟩ T) :
    Preserve Gamma ⟨sigma, k, t⟩ T := by
  cases h with
  | ok hsigma hk ht => exact .same (.ok hsigma hk ht.typed_inv.1)

end LambdaP.Repaired
