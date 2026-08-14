import LambdaP.Machine
import LambdaP.PathPreservation

/-! Operational progress cases that do not require canonical-form inversion. -/

namespace LambdaP

inductive State.Progress (s : State n) : Prop where
| final : s.IsFinal -> State.Progress s
| step : State.Step s s' -> State.Progress s

theorem Store.Ty.of_ctx_binds
    {n : Nat} {Gamma : Ctx n} {sigma : Store n} {x : Fin n}
    {T : LambdaP.Ty n}
    (hsigma : Store.Ty Gamma sigma) (hb : Ctx.Binds Gamma x T) :
    exists v, Store.Binds sigma x v /\ Tm.Ty Gamma v T := by
  induction hsigma with
  | empty => exact Fin.elim0 x
  | val hsigma ht ih =>
      cases hb with
      | here => exact ⟨_, Store.Binds.here, ht.weaken⟩
      | there hb =>
          obtain ⟨v, hv, hvt⟩ := ih hb
          exact ⟨v.weaken, Store.Binds.there hv, hvt.weaken⟩

theorem Store.Ty.lookup_exists
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    (hsigma : Store.Ty Gamma sigma) (x : Fin n) :
    exists v, Store.Binds sigma x v := by
  obtain ⟨T, hT⟩ := Ctx.Binds.exists Gamma x
  obtain ⟨v, hv, _⟩ := hsigma.of_ctx_binds hT
  exact ⟨v, hv⟩

theorem State.Progress.path_var
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    (hsigma : Store.Ty Gamma sigma) (x : Fin n) (k : Tm.Cont n) :
    State.Progress ⟨sigma, k, Tm.path (Path.var x)⟩ := by
  cases k with
  | nil =>
      obtain ⟨v, hv⟩ := hsigma.lookup_exists x
      exact .final (.is_var hv)
  | cons F k =>
      cases F with
      | «let» t => exact .step (.rename)

theorem State.Progress.value
    {n : Nat} {v : Tm n}
    (hv : v.IsValue) (sigma : Store n) (k : Tm.Cont n) :
    State.Progress ⟨sigma, k, v⟩ := by
  cases k with
  | nil => exact .final (.is_val hv)
  | cons F k =>
      cases F with
      | «let» t => exact .step (.lift hv)

theorem State.Progress.let_term
    {n : Nat}
    (sigma : Store n) (k : Tm.Cont n) (s : Tm n) (t : Tm (n + 1)) :
    State.Progress ⟨sigma, k, Tm.let s t⟩ :=
  .step (.let_push)

theorem State.Progress.typed
    {n : Nat}
    (sigma : Store n) (k : Tm.Cont n) (t : Tm n)
    (T : LambdaP.Ty n) :
    State.Progress ⟨sigma, k, Tm.typed t T⟩ :=
  .step (.ascribe)

theorem State.Progress.path
    {n : Nat} {sigma : Store n} {p : Path n} {x : Fin n}
    {k : Tm.Cont n}
    (hr : Path.reduce p sigma x) (hnv : ¬ p.IsVar) :
    State.Progress ⟨sigma, k, Tm.path p⟩ :=
  .step (.path hr hnv)

theorem State.Progress.app
    {n : Nat} {sigma : Store n} {p q : Path n} {x y : Fin n}
    {A : LambdaP.Ty n} {body : Tm (n + 1)}
    {k : Tm.Cont n}
    (hp : Path.reduce p sigma x)
    (hq : Path.reduce q sigma y)
    (hv : Store.Binds sigma x (Tm.abs A body)) :
    State.Progress ⟨sigma, k, Tm.app p q⟩ :=
  .step (.app hp hq hv)

end LambdaP
