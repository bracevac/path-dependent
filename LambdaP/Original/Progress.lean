import LambdaP.Original.Machine
import LambdaP.Original.StoreRefinement
import LambdaP.Original.PathPreservation

/-!
Progress cases for the original machine which do not require path or
subtyping inversion.

The remaining global progress theorem must supply resolution for compound
paths and a lambda lookup for applications.  Keeping those premises explicit
separates the operational case analysis from the canonical-form argument.
-/

namespace LambdaP.Original

/-- A state is final or takes one historical machine step. -/
inductive State.Progress (s : State n) : Prop where
| final : s.IsFinal -> State.Progress s
| step : State.Step s s' -> State.Progress s

/-- A public context lookup has a matching stored value. -/
theorem Store.Ty.of_ctx_binds
    {n : Nat} {Γ : Ctx n} {σ : Store n} {x : Fin n}
    {T : LambdaP.Original.Ty n}
    (hσ : Store.Ty Γ σ) (hb : Ctx.Binds Γ x T) :
    ∃ v, Store.Binds σ x v ∧ Tm.Ty Γ v T := by
  obtain ⟨v, P, hv, hp, ht, hsub⟩ := hσ.toRefined.of_ctx_binds hb
  exact ⟨v, hv, ht⟩

/-- Every context index of a well-typed store is occupied. -/
theorem Store.Ty.lookup_exists
    {n : Nat} {Γ : Ctx n} {σ : Store n}
    (hσ : Store.Ty Γ σ) (x : Fin n) :
    ∃ v, Store.Binds σ x v := by
  obtain ⟨T, hT⟩ := Ctx.Binds.exists Γ x
  obtain ⟨v, hv, ht⟩ := hσ.of_ctx_binds hT
  exact ⟨v, hv⟩

/-- An atomic path is final under an empty continuation and otherwise fires
the `rename` transition. -/
theorem State.Progress.path_var
    {n : Nat} {Γ : Ctx n} {σ : Store n}
    (hσ : Store.Ty Γ σ) (x : Fin n) (k : Tm.Cont n) :
    State.Progress ⟨σ, k, Tm.path (Path.var x)⟩ := by
  cases k with
  | nil =>
      obtain ⟨v, hv⟩ := hσ.lookup_exists x
      exact .final (.is_var hv)
  | cons F k =>
      cases F with
      | «let» t => exact .step (.rename)

/-- A value is final under an empty continuation and otherwise allocates. -/
theorem State.Progress.value
    {n : Nat} {v : Tm n}
    (hv : v.IsValue) (σ : Store n) (k : Tm.Cont n) :
    State.Progress ⟨σ, k, v⟩ := by
  cases k with
  | nil => exact .final (.is_val hv)
  | cons F k =>
      cases F with
      | «let» t => exact .step (.lift hv)

/-- `let` always pushes a frame. -/
theorem State.Progress.let_term
    {n : Nat}
    (σ : Store n) (k : Tm.Cont n) (s : Tm n) (t : Tm (n + 1)) :
    State.Progress ⟨σ, k, Tm.let s t⟩ :=
  .step (.let_push)

/-- Ascription erasure always steps. -/
theorem State.Progress.typed
    {n : Nat}
    (σ : Store n) (k : Tm.Cont n) (t : Tm n)
    (T : LambdaP.Original.Ty n) :
    State.Progress ⟨σ, k, Tm.typed t T⟩ :=
  .step (.ascribe)

/-- Resolution of a non-atomic path is exactly the remaining premise for its
progress case. -/
theorem State.Progress.path
    {n : Nat} {σ : Store n} {p : Path n} {x : Fin n}
    {k : Tm.Cont n}
    (hr : Path.reduce p σ x) (hnv : ¬ p.IsVar) :
    State.Progress ⟨σ, k, Tm.path p⟩ :=
  .step (.path hr hnv)

/-- The application case is operationally complete once both paths resolve
and the function location is known to contain an abstraction. -/
theorem State.Progress.app
    {n : Nat} {σ : Store n} {p q : Path n} {x y : Fin n}
    {A : LambdaP.Original.Ty n} {body : Tm (n + 1)}
    {k : Tm.Cont n}
    (hp : Path.reduce p σ x)
    (hq : Path.reduce q σ y)
    (hv : Store.Binds σ x (Tm.abs A body)) :
    State.Progress ⟨σ, k, Tm.app p q⟩ :=
  .step (.app hp hq hv)

end LambdaP.Original
