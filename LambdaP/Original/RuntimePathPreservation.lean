import LambdaP.Original.RuntimeTyping
import LambdaP.Original.State
import LambdaP.Original.Machine

/-!
State-level preservation for the historical path-normalization step.

The store and continuation retain their source typings.  Only the current
term is typed modulo store-justified conversion, exactly where the ordinary
preservation counterexample shows that source typing is too rigid.
-/

namespace LambdaP.Original

/-- A first runtime-aware state invariant: source-typed store and
continuation, with the current term typed modulo runtime path conversion. -/
inductive State.RuntimeTy :
    Ctx n -> State n -> LambdaP.Original.Ty n -> Prop where
| ok {n : Nat} {Γ : Ctx n} {σ : Store n}
    {S T : LambdaP.Original.Ty n}
    {k : Tm.Cont n} {t : Tm n} :
    Store.Ty Γ σ ->
    Tm.Cont.Ty Γ S k T ->
    Tm.RuntimeTy Γ σ t S ->
    State.RuntimeTy Γ ⟨σ, k, t⟩ T

/-- Every historically typed state satisfies the runtime-aware invariant. -/
theorem State.Ty.toRuntime (h : State.Ty Γ s T) :
    State.RuntimeTy Γ s T := by
  cases h with
  | ok hσ hk ht =>
      exact .ok hσ hk (.of_source ht)

/-- The path-normalization transition preserves the runtime-aware state
invariant, including under a nonempty continuation. -/
theorem State.RuntimeTy.preserve_path
    {n : Nat} {Γ : Ctx n} {σ : Store n} {p : Path n}
    {x : Fin n} {k : Tm.Cont n} {T : LambdaP.Original.Ty n}
    (hr : Path.reduce p σ x)
    (h : State.RuntimeTy Γ ⟨σ, k, Tm.path p⟩ T) :
    State.RuntimeTy Γ ⟨σ, k, Tm.path (Path.var x)⟩ T := by
  cases h with
  | ok hσ hk ht =>
      exact .ok hσ hk (ht.reduce_path hr)

/-- The historical path step therefore maps a source-typed state to a state
with the same observable result type in the runtime-aware invariant. -/
theorem State.Ty.path_step_runtime_preservation
    {n : Nat} {Γ : Ctx n} {σ : Store n} {p : Path n}
    {x : Fin n} {k : Tm.Cont n} {T : LambdaP.Original.Ty n}
    (hr : Path.reduce p σ x)
    (h : State.Ty Γ ⟨σ, k, Tm.path p⟩ T) :
    State.RuntimeTy Γ ⟨σ, k, Tm.path (Path.var x)⟩ T :=
  h.toRuntime.preserve_path hr

/-- With syntax-directed store entries, the stronger historical source
typing itself is preserved by path normalization. -/
theorem State.Ty.path_step_precise_preservation
    {n : Nat} {Γ : Ctx n} {σ : Store n} {p : Path n}
    {x : Fin n} {k : Tm.Cont n} {T : LambdaP.Original.Ty n}
    (hσ : Store.PreciseTy Γ σ)
    (hr : Path.reduce p σ x)
    (h : State.Ty Γ ⟨σ, k, Tm.path p⟩ T) :
    State.Ty Γ ⟨σ, k, Tm.path (Path.var x)⟩ T := by
  cases h with
  | ok hstore hk ht =>
      exact .ok hstore hk (Path.reduce_preserves_source_typing hσ hr ht)

end LambdaP.Original
