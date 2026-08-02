import LambdaPFC.SemanticTyping
import LambdaPFC.SemanticWeakening

/-!
Allocation weakening for normalized term and machine evidence.

An allocation shifts every old location by one.  Runtime terms, frames, and
their advertised types are renamed by the same weakening, while closures
use the lifted renaming supplied by `SemanticWeakening`.
-/

namespace LambdaPFC

noncomputable section

/-! ## Terms and values -/

private theorem tpairType_rename_weaken
    (y : Fin n) (A : Name) (W : Ty n) :
    (Ty.Pair (.Single (.var y)) A
      (Tau.intv W W).weaken).rename FinFun.weaken =
      Ty.Pair (.Single (.var (FinFun.weaken y))) A
        (Tau.intv (W.rename FinFun.weaken)
          (W.rename FinFun.weaken)).weaken := by
  simp only [Ty.rename, Path.rename]
  rw [← Tau.weaken_rename]
  rfl

/-- Value evidence for an old term survives allocation. -/
noncomputable def ValueEvidence.weaken
    {n : Nat} {sigma : Store n} {term : Tm n} {T : Ty n}
    (evidence : ValueEvidence sigma term T)
    (v : Tm n) (vv : v.IsValue) :
    ValueEvidence (Store.val sigma v vv) term.weaken T.weaken := by
  cases evidence with
  | abs closure suffix =>
      exact .abs (closure.weaken v vv) (suffix.weaken v vv)
  | pair suffix =>
      exact .pair (suffix.weaken v vv)
  | @tpair y A W T suffix =>
      have weakened := suffix.weaken v vv
      change Coercion (Store.val sigma v vv)
        (.ty ((Ty.Pair (.Single (.var y)) A
          (Tau.intv W W).weaken).rename FinFun.weaken))
        (.ty (T.rename FinFun.weaken)) at weakened
      rw [tpairType_rename_weaken] at weakened
      exact .tpair weakened

/-- Term evidence for an old term survives allocation. -/
noncomputable def TermEvidence.weaken
    {n : Nat} {sigma : Store n} {term : Tm n} {T : Ty n}
    (evidence : TermEvidence sigma term T)
    (v : Tm n) (vv : v.IsValue) :
    TermEvidence (Store.val sigma v vv) term.weaken T.weaken := by
  cases evidence with
  | path reduction suffix =>
      exact .path (reduction.weaken v vv) (suffix.weaken v vv)
  | value valueEvidence =>
      exact .value (valueEvidence.weaken v vv)
  | app function argument suffix =>
      refine .app (function.weaken v vv) (argument.weaken v vv) ?_
      simpa only [Tau.weaken, Tau.rename, Ty.weaken, Path.weaken,
        Ty.open_rename] using
        suffix.weaken v vv
  | «let» bound closure suffix =>
      refine .let (bound.weaken v vv) ?_ (suffix.weaken v vv)
      simpa only [← Ty.weaken_rename] using
        closure.weaken v vv
  | typed term suffix =>
      exact .typed (term.weaken v vv) (suffix.weaken v vv)

/-! ## Continuations and states -/

/-- Frame evidence survives allocation. -/
noncomputable def Tm.Frame.Evidence.weaken
    {n : Nat} {sigma : Store n} {S T : LambdaPFC.Ty n}
    {frame : Tm.Frame n}
    (evidence : Tm.Frame.Evidence sigma S frame T)
    (v : Tm n) (vv : v.IsValue) :
    Tm.Frame.Evidence (Store.val sigma v vv) S.weaken
      frame.weaken T.weaken := by
  cases evidence with
  | «let» closure suffix =>
      refine .let ?_ (suffix.weaken v vv)
      simpa only [Ty.weaken_rename] using
        closure.weaken v vv

/-- Continuation evidence survives allocation. -/
noncomputable def Tm.Cont.Evidence.weaken
    {n : Nat} {sigma : Store n} {S T : LambdaPFC.Ty n}
    {cont : Tm.Cont n}
    (evidence : Tm.Cont.Evidence sigma S cont T)
    (v : Tm n) (vv : v.IsValue) :
    Tm.Cont.Evidence (Store.val sigma v vv) S.weaken
      cont.weaken T.weaken := by
  induction evidence with
  | hole suffix =>
      exact .hole (suffix.weaken v vv)
  | cons tail frame ih =>
      exact .cons ih (frame.weaken v vv)

/-- Complete state evidence survives the uniform allocation renaming. -/
noncomputable def State.Evidence.weaken
    {n : Nat} {state : State n} {T : LambdaPFC.Ty n}
    (evidence : State.Evidence state T)
    (v : Tm n) (vv : v.IsValue) :
    State.Evidence
      (State.mk (Store.val state.store v vv)
        state.cont.weaken state.term.weaken)
      T.weaken := by
  cases state with
  | mk sigma cont term =>
      cases evidence with
      | ok continuation termEvidence =>
          exact .ok (continuation.weaken v vv)
            (termEvidence.weaken v vv)

end

end LambdaPFC
