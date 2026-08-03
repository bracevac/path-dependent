import LambdaPFC.SemanticTyping
import LambdaPFC.SemanticWeakening

/-!
Allocation weakening for normalized value and continuation evidence.

An allocation shifts every old location by one. Runtime values,
continuations, and their advertised types are renamed by the same weakening,
while closures use the lifted renaming supplied by `SemanticWeakening`.
-/

namespace LambdaPFC

noncomputable section

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
  | cons tail closure suffix ih =>
      refine .cons ih ?_ (suffix.weaken v vv)
      simpa only [Ty.weaken_rename] using closure.weaken v vv

end

end LambdaPFC
