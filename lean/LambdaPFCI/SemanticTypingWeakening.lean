import LambdaPFCI.SemanticTyping
import LambdaPFCI.SemanticWeakening

/-!
Allocation weakening for normalized value and continuation evidence.

An allocation shifts every old location by one. Runtime values,
continuations, and their advertised types are renamed by the same weakening,
while closures use the lifted renaming supplied by `SemanticWeakening`.
-/

namespace LambdaPFCI

noncomputable section

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
  | tpair suffix =>
      refine .tpair ?_
      simpa only [Ty.weaken, Tau.weaken, Ty.rename, Path.rename,
        Tau.rename, Ty.rename_rename, FinFun.comp_weaken] using
        suffix.weaken v vv

/-- Continuation evidence survives allocation. -/
noncomputable def Tm.Cont.Evidence.weaken
    {n : Nat} {sigma : Store n} {S T : LambdaPFCI.Ty n}
    {cont : Tm.Cont n}
    (evidence : Tm.Cont.Evidence sigma S cont T)
    (v : Tm n) (vv : v.IsValue) :
    Tm.Cont.Evidence (Store.val sigma v vv) S.weaken
      cont.weaken T.weaken := by
  induction evidence with
  | hole =>
      exact .hole
  | cons tail closure suffix ih =>
      refine .cons ih ?_ (suffix.weaken v vv)
      simpa only [Ty.weaken_rename] using closure.weaken v vv

end

end LambdaPFCI
