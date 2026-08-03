import LambdaPFC.SemanticClosure
import LambdaPFC.SemanticTypingWeakening
import LambdaPFC.SemanticAction

/-!
Semantic evidence for store allocation.  A value stored at a location realizes
its advertised type; the fresh-location instance supplies the argument needed
to interpret a suspended function or let body after allocation.
-/

namespace LambdaPFC

noncomputable section

/-! ## Realization of stored values -/

/-- A stored value realizes its advertised type at the location where it is
bound. -/
noncomputable def ValueEvidence.possibleOfBinding
    {n : Nat} {sigma : Store n} {v : Tm n} {T : Ty n}
    (evidence : ValueEvidence sigma v T) {x : Fin n}
    (binding : Store.Binds sigma x v) :
    Store.Possible sigma x T := by
  cases evidence with
  | abs closure suffix =>
      apply suffix.actionPossible
      exact .fun binding closure .refl .refl
  | @pair y z a _ suffix =>
      apply suffix.actionPossible
      refine .pair binding (.single .var) ?_
      simpa only [Tau.open, Tau.subst, Ty.weaken_open] using
        Path.Referent.Realizes.loc
          (Store.Possible.single (Path.Resolve.var (x := z)))
  | @tpair y A W _ suffix =>
      apply suffix.actionPossible
      refine .pair binding (.single .var) ?_
      simpa only [Tau.weaken_open] using
        Path.Referent.Realizes.type
          (Coercion.refl (d := .ty W)) (Coercion.refl (d := .ty W))

/-- The newly allocated location realizes the weakened advertised type. -/
noncomputable def ValueEvidence.freshPossible
    {n : Nat} {sigma : Store n} {v : Tm n} {T : Ty n}
    (evidence : ValueEvidence sigma v T) (vv : v.IsValue) :
    Store.Possible (Store.val sigma v vv) 0 T.weaken :=
  (evidence.weaken v vv).possibleOfBinding .here

/-! ## Applying a closure at the fresh location -/

private theorem FinFun.weaken_ext_comp_openAt_zero {n : Nat} :
    (FinFun.weaken (n := n)).ext.comp
      (FinFun.openAt (0 : Fin (n + 1))) = FinFun.id := by
  apply FinFun.funext
  intro x
  refine Fin.cases ?_ (fun _ => ?_) x <;> rfl

/-- Allocate an argument value and interpret a body closure with its formal
parameter mapped to the fresh location. -/
noncomputable def BodyClosure.allocate
    {n : Nat} {sigma : Store n} {S : Ty n}
    {body : Tm (n + 1)} {T : Ty (n + 1)}
    (closure : BodyClosure sigma S body T)
    {v : Tm n} (argument : ValueEvidence sigma v S)
    (vv : v.IsValue) :
    TermEvidence (Store.val sigma v vv) body T := by
  have applied :=
    (closure.weaken v vv).apply (argument.freshPossible vv)
  simpa only [Tm.open, Tm.rename_rename,
    FinFun.weaken_ext_comp_openAt_zero, Tm.rename_id,
    ← Ty.rename_openAt_eq_open_var, Ty.rename_rename,
    Ty.rename_id] using applied

end

end LambdaPFC
