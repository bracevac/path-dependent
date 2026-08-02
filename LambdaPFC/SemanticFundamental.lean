import LambdaPFC.SemanticAction
import LambdaPFC.SemanticTyping

/-!
The fundamental interpretation of source typing derivations.

Every free source variable is mapped to a concrete store location by an
`Environment`.  Interpreting a proof-relevant typing derivation then produces
normalized, store-local evidence for the renamed runtime term.  Function and
let bodies are retained as closures and interpreted only when execution
supplies their bound location.
-/

namespace LambdaPFC

noncomputable section

/-- Interpret a source typing derivation in a semantic environment. -/
noncomputable def TermCode.interpret
    {n m : Nat} {Gamma : Ctx n} {term : Tm n} {T : Ty n}
    {rho : Valuation n m} {sigma : Store m}
    (code : TermCode Gamma term T)
    (environment : Environment Gamma rho sigma) :
    TermEvidence sigma (term.rename rho) (T.rename rho) := by
  induction code with
  | path pathCode =>
      obtain ⟨endpoint, resolution, realizes⟩ :=
        pathCode.resolve environment
      cases realizes with
      | val possible =>
          exact .path resolution.toReduce .refl
  | abs body domain =>
      exact .value (.abs (.source environment body) .refl)
  | app function argument ihFunction ihArgument =>
      simpa only [Tm.rename, Ty.rename, Ty.open_rename] using
        TermEvidence.app (ihFunction environment)
          (ihArgument environment) .refl
  | pair first member =>
      exact .value (.pair .refl)
  | tpair first member =>
      simpa only [Tm.rename, Def.rename, LambdaPFC.Ty.rename,
        Tau.rename, Path.rename, ← Tau.weaken_rename] using
        TermEvidence.value (ValueEvidence.tpair
          (Coercion.refl (sigma := sigma)))
  | «let» bound result body ihBound =>
      refine .let (ihBound environment) ?_ .refl
      simpa only [← Ty.weaken_rename] using
        BodyClosure.source environment body
  | typed term wf ihTerm =>
      exact .typed (ihTerm environment) .refl
  | sub term subtype wf ihTerm =>
      exact (ihTerm environment).cast (subtype.compile environment)

/-- Declarative typing has a semantic interpretation after proof-relevant
elaboration. -/
theorem Tm.Ty.nonempty_interpret
    {n m : Nat} {Gamma : Ctx n} {term : Tm n}
    {T : LambdaPFC.Ty n}
    {rho : Valuation n m} {sigma : Store m}
    (typing : Tm.Ty Gamma term T)
    (environment : Environment Gamma rho sigma) :
    Nonempty (TermEvidence sigma (term.rename rho) (T.rename rho)) := by
  obtain ⟨code⟩ := TermCode.nonempty_of_ty typing
  exact ⟨code.interpret environment⟩

end

end LambdaPFC
