import LambdaPFCI.SemanticAction
import LambdaPFCI.SemanticTyping

/-!
The fundamental interpretation of source typing derivations.

Every free source variable is mapped to a concrete store location by an
`Environment`.  Interpreting a proof-relevant typing derivation then produces
normalized, store-local evidence for the renamed runtime term.  Function and
let bodies are retained as closures and interpreted only when execution
supplies their bound location.
-/

namespace LambdaPFCI

noncomputable section

/-- Interpret a source typing derivation in a semantic environment. -/
noncomputable def Tm.Ty.interpret
    {n m : Nat} {Gamma : Ctx n} {term : Tm n}
    {T : LambdaPFCI.Ty n}
    {rho : Valuation n m} {sigma : Store m}
    (code : Tm.Ty Gamma term T)
    (environment : Environment Gamma rho sigma) :
    TermEvidence sigma (term.rename rho) (T.rename rho) := by
  induction code with
  | path pathCode =>
      obtain ⟨referent, resolution, realizes⟩ :=
        pathCode.resolve environment
      cases realizes with
      | loc possible =>
          exact .path resolution .refl
  | abs body domain =>
      exact .value (.abs (.source environment body) .refl)
  | app function argument ihFunction ihArgument =>
      simpa only [Tm.rename, Ty.rename, Ty.open_rename] using
        TermEvidence.app (ihFunction environment)
          (ihArgument environment) .refl
  | pair =>
      exact .value (.pair .refl)
  | tpair member =>
      simpa only [Tm.rename, Def.rename, LambdaPFCI.Ty.rename,
        Tau.rename, Path.rename, ← Tau.weaken_rename] using
        TermEvidence.value (ValueEvidence.tpair
          (Coercion.refl (sigma := sigma)))
  | «let» bound result body ihBound =>
      refine .let (ihBound environment) ?_ .refl
      simpa only [← Ty.weaken_rename] using
        BodyClosure.source environment body
  | sub term subtype wf ihTerm =>
      exact (ihTerm environment).cast (subtype.compile environment)

/-- Interpret a closed source body after mapping its formal parameter to a
concrete argument location. -/
noncomputable def BodyClosure.apply
    {m : Nat} {sigma : Store m} {S : Ty m}
    {body : Tm (m + 1)} {T : Ty (m + 1)}
    (closure : BodyClosure sigma S body T)
    {x : Fin m} (argument : Store.Possible sigma x S) :
    TermEvidence sigma (body.open x) (T.open (.var x)) := by
  cases closure with
  | @source n m Gamma rho sigma A sourceBody sourceType
      environment code =>
      have interpreted := code.interpret (environment.snoc argument)
      simpa only [Tm.open, Tm.rename_ext_openAt,
        ← Ty.rename_openAt_eq_open_var, Ty.rename_ext_openAt] using
        interpreted

end

end LambdaPFCI
