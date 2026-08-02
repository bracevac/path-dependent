import LambdaPFC.SemanticFundamental
import LambdaPFC.SemanticAction

/-!
Application of source body closures to existing store locations.

Supplying an argument extends the saved semantic environment and exposes the
stored source typing derivation to the fundamental interpretation.  This
operation does not allocate a value or extend the store.
-/

namespace LambdaPFC

noncomputable section

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

end LambdaPFC
