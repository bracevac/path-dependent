import Coercions.DOT.Acyclic.Explicit.Erasure

/-!
# Erased explicit-coercion simulation

Explicit casts and member handles take no runtime steps.  Exact-object
binding retains precisely the source-level runtime let and therefore performs
the ordinary zeta step.
-/

namespace DotFC.Explicit

open DotFC

/-- The private equality introduced by `letExact` is absent from the runtime
reduct; only substitution of the unit-like object remains. -/
theorem erase_letExact_zeta {s : Sig} (label : Name) (witness : Source.Ty s)
    (body : Tm ((s ▹ .term) ▹ .evidence .equality)) :
    Source.Runtime.Step (Tm.letExact label witness body).erase
      ((Runtime.renameTerms body.erase
        ScopedTy.TermRename.dropEvidence).open .obj) := by
  exact Source.Runtime.Step.zeta Source.Runtime.IsValue.obj

/-- An explicit cast has exactly the erased behavior of its operand. -/
theorem cast_erasure_coherent {s : Sig} (term : Tm s) (evidence : LeCo s) :
    (.cast term evidence : Tm s).erase = term.erase := rfl

end DotFC.Explicit
