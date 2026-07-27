import LambdaP.Soundness.DenLemmas

/-!
Closing substitutions for the closure lemma: syntactically conforming,
with every image evaluating into the limit denotation of its substituted
declared type (the analog of ECOOP'17's `R_env` towers at all levels).
-/

namespace LambdaP

/-- A closing substitution that is syntactically conforming and whose
images evaluate into the limit denotations of their declared types. -/
structure SemSubst (Θ : Sto) (Ξ : SemSto) (h : Heap) (σ : Subst s 0)
    (Γ : Ctx s) : Prop where
  conforms : SubstTyping Θ σ Γ .empty
  realized : ∀ {x : BVar s} {T : Ty s}, Ctx.LookupVar Γ x T ->
    ∃ m, PathEval h (σ.var x) m ∧ DenAll Θ Ξ h (T.subst σ) m

end LambdaP
