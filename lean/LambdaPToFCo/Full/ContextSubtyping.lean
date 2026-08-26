import LambdaPToFCo.Full.ContextWellFormed
import LambdaPToFCo.Full.IllWfSubtypingRegression
import LambdaPToFCo.Full.PathTypingUniqueness

/-!
# Heterogeneous source-context subtyping

`ContextSubtyping source target` interprets both same-arity context spines at
the source context and records pointwise covariant subtyping.  At a `snoc`,
the target binding type is therefore required to be a well-typed supertype in
the source prefix; this is stronger and more precise than merely pairing two
arbitrary context declarations.

This relation is not a path substitution.  In particular, a covariant
`Bot <: Top` binder change cannot be represented by the identity typed path
substitution in the contravariant direction needed to reuse a target member
model under the source binder.

The relation is necessary but not sufficient for transporting homogeneous
`Tau.Wf` evidence or structural plan models. The final regression theorem
exhibits a target-binder result which is well formed under its `Top`-shaped
package binder and ill formed after narrowing that binder to `Bot`.
-/

namespace LambdaPToFCo.Full

open LambdaPFC

namespace Subtyping

/-- Static weakening of a full source subtyping derivation past one new
source binding. -/
noncomputable def weaken
    {n : Nat} {context : Ctx n}
    {source target : Tau n kind}
    (subtyping : Tau.Sub context source target)
    (newest : Ty n) :
    Tau.Sub (context.snoc newest) source.weaken target.weaken := by
  simpa only [Tau.subst_asSubst, Tau.weaken] using
    Subtyping.subst (TypedPathSubstitution.weaken context newest) subtyping

end Subtyping

/-- Pointwise covariant refinement of two same-arity source contexts.  Every
target declaration is compared in the corresponding source prefix. -/
inductive ContextSubtyping :
    {n : Nat} -> Ctx n -> Ctx n -> Type where
  | identity (context : Ctx n) : ContextSubtyping context context
  | snoc
      (older : ContextSubtyping source target)
      (newest : Tau.Sub source (.ty sourceType) (.ty targetType)) :
      ContextSubtyping (source.snoc sourceType) (target.snoc targetType)

namespace ContextSubtyping

/-- Corresponding lookups are covariantly related in the complete source
context.  Older evidence is statically weakened past every later source
binding. -/
noncomputable def lookup
    {n : Nat} {source target : Ctx n}
    (contexts : ContextSubtyping source target)
    (index : Fin n) :
    Tau.Sub source (.ty (source.lookup index))
      (.ty (target.lookup index)) := by
  induction contexts with
  | identity context => exact .refl
  | @snoc arity source target sourceType targetType older newest ih =>
      refine Fin.cases ?_ (fun olderIndex => ?_) index
      · simpa only [Ctx.lookup, Tau.weaken] using
          Subtyping.weaken newest sourceType
      · simpa only [Ctx.lookup, Tau.weaken] using
          Subtyping.weaken (ih olderIndex) sourceType

/-- The minimal covariant heterogeneous binder refinement. -/
def botTop (context : Ctx n) :
    ContextSubtyping (context.snoc .Bot) (context.snoc .Top) :=
  .snoc (.identity context) .bot

end ContextSubtyping

/-- Despite `Bot <: Top`, an identity path substitution cannot reinterpret a
target member model under `Top` as one under the source `Bot` binder.  The
newest variable would have to synthesize `Top` in a context where it has
precise type `Bot`. -/
theorem noIdentityTypedPathSubstitution_topToBot
    (context : Ctx n) :
    TypedPathSubstitution (context.snoc .Top) (context.snoc .Bot)
      PathSubst.id -> False := by
  intro typed
  have claimed : Path.Ty (context.snoc .Bot) (.var 0) (.ty .Top) := by
    simpa only [PathSubst.id, Ctx.lookup, Ty.subst, Ty.weaken,
      Ty.rename] using typed.lookup 0
  have actual : Path.Ty (context.snoc .Bot) (.var 0) (.ty .Bot) := by
    simpa only [Ctx.lookup, Ty.weaken, Ty.rename] using
      (Path.Ty.var : Path.Ty (context.snoc .Bot) (.var 0)
        (.ty ((context.snoc .Bot).lookup 0)))
  have impossible : (Tau.ty .Top : Tau (n + 1) .star) = .ty .Bot :=
    PathTyping.result_eq claimed actual
  cases impossible

/-! ## The boundary of context subtyping -/

/-- Pointwise binder subtyping does not imply homogeneous well-formedness
narrowing. The target result selects a member from its package-shaped newest
binder; after the covariant binder is narrowed to `Bot`, that same raw result
is not well formed. -/
def contextSubtyping_doesNotNarrowWellFormedness
    (context : Ctx n) :
    ContextSubtyping
        (context.snoc .Bot)
        (context.snoc IllWfSubtypingRegression.sourceDomain) ×
      Tau.Wf
        (context.snoc IllWfSubtypingRegression.sourceDomain)
        (.ty IllWfSubtypingRegression.sourceResult) ×
      (Tau.Wf
        (context.snoc .Bot)
        (.ty IllWfSubtypingRegression.sourceResult) -> Empty) :=
  ⟨ContextSubtyping.snoc (.identity context) .bot,
    IllWfSubtypingRegression.sourceResultWf,
    IllWfSubtypingRegression.sourceResult_not_wf_under_bot⟩

end LambdaPToFCo.Full
