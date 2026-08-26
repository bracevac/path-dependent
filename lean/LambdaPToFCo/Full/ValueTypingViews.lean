import LambdaPToFCo.Full.TypingViews

/-!
# Total typing views of full LambdaPFC values

Allocation needs the introduction typing hidden below any number of source
subsumption rules.  `ValueTypingView` is the value-only refinement of
`TypingView`: it retains exactly the abstraction, term-member pair, and
type-member pair introductions admitted by `LambdaPFC.Tm.IsValue`, together
with one composed subtyping suffix to the advertised type.

This module is source-only.  It does not depend on the restricted fragment,
operational admissibility, a target language, or semantic realization.
-/

namespace LambdaPToFCo.Full

/-- Introduction data for a source value, normalized below arbitrary outer
applications of `Tm.Ty.sub`. -/
inductive ValueTypingView {n : Nat} (context : LambdaPFC.Ctx n) :
    (value : LambdaPFC.Tm n) ->
    (advertised : LambdaPFC.Ty n) -> Type where
  | abs
      (bodyTyping : LambdaPFC.Tm.Ty (context.snoc domain) body codomain)
      (domainWf : LambdaPFC.Tau.Wf context (.ty domain))
      (suffix : LambdaPFC.Tau.Sub context
        (.ty (.Fun domain codomain)) (.ty advertised)) :
      ValueTypingView context (.abs domain body) advertised
  | valuePair
      (suffix : LambdaPFC.Tau.Sub context
        (.ty (.Pair (.Single (LambdaPFC.Path.var first)) label
          (.ty (.Single (LambdaPFC.Path.var member).weaken))))
        (.ty advertised)) :
      ValueTypingView context
        (.pair first label (LambdaPFC.Def.val member)) advertised
  | typePair
      (witnessWf : LambdaPFC.Tau.Wf context (.ty witness))
      (suffix : LambdaPFC.Tau.Sub context
        (.ty (.Pair (.Single (LambdaPFC.Path.var first)) label
          (LambdaPFC.Tau.intv witness witness).weaken))
        (.ty advertised)) :
      ValueTypingView context
        (.pair first label (LambdaPFC.Def.type witness)) advertised

namespace ValueTypingView

/-- Append one further source subsumption to a normalized value view. -/
def cast
    (view : ValueTypingView context value source)
    (suffix : LambdaPFC.Tau.Sub context (.ty source) (.ty target)) :
    ValueTypingView context value target := by
  cases view with
  | abs bodyTyping domainWf previous =>
      exact .abs bodyTyping domainWf (.trans previous suffix)
  | valuePair previous =>
      exact .valuePair (.trans previous suffix)
  | typePair witnessWf previous =>
      exact .typePair witnessWf (.trans previous suffix)

/-- Refine a syntax-directed typing view using the source value proof.  The
three non-value term forms are discharged solely by dependent elimination of
`Tm.IsValue`. -/
def ofTypingView
    (view : TypingView context value advertised)
    (ready : value.IsValue) :
    ValueTypingView context value advertised := by
  cases view with
  | path _ _ =>
      exact False.elim (by cases ready)
  | abs bodyTyping domainWf suffix =>
      exact .abs bodyTyping domainWf suffix
  | pair suffix => exact .valuePair suffix
  | typePair witnessWf suffix => exact .typePair witnessWf suffix
  | app _ _ _ =>
      exact False.elim (by cases ready)
  | «let» _ _ _ _ =>
      exact False.elim (by cases ready)

/-- Total value inversion for the complete source typing judgment. -/
def ofTyping
    (typing : LambdaPFC.Tm.Ty context value advertised)
    (ready : value.IsValue) :
    ValueTypingView context value advertised :=
  ofTypingView (TypingView.ofTyping typing) ready

/-- Refinement commutes with appending a subtyping suffix. -/
theorem ofTypingView_cast
    (view : TypingView context value source)
    (ready : value.IsValue)
    (suffix : LambdaPFC.Tau.Sub context (.ty source) (.ty target)) :
    ofTypingView (view.cast suffix) ready =
      (ofTypingView view ready).cast suffix := by
  cases view <;> cases ready <;> rfl

/-- Peeling an outer `Tm.Ty.sub` composes it onto the retained suffix. -/
@[simp] theorem ofTyping_sub
    (typing : LambdaPFC.Tm.Ty context value source)
    (suffix : LambdaPFC.Tau.Sub context (.ty source) (.ty target))
    (targetWf : LambdaPFC.Tau.Wf context (.ty target))
    (ready : value.IsValue) :
    ofTyping (.sub typing suffix targetWf) ready =
      (ofTyping typing ready).cast suffix := by
  exact ofTypingView_cast (TypingView.ofTyping typing) ready suffix

/-! ## Constructor and inversion regressions -/

example
    (bodyTyping : LambdaPFC.Tm.Ty (context.snoc domain) body codomain)
    (domainWf : LambdaPFC.Tau.Wf context (.ty domain)) :
    ofTyping (LambdaPFC.Tm.Ty.abs bodyTyping domainWf)
        LambdaPFC.Tm.IsValue.abs =
      ValueTypingView.abs bodyTyping domainWf .refl :=
  rfl

example {context : LambdaPFC.Ctx n} {first member : Fin n}
    {label : LambdaPFC.Name} :
    ofTyping
        (LambdaPFC.Tm.Ty.pair (Γ := context) (y := first)
          (a := label) (z := member))
        LambdaPFC.Tm.IsValue.pair =
      ValueTypingView.valuePair .refl :=
  rfl

example {context : LambdaPFC.Ctx n} {first : Fin n}
    {label : LambdaPFC.Name} {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf context (.ty witness)) :
    ofTyping
        (LambdaPFC.Tm.Ty.tpair (y := first) (A := label) witnessWf)
        LambdaPFC.Tm.IsValue.pair =
      ValueTypingView.typePair witnessWf .refl :=
  rfl

example
    (bodyTyping : LambdaPFC.Tm.Ty (context.snoc domain) body codomain)
    (domainWf : LambdaPFC.Tau.Wf context (.ty domain))
    (suffix : LambdaPFC.Tau.Sub context
      (.ty (.Fun domain codomain)) (.ty advertised))
    (advertisedWf : LambdaPFC.Tau.Wf context (.ty advertised)) :
    ofTyping
        (LambdaPFC.Tm.Ty.sub
          (LambdaPFC.Tm.Ty.abs bodyTyping domainWf)
          suffix advertisedWf)
        LambdaPFC.Tm.IsValue.abs =
      ValueTypingView.abs bodyTyping domainWf (.trans .refl suffix) :=
  rfl

/-- An abstraction-indexed value view can only expose abstraction
introduction data. -/
example
    (view : ValueTypingView context (.abs domain body) advertised) :
    Nonempty (Sigma fun codomain =>
      (LambdaPFC.Tm.Ty (context.snoc domain) body codomain) ×
      (LambdaPFC.Tau.Wf context (.ty domain)) ×
      (LambdaPFC.Tau.Sub context
        (.ty (.Fun domain codomain)) (.ty advertised))) := by
  cases view with
  | abs bodyTyping domainWf suffix =>
      exact ⟨_, bodyTyping, domainWf, suffix⟩

/-- A type-pair-indexed value view retains both the witness well-formedness
and its accumulated administration. -/
example
    (view : ValueTypingView context
      (.pair first label (LambdaPFC.Def.type witness)) advertised) :
    Nonempty
      ((LambdaPFC.Tau.Wf context (.ty witness)) ×
        LambdaPFC.Tau.Sub context
          (.ty (.Pair (.Single (LambdaPFC.Path.var first)) label
            (LambdaPFC.Tau.intv witness witness).weaken))
          (.ty advertised)) := by
  cases view with
  | typePair witnessWf suffix => exact ⟨witnessWf, suffix⟩

end ValueTypingView

end LambdaPToFCo.Full
