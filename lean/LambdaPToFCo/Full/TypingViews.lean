import LambdaPFC.Typing

/-!
# Total syntax-directed views of full LambdaPFC typing

The operational compiler must invert the constructor of the current source
term even when its typing derivation ends in arbitrarily many applications of
`Tm.Ty.sub`.  `TypingView` performs that normalization for the complete
existing `LambdaPFC` language.  It retains the direct introduction data and
composes every peeled subsumption derivation into one suffix.

This module is source-only.  In particular, it has no dependency on the
restricted `Fragment`, `OperationallyAdmissible`, a target representation, or
the semantic realization/runtime-subtyping development.
-/

namespace LambdaPToFCo.Full

/-- The direct typing constructor selected by a term's syntax, together with
one accumulated subtyping suffix from its introduction type to its advertised
type.  Both pair-definition kinds and all six term forms are represented.
-/
inductive TypingView {n : Nat} (context : LambdaPFC.Ctx n) :
    (term : LambdaPFC.Tm n) ->
    (advertised : LambdaPFC.Ty n) -> Type where
  | path
      (precise : LambdaPFC.Path.Ty context path (.ty preciseType))
      (suffix : LambdaPFC.Tau.Sub context
        (.ty (.Single path)) (.ty advertised)) :
      TypingView context (.path path) advertised
  | abs
      (bodyTyping : LambdaPFC.Tm.Ty (context.snoc domain) body codomain)
      (domainWf : LambdaPFC.Tau.Wf context (.ty domain))
      (suffix : LambdaPFC.Tau.Sub context
        (.ty (.Fun domain codomain)) (.ty advertised)) :
      TypingView context (.abs domain body) advertised
  | pair
      (suffix : LambdaPFC.Tau.Sub context
        (.ty (.Pair (.Single (LambdaPFC.Path.var first)) label
          (.ty (.Single (LambdaPFC.Path.var member).weaken))))
        (.ty advertised)) :
      TypingView context
        (.pair first label (LambdaPFC.Def.val member)) advertised
  | typePair
      (witnessWf : LambdaPFC.Tau.Wf context (.ty witness))
      (suffix : LambdaPFC.Tau.Sub context
        (.ty (.Pair (.Single (LambdaPFC.Path.var first)) label
          (LambdaPFC.Tau.intv witness witness).weaken))
        (.ty advertised)) :
      TypingView context
        (.pair first label (LambdaPFC.Def.type witness)) advertised
  | app
      (functionTyping : LambdaPFC.Tm.Ty context (.path function)
        (.Fun domain codomain))
      (argumentTyping : LambdaPFC.Tm.Ty context (.path argument) domain)
      (suffix : LambdaPFC.Tau.Sub context
        (.ty (codomain.open argument)) (.ty advertised)) :
      TypingView context (.app function argument) advertised
  | «let»
      (boundTyping : LambdaPFC.Tm.Ty context bound boundType)
      (resultWf : LambdaPFC.Tau.Wf context (.ty resultType))
      (bodyTyping : LambdaPFC.Tm.Ty (context.snoc boundType) body
        resultType.weaken)
      (suffix : LambdaPFC.Tau.Sub context
        (.ty resultType) (.ty advertised)) :
      TypingView context (.let bound body) advertised

namespace TypingView

/-- Append one further source subsumption to a normalized typing view. -/
def cast
    (view : TypingView context term source)
    (suffix : LambdaPFC.Tau.Sub context (.ty source) (.ty target)) :
    TypingView context term target := by
  cases view with
  | path precise previous =>
      exact .path precise (.trans previous suffix)
  | abs bodyTyping domainWf previous =>
      exact .abs bodyTyping domainWf (.trans previous suffix)
  | pair previous =>
      exact .pair (.trans previous suffix)
  | typePair witnessWf previous =>
      exact .typePair witnessWf (.trans previous suffix)
  | app functionTyping argumentTyping previous =>
      exact .app functionTyping argumentTyping (.trans previous suffix)
  | «let» boundTyping resultWf bodyTyping previous =>
      exact .let boundTyping resultWf bodyTyping (.trans previous suffix)

/-- Total inversion of a full source typing derivation by its runtime term
constructor.  The recursive `sub` case is the only normalization step. -/
def ofTyping :
    (typing : LambdaPFC.Tm.Ty context term advertised) ->
    TypingView context term advertised
  | .path precise => .path precise .refl
  | .abs bodyTyping domainWf => .abs bodyTyping domainWf .refl
  | .pair => .pair .refl
  | .tpair witnessWf => .typePair witnessWf .refl
  | .app functionTyping argumentTyping =>
      .app functionTyping argumentTyping .refl
  | .let boundTyping resultWf bodyTyping =>
      .let boundTyping resultWf bodyTyping .refl
  | .sub inner suffix _ => (ofTyping inner).cast suffix

/-! Definitional regression checks for every source typing constructor and
for the subsumption-peeling branch. -/

example {context : LambdaPFC.Ctx n} {path : LambdaPFC.Path n}
    {preciseType : LambdaPFC.Ty n}
    (precise : LambdaPFC.Path.Ty context path (.ty preciseType)) :
    ofTyping (LambdaPFC.Tm.Ty.path precise) =
      TypingView.path precise .refl :=
  rfl

example
    (bodyTyping : LambdaPFC.Tm.Ty (context.snoc domain) body codomain)
    (domainWf : LambdaPFC.Tau.Wf context (.ty domain)) :
    ofTyping (LambdaPFC.Tm.Ty.abs bodyTyping domainWf) =
      TypingView.abs bodyTyping domainWf .refl :=
  rfl

example {context : LambdaPFC.Ctx n} {first member : Fin n}
    {label : LambdaPFC.Name} :
    ofTyping (LambdaPFC.Tm.Ty.pair (Γ := context) (y := first)
      (a := label) (z := member)) = TypingView.pair .refl :=
  rfl

example {context : LambdaPFC.Ctx n} {first : Fin n}
    {label : LambdaPFC.Name} {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf context (.ty witness)) :
    ofTyping (LambdaPFC.Tm.Ty.tpair (y := first) (A := label) witnessWf) =
      TypingView.typePair witnessWf .refl :=
  rfl

example
    (functionTyping : LambdaPFC.Tm.Ty context (.path function)
      (.Fun domain codomain))
    (argumentTyping : LambdaPFC.Tm.Ty context (.path argument) domain) :
    ofTyping (LambdaPFC.Tm.Ty.app functionTyping argumentTyping) =
      TypingView.app functionTyping argumentTyping .refl :=
  rfl

example
    (boundTyping : LambdaPFC.Tm.Ty context bound boundType)
    (resultWf : LambdaPFC.Tau.Wf context (.ty resultType))
    (bodyTyping : LambdaPFC.Tm.Ty (context.snoc boundType) body
      resultType.weaken) :
    ofTyping (LambdaPFC.Tm.Ty.let boundTyping resultWf bodyTyping) =
      TypingView.let boundTyping resultWf bodyTyping .refl :=
  rfl

example
    (typing : LambdaPFC.Tm.Ty context term source)
    (suffix : LambdaPFC.Tau.Sub context (.ty source) (.ty target))
    (targetWf : LambdaPFC.Tau.Wf context (.ty target)) :
    ofTyping (LambdaPFC.Tm.Ty.sub typing suffix targetWf) =
      (ofTyping typing).cast suffix :=
  rfl

end TypingView

end LambdaPToFCo.Full
