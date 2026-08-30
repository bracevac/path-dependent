import Coercions.ManySortedFC.Evidence

/-!
# A Boolean consistency model for logical evidence

This module interprets every term capability and every static symbol as a
Boolean.  It is intentionally only a separating model: enough structure is
retained to validate the logical evidence rules and refute characteristic bad
closed judgments.  Quantified types receive a constant interpretation because
the evidence language has no congruence rule that crosses a quantifier.
-/

namespace ManySortedFC

/-- A heterogeneous Boolean valuation for the variables that static syntax
can observe.  Evidence variables are deliberately absent. -/
structure BoolValuation (scope : Sig) where
  term : BVar scope .term -> Bool
  typeSymbol : BVar scope (.symbol .type) -> Bool
  captureSymbol : BVar scope (.symbol .capture) -> Bool

namespace BoolSemantics

/-- The two-point preorder, written as preservation of truth. -/
def LE (left right : Bool) : Prop := left = true -> right = true

theorem refl (value : Bool) : LE value value := fun truth => truth

theorem trans {first middle last : Bool} (firstMiddle : LE first middle)
    (middleLast : LE middle last) : LE first last :=
  fun truth => middleLast (firstMiddle truth)

theorem equality_le {left right : Bool} (equality : left = right) :
    LE left right := by
  subst right
  exact refl left

theorem top (source : Bool) : LE source true := by
  intro _
  rfl

theorem bottom (target : Bool) : LE false target := by
  intro impossible
  cases impossible

/-- Boolean implication is contravariant in its premise and covariant in its
conclusion. -/
theorem implication_mono {sourceDomain targetDomain sourceCodomain
    targetCodomain : Bool}
    (domain : LE targetDomain sourceDomain)
    (codomain : LE sourceCodomain targetCodomain) :
    LE ((!sourceDomain) || sourceCodomain)
      ((!targetDomain) || targetCodomain) := by
  cases sourceDomain <;> cases targetDomain <;>
    cases sourceCodomain <;> cases targetCodomain <;>
    simp_all [LE]

/-- Conjunction is monotone in both components. -/
theorem and_mono {sourceLeft targetLeft sourceRight targetRight : Bool}
    (left : LE sourceLeft targetLeft)
    (right : LE sourceRight targetRight) :
    LE (sourceLeft && sourceRight) (targetLeft && targetRight) := by
  cases sourceLeft <;> cases targetLeft <;>
    cases sourceRight <;> cases targetRight <;>
    simp_all [LE]

theorem or_left (left right : Bool) : LE left (left || right) := by
  cases left <;> cases right <;> simp [LE]

theorem or_right (left right : Bool) : LE right (left || right) := by
  cases left <;> cases right <;> simp [LE]

theorem or_elim {left right target : Bool} (leftTarget : LE left target)
    (rightTarget : LE right target) : LE (left || right) target := by
  cases left <;> cases right <;> cases target <;> simp_all [LE]

end BoolSemantics

namespace Capture

/-- Captures denote whether at least one selected capability is present. -/
def eval {scope : Sig} (valuation : BoolValuation scope) :
    Capture scope -> Bool
  | .empty => false
  | .union left right => left.eval valuation || right.eval valuation
  | .singleton capability => valuation.term capability
  | .cvar name => valuation.captureSymbol name

end Capture

namespace Ty

/-- A small Boolean interpretation of types.

Arrows are implication.  Capturing types use conjunction, a monotone
combination of their capture and shape interpretations. -/
def eval {scope : Sig} (valuation : BoolValuation scope) : Ty scope -> Bool
  | .top => true
  | .bot => false
  | .one => true
  | .tvar name => valuation.typeSymbol name
  | .capturing captures shape =>
      captures.eval valuation && shape.eval valuation
  | .arr domain codomain => (!domain.eval valuation) || codomain.eval valuation
  | .forallT _ _ => true
  | .existsT _ _ => true

end Ty

namespace StaticExpr

/-- Interpret an expression without forgetting its intrinsic static sort. -/
def eval {scope : Sig} {sort : StaticSort}
    (valuation : BoolValuation scope) : StaticExpr sort scope -> Bool
  | StaticExpr.type expression => expression.eval valuation
  | StaticExpr.capture expression => expression.eval valuation

end StaticExpr

namespace Proposition

/-- Satisfaction by one Boolean valuation.  Equality is Boolean equality;
directed inclusion is the two-point preorder. -/
def Holds {scope : Sig} {relation : Relation}
    (valuation : BoolValuation scope) : Proposition relation scope -> Prop
  | .equality left right => left.eval valuation = right.eval valuation
  | .inclusion lower upper => BoolSemantics.LE
      (lower.eval valuation) (upper.eval valuation)

/-- Semantic validity means satisfaction by every heterogeneous valuation. -/
def Valid {scope : Sig} {relation : Relation}
    (proposition : Proposition relation scope) : Prop :=
  forall valuation : BoolValuation scope, proposition.Holds valuation

end Proposition

/-- A scope has no logical assumptions exactly when it has no evidence
variable of any relation. -/
def HasNoEvidenceBinders (scope : Sig) : Prop :=
  forall (relation : Relation), BVar scope (.evidence relation) -> False

namespace BoolValuation

/-- A valuation respects the capture summaries stored in term bindings.
Whenever a variable has capturing type `C ▷ S`, selecting that variable in
the Boolean model implies the interpretation of `C`. -/
def Respects {scope : Sig} (valuation : BoolValuation scope)
    (context : Ctx scope) : Prop :=
  ∀ (index : BVar scope .term) (captures : Capture scope) (shape : Ty scope),
    context.lookup index = Binding.term (.capturing captures shape) →
      BoolSemantics.LE (valuation.term index) (captures.eval valuation)

end BoolValuation

namespace Evidence.Proves

/-- Every declarative evidence derivation in an assumption-free scope is
valid in the Boolean model. -/
theorem sound_of_no_evidence {scope : Sig} {context : Ctx scope}
    {relation : Relation} {evidence : Evidence relation scope}
    {proposition : Proposition relation scope}
    (noEvidence : HasNoEvidenceBinders scope)
    (typing : Evidence.Proves context evidence proposition) :
    ∀ valuation : BoolValuation scope,
      valuation.Respects context → proposition.Holds valuation := by
  intro valuation
  intro respects
  induction typing with
  | @var relation index proposition binding =>
      exact (noEvidence relation index).elim
  | equalityRefl expression =>
      rfl
  | equalitySymm typing induction =>
      exact induction.symm
  | equalityTrans firstTyping secondTyping firstInduction secondInduction =>
      exact firstInduction.trans secondInduction
  | equalityArrow domainTyping codomainTyping domainInduction
      codomainInduction =>
      simp only [Proposition.Holds, StaticExpr.eval, Ty.eval] at domainInduction codomainInduction ⊢
      rw [domainInduction, codomainInduction]
  | equalityCapturing captureTyping shapeTyping captureInduction
      shapeInduction =>
      simp only [Proposition.Holds, StaticExpr.eval, Ty.eval] at captureInduction shapeInduction ⊢
      rw [captureInduction, shapeInduction]
  | equalityCaptureUnion leftTyping rightTyping leftInduction
      rightInduction =>
      simp only [Proposition.Holds, StaticExpr.eval, Capture.eval] at leftInduction rightInduction ⊢
      rw [leftInduction, rightInduction]
  | inclusionRefl expression =>
      exact BoolSemantics.refl _
  | inclusionTrans firstTyping secondTyping firstInduction secondInduction =>
      exact BoolSemantics.trans firstInduction secondInduction
  | equalityToInclusion typing induction =>
      exact BoolSemantics.equality_le induction
  | typeTop source =>
      exact BoolSemantics.top _
  | typeBottom target =>
      exact BoolSemantics.bottom _
  | typeArrow domainTyping codomainTyping domainInduction
      codomainInduction =>
      exact BoolSemantics.implication_mono domainInduction codomainInduction
  | typeCapturing captureTyping shapeTyping captureInduction
      shapeInduction =>
      exact BoolSemantics.and_mono captureInduction shapeInduction
  | captureEmpty target =>
      exact BoolSemantics.bottom _
  | captureUnionLeft left right =>
      exact BoolSemantics.or_left _ _
  | captureUnionRight left right =>
      exact BoolSemantics.or_right _ _
  | captureUnionElim leftTyping rightTyping leftInduction rightInduction =>
      exact BoolSemantics.or_elim leftInduction rightInduction
  | captureVariable binding =>
      exact respects _ _ _ binding

end Evidence.Proves

namespace BoolValuation

/-- The unique valuation of the empty scope. -/
def empty : BoolValuation [] where
  term := fun index => nomatch index
  typeSymbol := fun index => nomatch index
  captureSymbol := fun index => nomatch index

/-- A valuation distinguishing the sole term capability in a one-term scope. -/
def oneTermTrue : BoolValuation ([] ▹ .term) where
  term := fun
    | .here => true
    | .there index => nomatch index
  typeSymbol := fun
    | .there index => nomatch index
  captureSymbol := fun
    | .there index => nomatch index

end BoolValuation

theorem noEvidenceBinders_empty : HasNoEvidenceBinders [] := by
  intro relation index
  nomatch index

theorem noEvidenceBinders_oneTerm : HasNoEvidenceBinders ([] ▹ .term) := by
  intro relation index
  cases index with
  | there older => nomatch older

/-- There is no closed certificate for the inconsistent type inclusion
`Top <= Bottom`. -/
theorem no_closed_top_included_in_bottom
    {evidence : Evidence (.inclusion .type) []}
    (typing : Evidence.Proves .nil evidence
      (.inclusion (.type (.top : Ty [])) (.type (.bot : Ty [])))) :
    False := by
  have validity := Evidence.Proves.sound_of_no_evidence
    noEvidenceBinders_empty typing
  have holds := validity BoolValuation.empty (by
    intro index
    nomatch index)
  have impossible : false = true := holds rfl
  cases impossible

/-- With one available term capability and no evidence assumptions, its
singleton capture cannot be included in the empty capture. -/
theorem no_singleton_included_in_empty
    {evidence : Evidence (.inclusion .capture) ([] ▹ .term)}
    (typing : Evidence.Proves (Ctx.nil.extendTerm .one) evidence
      (.inclusion
        (.capture (.singleton
          (.here : BVar ([] ▹ .term) .term)))
        (.capture (.empty : Capture ([] ▹ .term))))) :
    False := by
  have validity := Evidence.Proves.sound_of_no_evidence
    noEvidenceBinders_oneTerm typing
  have holds := validity BoolValuation.oneTermTrue (by
    intro index captures shape binding
    cases index with
    | here => cases binding
    | there older => nomatch older)
  have impossible : false = true := holds rfl
  cases impossible

end ManySortedFC
