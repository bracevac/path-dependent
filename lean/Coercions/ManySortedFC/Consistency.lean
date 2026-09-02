import Coercions.ManySortedFC.Evidence
import Coercions.ManySortedFC.Classifier.Semantics

/-!
# A Boolean consistency model for logical evidence

This module interprets every term capability and every static symbol as a
Boolean.  It is intentionally only a small model for equality and inclusion:
mode, separation, and disjointness propositions are interpreted trivially
here and receive a dedicated access-view model in `SeparationConsistency`.
Modal and quantified types receive a constant interpretation because the
evidence language has no congruence rule that crosses either boundary.
-/

namespace ManySortedFC

/-- A heterogeneous Boolean valuation for the variables that static syntax
can observe.  Evidence variables are deliberately absent. -/
structure BoolValuation (scope : Sig) where
  term : BVar scope .term -> Bool
  typeSymbol : BVar scope (.symbol .type) -> Bool
  captureSymbol : BVar scope (.symbol .capture) -> Bool
  /-- Classifier of the single semantic capability observed by this
  two-point valuation. -/
  classifier : Classifier

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
  | .readOnly capture => capture.eval valuation
  | .singleton capability => valuation.term capability
  | .cvar name => valuation.captureSymbol name
  | .project capture kind =>
      if Classifier.Kind.Contains kind valuation.classifier then
        capture.eval valuation
      else
        false

/-- At the single capability observed by a Boolean valuation, capture
presence implies membership in the stated closed classifier kind. -/
def HasClassifierKind {scope : Sig} (valuation : BoolValuation scope)
    (capture : Capture scope) (kind : Classifier.Kind) : Prop :=
  capture.eval valuation = true ->
    Classifier.Kind.Contains kind valuation.classifier

theorem eval_project_equivalent {scope : Sig}
    (valuation : BoolValuation scope) {left right : Capture scope}
    {leftKind rightKind : Classifier.Kind}
    (captureEquality : left.eval valuation = right.eval valuation)
    (kindEquivalent : Classifier.Kind.Equivalent leftKind rightKind) :
    (Capture.project left leftKind).eval valuation =
      (Capture.project right rightKind).eval valuation := by
  by_cases inLeft : Classifier.Kind.Contains leftKind valuation.classifier
  · have inRight := kindEquivalent.1.contains inLeft
    simp only [eval, if_pos inLeft, if_pos inRight]
    exact captureEquality
  · have notInRight : ¬ Classifier.Kind.Contains rightKind
        valuation.classifier := by
      intro inRight
      exact inLeft (kindEquivalent.2.contains inRight)
    simp only [eval, if_neg inLeft, if_neg notInRight]

theorem eval_project_top {scope : Sig} (valuation : BoolValuation scope)
    (capture : Capture scope) :
    (Capture.project capture Classifier.Kind.top).eval valuation =
      capture.eval valuation := by
  simp only [eval, if_pos (Classifier.Kind.Contains.top
    (item := valuation.classifier))]

theorem eval_project_compose {scope : Sig} (valuation : BoolValuation scope)
    (capture : Capture scope) (innerKind outerKind : Classifier.Kind) :
    (Capture.project (Capture.project capture innerKind) outerKind).eval
        valuation =
      (Capture.project capture (outerKind.intersect innerKind)).eval
        valuation := by
  by_cases inOuter : Classifier.Kind.Contains outerKind valuation.classifier
  · by_cases inInner : Classifier.Kind.Contains innerKind
        valuation.classifier
    · have inBoth : Classifier.Kind.Contains
          (outerKind.intersect innerKind) valuation.classifier :=
        Classifier.Kind.Contains.intersect.mpr ⟨inOuter, inInner⟩
      simp only [eval, if_pos inOuter, if_pos inInner, if_pos inBoth]
    · have notInBoth : ¬ Classifier.Kind.Contains
          (outerKind.intersect innerKind) valuation.classifier := by
        intro inBoth
        exact inInner (Classifier.Kind.Contains.intersect.mp inBoth).2
      simp only [eval, if_pos inOuter, if_neg inInner, if_neg notInBoth]
  · have notInBoth : ¬ Classifier.Kind.Contains
        (outerKind.intersect innerKind) valuation.classifier := by
      intro inBoth
      exact inOuter (Classifier.Kind.Contains.intersect.mp inBoth).1
    simp only [eval, if_neg inOuter, if_neg notInBoth]

theorem eval_project_empty {scope : Sig} (valuation : BoolValuation scope)
    (capture : Capture scope) {kind : Classifier.Kind}
    (emptyKind : Classifier.Kind.IsEmpty kind) :
    (Capture.project capture kind).eval valuation =
      (Capture.empty : Capture scope).eval valuation := by
  have absent : ¬ Classifier.Kind.Contains kind valuation.classifier :=
    fun contained => emptyKind.not_contains contained
  simp only [eval, if_neg absent]

/-- A capture already known to contain only members of `kind` is unchanged
by filtering through `kind`. -/
theorem eval_project_complete {scope : Sig} (valuation : BoolValuation scope)
    {capture : Capture scope} {kind : Classifier.Kind}
    (membership : HasClassifierKind valuation capture kind) :
    (Capture.project capture kind).eval valuation = capture.eval valuation := by
  by_cases contained : Classifier.Kind.Contains kind valuation.classifier
  · simp only [eval, if_pos contained]
  · have captureFalse : capture.eval valuation = false := by
      cases value : capture.eval valuation with
      | false => rfl
      | true => exact (contained (membership value)).elim
    simp only [eval, if_neg contained, captureFalse]

/-- Every capability retained by a ground projection belongs to its filter. -/
theorem eval_project_has_kind {scope : Sig} (valuation : BoolValuation scope)
    (capture : Capture scope) (kind : Classifier.Kind) :
    HasClassifierKind valuation (.project capture kind) kind := by
  intro projectionTrue
  by_cases contained : Classifier.Kind.Contains kind valuation.classifier
  · exact contained
  · simp only [eval, if_neg contained] at projectionTrue
    cases projectionTrue

theorem eval_project_source_le {scope : Sig}
    (valuation : BoolValuation scope) (capture : Capture scope)
    (kind : Classifier.Kind) :
    BoolSemantics.LE (Capture.eval valuation (.project capture kind))
      (capture.eval valuation) := by
  by_cases contained : Classifier.Kind.Contains kind valuation.classifier
  · simp only [eval, if_pos contained]
    exact BoolSemantics.refl _
  · simp only [eval, if_neg contained]
    exact BoolSemantics.bottom _

theorem eval_project_mono {scope : Sig} (valuation : BoolValuation scope)
    {lower upper : Capture scope} {lowerKind upperKind : Classifier.Kind}
    (captureOrder : BoolSemantics.LE (lower.eval valuation)
      (upper.eval valuation))
    (kindOrder : Classifier.Kind.Subkind lowerKind upperKind) :
    BoolSemantics.LE ((Capture.project lower lowerKind).eval valuation)
      ((Capture.project upper upperKind).eval valuation) := by
  by_cases inLower : Classifier.Kind.Contains lowerKind valuation.classifier
  · have inUpper := kindOrder.contains inLower
    simp only [eval, if_pos inLower, if_pos inUpper]
    exact captureOrder
  · simp only [eval, if_neg inLower]
    exact BoolSemantics.bottom _

theorem eval_project_merge {scope : Sig} (valuation : BoolValuation scope)
    (capture : Capture scope) (leftKind rightKind : Classifier.Kind) :
    BoolSemantics.LE
      ((Capture.project capture (leftKind ++ rightKind)).eval valuation)
      ((Capture.union (Capture.project capture leftKind)
        (Capture.project capture rightKind)).eval valuation) := by
  by_cases inLeft : Classifier.Kind.Contains leftKind valuation.classifier
  · have inUnion : Classifier.Kind.Contains (leftKind ++ rightKind)
        valuation.classifier :=
      Classifier.Kind.Contains.append (Or.inl inLeft)
    simp only [eval, if_pos inUnion, if_pos inLeft]
    exact BoolSemantics.or_left _ _
  · by_cases inRight : Classifier.Kind.Contains rightKind
        valuation.classifier
    · have inUnion : Classifier.Kind.Contains (leftKind ++ rightKind)
          valuation.classifier :=
        Classifier.Kind.Contains.append (Or.inr inRight)
      simp only [eval, if_pos inUnion, if_neg inLeft, if_pos inRight,
        Bool.false_or]
      exact BoolSemantics.refl _
    · have notInUnion : ¬ Classifier.Kind.Contains
          (leftKind ++ rightKind) valuation.classifier := by
        intro inUnion
        cases Classifier.Kind.Contains.of_append inUnion with
        | inl contradiction => exact inLeft contradiction
        | inr contradiction => exact inRight contradiction
      simp only [eval, if_neg notInUnion, if_neg inLeft, if_neg inRight,
        Bool.false_or]
      exact BoolSemantics.bottom _

/-- The empty capture has every classifier kind. -/
theorem hasClassifierKind_empty {scope : Sig} (valuation : BoolValuation scope)
    (kind : Classifier.Kind) :
    HasClassifierKind valuation (.empty : Capture scope) kind := by
  intro impossible
  simp [eval] at impossible

/-- Capture kinding is closed under union. -/
theorem hasClassifierKind_union {scope : Sig} (valuation : BoolValuation scope)
    {left right : Capture scope} {kind : Classifier.Kind}
    (leftMembership : HasClassifierKind valuation left kind)
    (rightMembership : HasClassifierKind valuation right kind) :
    HasClassifierKind valuation (.union left right) kind := by
  intro unionTrue
  have componentTrue : left.eval valuation = true ∨
      right.eval valuation = true := by
    simpa [eval, Bool.or_eq_true] using unionTrue
  cases componentTrue with
  | inl leftTrue => exact leftMembership leftTrue
  | inr rightTrue => exact rightMembership rightTrue

/-- Capture kinding is downward closed under Boolean capture inclusion. -/
theorem hasClassifierKind_subcapture {scope : Sig}
    (valuation : BoolValuation scope) {lower upper : Capture scope}
    {kind : Classifier.Kind}
    (ordering : BoolSemantics.LE (lower.eval valuation) (upper.eval valuation))
    (upperMembership : HasClassifierKind valuation upper kind) :
    HasClassifierKind valuation lower kind := by
  intro lowerTrue
  exact upperMembership (ordering lowerTrue)

/-- Ground subkinding widens a Boolean capture-kind bound. -/
theorem hasClassifierKind_widen {scope : Sig}
    (valuation : BoolValuation scope) {capture : Capture scope}
    {sourceKind targetKind : Classifier.Kind}
    (membership : HasClassifierKind valuation capture sourceKind)
    (kindOrder : Classifier.Kind.Subkind sourceKind targetKind) :
    HasClassifierKind valuation capture targetKind := by
  intro captureTrue
  exact kindOrder.contains (membership captureTrue)

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
  | .modal _ _ => true
  | .forallT _ _ => true
  | .existsT _ _ => true
  /- Recursive projections are opaque to this deliberately finite model.
  The soundness theorem below is consequently scoped to certificates that do
  not use recursive unfolding.  A semantic account of guarded recursive
  equality requires regular trees or a step-indexed model, not an arbitrary
  Boolean equation. -/
  | .recProj _ _ => false

end Ty

namespace Evidence

/-- The fragment covered by the original Boolean consistency model.

Guarded recursive equality is independently checked, but negative recursive
types need not have a fixed point in `Bool`.  Recording this syntactic support
condition keeps the old theorem honest until the recursive target receives a
regular-tree or step-indexed semantics. -/
def recursionFree {scope : Sig} {relation : Relation} :
    Evidence relation scope -> Bool
  | .var _ => true
  | .equalityRefl _ => true
  | .equalitySymm inner => inner.recursionFree
  | .equalityTrans first second =>
      first.recursionFree && second.recursionFree
  | .unfoldRec _ _ => false
  | .equalityArrow domain codomain =>
      domain.recursionFree && codomain.recursionFree
  | .equalityCapturing captures shape =>
      captures.recursionFree && shape.recursionFree
  | .equalityCaptureUnion left right =>
      left.recursionFree && right.recursionFree
  | .equalityCaptureReadOnly capture => capture.recursionFree
  | .equalityCaptureProject equality _ _ => equality.recursionFree
  | .equalityCaptureProjectTop _ => true
  | .equalityCaptureProjectCompose _ _ _ => true
  | .equalityCaptureProjectEmpty _ _ => true
  | .equalityCaptureProjectComplete membership => membership.recursionFree
  | .inclusionRefl _ => true
  | .inclusionTrans first second =>
      first.recursionFree && second.recursionFree
  | .equalityToInclusion equality => equality.recursionFree
  | .typeTop _ => true
  | .typeBottom _ => true
  | .typeArrow domain codomain =>
      domain.recursionFree && codomain.recursionFree
  | .typeCapturing captures shape =>
      captures.recursionFree && shape.recursionFree
  | .captureEmpty _ => true
  | .captureUnionLeft _ _ => true
  | .captureUnionRight _ _ => true
  | .captureUnionElim left right =>
      left.recursionFree && right.recursionFree
  | .captureVariable _ => true
  | .captureReadOnly _ => true
  | .captureReadOnlyMono subcapture => subcapture.recursionFree
  | .captureProjectSource _ _ => true
  | .captureProjectMono subcapture _ _ => subcapture.recursionFree
  | .captureProjectMerge _ _ _ => true
  | .modeEmpty _ => true
  | .modeUnion left right => left.recursionFree && right.recursionFree
  | .modeSubcapture subcapture upperMode =>
      subcapture.recursionFree && upperMode.recursionFree
  | .modeWritable _ => true
  | .modeReadOnly _ => true
  | .separateSymm evidence => evidence.recursionFree
  | .separateUnion left right =>
      left.recursionFree && right.recursionFree
  | .separateEmpty _ => true
  | .separateReadOnly left right =>
      left.recursionFree && right.recursionFree
  | .separateSubcapture subcapture separation =>
      subcapture.recursionFree && separation.recursionFree
  | .separateOfDisjoint disjoint => disjoint.recursionFree
  | .disjointSymm evidence => evidence.recursionFree
  | .disjointUnion left right =>
      left.recursionFree && right.recursionFree
  | .disjointEmpty _ => true
  | .disjointEquality equality disjoint =>
      equality.recursionFree && disjoint.recursionFree
  | .disjointCaptureProject _ _ _ _ => true
  | .captureHasKindEmpty _ => true
  | .captureHasKindUnion left right =>
      left.recursionFree && right.recursionFree
  | .captureHasKindProject _ _ => true
  | .captureHasKindSubcapture subcapture upper =>
      subcapture.recursionFree && upper.recursionFree
  | .captureHasKindWiden membership _ _ => membership.recursionFree

/-- Certificates outside type equality and type inclusion cannot contain the
type-only recursive unfold constructor. -/
theorem recursionFree_of_nonTypeRelation {scope : Sig}
    {relation : Relation} (evidence : Evidence relation scope)
    (notEquality : relation ≠ .equality .type)
    (notInclusion : relation ≠ .inclusion .type) :
    evidence.recursionFree = true := by
  induction evidence <;> simp_all [recursionFree]

theorem captureInclusion_recursionFree {scope : Sig}
    (evidence : Evidence (.inclusion .capture) scope) :
    evidence.recursionFree = true :=
  recursionFree_of_nonTypeRelation evidence (by decide) (by decide)

end Evidence

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
  | .separate _ _ => True
  | .disjoint _ _ => True
  | .mode _ => True
  | .captureHasKind capture kind =>
      Capture.HasClassifierKind valuation capture kind

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

/-- Every recursion-free declarative evidence derivation in an
assumption-free scope is valid in the Boolean model. -/
theorem sound_of_no_evidence {scope : Sig} {context : Ctx scope}
    {relation : Relation} {evidence : Evidence relation scope}
    {proposition : Proposition relation scope}
    (noEvidence : HasNoEvidenceBinders scope)
    (typing : Evidence.Proves context evidence proposition)
    (noRecursion : evidence.recursionFree = true) :
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
      exact (induction noRecursion).symm
  | equalityTrans firstTyping secondTyping firstInduction secondInduction =>
      simp only [Evidence.recursionFree, Bool.and_eq_true] at noRecursion
      exact (firstInduction noRecursion.1).trans
        (secondInduction noRecursion.2)
  | unfoldRec guarded =>
      simp [Evidence.recursionFree] at noRecursion
  | equalityArrow domainTyping codomainTyping domainInduction
      codomainInduction =>
      simp only [Evidence.recursionFree, Bool.and_eq_true] at noRecursion
      simp only [Proposition.Holds, StaticExpr.eval, Ty.eval] at domainInduction codomainInduction ⊢
      rw [domainInduction noRecursion.1, codomainInduction noRecursion.2]
  | equalityCapturing captureTyping shapeTyping captureInduction
      shapeInduction =>
      simp only [Evidence.recursionFree, Bool.and_eq_true] at noRecursion
      simp only [Proposition.Holds, StaticExpr.eval, Ty.eval] at captureInduction shapeInduction ⊢
      rw [captureInduction noRecursion.1, shapeInduction noRecursion.2]
  | equalityCaptureUnion leftTyping rightTyping leftInduction
      rightInduction =>
      simp only [Evidence.recursionFree, Bool.and_eq_true] at noRecursion
      simp only [Proposition.Holds, StaticExpr.eval, Capture.eval] at leftInduction rightInduction ⊢
      rw [leftInduction noRecursion.1, rightInduction noRecursion.2]
  | equalityCaptureReadOnly typing induction =>
      simpa [Proposition.Holds, StaticExpr.eval, Capture.eval] using
        induction noRecursion
  | equalityCaptureProject typing kindEquivalent induction =>
      exact Capture.eval_project_equivalent valuation
        (induction noRecursion) kindEquivalent
  | equalityCaptureProjectTop capture =>
      exact Capture.eval_project_top valuation capture
  | equalityCaptureProjectCompose capture innerKind outerKind =>
      exact Capture.eval_project_compose valuation capture innerKind outerKind
  | equalityCaptureProjectEmpty capture kind emptyKind =>
      exact Capture.eval_project_empty valuation capture emptyKind
  | equalityCaptureProjectComplete typing induction =>
      exact Capture.eval_project_complete valuation (induction noRecursion)
  | inclusionRefl expression =>
      exact BoolSemantics.refl _
  | inclusionTrans firstTyping secondTyping firstInduction secondInduction =>
      simp only [Evidence.recursionFree, Bool.and_eq_true] at noRecursion
      exact BoolSemantics.trans (firstInduction noRecursion.1)
        (secondInduction noRecursion.2)
  | equalityToInclusion typing induction =>
      exact BoolSemantics.equality_le (induction noRecursion)
  | typeTop source =>
      exact BoolSemantics.top _
  | typeBottom target =>
      exact BoolSemantics.bottom _
  | typeArrow domainTyping codomainTyping domainInduction
      codomainInduction =>
      simp only [Evidence.recursionFree, Bool.and_eq_true] at noRecursion
      exact BoolSemantics.implication_mono
        (domainInduction noRecursion.1) (codomainInduction noRecursion.2)
  | typeCapturing captureTyping shapeTyping captureInduction
      shapeInduction =>
      simp only [Evidence.recursionFree, Bool.and_eq_true] at noRecursion
      exact BoolSemantics.and_mono
        (captureInduction noRecursion.1) (shapeInduction noRecursion.2)
  | captureEmpty target =>
      exact BoolSemantics.bottom _
  | captureUnionLeft left right =>
      exact BoolSemantics.or_left _ _
  | captureUnionRight left right =>
      exact BoolSemantics.or_right _ _
  | captureUnionElim leftTyping rightTyping leftInduction rightInduction =>
      simp only [Evidence.recursionFree, Bool.and_eq_true] at noRecursion
      exact BoolSemantics.or_elim (leftInduction noRecursion.1)
        (rightInduction noRecursion.2)
  | captureVariable binding =>
      exact respects _ _ _ binding
  | captureReadOnly capture =>
      exact BoolSemantics.refl _
  | captureReadOnlyMono typing induction =>
      simpa [Proposition.Holds, StaticExpr.eval, Capture.eval] using
        induction noRecursion
  | captureProjectSource capture kind =>
      exact Capture.eval_project_source_le valuation capture kind
  | captureProjectMono typing kindSubtyping induction =>
      exact Capture.eval_project_mono valuation (induction noRecursion)
        kindSubtyping
  | captureProjectMerge capture leftKind rightKind =>
      exact Capture.eval_project_merge valuation capture leftKind rightKind
  | modeEmpty => trivial
  | modeUnion => trivial
  | modeSubcapture => trivial
  | modeWritable => trivial
  | modeReadOnly => trivial
  | separateSymm => trivial
  | separateUnion => trivial
  | separateEmpty => trivial
  | separateReadOnly => trivial
  | separateSubcapture => trivial
  | separateOfDisjoint => trivial
  | disjointSymm => trivial
  | disjointUnion => trivial
  | disjointEmpty => trivial
  | disjointEquality => trivial
  | disjointCaptureProject => trivial
  | captureHasKindEmpty kind =>
      exact Capture.hasClassifierKind_empty valuation kind
  | captureHasKindUnion leftTyping rightTyping leftInduction rightInduction =>
      simp only [Evidence.recursionFree, Bool.and_eq_true] at noRecursion
      exact Capture.hasClassifierKind_union valuation
        (leftInduction noRecursion.1) (rightInduction noRecursion.2)
  | captureHasKindProject capture kind =>
      exact Capture.eval_project_has_kind valuation capture kind
  | captureHasKindSubcapture subcaptureTyping upperTyping
      subcaptureInduction upperInduction =>
      simp only [Evidence.recursionFree, Bool.and_eq_true] at noRecursion
      exact Capture.hasClassifierKind_subcapture valuation
        (subcaptureInduction noRecursion.1) (upperInduction noRecursion.2)
  | captureHasKindWiden membershipTyping kindSubtyping membershipInduction =>
      exact Capture.hasClassifierKind_widen valuation
        (membershipInduction noRecursion) kindSubtyping

end Evidence.Proves

namespace BoolValuation

/-- The unique valuation of the empty scope. -/
def empty : BoolValuation [] where
  term := fun index => nomatch index
  typeSymbol := fun index => nomatch index
  captureSymbol := fun index => nomatch index
  classifier := .top

/-- A valuation distinguishing the sole term capability in a one-term scope. -/
def oneTermTrue : BoolValuation ([] ▹ .term) where
  term := fun
    | .here => true
    | .there index => nomatch index
  typeSymbol := fun
    | .there index => nomatch index
  captureSymbol := fun
    | .there index => nomatch index
  classifier := .top

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
      (.inclusion (.type (.top : Ty [])) (.type (.bot : Ty []))))
    (noRecursion : evidence.recursionFree = true) :
    False := by
  have validity := Evidence.Proves.sound_of_no_evidence
    noEvidenceBinders_empty typing
  have holds := validity noRecursion BoolValuation.empty (by
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
  have holds := validity (Evidence.captureInclusion_recursionFree evidence)
    BoolValuation.oneTermTrue (by
    intro index captures shape binding
    cases index with
    | here => cases binding
    | there older => nomatch older)
  have impossible : false = true := holds rfl
  cases impossible

end ManySortedFC
