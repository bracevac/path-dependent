import Coercions.ManySortedFC.Evidence

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
