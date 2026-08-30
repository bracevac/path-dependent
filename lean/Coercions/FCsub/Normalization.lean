import Coercions.FCsub.CheckerCompleteness

/-!
# FCsub coercion normalization

This target-only pass removes reflexive links from equality and inclusion
transitivity spines and right-associates the remaining links.  It recursively
normalizes coercions nested below symmetry, equality-to-inclusion, arrows, and
quantified payloads.  Telescope morphisms are annotations rather than
coercion spines, so normalization leaves them unchanged.

The pass is certified independently of DOT: for the direct equality and
inclusion spine/payload positions it traverses, it preserves declarative
endpoints, remains accepted by the structural checker, never increases the
number of counted coercion constructors, and is idempotent.  Evidence nested
inside an opaque telescope morphism is intentionally outside this normal-form
claim.

Normalization is therefore a pass over already typed evidence, not a
sanitizer to run before checking untrusted syntax.  An ill-typed transitivity
tree has no certified intermediate endpoint, and deleting one of its
syntactic reflexive links need not preserve checker rejection.
-/

namespace FCsub

/-! ## Structural metrics -/

namespace EqCo

/-- Number of equality-coercion constructors in a certificate. -/
def nodeCount {scope : Sig} : EqCo scope → Nat
  | .var _ => 1
  | .refl _ => 1
  | .symm evidence => evidence.nodeCount + 1
  | .trans first second => first.nodeCount + second.nodeCount + 1
  | .unfoldRec _ _ => 1

end EqCo

namespace LeCo

/-- Number of inclusion-coercion constructors, including nested equality
coercions but excluding unchanged telescope-morphism annotations. -/
def nodeCount {scope : Sig} : LeCo scope → Nat
  | .var _ => 1
  | .refl _ => 1
  | .trans first second => first.nodeCount + second.nodeCount + 1
  | .top _ => 1
  | .bot _ => 1
  | .eqToLe equality => equality.nodeCount + 1
  | .arr domain codomain => domain.nodeCount + codomain.nodeCount + 1
  | .existsT _ _ _ payload => payload.nodeCount + 1
  | .forallT _ _ _ body => body.nodeCount + 1

end LeCo

/-! ## Smart transitivity spines -/

namespace EqCo

/-- Append a normalized equality spine, deleting a reflexive right link. -/
def finish {scope : Sig} (left right : EqCo scope) : EqCo scope :=
  match right with
  | .refl _ => left
  | right => .trans left right

/-- Compose two normalized equality spines into a right-associated spine. -/
def compose {scope : Sig} (left right : EqCo scope) : EqCo scope :=
  match left with
  | .refl _ => right
  | .trans first rest => .trans first (compose rest right)
  | left => finish left right

end EqCo

namespace LeCo

/-- Append a normalized inclusion spine, deleting a reflexive right link. -/
def finish {scope : Sig} (left right : LeCo scope) : LeCo scope :=
  match right with
  | .refl _ => left
  | right => .trans left right

/-- Compose two normalized inclusion spines into a right-associated spine. -/
def compose {scope : Sig} (left right : LeCo scope) : LeCo scope :=
  match left with
  | .refl _ => right
  | .trans first rest => .trans first (compose rest right)
  | left => finish left right

end LeCo

/-! ## Normalization and executable normal forms -/

namespace EqCo

/-- Normalize equality coercions recursively. -/
def normalize {scope : Sig} : EqCo scope → EqCo scope
  | .var index => .var index
  | .refl type => .refl type
  | .symm evidence => .symm evidence.normalize
  | .trans first second => compose first.normalize second.normalize
  | .unfoldRec bodies index => .unfoldRec bodies index

/-- Whether a certificate may head a canonical transitivity spine. -/
def isAtom {scope : Sig} : EqCo scope → Bool
  | .refl _ | .trans _ _ => false
  | _ => true

/-- Whether a certificate is syntactically reflexive. -/
def isRefl {scope : Sig} : EqCo scope → Bool
  | .refl _ => true
  | _ => false

/-- Executable normal-form predicate for equality coercions. -/
def reduced {scope : Sig} : EqCo scope → Bool
  | .var _ => true
  | .refl _ => true
  | .symm evidence => evidence.reduced
  | .trans first rest =>
      first.isAtom && rest.isRefl.not && first.reduced && rest.reduced
  | .unfoldRec _ _ => true

end EqCo

namespace LeCo

/-- Normalize inclusion coercions recursively. -/
def normalize {scope : Sig} : LeCo scope → LeCo scope
  | .var index => .var index
  | .refl type => .refl type
  | .trans first second => compose first.normalize second.normalize
  | .top source => .top source
  | .bot target => .bot target
  | .eqToLe equality => .eqToLe equality.normalize
  | .arr domain codomain => .arr domain.normalize codomain.normalize
  | .existsT adaptation sourcePayload targetPayload payload =>
      .existsT adaptation sourcePayload targetPayload payload.normalize
  | .forallT adaptation sourceBody targetBody body =>
      .forallT adaptation sourceBody targetBody body.normalize

/-- Whether a certificate may head a canonical transitivity spine. -/
def isAtom {scope : Sig} : LeCo scope → Bool
  | .refl _ | .trans _ _ => false
  | _ => true

/-- Whether a certificate is syntactically reflexive. -/
def isRefl {scope : Sig} : LeCo scope → Bool
  | .refl _ => true
  | _ => false

/-- Executable normal-form predicate for the direct inclusion spine and its
payload coercions.  Telescope-morphism adaptations are treated as opaque. -/
def reduced {scope : Sig} : LeCo scope → Bool
  | .var _ => true
  | .refl _ => true
  | .trans first rest =>
      first.isAtom && rest.isRefl.not && first.reduced && rest.reduced
  | .top _ => true
  | .bot _ => true
  | .eqToLe equality => equality.reduced
  | .arr domain codomain => domain.reduced && codomain.reduced
  | .existsT _ _ _ payload => payload.reduced
  | .forallT _ _ _ body => body.reduced

end LeCo

/-! ## Normalization produces fixed points -/

namespace EqCo

@[simp]
theorem isRefl_compose {scope : Sig} (left right : EqCo scope) :
    (compose left right).isRefl = (left.isRefl && right.isRefl) := by
  cases left <;> cases right <;> rfl

private theorem reduced_finish {scope : Sig} (left right : EqCo scope)
    (atom : left.isAtom = true) (leftReduced : left.reduced = true)
    (rightReduced : right.reduced = true) :
    (finish left right).reduced = true := by
  cases right <;> simp_all [finish, reduced, isRefl]

/-- Smart equality composition is closed over normal forms. -/
def reduced_compose {scope : Sig} (left right : EqCo scope)
    (leftReduced : left.reduced = true)
    (rightReduced : right.reduced = true) :
    (compose left right).reduced = true :=
  match left with
  | .var index =>
      reduced_finish (.var index) right rfl leftReduced rightReduced
  | .refl _ => by simpa [compose] using rightReduced
  | .symm evidence =>
      reduced_finish (.symm evidence) right rfl leftReduced rightReduced
  | .trans first rest => by
      have parts : ((first.isAtom = true ∧ rest.isRefl.not = true) ∧
          first.reduced = true) ∧ rest.reduced = true := by
        simpa only [reduced, Bool.and_eq_true] using leftReduced
      have tailReduced := reduced_compose rest right parts.2 rightReduced
      simp only [compose, reduced, Bool.and_eq_true]
      refine ⟨⟨⟨parts.1.1.1, ?_⟩, parts.1.2⟩, tailReduced⟩
      rw [isRefl_compose]
      have restFalse : rest.isRefl = false := by
        simpa only [Bool.not_eq_true'] using parts.1.1.2
      simp [restFalse]
  | .unfoldRec bodies index =>
      reduced_finish (.unfoldRec bodies index) right rfl leftReduced
        rightReduced

/-- Every equality certificate normalizes to executable normal form. -/
def reduced_normalize {scope : Sig} (evidence : EqCo scope) :
    evidence.normalize.reduced = true :=
  match evidence with
  | .var _ => rfl
  | .refl _ => rfl
  | .symm evidence => by
      simpa [normalize, reduced] using reduced_normalize evidence
  | .trans first second =>
      reduced_compose first.normalize second.normalize
        (reduced_normalize first) (reduced_normalize second)
  | .unfoldRec _ _ => rfl

private theorem compose_eq_trans {scope : Sig} (left right : EqCo scope)
    (atom : left.isAtom = true) (rightNotRefl : right.isRefl.not = true) :
    compose left right = .trans left right := by
  cases left <;> cases right <;>
    simp_all [compose, finish, isAtom, isRefl]

/-- Reduced equality certificates are fixed points. -/
def normalize_eq_self_of_reduced {scope : Sig} (evidence : EqCo scope)
    (isReduced : evidence.reduced = true) :
    evidence.normalize = evidence :=
  match evidence with
  | .var _ => rfl
  | .refl _ => rfl
  | .symm evidence => by
      have innerReduced : evidence.reduced = true := by
        simpa only [reduced] using isReduced
      simp [normalize, normalize_eq_self_of_reduced evidence innerReduced]
  | .trans first rest => by
      have parts : ((first.isAtom = true ∧ rest.isRefl.not = true) ∧
          first.reduced = true) ∧ rest.reduced = true := by
        simpa only [reduced, Bool.and_eq_true] using isReduced
      simp only [normalize]
      rw [normalize_eq_self_of_reduced first parts.1.2,
        normalize_eq_self_of_reduced rest parts.2]
      exact compose_eq_trans first rest parts.1.1.1 parts.1.1.2
  | .unfoldRec _ _ => rfl

/-- Equality normalization is idempotent. -/
theorem normalize_idempotent {scope : Sig} (evidence : EqCo scope) :
    evidence.normalize.normalize = evidence.normalize :=
  normalize_eq_self_of_reduced evidence.normalize (reduced_normalize evidence)

end EqCo

namespace LeCo

@[simp]
theorem isRefl_compose {scope : Sig} (left right : LeCo scope) :
    (compose left right).isRefl = (left.isRefl && right.isRefl) := by
  cases left <;> cases right <;> rfl

private theorem reduced_finish {scope : Sig} (left right : LeCo scope)
    (atom : left.isAtom = true) (leftReduced : left.reduced = true)
    (rightReduced : right.reduced = true) :
    (finish left right).reduced = true := by
  cases right <;> simp_all [finish, reduced, isRefl]

/-- Smart inclusion composition is closed over normal forms. -/
def reduced_compose {scope : Sig} (left right : LeCo scope)
    (leftReduced : left.reduced = true)
    (rightReduced : right.reduced = true) :
    (compose left right).reduced = true :=
  match left with
  | .refl _ => by simpa [compose] using rightReduced
  | .trans first rest => by
      have parts : ((first.isAtom = true ∧ rest.isRefl.not = true) ∧
          first.reduced = true) ∧ rest.reduced = true := by
        simpa only [reduced, Bool.and_eq_true] using leftReduced
      have tailReduced := reduced_compose rest right parts.2 rightReduced
      simp only [compose, reduced, Bool.and_eq_true]
      refine ⟨⟨⟨parts.1.1.1, ?_⟩, parts.1.2⟩, tailReduced⟩
      rw [isRefl_compose]
      have restFalse : rest.isRefl = false := by
        simpa only [Bool.not_eq_true'] using parts.1.1.2
      simp [restFalse]
  | .var index =>
      reduced_finish (.var index) right rfl leftReduced rightReduced
  | .top source =>
      reduced_finish (.top source) right rfl leftReduced rightReduced
  | .bot target =>
      reduced_finish (.bot target) right rfl leftReduced rightReduced
  | .eqToLe equality =>
      reduced_finish (.eqToLe equality) right rfl leftReduced rightReduced
  | .arr domain codomain =>
      reduced_finish (.arr domain codomain) right rfl leftReduced rightReduced
  | .existsT adaptation sourcePayload targetPayload payload =>
      reduced_finish (.existsT adaptation sourcePayload targetPayload payload)
        right rfl leftReduced rightReduced
  | .forallT adaptation sourceBody targetBody body =>
      reduced_finish (.forallT adaptation sourceBody targetBody body)
        right rfl leftReduced rightReduced

/-- Every inclusion certificate normalizes to executable normal form. -/
def reduced_normalize {scope : Sig} (evidence : LeCo scope) :
    evidence.normalize.reduced = true :=
  match evidence with
  | .var _ => rfl
  | .refl _ => rfl
  | .trans first second =>
      reduced_compose first.normalize second.normalize
        (reduced_normalize first) (reduced_normalize second)
  | .top _ => rfl
  | .bot _ => rfl
  | .eqToLe equality => EqCo.reduced_normalize equality
  | .arr domain codomain => by
      simp [normalize, reduced, reduced_normalize domain,
        reduced_normalize codomain]
  | .existsT _ _ _ payload => reduced_normalize payload
  | .forallT _ _ _ body => reduced_normalize body

private theorem compose_eq_trans {scope : Sig} (left right : LeCo scope)
    (atom : left.isAtom = true) (rightNotRefl : right.isRefl.not = true) :
    compose left right = .trans left right := by
  cases left <;> cases right <;>
    simp_all [compose, finish, isAtom, isRefl]

/-- Reduced inclusion certificates are fixed points. -/
def normalize_eq_self_of_reduced {scope : Sig} (evidence : LeCo scope)
    (isReduced : evidence.reduced = true) :
    evidence.normalize = evidence :=
  match evidence with
  | .var _ => rfl
  | .refl _ => rfl
  | .trans first rest => by
      have parts : ((first.isAtom = true ∧ rest.isRefl.not = true) ∧
          first.reduced = true) ∧ rest.reduced = true := by
        simpa only [reduced, Bool.and_eq_true] using isReduced
      simp only [normalize]
      rw [normalize_eq_self_of_reduced first parts.1.2,
        normalize_eq_self_of_reduced rest parts.2]
      exact compose_eq_trans first rest parts.1.1.1 parts.1.1.2
  | .top _ => rfl
  | .bot _ => rfl
  | .eqToLe equality => by
      have equalityReduced : equality.reduced = true := by
        simpa only [reduced] using isReduced
      simp [normalize,
        EqCo.normalize_eq_self_of_reduced equality equalityReduced]
  | .arr domain codomain => by
      have parts : domain.reduced = true ∧ codomain.reduced = true := by
        simpa only [reduced, Bool.and_eq_true] using isReduced
      simp [normalize,
        normalize_eq_self_of_reduced domain parts.1,
        normalize_eq_self_of_reduced codomain parts.2]
  | .existsT adaptation sourcePayload targetPayload payload => by
      have payloadReduced : payload.reduced = true := by
        simpa only [reduced] using isReduced
      simp [normalize,
        normalize_eq_self_of_reduced payload payloadReduced]
  | .forallT adaptation sourceBody targetBody body => by
      have bodyReduced : body.reduced = true := by
        simpa only [reduced] using isReduced
      simp [normalize,
        normalize_eq_self_of_reduced body bodyReduced]

/-- Inclusion normalization is idempotent. -/
theorem normalize_idempotent {scope : Sig} (evidence : LeCo scope) :
    evidence.normalize.normalize = evidence.normalize :=
  normalize_eq_self_of_reduced evidence.normalize (reduced_normalize evidence)

end LeCo

/-! ## Size bounds and the alias-chain profile -/

namespace EqCo

/-- Smart equality composition costs no more constructors than an ordinary
transitivity node. -/
theorem nodeCount_compose_le {scope : Sig} (left right : EqCo scope) :
    (compose left right).nodeCount ≤
      left.nodeCount + right.nodeCount + 1 := by
  induction left with
  | var index => cases right <;> simp [compose, finish, nodeCount]
  | refl type =>
      simp only [compose, nodeCount]
      omega
  | symm evidence induction =>
      cases right <;> simp [compose, finish, nodeCount]
  | trans first rest firstInduction restInduction =>
      simp only [compose, nodeCount]
      omega
  | unfoldRec bodies index =>
      cases right <;> simp [compose, finish, nodeCount]

/-- Equality normalization never increases constructor count. -/
theorem nodeCount_normalize_le {scope : Sig} (evidence : EqCo scope) :
    evidence.normalize.nodeCount ≤ evidence.nodeCount := by
  induction evidence with
  | var => exact Nat.le_refl _
  | refl => exact Nat.le_refl _
  | symm evidence induction =>
      simp only [normalize, nodeCount]
      omega
  | trans first second firstInduction secondInduction =>
      simp only [normalize, nodeCount]
      have composed := nodeCount_compose_le first.normalize second.normalize
      omega
  | unfoldRec => exact Nat.le_refl _

/-- The generic shape emitted by `PathAliases.AliasScope.between` when its anchors are
definitionally equal.  It contains six equality constructors. -/
@[simp]
theorem nodeCount_aliasBetween {scope : Sig}
    (first second : BVar scope (.evidence .equality)) (anchor : Ty scope) :
    nodeCount
      (.trans (.var first) (.trans (.refl anchor) (.symm (.var second)))) =
      6 := rfl

/-- Normalization deletes the reflexive anchor link from an alias chain. -/
@[simp]
theorem normalize_aliasBetween {scope : Sig}
    (first second : BVar scope (.evidence .equality)) (anchor : Ty scope) :
    normalize
      (.trans (.var first) (.trans (.refl anchor) (.symm (.var second)))) =
      .trans (.var first) (.symm (.var second)) := rfl

/-- The normalized path-alias chain shape contains four constructors. -/
@[simp]
theorem nodeCount_normalize_aliasBetween {scope : Sig}
    (first second : BVar scope (.evidence .equality)) (anchor : Ty scope) :
    nodeCount (normalize
      (.trans (.var first) (.trans (.refl anchor) (.symm (.var second))))) =
      4 := rfl

end EqCo

namespace LeCo

/-- Smart inclusion composition costs no more constructors than an ordinary
transitivity node. -/
theorem nodeCount_compose_le {scope : Sig} (left right : LeCo scope) :
    (compose left right).nodeCount ≤
      left.nodeCount + right.nodeCount + 1 :=
  match left with
  | .var index => by
      cases right <;> simp [compose, finish, nodeCount]
  | .refl type => by
      simp only [compose, nodeCount]
      omega
  | .trans first rest => by
      simp only [compose, nodeCount]
      have restBound := nodeCount_compose_le rest right
      omega
  | .top source => by
      cases right <;> simp [compose, finish, nodeCount]
  | .bot target => by
      cases right <;> simp [compose, finish, nodeCount]
  | .eqToLe equality => by
      cases right <;> simp [compose, finish, nodeCount]
  | .arr domain codomain => by
      cases right <;> simp [compose, finish, nodeCount]
  | .existsT adaptation sourcePayload targetPayload payload => by
      cases right <;> simp [compose, finish, nodeCount]
  | .forallT adaptation sourceBody targetBody body => by
      cases right <;> simp [compose, finish, nodeCount]

/-- Inclusion normalization never increases constructor count. -/
theorem nodeCount_normalize_le {scope : Sig} (evidence : LeCo scope) :
    evidence.normalize.nodeCount ≤ evidence.nodeCount :=
  match evidence with
  | .var _ => Nat.le_refl _
  | .refl _ => Nat.le_refl _
  | .trans first second => by
      simp only [normalize, nodeCount]
      have composed := nodeCount_compose_le first.normalize second.normalize
      have firstInduction := nodeCount_normalize_le first
      have secondInduction := nodeCount_normalize_le second
      omega
  | .top _ => Nat.le_refl _
  | .bot _ => Nat.le_refl _
  | .eqToLe equality => by
      simp only [normalize, nodeCount]
      exact Nat.add_le_add_right (EqCo.nodeCount_normalize_le equality) 1
  | .arr domain codomain => by
      simp only [normalize, nodeCount]
      have domainInduction := nodeCount_normalize_le domain
      have codomainInduction := nodeCount_normalize_le codomain
      omega
  | .existsT adaptation sourcePayload targetPayload payload => by
      simp only [normalize, nodeCount]
      have induction := nodeCount_normalize_le payload
      omega
  | .forallT adaptation sourceBody targetBody body => by
      simp only [normalize, nodeCount]
      have induction := nodeCount_normalize_le body
      omega

end LeCo

/-! ## Declarative endpoint preservation -/

namespace EqCo

/-- Deleting a reflexive right link preserves checked equality endpoints. -/
def finish_hasType {scope : Sig} {context : Ctx scope}
    {left right : EqCo scope} {source middle target : Ty scope}
    (leftTyping : HasType context left source middle)
    (rightTyping : HasType context right middle target) :
    HasType context (finish left right) source target :=
  match rightTyping with
  | .var binding => .trans leftTyping (.var binding)
  | .refl _ => leftTyping
  | .symm inner => .trans leftTyping (.symm inner)
  | .trans first second => .trans leftTyping (.trans first second)
  | .unfoldRec guarded => .trans leftTyping (.unfoldRec guarded)

/-- Right-associating a checked equality spine preserves its endpoints. -/
def compose_hasType {scope : Sig} {context : Ctx scope}
    {left right : EqCo scope} {source middle target : Ty scope}
    (leftTyping : HasType context left source middle)
    (rightTyping : HasType context right middle target) :
    HasType context (compose left right) source target :=
  match leftTyping with
  | .var binding => finish_hasType (.var binding) rightTyping
  | .refl _ => rightTyping
  | .symm inner => finish_hasType (.symm inner) rightTyping
  | .trans first rest => .trans first (compose_hasType rest rightTyping)
  | .unfoldRec guarded => finish_hasType (.unfoldRec guarded) rightTyping

/-- Equality normalization preserves both declarative endpoints. -/
def normalize_hasType {scope : Sig} {context : Ctx scope}
    {evidence : EqCo scope} {source target : Ty scope}
    (typing : HasType context evidence source target) :
    HasType context evidence.normalize source target :=
  match typing with
  | .var binding => .var binding
  | .refl type => .refl type
  | .symm inner => .symm (normalize_hasType inner)
  | .trans first second =>
      compose_hasType (normalize_hasType first) (normalize_hasType second)
  | .unfoldRec guarded => .unfoldRec guarded

/-- The independent checker accepts normalized equality evidence at the same
endpoints. -/
theorem synthEq_normalize {scope : Sig} {context : Ctx scope}
    {evidence : EqCo scope} {source target : Ty scope}
    (typing : HasType context evidence source target) :
    synthEq context evidence.normalize = some (source, target) :=
  synthEq_complete (normalize_hasType typing)

/-- On well-typed equality evidence, normalization preserves the checker's
complete synthesized result. -/
theorem synthEq_normalize_eq {scope : Sig} {context : Ctx scope}
    {evidence : EqCo scope} {source target : Ty scope}
    (typing : HasType context evidence source target) :
    synthEq context evidence.normalize = synthEq context evidence := by
  rw [synthEq_normalize typing, synthEq_complete typing]

end EqCo

namespace LeCo

/-- Deleting a reflexive right link preserves checked inclusion endpoints. -/
def finish_hasType {scope : Sig} {context : Ctx scope}
    {left right : LeCo scope} {source middle target : Ty scope}
    (leftTyping : HasType context left source middle)
    (rightTyping : HasType context right middle target) :
    HasType context (finish left right) source target :=
  match rightTyping with
  | .var binding => .trans leftTyping (.var binding)
  | .refl _ => leftTyping
  | .trans first second => .trans leftTyping (.trans first second)
  | .top sourceType => .trans leftTyping (.top sourceType)
  | .bot targetType => .trans leftTyping (.bot targetType)
  | .eqToLe equality => .trans leftTyping (.eqToLe equality)
  | .arr domain codomain => .trans leftTyping (.arr domain codomain)
  | .existsT adaptation payload =>
      .trans leftTyping (.existsT adaptation payload)
  | .forallT adaptation body =>
      .trans leftTyping (.forallT adaptation body)

/-- Right-associating a checked inclusion spine preserves its endpoints. -/
def compose_hasType {scope : Sig} {context : Ctx scope}
    {left right : LeCo scope} {source middle target : Ty scope}
    (leftTyping : HasType context left source middle)
    (rightTyping : HasType context right middle target) :
    HasType context (compose left right) source target :=
  match leftTyping with
  | .var binding => finish_hasType (.var binding) rightTyping
  | .refl _ => rightTyping
  | .trans first rest => .trans first (compose_hasType rest rightTyping)
  | .top sourceType => finish_hasType (.top sourceType) rightTyping
  | .bot targetType => finish_hasType (.bot targetType) rightTyping
  | .eqToLe equality => finish_hasType (.eqToLe equality) rightTyping
  | .arr domain codomain => finish_hasType (.arr domain codomain) rightTyping
  | .existsT adaptation payload =>
      finish_hasType (.existsT adaptation payload) rightTyping
  | .forallT adaptation body =>
      finish_hasType (.forallT adaptation body) rightTyping

/-- Inclusion normalization preserves both declarative endpoints. -/
def normalize_hasType {scope : Sig} {context : Ctx scope}
    {evidence : LeCo scope} {source target : Ty scope}
    (typing : HasType context evidence source target) :
    HasType context evidence.normalize source target :=
  match typing with
  | .var binding => .var binding
  | .refl type => .refl type
  | .trans first second =>
      compose_hasType (normalize_hasType first) (normalize_hasType second)
  | .top sourceType => .top sourceType
  | .bot targetType => .bot targetType
  | .eqToLe equality => .eqToLe (EqCo.normalize_hasType equality)
  | .arr domain codomain =>
      .arr (normalize_hasType domain) (normalize_hasType codomain)
  | .existsT adaptation payload =>
      .existsT adaptation (normalize_hasType payload)
  | .forallT adaptation body =>
      .forallT adaptation (normalize_hasType body)

/-- The independent checker accepts normalized inclusion evidence at the
same endpoints. -/
theorem synthLe_normalize {scope : Sig} {context : Ctx scope}
    {evidence : LeCo scope} {source target : Ty scope}
    (typing : HasType context evidence source target) :
    synthLe context evidence.normalize = some (source, target) :=
  synthLe_complete (normalize_hasType typing)

/-- On well-typed inclusion evidence, normalization preserves the checker's
complete synthesized result. -/
theorem synthLe_normalize_eq {scope : Sig} {context : Ctx scope}
    {evidence : LeCo scope} {source target : Ty scope}
    (typing : HasType context evidence source target) :
    synthLe context evidence.normalize = synthLe context evidence := by
  rw [synthLe_normalize typing, synthLe_complete typing]

end LeCo

end FCsub
