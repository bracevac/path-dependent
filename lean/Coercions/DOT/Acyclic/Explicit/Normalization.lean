import Coercions.DOT.Acyclic.Explicit.Typing

/-!
# Recursive certificate normalization

The normalizer removes reflexive links from every equality and inclusion
transitivity spine, right-associates the remaining links, and recursively
normalizes all compound evidence, exposure recipes, and context morphisms.
`lower h` and `upper h` remain atoms, so a bad-bounds path through one reusable
handle stays visible.
-/

namespace DotFC.Explicit

namespace EqCo

/-- Append an equality atom to a right spine, deleting a reflexive right
endpoint. -/
def finish {s : Sig} (left right : EqCo s) : EqCo s :=
  match right with
  | .refl _ => left
  | right => .trans left right

/-- Compose two normalized equality spines into one right-associated spine. -/
def compose {s : Sig} (left right : EqCo s) : EqCo s :=
  match left with
  | .refl _ => right
  | .trans first rest => .trans first (compose rest right)
  | left => finish left right

end EqCo

namespace LeCo

/-- Append an atom to a right spine, deleting a reflexive right endpoint. -/
def finish {s : Sig} (left right : LeCo s) : LeCo s :=
  match right with
  | .refl _ => left
  | right => .trans left right

/-- Compose two already normalized spines.  Recursing down the left spine
makes the result right-associated. -/
def compose {s : Sig} (left right : LeCo s) : LeCo s :=
  match left with
  | .refl _ => right
  | .trans first rest => .trans first (compose rest right)
  | left => finish left right

end LeCo

mutual

/-- Recursively normalize symmetric equality evidence. -/
def EqCo.normalize {s : Sig} : EqCo s → EqCo s
  | .var index => .var index
  | .refl type => .refl type
  | .symm evidence => .symm evidence.normalize
  | .trans first second => EqCo.compose first.normalize second.normalize

/-- Recursively normalize directed inclusion evidence. -/
def LeCo.normalize {s : Sig} : LeCo s → LeCo s
  | .var index => .var index
  | .refl type => .refl type
  | .trans first second => LeCo.compose first.normalize second.normalize
  | .top source => .top source
  | .bot target => .bot target
  | .eqToLe equality => .eqToLe equality.normalize
  | .member label lower upper =>
      .member label lower.normalize upper.normalize
  | .all domain view codomain =>
      .all domain.normalize view.normalize codomain.normalize
  | .lower handle => .lower handle
  | .upper handle => .upper handle
  | .letHandle exposure body =>
      .letHandle exposure.normalize body.normalize

/-- Recursively normalize the inclusion carried by an exposure recipe. -/
def Exposure.normalize {s : Sig} : Exposure s → Exposure s
  | .view path label lower upper inclusion =>
      .view path label lower upper inclusion.normalize

/-- Recursively normalize a function-context adjustment. -/
def CtxMor.normalize {s : Sig} : CtxMor s → CtxMor s
  | .refl => .refl
  | .function domain => .function domain.normalize

end

/-! ## Executable normal-form graph -/

namespace EqCo

/-- True exactly for equality syntax that can head a canonical transitivity
spine. -/
def isAtom {s : Sig} : EqCo s → Bool
  | .refl _ | .trans _ _ => false
  | _ => true

/-- True exactly for reflexive equality syntax. -/
def isRefl {s : Sig} : EqCo s → Bool
  | .refl _ => true
  | _ => false

/-- Executable structural normal-form predicate for equality evidence. -/
def reduced {s : Sig} : EqCo s → Bool
  | .var _ => true
  | .refl _ => true
  | .symm evidence => evidence.reduced
  | .trans first rest =>
      first.isAtom && rest.isRefl.not &&
        first.reduced && rest.reduced

end EqCo

namespace LeCo

/-- True exactly for inclusion syntax that can head a canonical transitivity
spine. -/
def isAtom {s : Sig} : LeCo s → Bool
  | .refl _ | .trans _ _ => false
  | _ => true

/-- True exactly for reflexive inclusion syntax. -/
def isRefl {s : Sig} : LeCo s → Bool
  | .refl _ => true
  | _ => false

end LeCo

mutual

/-- Executable structural normal-form predicate for inclusion evidence. -/
def LeCo.reduced {s : Sig} : LeCo s → Bool
  | .var _ => true
  | .refl _ => true
  | .trans first rest =>
      first.isAtom && rest.isRefl.not &&
        first.reduced && rest.reduced
  | .top _ => true
  | .bot _ => true
  | .eqToLe equality => equality.reduced
  | .member _ lower upper => lower.reduced && upper.reduced
  | .all domain view codomain =>
      domain.reduced && view.reduced && codomain.reduced
  | .lower _ => true
  | .upper _ => true
  | .letHandle exposure body => exposure.reduced && body.reduced

/-- Exposure recipes are reduced when their view coercion is reduced. -/
def Exposure.reduced {s : Sig} : Exposure s → Bool
  | .view _ _ _ _ inclusion => inclusion.reduced

/-- Context morphisms are reduced when their domain coercion is reduced. -/
def CtxMor.reduced {s : Sig} : CtxMor s → Bool
  | .refl => true
  | .function domain => domain.reduced

end

namespace LeCo

/-- A small measure specialized to the transitivity spine. -/
def spineRank {s : Sig} : LeCo s → Nat
  | .trans left right => spineRank left + spineRank right + 1
  | _ => 1

/-- The corresponding measure on a checked transitivity spine. -/
def checkedSpineRank {s : Sig} {context : Ctx s} {evidence : LeCo s}
    {source target : Source.Ty s} : HasType context evidence source target → Nat
  | .trans first second => checkedSpineRank first + checkedSpineRank second + 1
  | _ => 1

@[simp]
theorem compose_refl_left {s : Sig} (type : Source.Ty s) (right : LeCo s) :
    compose (.refl type) right = right := rfl

@[simp]
theorem compose_refl_right {s : Sig} (left : LeCo s) (type : Source.Ty s)
    (notRefl : ∀ actual, left ≠ .refl actual)
    (notTrans : ∀ first rest, left ≠ .trans first rest) :
    compose left (.refl type) = left := by
  cases left <;> simp_all [compose, finish]

@[simp]
theorem normalize_refl {s : Sig} (type : Source.Ty s) :
    normalize (.refl type) = .refl type := rfl

@[simp]
theorem normalize_lower {s : Sig} (handle : BVar s .member) :
    normalize (.lower handle) = .lower handle := rfl

@[simp]
theorem normalize_upper {s : Sig} (handle : BVar s .member) :
    normalize (.upper handle) = .upper handle := rfl

/-- The characteristic bad-bounds path is irreducible: normalization never
collapses locally assumed lower and upper evidence into an opaque axiom. -/
@[simp]
theorem normalize_lower_upper {s : Sig} (handle : BVar s .member) :
    normalize (.trans (.lower handle) (.upper handle)) =
      .trans (.lower handle) (.upper handle) := rfl

end LeCo

/-! ## Reducedness and fixed points -/

namespace EqCo

/-- Reflexivity of smart composition is completely determined by its two
inputs. -/
@[simp]
theorem isRefl_compose {s : Sig} (left right : EqCo s) :
    (compose left right).isRefl = (left.isRefl && right.isRefl) := by
  cases left <;> cases right <;> rfl

private theorem reduced_finish {s : Sig} (left right : EqCo s)
    (atom : left.isAtom = true) (leftReduced : left.reduced = true)
    (rightReduced : right.reduced = true) :
    (finish left right).reduced = true := by
  cases right <;> simp_all [finish, reduced, isRefl]

/-- Smart composition is closed over the executable equality normal-form
graph. -/
def reduced_compose {s : Sig} (left right : EqCo s)
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
      have firstAtom := parts.1.1.1
      have restNotRefl := parts.1.1.2
      have firstReduced := parts.1.2
      have restReduced := parts.2
      have tailReduced := reduced_compose rest right restReduced rightReduced
      simp only [compose, reduced, Bool.and_eq_true]
      refine ⟨⟨⟨firstAtom, ?_⟩, firstReduced⟩, tailReduced⟩
      rw [isRefl_compose]
      have restFalse : rest.isRefl = false := by
        simpa only [Bool.not_eq_true'] using restNotRefl
      simp [restFalse]

/-- Every equality certificate normalizes into the executable normal-form
graph. -/
def reduced_normalize {s : Sig} (evidence : EqCo s) :
    evidence.normalize.reduced = true :=
  match evidence with
  | .var _ => rfl
  | .refl _ => rfl
  | .symm evidence => by
      simpa [normalize, reduced] using reduced_normalize evidence
  | .trans first second =>
      reduced_compose first.normalize second.normalize
        (reduced_normalize first) (reduced_normalize second)

private theorem compose_eq_trans {s : Sig} (left right : EqCo s)
    (atom : left.isAtom = true) (rightNotRefl : right.isRefl.not = true) :
    compose left right = .trans left right := by
  cases left <;> cases right <;> simp_all [compose, finish, isAtom, isRefl]

/-- The executable graph characterizes fixed points of equality
normalization. -/
def normalize_eq_self_of_reduced {s : Sig} (evidence : EqCo s)
    (isReduced : evidence.reduced = true) :
    evidence.normalize = evidence :=
  match evidence with
  | .var _ => rfl
  | .refl _ => rfl
  | .symm evidence => by
      have innerReduced := isReduced
      simp only [reduced] at innerReduced
      simp [normalize, normalize_eq_self_of_reduced evidence innerReduced]
  | .trans first rest => by
      have parts : ((first.isAtom = true ∧ rest.isRefl.not = true) ∧
          first.reduced = true) ∧ rest.reduced = true := by
        simpa only [reduced, Bool.and_eq_true] using isReduced
      have firstAtom := parts.1.1.1
      have restNotRefl := parts.1.1.2
      have firstReduced := parts.1.2
      have restReduced := parts.2
      simp only [normalize]
      rw [normalize_eq_self_of_reduced first firstReduced,
        normalize_eq_self_of_reduced rest restReduced]
      exact compose_eq_trans first rest firstAtom restNotRefl

/-- Equality normalization is idempotent. -/
theorem normalize_idempotent {s : Sig} (evidence : EqCo s) :
    evidence.normalize.normalize = evidence.normalize :=
  normalize_eq_self_of_reduced evidence.normalize (reduced_normalize evidence)

end EqCo

namespace LeCo

/-- Reflexivity of smart composition is completely determined by its two
inputs. -/
@[simp]
theorem isRefl_compose {s : Sig} (left right : LeCo s) :
    (compose left right).isRefl = (left.isRefl && right.isRefl) := by
  cases left <;> cases right <;> rfl

private theorem reduced_finish {s : Sig} (left right : LeCo s)
    (atom : left.isAtom = true) (leftReduced : left.reduced = true)
    (rightReduced : right.reduced = true) :
    (finish left right).reduced = true := by
  cases right <;> simp_all [finish, reduced, isRefl]

/-- Smart composition is closed over the executable inclusion normal-form
graph. -/
def reduced_compose {s : Sig} (left right : LeCo s)
    (leftReduced : left.reduced = true)
    (rightReduced : right.reduced = true) :
    (compose left right).reduced = true :=
  match left with
  | .refl _ => by simpa [compose] using rightReduced
  | .trans first rest => by
      have parts : ((first.isAtom = true ∧ rest.isRefl.not = true) ∧
          first.reduced = true) ∧ rest.reduced = true := by
        simpa only [reduced, Bool.and_eq_true] using leftReduced
      have firstAtom := parts.1.1.1
      have restNotRefl := parts.1.1.2
      have firstReduced := parts.1.2
      have restReduced := parts.2
      have tailReduced := reduced_compose rest right restReduced rightReduced
      simp only [compose, reduced, Bool.and_eq_true]
      refine ⟨⟨⟨firstAtom, ?_⟩, firstReduced⟩, tailReduced⟩
      rw [isRefl_compose]
      have restFalse : rest.isRefl = false := by
        simpa only [Bool.not_eq_true'] using restNotRefl
      simp [restFalse]
  | .var index =>
      reduced_finish (.var index) right rfl leftReduced rightReduced
  | .top source =>
      reduced_finish (.top source) right rfl leftReduced rightReduced
  | .bot target =>
      reduced_finish (.bot target) right rfl leftReduced rightReduced
  | .eqToLe equality =>
      reduced_finish (.eqToLe equality) right rfl leftReduced rightReduced
  | .member label lowerEvidence upperEvidence =>
      reduced_finish (.member label lowerEvidence upperEvidence) right rfl
        leftReduced rightReduced
  | .all domain view codomain =>
      reduced_finish (.all domain view codomain) right rfl
        leftReduced rightReduced
  | .lower handle =>
      reduced_finish (.lower handle) right rfl leftReduced rightReduced
  | .upper handle =>
      reduced_finish (.upper handle) right rfl leftReduced rightReduced
  | .letHandle exposure body =>
      reduced_finish (.letHandle exposure body) right rfl
        leftReduced rightReduced

private theorem compose_eq_trans {s : Sig} (left right : LeCo s)
    (atom : left.isAtom = true) (rightNotRefl : right.isRefl.not = true) :
    compose left right = .trans left right := by
  cases left <;> cases right <;> simp_all [compose, finish, isAtom, isRefl]

end LeCo

mutual

/-- Every inclusion certificate normalizes into the executable normal-form
graph, recursively including compound certificates. -/
def LeCo.reduced_normalize {s : Sig} (evidence : LeCo s) :
    evidence.normalize.reduced = true :=
  match evidence with
  | .var _ => rfl
  | .refl _ => rfl
  | .trans first second =>
      LeCo.reduced_compose first.normalize second.normalize
        (LeCo.reduced_normalize first) (LeCo.reduced_normalize second)
  | .top _ => rfl
  | .bot _ => rfl
  | .eqToLe equality => EqCo.reduced_normalize equality
  | .member _ lowerEvidence upperEvidence => by
      simp [LeCo.normalize, LeCo.reduced,
        LeCo.reduced_normalize lowerEvidence,
        LeCo.reduced_normalize upperEvidence]
  | .all domain view codomain => by
      simp [LeCo.normalize, LeCo.reduced,
        LeCo.reduced_normalize domain,
        CtxMor.reduced_normalize view,
        LeCo.reduced_normalize codomain]
  | .lower _ => rfl
  | .upper _ => rfl
  | .letHandle exposure body => by
      simp [LeCo.normalize, LeCo.reduced,
        Exposure.reduced_normalize exposure,
        LeCo.reduced_normalize body]

/-- Every normalized exposure has a recursively reduced view coercion. -/
def Exposure.reduced_normalize {s : Sig} (exposure : Exposure s) :
    exposure.normalize.reduced = true :=
  match exposure with
  | .view _ _ _ _ inclusion => LeCo.reduced_normalize inclusion

/-- Every normalized context morphism has a recursively reduced domain
coercion. -/
def CtxMor.reduced_normalize {s : Sig} (morphism : CtxMor s) :
    morphism.normalize.reduced = true :=
  match morphism with
  | .refl => rfl
  | .function domain => LeCo.reduced_normalize domain

end

mutual

/-- The executable graph characterizes fixed points of recursive inclusion
normalization. -/
def LeCo.normalize_eq_self_of_reduced {s : Sig} (evidence : LeCo s)
    (isReduced : evidence.reduced = true) :
    evidence.normalize = evidence :=
  match evidence with
  | .var _ => rfl
  | .refl _ => rfl
  | .trans first rest => by
      have parts : ((first.isAtom = true ∧ rest.isRefl.not = true) ∧
          first.reduced = true) ∧ rest.reduced = true := by
        simpa only [LeCo.reduced, Bool.and_eq_true] using isReduced
      have firstAtom := parts.1.1.1
      have restNotRefl := parts.1.1.2
      have firstReduced := parts.1.2
      have restReduced := parts.2
      simp only [LeCo.normalize]
      rw [LeCo.normalize_eq_self_of_reduced first firstReduced,
        LeCo.normalize_eq_self_of_reduced rest restReduced]
      exact LeCo.compose_eq_trans first rest firstAtom restNotRefl
  | .top _ => rfl
  | .bot _ => rfl
  | .eqToLe equality => by
      have equalityReduced : equality.reduced = true := by
        simpa only [LeCo.reduced] using isReduced
      simp [LeCo.normalize,
        EqCo.normalize_eq_self_of_reduced equality equalityReduced]
  | .member label lowerEvidence upperEvidence => by
      have parts : lowerEvidence.reduced = true ∧
          upperEvidence.reduced = true := by
        simpa only [LeCo.reduced, Bool.and_eq_true] using isReduced
      simp [LeCo.normalize,
        LeCo.normalize_eq_self_of_reduced lowerEvidence parts.1,
        LeCo.normalize_eq_self_of_reduced upperEvidence parts.2]
  | .all domain view codomain => by
      have parts : (domain.reduced = true ∧ view.reduced = true) ∧
          codomain.reduced = true := by
        simpa only [LeCo.reduced, Bool.and_eq_true] using isReduced
      simp [LeCo.normalize,
        LeCo.normalize_eq_self_of_reduced domain parts.1.1,
        CtxMor.normalize_eq_self_of_reduced view parts.1.2,
        LeCo.normalize_eq_self_of_reduced codomain parts.2]
  | .lower _ => rfl
  | .upper _ => rfl
  | .letHandle exposure body => by
      have parts : exposure.reduced = true ∧ body.reduced = true := by
        simpa only [LeCo.reduced, Bool.and_eq_true] using isReduced
      simp [LeCo.normalize,
        Exposure.normalize_eq_self_of_reduced exposure parts.1,
        LeCo.normalize_eq_self_of_reduced body parts.2]

/-- Reduced exposure recipes are fixed points. -/
def Exposure.normalize_eq_self_of_reduced {s : Sig}
    (exposure : Exposure s) (isReduced : exposure.reduced = true) :
    exposure.normalize = exposure :=
  match exposure with
  | .view path label lower upper inclusion => by
      have inclusionReduced : inclusion.reduced = true := by
        simpa only [Exposure.reduced] using isReduced
      simp [Exposure.normalize,
        LeCo.normalize_eq_self_of_reduced inclusion inclusionReduced]

/-- Reduced context morphisms are fixed points. -/
def CtxMor.normalize_eq_self_of_reduced {s : Sig} (morphism : CtxMor s)
    (isReduced : morphism.reduced = true) :
    morphism.normalize = morphism :=
  match morphism with
  | .refl => rfl
  | .function domain => by
      have domainReduced : domain.reduced = true := by
        simpa only [CtxMor.reduced] using isReduced
      simp [CtxMor.normalize,
        LeCo.normalize_eq_self_of_reduced domain domainReduced]

end


/-- Inclusion normalization is idempotent. -/
theorem LeCo.normalize_idempotent {s : Sig} (evidence : LeCo s) :
    evidence.normalize.normalize = evidence.normalize :=
  LeCo.normalize_eq_self_of_reduced evidence.normalize
    (LeCo.reduced_normalize evidence)

/-- Exposure normalization is idempotent. -/
theorem Exposure.normalize_idempotent {s : Sig} (exposure : Exposure s) :
    exposure.normalize.normalize = exposure.normalize :=
  Exposure.normalize_eq_self_of_reduced exposure.normalize
    (Exposure.reduced_normalize exposure)

/-- Context-morphism normalization is idempotent. -/
theorem CtxMor.normalize_idempotent {s : Sig} (morphism : CtxMor s) :
    morphism.normalize.normalize = morphism.normalize :=
  CtxMor.normalize_eq_self_of_reduced morphism.normalize
    (CtxMor.reduced_normalize morphism)

/-! ## Endpoint preservation -/

namespace EqCo

/-- Appending one checked equality atom preserves the endpoints. -/
def finishHasType {s : Sig} {context : Ctx s}
    {left right : EqCo s} {source middle target : Source.Ty s}
    (leftTyping : HasType context left source middle)
    (rightTyping : HasType context right middle target) :
    HasType context (finish left right) source target := by
  cases rightTyping with
  | refl => exact leftTyping
  | var index => exact .trans leftTyping (.var index)
  | symm evidence => exact .trans leftTyping (.symm evidence)
  | trans first second => exact .trans leftTyping (.trans first second)

/-- Smart equality-spine composition preserves structurally synthesized
endpoints. -/
def composeHasType {s : Sig} {context : Ctx s}
    {left right : EqCo s} {source middle target : Source.Ty s}
    (leftTyping : HasType context left source middle)
    (rightTyping : HasType context right middle target) :
    HasType context (compose left right) source target :=
  match left, leftTyping with
  | .refl _, .refl _ => rightTyping
  | .trans _ _, .trans first rest =>
      .trans first (composeHasType rest rightTyping)
  | .var _, .var index => finishHasType (.var index) rightTyping
  | .symm _, .symm evidence => finishHasType (.symm evidence) rightTyping

/-- Recursive equality normalization preserves both endpoints. -/
def normalizeHasType {s : Sig} {context : Ctx s}
    {evidence : EqCo s} {source target : Source.Ty s}
    (typing : HasType context evidence source target) :
    HasType context evidence.normalize source target :=
  match evidence, typing with
  | .var _, .var index => .var index
  | .refl _, .refl type => .refl type
  | .symm _, .symm inner => .symm (normalizeHasType inner)
  | .trans _ _, .trans first second =>
      composeHasType (normalizeHasType first) (normalizeHasType second)

end EqCo

namespace LeCo

/-- Appending one checked atom preserves the endpoints. -/
def finishHasType {s : Sig} {context : Ctx s}
    {left right : LeCo s} {source middle target : Source.Ty s}
    (leftTyping : HasType context left source middle)
    (rightTyping : HasType context right middle target) :
    HasType context (finish left right) source target := by
  cases rightTyping with
  | refl => exact leftTyping
  | var index => exact .trans leftTyping (.var index)
  | trans first second => exact .trans leftTyping (.trans first second)
  | top source => exact .trans leftTyping (.top middle)
  | bot target => exact .trans leftTyping (.bot target)
  | eqToLe equality => exact .trans leftTyping (.eqToLe equality)
  | member lower upper => exact .trans leftTyping (.member lower upper)
  | all domain view codomain => exact .trans leftTyping (.all domain view codomain)
  | lower => exact .trans leftTyping .lower
  | upper => exact .trans leftTyping .upper
  | letHandle exposure body => exact .trans leftTyping (.letHandle exposure body)

/-- Smart spine composition preserves structurally synthesized endpoints. -/
def composeHasType {s : Sig} {context : Ctx s}
    {left right : LeCo s} {source middle target : Source.Ty s}
    (leftTyping : HasType context left source middle)
    (rightTyping : HasType context right middle target) :
    HasType context (compose left right) source target :=
  match left, leftTyping with
  | .refl _, .refl _ => rightTyping
  | .trans _ _, .trans first rest =>
      .trans first (composeHasType rest rightTyping)
  | .var _, .var index => finishHasType (.var index) rightTyping
  | .top _, .top source => finishHasType (.top source) rightTyping
  | .bot _, .bot _ => finishHasType (.bot middle) rightTyping
  | .eqToLe _, .eqToLe equality => finishHasType (.eqToLe equality) rightTyping
  | .member _ _ _, .member lowerTyping upperTyping =>
      finishHasType (.member lowerTyping upperTyping) rightTyping
  | .all _ _ _, .all domainTyping viewTyping codomainTyping =>
      finishHasType (.all domainTyping viewTyping codomainTyping) rightTyping
  | LeCo.lower .., HasType.lower => finishHasType .lower rightTyping
  | LeCo.upper .., HasType.upper => finishHasType .upper rightTyping
  | .letHandle _ _, .letHandle exposure body =>
      finishHasType (.letHandle exposure body) rightTyping

end LeCo

mutual

/-- Recursive inclusion normalization preserves both endpoints and therefore
remains accepted by the independent structural checker. -/
def LeCo.normalizeHasType {s : Sig} {context : Ctx s}
    {evidence : LeCo s} {source target : Source.Ty s}
    (typing : LeCo.HasType context evidence source target) :
    LeCo.HasType context evidence.normalize source target :=
  match evidence, typing with
  | .var _, .var index => .var index
  | .refl _, .refl type => .refl type
  | .trans _ _, .trans firstTyping secondTyping =>
      LeCo.composeHasType (LeCo.normalizeHasType firstTyping)
        (LeCo.normalizeHasType secondTyping)
  | .top _, .top source => .top source
  | .bot _, .bot target => .bot target
  | .eqToLe _, .eqToLe equalityTyping =>
      .eqToLe (EqCo.normalizeHasType equalityTyping)
  | .member _ _ _, .member lowerTyping upperTyping =>
      .member (LeCo.normalizeHasType lowerTyping)
        (LeCo.normalizeHasType upperTyping)
  | .all _ _ _, .all domainTyping viewTyping codomainTyping =>
      .all (LeCo.normalizeHasType domainTyping)
        (CtxMor.normalizeHasType viewTyping)
        (LeCo.normalizeHasType codomainTyping)
  | LeCo.lower .., LeCo.HasType.lower => .lower
  | LeCo.upper .., LeCo.HasType.upper => .upper
  | .letHandle _ _, .letHandle exposureTyping bodyTyping =>
      .letHandle (Exposure.normalizeHasType exposureTyping)
        (LeCo.normalizeHasType bodyTyping)

/-- Recursive exposure normalization preserves the synthesized member fact. -/
def Exposure.normalizeHasType {s : Sig} {context : Ctx s}
    {exposure : Exposure s} {member : MemberSpec s}
    (typing : Exposure.HasType context exposure member) :
    Exposure.HasType context exposure.normalize member :=
  match exposure, typing with
  | .view _ _ _ _ _, .view inclusionTyping =>
      .view (LeCo.normalizeHasType inclusionTyping)

/-- Recursive context-morphism normalization preserves both complete endpoint
contexts. -/
def CtxMor.normalizeHasType {s : Sig} {actual view : Ctx s}
    {morphism : CtxMor s}
    (typing : CtxMor.HasType actual view morphism) :
    CtxMor.HasType actual view morphism.normalize :=
  match morphism, typing with
  | .refl, .refl => .refl
  | .function _, .function domainTyping =>
      .function (LeCo.normalizeHasType domainTyping)

end

end DotFC.Explicit
