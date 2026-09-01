import Coercions.ManySortedFC.Evidence

/-!
# Access-view semantics for capture separation

This module gives the M13 capture relations a small, independent semantics.
Each capability is observed at one of three access levels:

```
absent < readOnly < writable
```

Capture union is pointwise join.  A read-only capture view preserves which
capabilities are present while lowering every present access to `readOnly`.
The semantics distinguishes separation (read-only overlap is allowed) from
disjointness (no overlap is allowed).
-/

namespace ManySortedFC

/-- The access available for one capability through a capture expression. -/
inductive AccessView : Type where
  | absent
  | readOnly
  | writable
deriving DecidableEq, Repr

namespace AccessView

/-- The access preorder `absent < readOnly < writable`. -/
def LE : AccessView -> AccessView -> Prop
  | .absent, _ => True
  | .readOnly, .readOnly => True
  | .readOnly, .writable => True
  | .writable, .writable => True
  | _, _ => False

/-- Pointwise union of access views. -/
def join : AccessView -> AccessView -> AccessView
  | .absent, right => right
  | left, .absent => left
  | .writable, _ => .writable
  | _, .writable => .writable
  | .readOnly, .readOnly => .readOnly

/-- Restrict a present capability to read-only access. -/
def restrictReadOnly : AccessView -> AccessView
  | .absent => .absent
  | .readOnly => .readOnly
  | .writable => .readOnly

@[simp]
theorem le_refl (view : AccessView) : LE view view := by
  cases view <;> trivial

theorem le_trans {first middle last : AccessView}
    (firstMiddle : LE first middle) (middleLast : LE middle last) :
    LE first last := by
  cases first <;> cases middle <;> cases last <;>
    simp_all [LE]

@[simp]
theorem absent_le (view : AccessView) : LE .absent view := by
  trivial

@[simp]
theorem le_writable (view : AccessView) : LE view .writable := by
  cases view <;> trivial

@[simp]
theorem join_absent_left (view : AccessView) :
    join .absent view = view := rfl

@[simp]
theorem join_absent_right (view : AccessView) :
    join view .absent = view := by
  cases view <;> rfl

theorem le_join_left (left right : AccessView) : LE left (join left right) := by
  cases left <;> cases right <;> trivial

theorem le_join_right (left right : AccessView) :
    LE right (join left right) := by
  cases left <;> cases right <;> trivial

theorem join_le {left right upper : AccessView}
    (leftUpper : LE left upper) (rightUpper : LE right upper) :
    LE (join left right) upper := by
  cases left <;> cases right <;> cases upper <;>
    simp_all [LE, join]

theorem join_comm (left right : AccessView) :
    join left right = join right left := by
  cases left <;> cases right <;> rfl

theorem join_assoc (first second third : AccessView) :
    join (join first second) third = join first (join second third) := by
  cases first <;> cases second <;> cases third <;> rfl

theorem restrict_le (view : AccessView) :
    LE (restrictReadOnly view) view := by
  cases view <;> trivial

theorem restrict_mono {left right : AccessView} (ordering : LE left right) :
    LE (restrictReadOnly left) (restrictReadOnly right) := by
  cases left <;> cases right <;> simp_all [LE, restrictReadOnly]

theorem restrict_le_readOnly (view : AccessView) :
    LE (restrictReadOnly view) .readOnly := by
  cases view <;> trivial

theorem restrict_join (left right : AccessView) :
    restrictReadOnly (join left right) =
      join (restrictReadOnly left) (restrictReadOnly right) := by
  cases left <;> cases right <;> rfl

/-- Two capabilities are disjoint at one observation point when at least one
side is absent. -/
def Disjoint (left right : AccessView) : Prop :=
  left = .absent ∨ right = .absent

/-- Two capabilities are separate at one observation point when at least one
side is absent, or when both overlapping views are at most read-only. -/
def Separate (left right : AccessView) : Prop :=
  left = .absent ∨ right = .absent ∨
    (LE left .readOnly ∧ LE right .readOnly)

theorem disjoint_symm {left right : AccessView} :
    Disjoint left right -> Disjoint right left := by
  intro disjoint
  rcases disjoint with leftAbsent | rightAbsent
  · exact Or.inr leftAbsent
  · exact Or.inl rightAbsent

theorem disjoint_empty (view : AccessView) : Disjoint .absent view :=
  Or.inl rfl

theorem disjoint_join {left right other : AccessView}
    (leftOther : Disjoint left other) (rightOther : Disjoint right other) :
    Disjoint (join left right) other := by
  cases left <;> cases right <;> cases other <;>
    simp_all [Disjoint, join]

theorem separate_symm {left right : AccessView} :
    Separate left right -> Separate right left := by
  intro separate
  rcases separate with leftAbsent | rightAbsent | readOnlyOverlap
  · exact Or.inr (Or.inl leftAbsent)
  · exact Or.inl rightAbsent
  · exact Or.inr (Or.inr ⟨readOnlyOverlap.2, readOnlyOverlap.1⟩)

theorem separate_empty (view : AccessView) : Separate .absent view :=
  Or.inl rfl

theorem separate_readOnly {left right : AccessView}
    (leftReadOnly : LE left .readOnly)
    (rightReadOnly : LE right .readOnly) : Separate left right :=
  Or.inr (Or.inr ⟨leftReadOnly, rightReadOnly⟩)

theorem separate_of_disjoint {left right : AccessView}
    (disjoint : Disjoint left right) : Separate left right := by
  rcases disjoint with leftAbsent | rightAbsent
  · exact Or.inl leftAbsent
  · exact Or.inr (Or.inl rightAbsent)

theorem separate_join {left right other : AccessView}
    (leftOther : Separate left other) (rightOther : Separate right other) :
    Separate (join left right) other := by
  cases left <;> cases right <;> cases other <;>
    simp_all [Separate, LE, join]

theorem separate_mono {smallLeft largeLeft smallRight largeRight : AccessView}
    (leftOrder : LE smallLeft largeLeft)
    (rightOrder : LE smallRight largeRight)
    (largeSeparate : Separate largeLeft largeRight) :
    Separate smallLeft smallRight := by
  cases smallLeft <;> cases largeLeft <;>
    cases smallRight <;> cases largeRight <;>
    simp_all [Separate, LE]

end AccessView

/-- A valuation gives each term capability and abstract capture symbol an
access view at every semantic capability.  The semantic capability type is a
parameter so the model can also observe capabilities not named by term
variables in the current scope. -/
structure AccessValuation (scope : Sig) (Capability : Type) where
  term : BVar scope .term -> Capability -> AccessView
  captureSymbol : BVar scope (.symbol .capture) -> Capability -> AccessView

namespace Capture

/-- Pointwise access-view interpretation of a capture expression. -/
def access {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) :
    Capture scope -> Capability -> AccessView
  | .empty, _ => .absent
  | .union left right, capability =>
      AccessView.join (left.access valuation capability)
        (right.access valuation capability)
  | .readOnly capture, capability =>
      AccessView.restrictReadOnly (capture.access valuation capability)
  | .singleton term, capability => valuation.term term capability
  | .cvar name, capability => valuation.captureSymbol name capability

end Capture

namespace SeparationSemantics

/-- Capture equality is pointwise equality of access views. -/
def Equivalent {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability)
    (left right : Capture scope) : Prop :=
  ∀ capability, left.access valuation capability = right.access valuation capability

/-- Capture inclusion is the pointwise access preorder. -/
def Subcapture {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability)
    (lower upper : Capture scope) : Prop :=
  ∀ capability, AccessView.LE (lower.access valuation capability)
    (upper.access valuation capability)

/-- Writable mode places no restriction on a capture.  Read-only mode says
that every capability is observed at no more than read-only access. -/
def HasMode {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) :
    CaptureMode -> Capture scope -> Prop
  | .writable, _ => True
  | .readOnly, capture => ∀ capability,
      AccessView.LE (capture.access valuation capability) .readOnly

/-- Disjoint captures never expose the same semantic capability. -/
def Disjoint {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability)
    (left right : Capture scope) : Prop :=
  ∀ capability, AccessView.Disjoint (left.access valuation capability)
    (right.access valuation capability)

/-- Separate captures may overlap only through read-only access on both
sides. -/
def Separate {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability)
    (left right : Capture scope) : Prop :=
  ∀ capability, AccessView.Separate (left.access valuation capability)
    (right.access valuation capability)

theorem equivalent_refl {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) (capture : Capture scope) :
    Equivalent valuation capture capture := by
  intro capability
  rfl

theorem equivalent_symm {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability} {left right : Capture scope}
    (equivalent : Equivalent valuation left right) :
    Equivalent valuation right left := by
  intro capability
  exact (equivalent capability).symm

theorem equivalent_trans {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability}
    {first middle last : Capture scope}
    (firstMiddle : Equivalent valuation first middle)
    (middleLast : Equivalent valuation middle last) :
    Equivalent valuation first last := by
  intro capability
  exact (firstMiddle capability).trans (middleLast capability)

theorem equivalent_union {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability}
    {sourceLeft targetLeft sourceRight targetRight : Capture scope}
    (left : Equivalent valuation sourceLeft targetLeft)
    (right : Equivalent valuation sourceRight targetRight) :
    Equivalent valuation (.union sourceLeft sourceRight)
      (.union targetLeft targetRight) := by
  intro capability
  simp only [Capture.access]
  rw [left capability, right capability]

theorem equivalent_readOnly {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability}
    {left right : Capture scope} (equivalent : Equivalent valuation left right) :
    Equivalent valuation (.readOnly left) (.readOnly right) := by
  intro capability
  simp only [Capture.access]
  rw [equivalent capability]

theorem subcapture_refl {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) (capture : Capture scope) :
    Subcapture valuation capture capture := by
  intro capability
  exact AccessView.le_refl _

theorem subcapture_trans {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability}
    {first middle last : Capture scope}
    (firstMiddle : Subcapture valuation first middle)
    (middleLast : Subcapture valuation middle last) :
    Subcapture valuation first last := by
  intro capability
  exact AccessView.le_trans (firstMiddle capability) (middleLast capability)

theorem subcapture_of_equivalent {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability} {left right : Capture scope}
    (equivalent : Equivalent valuation left right) :
    Subcapture valuation left right := by
  intro capability
  rw [equivalent capability]
  exact AccessView.le_refl _

theorem empty_subcapture {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) (upper : Capture scope) :
    Subcapture valuation .empty upper := by
  intro capability
  exact AccessView.absent_le _

theorem union_left_subcapture {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) (left right : Capture scope) :
    Subcapture valuation left (.union left right) := by
  intro capability
  exact AccessView.le_join_left _ _

theorem union_right_subcapture {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) (left right : Capture scope) :
    Subcapture valuation right (.union left right) := by
  intro capability
  exact AccessView.le_join_right _ _

theorem union_elim_subcapture {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability}
    {left right upper : Capture scope}
    (leftUpper : Subcapture valuation left upper)
    (rightUpper : Subcapture valuation right upper) :
    Subcapture valuation (.union left right) upper := by
  intro capability
  exact AccessView.join_le (leftUpper capability) (rightUpper capability)

theorem readOnly_subcapture {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) (capture : Capture scope) :
    Subcapture valuation (.readOnly capture) capture := by
  intro capability
  exact AccessView.restrict_le _

theorem readOnly_mono {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability} {lower upper : Capture scope}
    (ordering : Subcapture valuation lower upper) :
    Subcapture valuation (.readOnly lower) (.readOnly upper) := by
  intro capability
  exact AccessView.restrict_mono (ordering capability)

theorem mode_writable {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) (capture : Capture scope) :
    HasMode valuation .writable capture := by
  trivial

theorem mode_empty {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) (mode : CaptureMode) :
    HasMode valuation mode (.empty : Capture scope) := by
  cases mode with
  | writable => trivial
  | readOnly =>
      intro capability
      exact AccessView.absent_le _

theorem mode_union {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability} {mode : CaptureMode}
    {left right : Capture scope}
    (leftMode : HasMode valuation mode left)
    (rightMode : HasMode valuation mode right) :
    HasMode valuation mode (.union left right) := by
  cases mode with
  | writable => trivial
  | readOnly =>
      intro capability
      exact AccessView.join_le (leftMode capability) (rightMode capability)

theorem mode_subcapture {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability} {mode : CaptureMode}
    {lower upper : Capture scope}
    (ordering : Subcapture valuation lower upper)
    (upperMode : HasMode valuation mode upper) :
    HasMode valuation mode lower := by
  cases mode with
  | writable => trivial
  | readOnly =>
      intro capability
      exact AccessView.le_trans (ordering capability) (upperMode capability)

theorem mode_readOnly {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) (capture : Capture scope) :
    HasMode valuation .readOnly (.readOnly capture) := by
  intro capability
  exact AccessView.restrict_le_readOnly _

theorem separate_symm {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability} {left right : Capture scope}
    (separate : Separate valuation left right) :
    Separate valuation right left := by
  intro capability
  exact AccessView.separate_symm (separate capability)

theorem separate_empty {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) (capture : Capture scope) :
    Separate valuation .empty capture := by
  intro capability
  exact AccessView.separate_empty _

theorem separate_union {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability}
    {left right other : Capture scope}
    (leftOther : Separate valuation left other)
    (rightOther : Separate valuation right other) :
    Separate valuation (.union left right) other := by
  intro capability
  exact AccessView.separate_join (leftOther capability) (rightOther capability)

theorem separate_readOnly {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability} {left right : Capture scope}
    (leftMode : HasMode valuation .readOnly left)
    (rightMode : HasMode valuation .readOnly right) :
    Separate valuation left right := by
  intro capability
  exact AccessView.separate_readOnly (leftMode capability)
    (rightMode capability)

theorem separate_subcapture {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability}
    {smallLeft largeLeft smallRight largeRight : Capture scope}
    (leftOrder : Subcapture valuation smallLeft largeLeft)
    (rightOrder : Subcapture valuation smallRight largeRight)
    (largeSeparate : Separate valuation largeLeft largeRight) :
    Separate valuation smallLeft smallRight := by
  intro capability
  exact AccessView.separate_mono (leftOrder capability)
    (rightOrder capability) (largeSeparate capability)

theorem separate_of_disjoint {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability} {left right : Capture scope}
    (disjoint : Disjoint valuation left right) :
    Separate valuation left right := by
  intro capability
  exact AccessView.separate_of_disjoint (disjoint capability)

theorem disjoint_symm {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability} {left right : Capture scope}
    (disjoint : Disjoint valuation left right) :
    Disjoint valuation right left := by
  intro capability
  exact AccessView.disjoint_symm (disjoint capability)

theorem disjoint_empty {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) (capture : Capture scope) :
    Disjoint valuation .empty capture := by
  intro capability
  exact AccessView.disjoint_empty _

theorem disjoint_union {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability}
    {left right other : Capture scope}
    (leftOther : Disjoint valuation left other)
    (rightOther : Disjoint valuation right other) :
    Disjoint valuation (.union left right) other := by
  intro capability
  exact AccessView.disjoint_join (leftOther capability) (rightOther capability)

theorem disjoint_equivalent_left {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability}
    {source target other : Capture scope}
    (equivalent : Equivalent valuation source target)
    (targetOther : Disjoint valuation target other) :
    Disjoint valuation source other := by
  intro capability
  rw [equivalent capability]
  exact targetOther capability

end SeparationSemantics

namespace Proposition

/-- The access-view interpretation of every proposition.  Type equality and
type inclusion are deliberately abstracted to `True`: this model exists to
separate the capture relations, while still supporting one induction over the
heterogeneous evidence judgment. -/
def AccessHolds {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) {relation : Relation} :
    Proposition relation scope -> Prop
  | .equality (.type _) (.type _) => True
  | .equality (.capture left) (.capture right) =>
      SeparationSemantics.Equivalent valuation left right
  | .inclusion (.type _) (.type _) => True
  | .inclusion (.capture lower) (.capture upper) =>
      SeparationSemantics.Subcapture valuation lower upper
  | .separate left right =>
      SeparationSemantics.Separate valuation left right
  | .disjoint left right =>
      SeparationSemantics.Disjoint valuation left right
  | @Proposition.mode _ selectedMode capture =>
      SeparationSemantics.HasMode valuation selectedMode capture

theorem accessHolds_equality_refl {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) {sort : StaticSort}
    (expression : StaticExpr sort scope) :
    AccessHolds valuation (.equality expression expression) := by
  cases expression with
  | type type => trivial
  | capture capture =>
      exact SeparationSemantics.equivalent_refl valuation capture

theorem accessHolds_equality_symm {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability} {sort : StaticSort}
    {left right : StaticExpr sort scope}
    (holds : AccessHolds valuation (.equality left right)) :
    AccessHolds valuation (.equality right left) := by
  cases left with
  | type left =>
      cases right
      trivial
  | capture left =>
      cases right with
      | capture right =>
          exact SeparationSemantics.equivalent_symm holds

theorem accessHolds_equality_trans {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability} {sort : StaticSort}
    {first middle last : StaticExpr sort scope}
    (firstMiddle : AccessHolds valuation (.equality first middle))
    (middleLast : AccessHolds valuation (.equality middle last)) :
    AccessHolds valuation (.equality first last) := by
  cases first with
  | type first =>
      cases middle
      cases last
      trivial
  | capture first =>
      cases middle with
      | capture middle =>
          cases last with
          | capture last =>
              exact SeparationSemantics.equivalent_trans firstMiddle
                middleLast

theorem accessHolds_inclusion_refl {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) {sort : StaticSort}
    (expression : StaticExpr sort scope) :
    AccessHolds valuation (.inclusion expression expression) := by
  cases expression with
  | type type => trivial
  | capture capture =>
      exact SeparationSemantics.subcapture_refl valuation capture

theorem accessHolds_inclusion_trans {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability} {sort : StaticSort}
    {first middle last : StaticExpr sort scope}
    (firstMiddle : AccessHolds valuation (.inclusion first middle))
    (middleLast : AccessHolds valuation (.inclusion middle last)) :
    AccessHolds valuation (.inclusion first last) := by
  cases first with
  | type first =>
      cases middle
      cases last
      trivial
  | capture first =>
      cases middle with
      | capture middle =>
          cases last with
          | capture last =>
              exact SeparationSemantics.subcapture_trans firstMiddle
                middleLast

theorem accessHolds_equality_to_inclusion {scope : Sig} {Capability : Type}
    {valuation : AccessValuation scope Capability} {sort : StaticSort}
    {left right : StaticExpr sort scope}
    (holds : AccessHolds valuation (.equality left right)) :
    AccessHolds valuation (.inclusion left right) := by
  cases left with
  | type left =>
      cases right
      trivial
  | capture left =>
      cases right with
      | capture right =>
          exact SeparationSemantics.subcapture_of_equivalent holds

end Proposition

namespace AccessValuation

/-- Semantic context validity.  Term bindings constrain the view assigned to
their singleton capability, and every ambient evidence binding must denote a
true proposition.  Requiring the latter explicitly prevents the soundness
theorem from treating arbitrary evidence assumptions as semantic facts. -/
def Respects {scope : Sig} {Capability : Type}
    (valuation : AccessValuation scope Capability) (context : Ctx scope) :
    Prop :=
  (∀ (index : BVar scope .term) (captures : Capture scope) (shape : Ty scope),
    context.lookup index = Binding.term (.capturing captures shape) ->
      SeparationSemantics.Subcapture valuation (.singleton index) captures) ∧
  (∀ (relation : Relation) (index : BVar scope (.evidence relation))
      (proposition : Proposition relation scope),
    context.lookup index = Binding.evidence proposition ->
      proposition.AccessHolds valuation)

end AccessValuation

namespace Evidence.Proves

/-- Every checked evidence derivation preserves the access-view semantics,
provided the ambient context itself is semantically valid. -/
theorem access_sound {scope : Sig} {context : Ctx scope}
    {relation : Relation} {evidence : Evidence relation scope}
    {proposition : Proposition relation scope} {Capability : Type}
    {valuation : AccessValuation scope Capability}
    (typing : Evidence.Proves context evidence proposition)
    (respects : valuation.Respects context) :
    proposition.AccessHolds valuation := by
  induction typing with
  | @var relation index proposition binding =>
      exact respects.2 relation index proposition binding
  | equalityRefl expression =>
      exact Proposition.accessHolds_equality_refl valuation expression
  | equalitySymm typing induction =>
      exact Proposition.accessHolds_equality_symm induction
  | equalityTrans firstTyping secondTyping firstInduction secondInduction =>
      exact Proposition.accessHolds_equality_trans firstInduction
        secondInduction
  | unfoldRec => trivial
  | equalityArrow => trivial
  | equalityCapturing => trivial
  | equalityCaptureUnion leftTyping rightTyping leftInduction rightInduction =>
      exact SeparationSemantics.equivalent_union leftInduction rightInduction
  | equalityCaptureReadOnly typing induction =>
      exact SeparationSemantics.equivalent_readOnly induction
  | inclusionRefl expression =>
      exact Proposition.accessHolds_inclusion_refl valuation expression
  | inclusionTrans firstTyping secondTyping firstInduction secondInduction =>
      exact Proposition.accessHolds_inclusion_trans firstInduction
        secondInduction
  | equalityToInclusion typing induction =>
      exact Proposition.accessHolds_equality_to_inclusion induction
  | typeTop => trivial
  | typeBottom => trivial
  | typeArrow => trivial
  | typeCapturing => trivial
  | captureEmpty target =>
      exact SeparationSemantics.empty_subcapture valuation target
  | captureUnionLeft left right =>
      exact SeparationSemantics.union_left_subcapture valuation left right
  | captureUnionRight left right =>
      exact SeparationSemantics.union_right_subcapture valuation left right
  | captureUnionElim leftTyping rightTyping leftInduction rightInduction =>
      exact SeparationSemantics.union_elim_subcapture leftInduction
        rightInduction
  | captureVariable binding =>
      exact respects.1 _ _ _ binding
  | captureReadOnly capture =>
      exact SeparationSemantics.readOnly_subcapture valuation capture
  | captureReadOnlyMono typing induction =>
      exact SeparationSemantics.readOnly_mono induction
  | modeEmpty mode =>
      exact SeparationSemantics.mode_empty valuation mode
  | modeUnion leftTyping rightTyping leftInduction rightInduction =>
      exact SeparationSemantics.mode_union leftInduction rightInduction
  | modeSubcapture subcaptureTyping modeTyping subcaptureInduction
      modeInduction =>
      exact SeparationSemantics.mode_subcapture subcaptureInduction
        modeInduction
  | modeWritable capture =>
      exact SeparationSemantics.mode_writable valuation capture
  | modeReadOnly capture =>
      exact SeparationSemantics.mode_readOnly valuation capture
  | separateSymm typing induction =>
      exact SeparationSemantics.separate_symm induction
  | separateUnion leftTyping rightTyping leftInduction rightInduction =>
      exact SeparationSemantics.separate_union leftInduction rightInduction
  | separateEmpty capture =>
      exact SeparationSemantics.separate_empty valuation capture
  | separateReadOnly leftTyping rightTyping leftInduction rightInduction =>
      exact SeparationSemantics.separate_readOnly leftInduction rightInduction
  | separateSubcapture subcaptureTyping separationTyping
      subcaptureInduction separationInduction =>
      exact SeparationSemantics.separate_subcapture subcaptureInduction
        (SeparationSemantics.subcapture_refl valuation _)
        separationInduction
  | separateOfDisjoint typing induction =>
      exact SeparationSemantics.separate_of_disjoint induction
  | disjointSymm typing induction =>
      exact SeparationSemantics.disjoint_symm induction
  | disjointUnion leftTyping rightTyping leftInduction rightInduction =>
      exact SeparationSemantics.disjoint_union leftInduction rightInduction
  | disjointEmpty capture =>
      exact SeparationSemantics.disjoint_empty valuation capture
  | disjointEquality equalityTyping disjointTyping equalityInduction
      disjointInduction =>
      exact SeparationSemantics.disjoint_equivalent_left equalityInduction
        disjointInduction

end Evidence.Proves

namespace SeparationExamples

/-- A scope with one named term capability. -/
abbrev OneCapabilityScope : Sig := [] ▹ .term

/-- The corresponding context carries no logical assumptions. -/
def oneCapabilityContext : Ctx OneCapabilityScope :=
  Ctx.nil.extendTerm .one

/-- The named capability is writable at the sole semantic capability. -/
def oneWritable : AccessValuation OneCapabilityScope Unit where
  term := fun
    | .here => fun _ => .writable
    | .there older => nomatch older
  captureSymbol := fun
    | .there older => nomatch older

/-- A read-only view of the sole, nonempty capability. -/
def sharedReadOnly : Capture OneCapabilityScope :=
  .readOnly (.singleton .here)

/-- The explicit checked certificate for the allowed read-only overlap. -/
def sharedReadOnlySeparation : Evidence .separate OneCapabilityScope :=
  .separateReadOnly
    (.modeReadOnly (.singleton .here))
    (.modeReadOnly (.singleton .here))

def sharedReadOnlySeparation_proves :
    Evidence.Proves oneCapabilityContext sharedReadOnlySeparation
      (.separate sharedReadOnly sharedReadOnly) := by
  exact Evidence.Proves.separateReadOnly
    (Evidence.Proves.modeReadOnly (.singleton .here))
    (Evidence.Proves.modeReadOnly (.singleton .here))

@[simp]
theorem sharedReadOnly_access :
    sharedReadOnly.access oneWritable () = .readOnly := rfl

/-- The same nonempty read-only capability is separate from itself. -/
theorem shared_readOnly_is_separate :
    SeparationSemantics.Separate oneWritable sharedReadOnly sharedReadOnly := by
  intro capability
  cases capability
  exact Or.inr (Or.inr ⟨trivial, trivial⟩)

/-- The same nonempty read-only capability is not disjoint from itself. -/
theorem shared_readOnly_is_not_disjoint :
    ¬ SeparationSemantics.Disjoint oneWritable sharedReadOnly sharedReadOnly := by
  intro disjoint
  have overlap := disjoint ()
  rcases overlap with leftAbsent | rightAbsent
  · cases leftAbsent
  · cases rightAbsent

/-- The separating valuation is valid for the one-capability context.  The
bare `One` binding imposes no capture-summary condition, and there are no
ambient evidence binders. -/
theorem oneWritable_respects : oneWritable.Respects oneCapabilityContext := by
  constructor
  · intro index captures shape binding
    cases index with
    | here => cases binding
    | there older => nomatch older
  · intro relation index proposition binding
    cases index with
    | there older => nomatch older

/-- No evidence term can derive disjointness for the same nonempty read-only
capability in an assumption-free context. -/
theorem no_evidence_for_shared_readOnly_disjoint
    {evidence : Evidence .disjoint OneCapabilityScope}
    (typing : Evidence.Proves oneCapabilityContext evidence
      (.disjoint sharedReadOnly sharedReadOnly)) : False := by
  apply shared_readOnly_is_not_disjoint
  exact typing.access_sound oneWritable_respects

end SeparationExamples

end ManySortedFC
