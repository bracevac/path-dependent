import Coercions.ManySortedFC.Intervals
import Coercions.ManySortedFC.Evidence

/-!
# Static slots for many-sorted source translations

A source-level static binder, or later a path-indexed abstract member, is
represented by one generated target symbol together with whichever directed
interval assumptions its declaration exports.  The slot is deliberately
independent of the source key used to find it: binder variables and future
`(path, label)` lookups can therefore share this target-side representation.
-/

namespace ManySortedTranslation

open ManySortedFC

/-- Target coordinates allocated for one abstract symbol of a fixed sort.

The name is always present.  A missing interval endpoint allocates no logical
assumption, represented by `none` rather than by a fabricated top or bottom
expression. -/
structure StaticSlot (scope : Sig) (sort : StaticSort) where
  name : BVar scope (.symbol sort)
  lower : Option (BVar scope (.evidence (.inclusion sort)))
  upper : Option (BVar scope (.evidence (.inclusion sort)))
deriving DecidableEq

namespace StaticSlot

/-- Regard the generated coordinate as a static expression of its sort. -/
def expression {scope : Sig} {sort : StaticSort}
    (slot : StaticSlot scope sort) : StaticExpr sort scope :=
  StaticExpr.symbol slot.name

/-- Transport every coordinate through a heterogeneous target renaming. -/
def rename {source target : Sig} {sort : StaticSort}
    (slot : StaticSlot source sort) (rho : Rename source target) :
    StaticSlot target sort where
  name := rho.var slot.name
  lower := slot.lower.map rho.var
  upper := slot.upper.map rho.var

/-- Weaken every coordinate below one new target binder. -/
def weaken {scope : Sig} {sort : StaticSort} {kind : BinderKind}
    (slot : StaticSlot scope sort) : StaticSlot (scope ▹ kind) sort :=
  slot.rename Rename.succ

@[simp]
theorem rename_id {scope : Sig} {sort : StaticSort}
    (slot : StaticSlot scope sort) :
    slot.rename Rename.id = slot := by
  cases slot with
  | mk name lower upper =>
      cases lower <;> cases upper <;> rfl

@[simp]
theorem rename_comp {first second third : Sig} {sort : StaticSort}
    (slot : StaticSlot first sort) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (slot.rename rho₁).rename rho₂ =
      slot.rename (rho₁.comp rho₂) := by
  cases slot with
  | mk name lower upper =>
      cases lower <;> cases upper <;> rfl

/-! ## Canonical one-name interval layouts -/

/-- The sole name of an unconstrained one-symbol theory. -/
def unconstrained (scope : Sig) (sort : StaticSort) :
    StaticSlot (StaticScope scope [sort] []) sort where
  name := .here
  lower := none
  upper := none

/-- Coordinates of a one-symbol theory with only a lower assumption. -/
def lowerBounded {scope : Sig} {sort : StaticSort}
    (_lower : StaticExpr sort scope) :
    StaticSlot
      (StaticScope scope [sort] [.inclusion sort]) sort where
  name := .there .here
  lower := some .here
  upper := none

/-- Coordinates of a one-symbol theory with only an upper assumption. -/
def upperBounded {scope : Sig} {sort : StaticSort}
    (_upper : StaticExpr sort scope) :
    StaticSlot
      (StaticScope scope [sort] [.inclusion sort]) sort where
  name := .there .here
  lower := none
  upper := some .here

/-- Coordinates of a true two-sided one-symbol interval.  The lower
assumption is the newest evidence binder; the upper assumption follows it. -/
def between {scope : Sig} {sort : StaticSort}
    (_lower _upper : StaticExpr sort scope) :
    StaticSlot (StaticScope scope [sort]
      [.inclusion sort, .inclusion sort]) sort where
  name := .there (.there .here)
  lower := some .here
  upper := some (.there .here)

@[simp]
theorem unconstrained_name (scope : Sig) (sort : StaticSort) :
    (unconstrained scope sort).name = .here := rfl

@[simp]
theorem unconstrained_lower (scope : Sig) (sort : StaticSort) :
    (unconstrained scope sort).lower = none := rfl

@[simp]
theorem unconstrained_upper (scope : Sig) (sort : StaticSort) :
    (unconstrained scope sort).upper = none := rfl

@[simp]
theorem lowerBounded_name {scope : Sig} {sort : StaticSort}
    (lower : StaticExpr sort scope) :
    (lowerBounded lower).name = .there .here := rfl

@[simp]
theorem lowerBounded_lower {scope : Sig} {sort : StaticSort}
    (lower : StaticExpr sort scope) :
    (lowerBounded lower).lower = some .here := rfl

@[simp]
theorem lowerBounded_upper {scope : Sig} {sort : StaticSort}
    (lower : StaticExpr sort scope) :
    (lowerBounded lower).upper = none := rfl

@[simp]
theorem upperBounded_name {scope : Sig} {sort : StaticSort}
    (upper : StaticExpr sort scope) :
    (upperBounded upper).name = .there .here := rfl

@[simp]
theorem upperBounded_lower {scope : Sig} {sort : StaticSort}
    (upper : StaticExpr sort scope) :
    (upperBounded upper).lower = none := rfl

@[simp]
theorem upperBounded_upper {scope : Sig} {sort : StaticSort}
    (upper : StaticExpr sort scope) :
    (upperBounded upper).upper = some .here := rfl

@[simp]
theorem between_name {scope : Sig} {sort : StaticSort}
    (lower upper : StaticExpr sort scope) :
    (between lower upper).name = .there (.there .here) := rfl

@[simp]
theorem between_lower {scope : Sig} {sort : StaticSort}
    (lower upper : StaticExpr sort scope) :
    (between lower upper).lower = some .here := rfl

@[simp]
theorem between_upper {scope : Sig} {sort : StaticSort}
    (lower upper : StaticExpr sort scope) :
    (between lower upper).upper = some (.there .here) := rfl

/-! ## Exported propositions and context lookup -/

/-- Install the head proposition of a theory below its older evidence tail and
then below its own evidence binder.  This is the scope transport performed by
`Ctx.extendTheoryEvidence`, exposed here so translation coordinates and
context lookup share one exact convention. -/
def exportHead {scope : Sig} {symbols : List StaticSort}
    {relation : Relation}
    (proposition : Proposition relation (SymbolScope scope symbols))
    (older : List Relation) :
    Proposition relation
      (StaticScope scope symbols (relation :: older)) :=
  (proposition.rename
    (Rename.weakenMany (SymbolScope scope symbols)
      (evidenceKinds older))).rename Rename.succ

/-- Lower-only proposition as installed in the complete target static scope. -/
def lowerBoundedProposition {scope : Sig} {sort : StaticSort}
    (lower : StaticExpr sort scope) :
    Proposition (.inclusion sort)
      (StaticScope scope [sort] [.inclusion sort]) :=
  exportHead (.inclusion lower.weaken
    (Interval.name (scope := scope) (sort := sort))) []

/-- Upper-only proposition as installed in the complete target static scope. -/
def upperBoundedProposition {scope : Sig} {sort : StaticSort}
    (upper : StaticExpr sort scope) :
    Proposition (.inclusion sort)
      (StaticScope scope [sort] [.inclusion sort]) :=
  exportHead (.inclusion
    (Interval.name (scope := scope) (sort := sort)) upper.weaken) []

/-- Lower proposition of a two-sided interval as installed after its older
upper proposition. -/
def betweenLowerProposition {scope : Sig} {sort : StaticSort}
    (lower _upper : StaticExpr sort scope) :
    Proposition (.inclusion sort)
      (StaticScope scope [sort]
        [.inclusion sort, .inclusion sort]) :=
  exportHead (.inclusion lower.weaken
    (Interval.name (scope := scope) (sort := sort)))
    [.inclusion sort]

/-- Upper proposition of a two-sided interval, first installed as the tail
head and then weakened below the newer lower proposition. -/
def betweenUpperProposition {scope : Sig} {sort : StaticSort}
    (_lower upper : StaticExpr sort scope) :
    Proposition (.inclusion sort)
      (StaticScope scope [sort]
        [.inclusion sort, .inclusion sort]) :=
  (exportHead (.inclusion
    (Interval.name (scope := scope) (sort := sort)) upper.weaken) []).rename
      Rename.succ

@[simp]
theorem lookup_unconstrained_name {scope : Sig} (context : Ctx scope)
    (sort : StaticSort) :
    (context.extendTheory (Interval.unconstrained sort)).lookup
      (unconstrained scope sort).name = Binding.symbol := by
  rfl

@[simp]
theorem lookup_lowerBounded_name {scope : Sig} (context : Ctx scope)
    {sort : StaticSort} (lower : StaticExpr sort scope) :
    (context.extendTheory (Interval.lowerBounded lower)).lookup
      (lowerBounded lower).name = Binding.symbol := by
  rfl

@[simp]
theorem lookup_upperBounded_name {scope : Sig} (context : Ctx scope)
    {sort : StaticSort} (upper : StaticExpr sort scope) :
    (context.extendTheory (Interval.upperBounded upper)).lookup
      (upperBounded upper).name = Binding.symbol := by
  rfl

@[simp]
theorem lookup_between_name {scope : Sig} (context : Ctx scope)
    {sort : StaticSort} (lower upper : StaticExpr sort scope) :
    (context.extendTheory (Interval.between lower upper)).lookup
      (between lower upper).name = Binding.symbol := by
  rfl

@[simp]
theorem lookup_lowerBounded_lower {scope : Sig} (context : Ctx scope)
    {sort : StaticSort} (lower : StaticExpr sort scope) :
    (context.extendTheory (Interval.lowerBounded lower)).lookup
      (.here : BVar
        (StaticScope scope [sort] [.inclusion sort])
        (.evidence (.inclusion sort))) =
      Binding.evidence (lowerBoundedProposition lower) := by
  rfl

@[simp]
theorem lookup_upperBounded_upper {scope : Sig} (context : Ctx scope)
    {sort : StaticSort} (upper : StaticExpr sort scope) :
    (context.extendTheory (Interval.upperBounded upper)).lookup
      (.here : BVar
        (StaticScope scope [sort] [.inclusion sort])
        (.evidence (.inclusion sort))) =
      Binding.evidence (upperBoundedProposition upper) := by
  rfl

@[simp]
theorem lookup_between_lower {scope : Sig} (context : Ctx scope)
    {sort : StaticSort} (lower upper : StaticExpr sort scope) :
    (context.extendTheory (Interval.between lower upper)).lookup
      (.here : BVar
        (StaticScope scope [sort]
          [.inclusion sort, .inclusion sort])
        (.evidence (.inclusion sort))) =
      Binding.evidence (betweenLowerProposition lower upper) := by
  rfl

@[simp]
theorem lookup_between_upper {scope : Sig} (context : Ctx scope)
    {sort : StaticSort} (lower upper : StaticExpr sort scope) :
    (context.extendTheory (Interval.between lower upper)).lookup
      (.there .here : BVar
        (StaticScope scope [sort]
          [.inclusion sort, .inclusion sort])
        (.evidence (.inclusion sort))) =
      Binding.evidence (betweenUpperProposition lower upper) := by
  rfl

/-- The canonical lower-only variable proves its exported proposition. -/
def proves_lowerBounded_lower {scope : Sig} (context : Ctx scope)
    {sort : StaticSort} (lower : StaticExpr sort scope) :
    Evidence.Proves (context.extendTheory (Interval.lowerBounded lower))
      (.var .here) (lowerBoundedProposition lower) :=
  .var (lookup_lowerBounded_lower context lower)

/-- The canonical upper-only variable proves its exported proposition. -/
def proves_upperBounded_upper {scope : Sig} (context : Ctx scope)
    {sort : StaticSort} (upper : StaticExpr sort scope) :
    Evidence.Proves (context.extendTheory (Interval.upperBounded upper))
      (.var .here) (upperBoundedProposition upper) :=
  .var (lookup_upperBounded_upper context upper)

/-- The newest evidence coordinate proves the lower side of a true interval. -/
def proves_between_lower {scope : Sig} (context : Ctx scope)
    {sort : StaticSort} (lower upper : StaticExpr sort scope) :
    Evidence.Proves (context.extendTheory (Interval.between lower upper))
      (.var .here) (betweenLowerProposition lower upper) :=
  .var (lookup_between_lower context lower upper)

/-- The second evidence coordinate proves the upper side of a true interval. -/
def proves_between_upper {scope : Sig} (context : Ctx scope)
    {sort : StaticSort} (lower upper : StaticExpr sort scope) :
    Evidence.Proves (context.extendTheory (Interval.between lower upper))
      (.var (.there .here)) (betweenUpperProposition lower upper) :=
  .var (lookup_between_upper context lower upper)

end StaticSlot

end ManySortedTranslation
