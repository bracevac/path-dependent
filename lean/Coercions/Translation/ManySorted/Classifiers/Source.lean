import Coercions.ManySortedFC.Classifier.Subtract

/-!
# Surface classifier projections

This file isolates the source-facing `.only` and `.except` notation used by
the classifier case study.  A surface projection is a base capture followed
by a left-to-right chain of filters.  Classifiers and kinds are closed: there
are no kind variables, kind binders, or kind solver in this layer.

The source term spine below is deliberately small but computational.  It is
the ordinary call-by-value lambda calculus with `let`; classifier filters are
static annotations on a complete program, not new runtime operations.
-/

namespace DOTCaptureToManySortedFC.Classifiers.Source

abbrev Classifier := ManySortedFC.Classifier
abbrev Kind := ManySortedFC.Classifier.Kind

/-! ## Surface filter chains -/

/-- One source-level classifier filter. -/
inductive Filter where
  | only (classifier : Classifier)
  | except (classifier : Classifier)
deriving DecidableEq

namespace Filter

/-- Apply one surface filter to the kind accumulated to its left. -/
def apply : Filter -> Kind -> Kind
  | .only classifier, kind =>
      ManySortedFC.Classifier.Kind.intersect kind
        (ManySortedFC.Classifier.Kind.classifier classifier)
  | .except classifier, kind =>
      ManySortedFC.Classifier.Kind.subtract kind
        (ManySortedFC.Classifier.Kind.classifier classifier)

end Filter

/-- A base capture followed by surface filters in source order.  For example,
`x.only[A].except[B]` is represented by
`((base x).only A).except B`. -/
inductive ProjectedCapture (Base : Type) where
  | base (capture : Base)
  | only (preceding : ProjectedCapture Base) (classifier : Classifier)
  | except (preceding : ProjectedCapture Base) (classifier : Classifier)
deriving DecidableEq

namespace ProjectedCapture

/-- The unfiltered capture at the root of a surface chain. -/
def root {Base : Type} : ProjectedCapture Base -> Base
  | .base capture => capture
  | .only preceding _ => preceding.root
  | .except preceding _ => preceding.root

/-- Surface filters in the order in which they are written. -/
def filters {Base : Type} : ProjectedCapture Base -> List Filter
  | .base _ => []
  | .only preceding classifier => preceding.filters ++ [.only classifier]
  | .except preceding classifier => preceding.filters ++ [.except classifier]

/-- Whether the source capture contains an actual projection. -/
def isProjected {Base : Type} : ProjectedCapture Base -> Bool
  | .base _ => false
  | .only _ _ => true
  | .except _ _ => true

/-- Interpret a filter list from a supplied initial kind. -/
def applyFilters (initial : Kind) : List Filter -> Kind
  | [] => initial
  | filter :: remaining =>
      applyFilters (filter.apply initial) remaining

/-- Collapse the whole source chain to one closed classifier kind.  The
implicit filter on an unqualified capture is `top`. -/
def kind {Base : Type} (capture : ProjectedCapture Base) : Kind :=
  applyFilters ManySortedFC.Classifier.Kind.top capture.filters

@[simp]
theorem root_base {Base : Type} (capture : Base) :
    (base capture : ProjectedCapture Base).root = capture := rfl

@[simp]
theorem root_only {Base : Type} (capture : ProjectedCapture Base)
    (classifier : Classifier) :
    (capture.only classifier).root = capture.root := rfl

@[simp]
theorem root_except {Base : Type} (capture : ProjectedCapture Base)
    (classifier : Classifier) :
    (capture.except classifier).root = capture.root := rfl

@[simp]
theorem filters_base {Base : Type} (capture : Base) :
    (base capture : ProjectedCapture Base).filters = [] := rfl

@[simp]
theorem filters_only {Base : Type} (capture : ProjectedCapture Base)
    (classifier : Classifier) :
    (capture.only classifier).filters =
      capture.filters ++ [.only classifier] := rfl

@[simp]
theorem filters_except {Base : Type} (capture : ProjectedCapture Base)
    (classifier : Classifier) :
    (capture.except classifier).filters =
      capture.filters ++ [.except classifier] := rfl

@[simp]
theorem applyFilters_append (initial : Kind) (first second : List Filter) :
    applyFilters initial (first ++ second) =
      applyFilters (applyFilters initial first) second := by
  induction first generalizing initial with
  | nil => rfl
  | cons filter remaining induction =>
      simp only [List.cons_append, applyFilters]
      exact induction (filter.apply initial)

@[simp]
theorem kind_base {Base : Type} (capture : Base) :
    (base capture : ProjectedCapture Base).kind =
      ManySortedFC.Classifier.Kind.top := rfl

@[simp]
theorem kind_only {Base : Type} (capture : ProjectedCapture Base)
    (classifier : Classifier) :
    (capture.only classifier).kind =
      ManySortedFC.Classifier.Kind.intersect capture.kind
        (ManySortedFC.Classifier.Kind.classifier classifier) := by
  simp [kind, filters, applyFilters_append, applyFilters, Filter.apply]

@[simp]
theorem kind_except {Base : Type} (capture : ProjectedCapture Base)
    (classifier : Classifier) :
    (capture.except classifier).kind =
      ManySortedFC.Classifier.Kind.subtract capture.kind
        (ManySortedFC.Classifier.Kind.classifier classifier) := by
  simp [kind, filters, applyFilters_append, applyFilters, Filter.apply]

end ProjectedCapture

/-! ## Computational source programs -/

/-- The source runtime spine used by the classifier regressions. -/
inductive Term : Nat -> Type where
  | var {scope : Nat} (index : Fin scope) : Term scope
  | unit {scope : Nat} : Term scope
  | lam {scope : Nat} (body : Term (scope + 1)) : Term scope
  | app {scope : Nat} (function argument : Term scope) : Term scope
  | let' {scope : Nat} (rhs : Term scope)
      (body : Term (scope + 1)) : Term scope
deriving DecidableEq

/-- A source program with one advertised capture expression.  The annotation
may contain any number of `.only` and `.except` filters; the term remains a
genuine lambda-calculus computation. -/
structure Program (Base : Type) (scope : Nat) where
  capture : ProjectedCapture Base
  term : Term scope
deriving DecidableEq

end DOTCaptureToManySortedFC.Classifiers.Source
