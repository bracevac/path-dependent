import Coercions.ManySortedFC.Intervals

/-!
# Binder-only interval elaboration

This module is the first source-facing boundary of the development.  A small
surface declaration records its lower and upper endpoints independently.  An
omitted endpoint is a marker, not a static expression; elaboration translates
only the concrete endpoints into propositions in a one-symbol target theory.

There is deliberately no endpoint-consistency field in `Declaration` and no
proof search in `elaborate`.  Bad intervals elaborate just as structurally as
realizable ones; model construction is the later point at which their
evidence obligations must be met.
-/

namespace ManySortedFC.IntervalElaboration

/-- A surface endpoint is either omitted or a concrete expression of the
binder's static sort.  For an upper capture endpoint, `omitted` is the `*`
marker and does not denote a capture-top expression. -/
inductive Endpoint (scope : Sig) (sort : StaticSort) : Type where
  | omitted
  | bounded (expression : StaticExpr sort scope)
deriving DecidableEq

/-- A binder-only true interval declaration with independent endpoints. -/
structure Declaration (scope : Sig) (sort : StaticSort) where
  lower : Endpoint scope sort
  upper : Endpoint scope sort
deriving DecidableEq

/-- A compiled one-name theory, existentially packaging its exact relation
shape while retaining it as an index of the target syntax. -/
structure Compiled (scope : Sig) (sort : StaticSort) where
  relations : List Relation
  theory : Theory scope [sort] relations

/-- Compile one surface interval to a names-first target theory.

Each concrete endpoint contributes exactly one directed-inclusion
proposition.  No branch asks whether the lower endpoint is included in the
upper endpoint. -/
def elaborate {scope : Sig} {sort : StaticSort}
    (declaration : Declaration scope sort) : Compiled scope sort :=
  match declaration.lower, declaration.upper with
  | .omitted, .omitted => ⟨[], Interval.unconstrained sort⟩
  | .bounded lower, .omitted =>
      ⟨[.inclusion sort], Interval.lowerBounded lower⟩
  | .omitted, .bounded upper =>
      ⟨[.inclusion sort], Interval.upperBounded upper⟩
  | .bounded lower, .bounded upper =>
      ⟨[.inclusion sort, .inclusion sort],
        Interval.between lower upper⟩

/-- A true type interval, including deliberately inconsistent endpoints. -/
def typeBetween {scope : Sig} (lower upper : Ty scope) :
    Declaration scope .type :=
  ⟨.bounded (.type lower), .bounded (.type upper)⟩

/-- A true capture interval, including deliberately incompatible endpoints. -/
def captureBetween {scope : Sig} (lower upper : Capture scope) :
    Declaration scope .capture :=
  ⟨.bounded (.capture lower), .bounded (.capture upper)⟩

/-- An upper-bounded capture parameter with the empty lower endpoint. -/
def captureUpper {scope : Sig} (upper : Capture scope) :
    Declaration scope .capture :=
  captureBetween .empty upper

/-- A completely unbounded capture parameter. -/
def captureUnbounded {scope : Sig} : Declaration scope .capture :=
  ⟨.omitted, .omitted⟩

/-- A lower-bounded capture parameter whose upper endpoint is `*`. -/
def captureLowerUnbounded {scope : Sig} (lower : Capture scope) :
    Declaration scope .capture :=
  ⟨.bounded (.capture lower), .omitted⟩

@[simp]
theorem elaborate_type_between_relations {scope : Sig}
    (lower upper : Ty scope) :
    (elaborate (typeBetween lower upper)).relations =
      [.inclusion .type, .inclusion .type] := rfl

@[simp]
theorem elaborate_capture_between_relations {scope : Sig}
    (lower upper : Capture scope) :
    (elaborate (captureBetween lower upper)).relations =
      [.inclusion .capture, .inclusion .capture] := rfl

@[simp]
theorem elaborate_unbounded_capture_relations {scope : Sig} :
    (elaborate (captureUnbounded (scope := scope))).relations = [] := rfl

@[simp]
theorem elaborate_lower_unbounded_capture_relations {scope : Sig}
    (lower : Capture scope) :
    (elaborate (captureLowerUnbounded lower)).relations =
      [.inclusion .capture] := rfl

end ManySortedFC.IntervalElaboration
