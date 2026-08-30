import Coercions.ManySortedFC.Substitution

/-!
# True interval theories

These constructors are the small binder-only interface to names-first local
theories.  Endpoint consistency is never an input: a two-sided interval
always exports its lower and upper assumptions independently.  One-sided and
unconstrained binders omit propositions instead of inventing a top element
for every static sort.
-/

namespace ManySortedFC

namespace Interval

/-- The single symbol introduced by a one-name local theory. -/
def name {scope : Sig} {sort : StaticSort} :
    StaticExpr sort (SymbolScope scope [sort]) :=
  StaticExpr.symbol (.here :
    BVar (SymbolScope scope [sort]) (.symbol sort))

/-- A one-name theory with no constraints. -/
def unconstrained {scope : Sig} (sort : StaticSort) :
    Theory scope [sort] [] :=
  .nil

/-- A one-name theory with only a concrete lower endpoint. -/
def lowerBounded {scope : Sig} {sort : StaticSort}
    (lower : StaticExpr sort scope) :
    Theory scope [sort] [.inclusion sort] :=
  .cons (.inclusion lower.weaken (name (scope := scope) (sort := sort)))
    .nil

/-- A one-name theory with only a concrete upper endpoint. -/
def upperBounded {scope : Sig} {sort : StaticSort}
    (upper : StaticExpr sort scope) :
    Theory scope [sort] [.inclusion sort] :=
  .cons (.inclusion (name (scope := scope) (sort := sort)) upper.weaken)
    .nil

/-- A true two-sided interval.  No proof relating the endpoints is required. -/
def between {scope : Sig} {sort : StaticSort}
    (lower upper : StaticExpr sort scope) :
    Theory scope [sort] [.inclusion sort, .inclusion sort] :=
  .cons (.inclusion lower.weaken (name (scope := scope) (sort := sort)))
    (.cons (.inclusion (name (scope := scope) (sort := sort)) upper.weaken)
      .nil)

/-- Ordinary upper-bounded type variable, with `Bottom` as its lower bound. -/
def typeUpper {scope : Sig} (upper : Ty scope) :
    Theory scope [.type] [.inclusion .type, .inclusion .type] :=
  between (.type .bot) (.type upper)

/-- Ordinary upper-bounded capture variable, with the empty lower bound. -/
def captureUpper {scope : Sig} (upper : Capture scope) :
    Theory scope [.capture]
      [.inclusion .capture, .inclusion .capture] :=
  between (.capture .empty) (.capture upper)

/-- An unbounded capture variable.

There is no capture-top endpoint hidden in this definition: the theory simply
contains no upper proposition. -/
def captureUnbounded {scope : Sig} : Theory scope [.capture] [] :=
  unconstrained .capture

/-- A lower-bounded capture variable whose upper endpoint is the `*` marker.

Again, `*` is represented by omission rather than by a capture expression. -/
def captureLowerUnbounded {scope : Sig} (lower : Capture scope) :
    Theory scope [.capture] [.inclusion .capture] :=
  lowerBounded (.capture lower)

end Interval

end ManySortedFC
