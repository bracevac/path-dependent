import LambdaPFCI.SemanticSafety

/-!
A closed regression for opaque intersections of proper types.  The same
closure receives two incomparable function views and is then used through
both views in one self-application:

```text
F = Top -> Top
S = Top -> F
L = F -> F
R = Top -> Top

v = fun (_ : Top) => fun (y : Top) => y
f : L ∧ R = v
in f f
```

The exact source type `S` is below both `L` (by narrowing the domain) and `R`
(by widening the codomain).  Intersection introduction records both views.
The application projects `L` for the function and `R = F` for its argument.
-/

namespace LambdaPFCI.IntersectionRegression

noncomputable section

def functionType : Ty n :=
  .Fun .Top .Top

def sourceType : Ty n :=
  .Fun .Top functionType.weaken

def leftView : Ty n :=
  .Fun functionType functionType.weaken

def rightView : Ty n :=
  functionType

def intersectionType : Ty n :=
  .Inter leftView rightView

def functionTypeWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (functionType (n := n))) :=
  .fun .top .top

def leftViewWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (leftView (n := n))) :=
  .fun functionTypeWf functionTypeWf

def rightViewWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (rightView (n := n))) :=
  functionTypeWf

def intersectionTypeWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (intersectionType (n := n))) :=
  .inter leftViewWf rightViewWf

def sourceToLeft {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceType (n := n)))
      (.ty (leftView (n := n))) :=
  .fun .top .refl

def sourceToRight {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceType (n := n)))
      (.ty (rightView (n := n))) :=
  .fun .refl .top

def sourceToIntersection {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceType (n := n)))
      (.ty (intersectionType (n := n))) :=
  .inter sourceToLeft sourceToRight

def value : Tm 0 :=
  .abs .Top (.abs .Top (.path (.var 0)))

def body : Tm 1 :=
  .app (.var 0) (.var 0)

def term : Tm 0 :=
  .let value body

private def context : Ctx 1 :=
  Ctx.nil.snoc intersectionType

private def valueSourceTyping :
    Tm.Ty Ctx.nil value sourceType :=
  .abs
    (.abs
      (.sub (.path .var) (.widen .var) .top)
      .top)
    .top

def valueIntersectionTyping :
    Tm.Ty Ctx.nil value intersectionType :=
  .sub valueSourceTyping sourceToIntersection intersectionTypeWf

/-- The bound path is used through the left projection `F -> F`. -/
def functionViewTyping :
    Tm.Ty context (.path (.var 0)) leftView :=
  .sub
    (.path .var)
    (.trans (.widen .var) .inter_left)
    leftViewWf

/-- The same bound path is used through the right projection `F`. -/
def argumentViewTyping :
    Tm.Ty context (.path (.var 0)) rightView :=
  .sub
    (.path .var)
    (.trans (.widen .var) .inter_right)
    rightViewWf

private def bodyTyping :
    Tm.Ty context body functionType.weaken := by
  simpa [body, leftView, rightView, functionType, Ty.weaken_open] using
    Tm.Ty.app functionViewTyping argumentViewTyping

def term_typing : Tm.Ty Ctx.nil term functionType :=
  .let valueIntersectionTyping functionTypeWf bodyTyping

theorem term_type_safety
    {n : Nat} {target : State n}
    (steps : State.Steps (State.initial term) target) :
    State.Progress target :=
  term_typing.closed_type_safety steps

end

end LambdaPFCI.IntersectionRegression
