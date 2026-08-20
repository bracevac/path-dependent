import LambdaPCCI.CaptureSafety

/-!
A capture-aware mirror of the closed intersection regression in
`LambdaPFCI.IntersectionRegression`.  Every exposed capture set is empty, so
erasing capture information gives the same two incomparable function views:

```text
F = Top -> Top
S = Top -> F
L = F -> F
R = Top -> Top

v = fun (_ : Top) => fun (y : Top) => y
f : L ∧ R = v
in f f
```

The application projects `L` for the function and `R = F` for its argument.
-/

namespace LambdaPCCI.IntersectionRegression

noncomputable section

def pureTop (n : Nat) : Ty n :=
  .capt .empty .Top

def functionShape (n : Nat) : Shape n :=
  .Fun (pureTop n) (pureTop (n + 1))

def functionType (n : Nat) : Ty n :=
  .capt .empty (functionShape n)

def sourceShape (n : Nat) : Shape n :=
  .Fun (pureTop n) (functionType n).weaken

def sourceType (n : Nat) : Ty n :=
  .capt .empty (sourceShape n)

def leftViewShape (n : Nat) : Shape n :=
  .Fun (functionType n) (functionType n).weaken

def leftView (n : Nat) : Ty n :=
  .capt .empty (leftViewShape n)

def rightViewShape (n : Nat) : Shape n :=
  functionShape n

def rightView (n : Nat) : Ty n :=
  .capt .empty (rightViewShape n)

def intersectionShape (n : Nat) : Shape n :=
  .Inter (leftViewShape n) (rightViewShape n)

def intersectionType (n : Nat) : Ty n :=
  .capt .empty (intersectionShape n)

private def pureTopWf {Gamma : Ctx n} :
    Ty.Wf Gamma (pureTop n) :=
  .capt .empty .top

private def functionShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma (functionShape n) :=
  .fun pureTopWf pureTopWf

def functionTypeWf {Gamma : Ctx n} :
    Ty.Wf Gamma (functionType n) :=
  .capt .empty functionShapeWf

private def leftViewShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma (leftViewShape n) :=
  .fun functionTypeWf functionTypeWf

def leftViewWf {Gamma : Ctx n} :
    Ty.Wf Gamma (leftView n) :=
  .capt .empty leftViewShapeWf

def rightViewWf {Gamma : Ctx n} :
    Ty.Wf Gamma (rightView n) :=
  functionTypeWf

def intersectionTypeWf {Gamma : Ctx n} :
    Ty.Wf Gamma (intersectionType n) :=
  .capt .empty (.inter leftViewShapeWf functionShapeWf)

def sourceToLeft {Gamma : Ctx n} :
    Shape.Sub Gamma (sourceShape n) (leftViewShape n) :=
  .fun (.capt .refl .top) .refl

def sourceToRight {Gamma : Ctx n} :
    Shape.Sub Gamma (sourceShape n) (rightViewShape n) :=
  .fun .refl (.capt .refl .top)

def sourceToIntersection {Gamma : Ctx n} :
    Ty.Sub Gamma (sourceType n) (intersectionType n) :=
  .capt .refl (.inter sourceToLeft sourceToRight)

def value : Tm 0 :=
  .abs (pureTop 0)
    (.abs (pureTop 1) (.path (.var 0)))

def body : Tm 1 :=
  .app (.var 0) (.var 0)

def term : Tm 0 :=
  .let value body

private def context : Ctx 1 :=
  Ctx.nil.snoc (intersectionType 0)

private def innerBodyTyping :
    Tm.Ty ((Ctx.nil.snoc (pureTop 0)).snoc (pureTop 1))
      (.path (.var 0)) (pureTop 2)
      (.union .empty (.singleton (.var 0))) :=
  .sub
    (.path .var)
    (.capt (.path .var) .top)
    .union_right
    pureTopWf
    (.union .empty (.singleton .var))

private def innerValueTyping :
    Tm.Ty (Ctx.nil.snoc (pureTop 0))
      (.abs (pureTop 1) (.path (.var 0)))
      (functionType 1) .empty :=
  .abs innerBodyTyping pureTopWf .empty

private def outerBodyTyping :
    Tm.Ty (Ctx.nil.snoc (pureTop 0))
      (.abs (pureTop 1) (.path (.var 0)))
      (functionType 0).weaken
      (.union .empty (.singleton (.var 0))) := by
  apply Tm.Ty.sub
  · simpa [functionType, functionShape] using innerValueTyping
  · exact .refl
  · exact .empty
  · simpa [functionType, functionShape] using
      (functionTypeWf (Gamma := Ctx.nil.snoc (pureTop 0)))
  · exact .union .empty (.singleton .var)

private def valueSourceTyping :
    Tm.Ty Ctx.nil value (sourceType 0) .empty :=
  .abs outerBodyTyping pureTopWf .empty

def valueIntersectionTyping :
    Tm.Ty Ctx.nil value (intersectionType 0) .empty :=
  .sub valueSourceTyping sourceToIntersection .refl intersectionTypeWf .empty

/-- The bound path is used through the left projection `F -> F`. -/
def functionViewTyping :
    Tm.Ty context (.path (.var 0)) (leftView 1) .empty :=
  .sub
    (.path .var)
    (.capt (.path .var)
      (.trans (.singleton_widen .var) .inter_left))
    (.path .var)
    leftViewWf
    .empty

/-- The same bound path is used through the right projection `F`. -/
def argumentViewTyping :
    Tm.Ty context (.path (.var 0)) (rightView 1) .empty :=
  .sub
    (.path .var)
    (.capt (.path .var)
      (.trans (.singleton_widen .var) .inter_right))
    (.path .var)
    rightViewWf
    .empty

private def bodyTyping :
    Tm.Ty context body (functionType 1) .empty := by
  apply Tm.Ty.sub
  · simpa [body, leftView, leftViewShape, rightView, rightViewShape,
      functionType, functionShape, Ty.weaken_open] using
      Tm.Ty.app functionViewTyping argumentViewTyping
  · exact .refl
  · exact .union_elim .empty .empty
  · exact functionTypeWf
  · exact .empty

def term_typing :
    Tm.Ty Ctx.nil term (functionType 0) .empty :=
  .let valueIntersectionTyping bodyTyping functionTypeWf .empty

theorem term_type_safety
    {n : Nat} {target : State n}
    (steps : State.Steps (State.initial term) target) :
    State.Progress target :=
  term_typing.closed_type_safety steps

end

end LambdaPCCI.IntersectionRegression
