import DotFC.Source.Runtime

/-!
# Checked source regressions

These examples exercise the source rules that matter most for the later
coercion elaborations: explicit bad-bound provenance, dependent codomains,
independently justified object bounds, and erased execution.
-/

namespace DotFC.Source.Examples

/-- The label used by the one-member examples. -/
def A : Name := 0

/-! ## Bad bounds remain explicit -/

/-- An open context whose newest variable has the deliberately uninhabited
view `{ A : ⊤ .. ⊥ }`. -/
def badBoundsContext : Ctx ([] ▹ .term) :=
  Ctx.nil.snoc (.member A .top .bot)

/-- The member is exposed once.  Both selection coercions below reuse this
same handle value. -/
def badBoundsHandle :
    Handle badBoundsContext (.here : BVar ([] ▹ .term) .term) A .top .bot :=
  .direct .here

/-- The lower-bound half of the bad-bounds derivation. -/
def badBoundsLower : Sub badBoundsContext .top (.sel .here A) :=
  .lower badBoundsHandle

/-- The upper-bound half of the bad-bounds derivation. -/
def badBoundsUpper : Sub badBoundsContext (.sel .here A) .bot :=
  .upper badBoundsHandle

/-- Bad bounds are not hidden in an oracle: the derivation is visibly the
composition `lower ; upper` through one reusable exposure handle. -/
def badBounds : Sub badBoundsContext .top .bot :=
  .trans badBoundsLower badBoundsUpper

/-! ## A dependent function returning the argument's member type -/

/-- A closed, well-formed member interface with nonempty bounds. -/
def dependentDomain : Ty [] := .member A .bot .top

def dependentDomainWf : Wf Ctx.nil dependentDomain :=
  .member .bot .top

/-- `λx:{A:⊥..⊤}. λy:⊥. y`. -/
def dependentFunction : Tm [] :=
  .lam dependentDomain (.lam .bot (.var .here))

/-- The dependent result type mentions the outer parameter through the stable
path `there here`. -/
def dependentFunctionType : Ty [] :=
  .all dependentDomain (.all .bot (.sel (.there .here) A))

private def xMemberHandle :
    Handle
      ((Ctx.nil.snoc dependentDomain).snoc (.bot : Ty ([] ▹ .term)))
      (.there .here : BVar (([] ▹ .term) ▹ .term) .term)
      A .bot .top :=
  .direct (.there .here)

private def dependentBodyTyping :
    HasTy
      ((Ctx.nil.snoc dependentDomain).snoc (.bot : Ty ([] ▹ .term)))
      (.var (.here : BVar (([] ▹ .term) ▹ .term) .term))
      (.sel (.there .here) A) :=
  .sub (.var .here) (.lower xMemberHandle) (.sel xMemberHandle)

/-- Fully checked typing of the dependent function. -/
def dependentFunctionTyping :
    HasTy Ctx.nil dependentFunction dependentFunctionType :=
  .lam dependentDomainWf (.lam .bot dependentBodyTyping)

/-! ## Exact introduction, then abstraction with independent bounds -/

/-- A concrete exact object `{ A = ⊥ }`. -/
def exactObject : Tm [] := .obj A .bot

def exactObjectTyping :
    HasTy Ctx.nil exactObject (.member A .bot .bot) :=
  .obj .bot

/-- Independent evidence that the abstract lower bound lies below the exact
witness. -/
def exactLowerEvidence : Sub Ctx.nil .bot .bot :=
  .refl .bot

/-- Independent evidence that the exact witness lies below the abstract upper
bound. -/
def exactUpperEvidence : Sub Ctx.nil .bot .top :=
  .top .bot

def exactToAbstract :
    Sub Ctx.nil (.member A .bot .bot) (.member A .bot .top) :=
  .member exactLowerEvidence exactUpperEvidence

/-- Exact construction can be hidden behind valid abstract bounds only after
both bound derivations have been supplied. -/
def abstractObjectTyping :
    HasTy Ctx.nil exactObject (.member A .bot .top) :=
  .sub exactObjectTyping exactToAbstract (.member .bot .top)

/-! ## Erased execution -/

/-- A source let whose exact type witness disappears at runtime. -/
def erasedObjectLet : Tm [] :=
  .let' (.obj A .top) (.var .here)

/-- Erasure performs an ordinary CBV zeta step.  The runtime object is the
unit-like object tag; neither its label nor exact type witness remains. -/
theorem erasedObjectLet_zeta :
    Runtime.Step erasedObjectLet.erase (.obj : Runtime.Tm []) := by
  exact Runtime.Step.zeta Runtime.IsValue.obj

/-- A direct runtime beta regression, included to pin down full substitution
after erasure. -/
theorem erasedIdentity_beta :
    Runtime.Step
      (.app (.lam (.var .here)) .obj : Runtime.Tm [])
      (.obj : Runtime.Tm []) := by
  exact Runtime.Step.beta Runtime.IsValue.obj

end DotFC.Source.Examples
