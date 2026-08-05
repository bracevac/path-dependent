import LambdaPCC.Typing
import LambdaPCC.StaticMetatheory

/-!
Small static regressions for capture-set members, capture-dependent types, and
the root accounting of term paths.
-/

namespace LambdaPCC.CaptureRegression

noncomputable section

def captureLabel : Name := 0
def termLabel : Name := 1

/-! ## Exact and abstract capture-set members -/

def firstType : Ty 0 := .capt .empty .Top

/-- The capture-set member is exactly the pair's dependent first component. -/
def receiverType : Ty 0 :=
  .capt .empty
    (.Pair firstType captureLabel
      (.capture
        (.singleton (.var 0))
        (.singleton (.var 0))))

def receiverContext : Ctx 1 := Ctx.nil.snoc receiverType
def receiver : Path 1 := .var 0

def exact_capture_member :
    Path.Ty receiverContext (receiver.sel captureLabel)
      (.capture
        (.singleton receiver.fst)
        (.singleton receiver.fst)) := by
  have hreceiver :
      Path.Ty receiverContext receiver (.term receiverType.weaken) := by
    unfold receiverContext receiver
    exact .var
  simpa [receiverType, firstType, captureLabel, receiver, Ty.weaken,
    Shape.rename, Tau.rename, CaptureSet.rename, Path.rename, Tau.open,
    Tau.subst, CaptureSet.subst, Path.subst, PathSubst.openAt] using
    Path.Ty.sel_r hreceiver

def capture_member_lower :
    CaptureSet.Sub receiverContext
      (.singleton receiver.fst)
      (.select receiver captureLabel) :=
  .select_lower exact_capture_member .refl

def capture_member_upper :
    CaptureSet.Sub receiverContext
      (.select receiver captureLabel)
      (.singleton receiver.fst) :=
  .select_upper exact_capture_member .refl

/-! ## Pair covariance at capture-set-member kind -/

def pairSource : Shape 0 :=
  .Pair firstType captureLabel
    (.capture
      (.singleton (.var 0))
      (.singleton (.var 0)))

def pairTarget : Shape 0 :=
  .Pair firstType captureLabel
    (.capture
      .empty
      (.singleton (.var 0)))

/-- The member comparison is checked under the source first-component type. -/
def capture_pair_covariance :
    Shape.Sub .nil pairSource pairTarget :=
  .pair .refl (.capture .empty .refl .refl)

/-! ## Capture-dependent function results -/

/-- A codomain whose capture set mentions both a projection of its argument
and a term selection rooted at that projection. -/
def dependentCodomain (n : Nat) : Ty (n + 1) :=
  .capt
    (.union
      (.singleton (.fst (.var 0)))
      (.singleton (.sel (.fst (.var 0)) termLabel)))
    .Top

theorem dependent_codomain_beta (q : Path n) :
    (dependentCodomain n).open q =
      .capt
        (.union
          (.singleton q.fst)
          (.singleton (q.fst.sel termLabel)))
        .Top := by
  rfl

/-- Application opens the dependent capture set with the caller's argument
path and combines the uses of the function and argument paths. -/
def application_opens_capture
    {Gamma : Ctx n} {p q : Path n} {S : Ty n}
    {Cf Cp Cq : CaptureSet n}
    (hfun : Tm.Ty Gamma (.path p)
      (.capt Cf (.Fun S (dependentCodomain n))) Cp)
    (harg : Tm.Ty Gamma (.path q) S Cq) :
    Tm.Ty Gamma (.app p q)
      (.capt
        (.union
          (.singleton q.fst)
          (.singleton (q.fst.sel termLabel)))
        .Top)
      (.union Cp Cq) := by
  simpa only [dependent_codomain_beta] using Tm.Ty.app hfun harg

/-! ## Roots of term paths -/

def first_projection_contracts
    (h : Path.Ty Gamma p.fst (.term T)) :
    CaptureSet.Sub Gamma (.singleton p.fst) (.singleton p) :=
  .fst_root h

def term_selection_contracts
    (h : Path.Ty Gamma (p.sel a) (.term T)) :
    CaptureSet.Sub Gamma (.singleton (p.sel a)) (.singleton p) :=
  .sel_root h

/-!
There is deliberately no corresponding root-contraction rule from the
abstract capture-set selection `CaptureSet.select p a` to the owner path
`p`. Abstract capture-set members participate in subcapturing only through their
declared lower and upper bounds.
-/

end
end LambdaPCC.CaptureRegression
