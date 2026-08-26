import SystemFCo.ChurchPackageCovariance
import SystemFCo.Safety
import SystemFCo.Operational

/-!
# Closed Church-package regression

This example packages the identity function behind the exact witness
`Top -> Top`, converts the package to a wider interval and payload with the
object-language coercion `Co.member`, and then eliminates the converted
package.  In particular, the conversion is not a metatheoretic shortcut:
`convertedPackage` is an `Exp.cast` containing the structural package
coercion.
-/

namespace SystemFCo.ChurchPackageRegression

open SystemFCo

def arrowTop : Ty {} :=
  .arrow .top .top

/-- A proper subtype of `arrowTop`, used as the widened package's lower
bound. -/
def deeperArrow : Ty {} :=
  .arrow .top arrowTop

def sourcePayload : Ty ({} ,, .tvar) :=
  arrowTop.weaken .tvar

def targetPayload : Ty ({} ,, .tvar) :=
  .top

def identity : Exp {} :=
  .abs .top (.var .here)

def identityTyping :
    Ctx.empty |-e identity : arrowTop :=
  .abs (.var .here)

/-- `deeperArrow => arrowTop`, using covariance of the result. -/
def lowerAdapter : Co {} :=
  .arrow (.refl .top) (.top arrowTop)

def lowerAdapterTyping :
    Ctx.empty |-c lowerAdapter : deeperArrow => arrowTop :=
  .arrow .refl .top

/-- `arrowTop => Top`, widening the upper endpoint. -/
def upperAdapter : Co {} :=
  .top arrowTop

def upperAdapterTyping :
    Ctx.empty |-c upperAdapter : arrowTop => .top :=
  .top

/-- The payload family changes from the constant `Top -> Top` family to the
constant `Top` family. -/
def payloadAdapter : Co ({} ,, .tvar) :=
  .top (arrowTop.weaken .tvar)

def payloadAdapterTyping :
    Ctx.empty.bindTVar |-c payloadAdapter :
      sourcePayload => targetPayload :=
  .top

/-- The actual structural package coercion.  Its expansion contains
`poly`, `arrow`, two nested `qual` coercions, and the three adapters above. -/
def packageAdapter : Co {} :=
  Co.member lowerAdapter upperAdapter payloadAdapter

noncomputable def packageAdapterTyping :
    Ctx.empty |-c packageAdapter :
      Ty.member arrowTop arrowTop sourcePayload =>
      Ty.member deeperArrow .top targetPayload :=
  Co.HasType.member lowerAdapterTyping upperAdapterTyping
    payloadAdapterTyping

/-- An exact package whose hidden witness and both interval endpoints are
`Top -> Top`; its payload is the identity function. -/
def exactPackage : Exp {} :=
  Exp.packMember arrowTop arrowTop arrowTop sourcePayload
    (.refl arrowTop) (.refl arrowTop) identity

noncomputable def exactPackageTyping :
    Ctx.empty |-e exactPackage :
      Ty.member arrowTop arrowTop sourcePayload :=
  Exp.HasType.packMember .refl .refl identityTyping

/-- Package conversion happens through a genuine target-language cast. -/
def convertedPackage : Exp {} :=
  .cast exactPackage packageAdapter

noncomputable def convertedPackageTyping :
    Ctx.empty |-e convertedPackage :
      Ty.member deeperArrow .top targetPayload :=
  .cast exactPackageTyping packageAdapterTyping

/-- The consumer returns the converted payload, now viewed at `Top`. -/
def consumer : Exp {} :=
  Exp.memberHandler deeperArrow .top targetPayload (.var .here)

noncomputable def consumerTyping :
    Ctx.empty |-e consumer :
      Ty.memberHandler deeperArrow .top .top targetPayload :=
  Exp.HasType.memberHandler (.var .here)

def program : Exp {} :=
  Exp.unpackMember convertedPackage .top consumer

noncomputable def programTyping :
    Ctx.empty |-e program : (.top : Ty {}) :=
  Exp.HasType.unpackMember convertedPackageTyping consumerTyping

theorem programSound :
    Not (Exp.GoesWrong program) :=
  Exp.soundness programTyping

/-! ## A concrete administrative prefix

The following named subterms are definitionally the corresponding pieces of
`Co.member`, `packMember`, and `memberHandler`.  Their shape equations ensure
that none of the operational proof below can select a fallback branch. -/

def packageAdapterBody : Co ({} ,, .tvar) :=
  match packageAdapter with
  | .poly body => body
  | _ => .refl .top

def instantiatedPackageAdapter : Co {} :=
  packageAdapterBody.subst (Subst.openTVar .top)

def packageHandlerAdapter : Co {} :=
  match instantiatedPackageAdapter with
  | .arrow parameter _ => parameter
  | _ => .refl .top

def packageResultAdapter : Co {} :=
  match instantiatedPackageAdapter with
  | .arrow _ result => result
  | _ => .refl .top

def exactPackageBody : Exp ({} ,, .tvar) :=
  match exactPackage with
  | .tabs body => body
  | _ => .abs .top (.var .here)

def instantiatedExactPackageBody : Exp {} :=
  exactPackageBody.subst (Subst.openTVar .top)

theorem packageAdapterShape :
    packageAdapter = .poly packageAdapterBody := rfl

theorem instantiatedPackageAdapterShape :
    instantiatedPackageAdapter =
      .arrow packageHandlerAdapter packageResultAdapter := rfl

theorem exactPackageShape :
    exactPackage = .tabs exactPackageBody := rfl

def afterOuterPoly : Exp {} :=
  .app
    (.cast (.tapp exactPackage .top) instantiatedPackageAdapter)
    consumer

def afterPackageTypeBeta : Exp {} :=
  .app
    (.cast instantiatedExactPackageBody instantiatedPackageAdapter)
    consumer

def afterOuterArrow : Exp {} :=
  .cast
    (.app instantiatedExactPackageBody
      (.cast consumer packageHandlerAdapter))
    packageResultAdapter

theorem outerPolyStep : Exp.Step program afterOuterPoly := by
  exact .appFunction (.castPolyTapp .tabs)

theorem packageTypeBetaStep :
    Exp.Step afterOuterPoly afterPackageTypeBeta := by
  exact .appFunction (.castExpression .typeBeta)

theorem outerArrowStep :
    Exp.Step afterPackageTypeBeta afterOuterArrow := by
  exact .castArrowApp .abs .tabs

/-! The handler adapter selected by the arrow cast is itself polymorphic and
starts with the lower-bound qualifier generated by `Co.member`. -/

def packageHandlerAdapterBody : Co ({} ,, .tvar) :=
  match packageHandlerAdapter with
  | .poly body => body
  | _ => .refl .top

def instantiatedHandlerAdapter : Co {} :=
  packageHandlerAdapterBody.subst (Subst.openTVar arrowTop)

def consumerBody : Exp ({} ,, .tvar) :=
  match consumer with
  | .tabs body => body
  | _ => .abs .top (.var .here)

def instantiatedConsumerBody : Exp {} :=
  consumerBody.subst (Subst.openTVar arrowTop)

theorem packageHandlerAdapterShape :
    packageHandlerAdapter = .poly packageHandlerAdapterBody := rfl

theorem consumerShape :
    consumer = .tabs consumerBody := rfl

def beforeHandlerPoly : Exp {} :=
  .tapp (.cast consumer packageHandlerAdapter) arrowTop

def afterHandlerPoly : Exp {} :=
  .cast (.tapp consumer arrowTop) instantiatedHandlerAdapter

def afterHandlerTypeBeta : Exp {} :=
  .cast instantiatedConsumerBody instantiatedHandlerAdapter

theorem handlerPolyStep :
    Exp.Step beforeHandlerPoly afterHandlerPoly := by
  exact .castPolyTapp .tabs

theorem handlerTypeBetaStep :
    Exp.Step afterHandlerPoly afterHandlerTypeBeta := by
  exact .castExpression .typeBeta

def lowerEvidenceAdapter : Co ({} ,, .cvar) :=
  match instantiatedHandlerAdapter with
  | .qual argument _ => argument
  | _ => .refl .top

def remainingHandlerAdapter : Co ({} ,, .cvar) :=
  match instantiatedHandlerAdapter with
  | .qual _ result => result
  | _ => .refl .top

theorem instantiatedHandlerAdapterShape :
    instantiatedHandlerAdapter =
      .qual lowerEvidenceAdapter remainingHandlerAdapter := rfl

def suppliedLowerEvidence : Co {} :=
  .refl arrowTop

def afterLowerQual : Exp {} :=
  .cast
    (.capp instantiatedConsumerBody
      (lowerEvidenceAdapter.subst
        (Subst.openCVar suppliedLowerEvidence)))
    (remainingHandlerAdapter.subst
      (Subst.openCVar suppliedLowerEvidence))

theorem lowerQualStep :
    Exp.Step (.capp afterHandlerTypeBeta suppliedLowerEvidence)
      afterLowerQual := by
  exact .castQualCapp .cabs

/-- The invocation context used by the exact package after its Church
function receives the converted consumer. -/
def packageInvocationAtWitness (atWitness : Exp {}) : Exp {} :=
  .cast
    (.app
      (.capp (.capp atWitness suppliedLowerEvidence)
        suppliedLowerEvidence)
      identity)
    packageResultAdapter

def afterPackageApplication : Exp {} :=
  packageInvocationAtWitness beforeHandlerPoly

theorem packageApplicationBetaStep :
    Exp.Step afterOuterArrow afterPackageApplication := by
  exact .castExpression (.beta (.castPoly .tabs))

def afterNestedHandlerPoly : Exp {} :=
  packageInvocationAtWitness afterHandlerPoly

theorem nestedHandlerPolyStep :
    Exp.Step afterPackageApplication afterNestedHandlerPoly := by
  exact .castExpression
    (.appFunction (.cappFunction (.cappFunction handlerPolyStep)))

def afterNestedHandlerTypeBeta : Exp {} :=
  packageInvocationAtWitness afterHandlerTypeBeta

theorem nestedHandlerTypeBetaStep :
    Exp.Step afterNestedHandlerPoly afterNestedHandlerTypeBeta := by
  exact .castExpression
    (.appFunction (.cappFunction (.cappFunction handlerTypeBetaStep)))

def afterNestedLowerQual : Exp {} :=
  .cast
    (.app (.capp afterLowerQual suppliedLowerEvidence) identity)
    packageResultAdapter

theorem nestedLowerQualStep :
    Exp.Step afterNestedHandlerTypeBeta afterNestedLowerQual := by
  exact .castExpression (.appFunction (.cappFunction lowerQualStep))

/-- Seven real target steps from the closed unpacking program.  The prefix
pushes the outer package `poly` cast, beta-reduces the Church package, pushes
the handler's `poly` cast, and finally pushes the first `qual` cast while
adapting the supplied lower-bound coercion. -/
theorem administrationPrefix :
    Exp.Steps program afterNestedLowerQual :=
  .tail outerPolyStep
    (.tail packageTypeBetaStep
      (.tail outerArrowStep
        (.tail packageApplicationBetaStep
          (.tail nestedHandlerPolyStep
            (.tail nestedHandlerTypeBetaStep
              (.tail nestedLowerQualStep .refl))))))

end SystemFCo.ChurchPackageRegression
