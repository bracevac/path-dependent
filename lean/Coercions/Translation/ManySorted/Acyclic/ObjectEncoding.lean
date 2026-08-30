import Coercions.ManySortedFC.TermChecker
import Coercions.Translation.ManySorted.StaticSlot

/-!
# Two-member acyclic object encoding

This module fixes the source-independent target convention for one acyclic
object carrying an abstract type member, an abstract capture member, and one
value payload.  The local theory always allocates both names first and then
exactly four independent directed-inclusion assumptions.  It deliberately
contains no endpoint-consistency proposition.
-/

namespace DOTCaptureToManySortedFC.Acyclic.ObjectEncoding

open ManySortedFC

/-! ## Fixed telescope shape -/

/-- The type name is newest and the capture name is the older symbol. -/
abbrev symbols : List StaticSort := [.type, .capture]

/-- Evidence order, newest first: `L ≤ α`, `α ≤ U`, `D ≤ χ`, `χ ≤ E`. -/
abbrev relations : List Relation :=
  [.inclusion .type, .inclusion .type,
    .inclusion .capture, .inclusion .capture]

abbrev SymbolScope (scope : Sig) : Sig :=
  ManySortedFC.SymbolScope scope symbols

abbrev StaticScope (scope : Sig) : Sig :=
  ManySortedFC.StaticScope scope symbols relations

abbrev PayloadScope (scope : Sig) : Sig :=
  ManySortedFC.PayloadScope scope symbols relations

/-- The four ambient endpoints of the two true intervals. -/
structure Bounds (scope : Sig) where
  typeLower : Ty scope
  typeUpper : Ty scope
  captureLower : Capture scope
  captureUpper : Capture scope
deriving DecidableEq

/-- Move ambient endpoints below the two generated names. -/
def symbolWeakening {scope : Sig} : Rename scope (SymbolScope scope) :=
  Rename.weakenSymbols symbols

/-- Move ambient syntax below the names and all four assumptions. -/
def staticWeakening {scope : Sig} : Rename scope (StaticScope scope) :=
  Rename.weakenStatic symbols relations

/-! ## Intrinsically sorted name coordinates -/

def alphaSymbolName {scope : Sig} :
    BVar (SymbolScope scope) (.symbol .type) :=
  .here

def chiSymbolName {scope : Sig} :
    BVar (SymbolScope scope) (.symbol .capture) :=
  .there .here

def alphaSymbol {scope : Sig} : StaticExpr .type (SymbolScope scope) :=
  StaticExpr.symbol alphaSymbolName

def chiSymbol {scope : Sig} : StaticExpr .capture (SymbolScope scope) :=
  StaticExpr.symbol chiSymbolName

def alphaStaticName {scope : Sig} :
    BVar (StaticScope scope) (.symbol .type) :=
  (Rename.weakenMany (SymbolScope scope)
    (evidenceKinds relations)).var alphaSymbolName

def chiStaticName {scope : Sig} :
    BVar (StaticScope scope) (.symbol .capture) :=
  (Rename.weakenMany (SymbolScope scope)
    (evidenceKinds relations)).var chiSymbolName

def alphaStatic {scope : Sig} : StaticExpr .type (StaticScope scope) :=
  StaticExpr.symbol alphaStaticName

def chiStatic {scope : Sig} : StaticExpr .capture (StaticScope scope) :=
  StaticExpr.symbol chiStaticName

def alphaPayloadName {scope : Sig} :
    BVar (PayloadScope scope) (.symbol .type) :=
  .there alphaStaticName

def chiPayloadName {scope : Sig} :
    BVar (PayloadScope scope) (.symbol .capture) :=
  .there chiStaticName

def alphaPayload {scope : Sig} : StaticExpr .type (PayloadScope scope) :=
  StaticExpr.symbol alphaPayloadName

def chiPayload {scope : Sig} : StaticExpr .capture (PayloadScope scope) :=
  StaticExpr.symbol chiPayloadName

/-! ## Exact proof and payload coordinates -/

/-- Coordinate of `L ≤ α` (the newest exported assumption). -/
def typeLowerEvidence {scope : Sig} :
    BVar (StaticScope scope) (.evidence (.inclusion .type)) :=
  .here

/-- Coordinate of `α ≤ U`. -/
def typeUpperEvidence {scope : Sig} :
    BVar (StaticScope scope) (.evidence (.inclusion .type)) :=
  .there .here

/-- Coordinate of `D ≤ χ`. -/
def captureLowerEvidence {scope : Sig} :
    BVar (StaticScope scope) (.evidence (.inclusion .capture)) :=
  .there (.there .here)

/-- Coordinate of `χ ≤ E` (the oldest exported assumption). -/
def captureUpperEvidence {scope : Sig} :
    BVar (StaticScope scope) (.evidence (.inclusion .capture)) :=
  .there (.there (.there .here))

/-- Opening adds exactly one ordinary payload binder after the complete
static block.  It is deliberately not reused as either static coordinate. -/
def payloadTerm {scope : Sig} : BVar (PayloadScope scope) .term :=
  .here

/-- Reusable slot for the abstract type member. -/
def alphaSlot {scope : Sig} :
    ManySortedTranslation.StaticSlot (StaticScope scope) .type where
  name := alphaStaticName
  lower := some typeLowerEvidence
  upper := some typeUpperEvidence

/-- Reusable slot for the abstract capture member. -/
def chiSlot {scope : Sig} :
    ManySortedTranslation.StaticSlot (StaticScope scope) .capture where
  name := chiStaticName
  lower := some captureLowerEvidence
  upper := some captureUpperEvidence

/-! ## Theory and representation types -/

private def ambientTypeEndpoint {scope : Sig} (type : Ty scope) :
    StaticExpr .type (SymbolScope scope) :=
  .type (type.rename symbolWeakening)

private def ambientCaptureEndpoint {scope : Sig} (capture : Capture scope) :
    StaticExpr .capture (SymbolScope scope) :=
  .capture (capture.rename symbolWeakening)

/-- The complete two-name theory.  The constructor has exactly four fields;
there is no fifth proposition asking whether either interval is consistent. -/
def theory {scope : Sig} (bounds : Bounds scope) :
    Theory scope symbols relations :=
  .cons (.inclusion (ambientTypeEndpoint bounds.typeLower) alphaSymbol)
    (.cons (.inclusion alphaSymbol
      (ambientTypeEndpoint bounds.typeUpper))
      (.cons (.inclusion (ambientCaptureEndpoint bounds.captureLower)
        chiSymbol)
        (.cons (.inclusion chiSymbol
          (ambientCaptureEndpoint bounds.captureUpper)) .nil)))

/-- Runtime representation under the opened names: the payload has abstract
shape `α` and retained capture `χ`. -/
def payloadType {scope : Sig} : Ty (StaticScope scope) :=
  .capturing (.cvar chiStaticName) (.tvar alphaStaticName)

/-- The payload type as seen below the additional ordinary open binder. -/
def payloadTypeOpened {scope : Sig} : Ty (PayloadScope scope) :=
  (payloadType (scope := scope)).weaken

/-- Positive shape of a first-class object, before its ambient closure is
made explicit. -/
def existentialShape {scope : Sig} (bounds : Bounds scope) : Ty scope :=
  .existsT (theory bounds) payloadType

/-- A first-class object retains exactly the declared upper capture `E`.
This annotation is not another relation in the local theory. -/
def objectType {scope : Sig} (bounds : Bounds scope) : Ty scope :=
  .capturing bounds.captureUpper (existentialShape bounds)

/-- Body of the negative encoding after the model has been opened. -/
def negativeConsumerBody {scope : Sig} (result : Ty scope) :
    Ty (StaticScope scope) :=
  .arr payloadType (result.rename staticWeakening)

/-- Negative occurrence of the interface: universally receive one model and
then consume its representation. -/
def negativeConsumer {scope : Sig} (bounds : Bounds scope)
    (result : Ty scope) : Ty scope :=
  .forallT (theory bounds) (negativeConsumerBody result)

/-! ## Model arguments and term helpers -/

/-- Simultaneous witnesses in the fixed heterogeneous symbol order. -/
def symbolArguments {scope : Sig} (typeWitness : Ty scope)
    (captureWitness : Capture scope) : SymbolArgs scope symbols :=
  .cons (.type typeWitness) (.cons (.capture captureWitness) .nil)

/-- Certificates in the exact exported-assumption order. -/
def evidenceArguments {scope : Sig}
    (typeLower typeUpper : Evidence (.inclusion .type) scope)
    (captureLower captureUpper : Evidence (.inclusion .capture) scope) :
    EvidenceArgs scope relations :=
  .cons typeLower (.cons typeUpper
    (.cons captureLower (.cons captureUpper .nil)))

/-- Explicitly retag an already-typed payload with the chosen abstract
capture and type witnesses.  Both logical premises remain caller supplied. -/
def retagPayload {scope : Sig} (payload : Tm scope)
    (sourceType : Ty scope) (typeWitness : Ty scope)
    (captureWitness : Capture scope)
    (captures : Evidence (.inclusion .capture) scope)
    (shape : Evidence (.inclusion .type) scope) : Tm scope :=
  .adapt payload
    (.retagCapture sourceType captureWitness typeWitness captures shape)

/-- Package one object model.  The fourth bound certificate is reused at the
erasing package boundary to cover the adapted payload's retained `χ` by the
object's ambient closure `E`. -/
def pack {scope : Sig} (bounds : Bounds scope)
    (typeWitness : Ty scope) (captureWitness : Capture scope)
    (typeLower typeUpper : Evidence (.inclusion .type) scope)
    (captureLower captureUpper : Evidence (.inclusion .capture) scope)
    (payload : Tm scope) (payloadSourceType : Ty scope)
    (payloadCaptures : Evidence (.inclusion .capture) scope)
    (payloadShape : Evidence (.inclusion .type) scope) : Tm scope :=
  .pack (theory bounds) payloadType bounds.captureUpper
    (symbolArguments typeWitness captureWitness)
    (evidenceArguments typeLower typeUpper captureLower captureUpper)
    (retagPayload payload payloadSourceType typeWitness captureWitness
      payloadCaptures payloadShape)
    captureUpper

/-- Open one object package once.  All uses of `α`, `χ`, their four proofs,
and the payload term in `body` share this single generated scope. -/
def openOnce {scope : Sig} (bounds : Bounds scope)
    (result : Ty scope) (bodyOuterUse : Capture scope)
    (package : Tm scope) (body : Tm (PayloadScope scope))
    (discharge : Evidence (.inclusion .capture) (PayloadScope scope)) :
    Tm scope :=
  .«open» (theory bounds) payloadType result bodyOuterUse package body
    discharge

/-! ## Structural regressions -/

theorem relation_count_is_four : relations.length = 4 := rfl

theorem alpha_and_chi_sorts_are_distinct :
    StaticSort.type ≠ StaticSort.capture := by
  decide

theorem alpha_symbol_shape {scope : Sig} :
    alphaSymbol (scope := scope) = .type (.tvar .here) := rfl

theorem chi_symbol_shape {scope : Sig} :
    chiSymbol (scope := scope) = .capture (.cvar (.there .here)) := rfl

theorem object_closure_is_upper_capture {scope : Sig}
    (bounds : Bounds scope) :
    (objectType bounds).outerCapture = bounds.captureUpper := rfl

theorem payload_is_one_separate_term_binder {scope : Sig} :
    payloadTerm (scope := scope) = (.here : BVar (PayloadScope scope) .term) :=
  rfl

/-! ## Exact realizable object -/

def exactBounds : Bounds [] where
  typeLower := .one
  typeUpper := .one
  captureLower := .empty
  captureUpper := .empty

def exactSymbols : SymbolArgs [] symbols :=
  symbolArguments .one .empty

def exactEvidence : EvidenceArgs [] relations :=
  evidenceArguments
    (.inclusionRefl (.type .one))
    (.inclusionRefl (.type .one))
    (.inclusionRefl (.capture .empty))
    (.inclusionRefl (.capture .empty))

theorem exact_one_empty_model_is_accepted :
    (Theory.checkModel Ctx.nil (theory exactBounds)
      exactSymbols exactEvidence).isSome = true := by
  native_decide

/-- `unit` is explicitly retagged to the representation type
`One^{∅}` before packaging. -/
def exactPackage : Tm [] :=
  pack exactBounds .one .empty
    (.inclusionRefl (.type .one))
    (.inclusionRefl (.type .one))
    (.inclusionRefl (.capture .empty))
    (.inclusionRefl (.capture .empty))
    .unit .one
    (.captureEmpty .empty)
    (.inclusionRefl (.type .one))

theorem exact_package_is_accepted :
    Tm.synth Ctx.nil exactPackage =
      some (.empty, objectType exactBounds) := by
  native_decide

/-- A concrete open crosses one complete static scope and adds one payload
binder.  The body ignores the payload operationally, but its annotation and
discharge are checked in `PayloadScope []`. -/
def exactOpenOnce : Tm [] :=
  openOnce exactBounds .one .empty exactPackage .unit
    (.captureEmpty (.union .empty (.singleton payloadTerm)))

theorem exact_open_once_is_accepted :
    Tm.synth Ctx.nil exactOpenOnce =
      some (.union .empty .empty, .one) := by
  native_decide

/-! ## Bad open theory versus fabricated ambient model -/

abbrev BadScope : Sig := ([] : Sig) ▹ .term

def badContext : Ctx BadScope :=
  Ctx.nil.extendTerm .one

def badCapability : Capture BadScope :=
  .singleton .here

def badBounds : Bounds BadScope where
  typeLower := .top
  typeUpper := .bot
  captureLower := badCapability
  captureUpper := .empty

abbrev BadOpenScope : Sig := StaticScope BadScope

def badOpenContext : Ctx BadOpenScope :=
  badContext.extendTheory (theory badBounds)

def badCapabilityOpened : Capture BadOpenScope :=
  badCapability.rename staticWeakening

def badTypeCollapse : Evidence (.inclusion .type) BadOpenScope :=
  .inclusionTrans (.var typeLowerEvidence) (.var typeUpperEvidence)

def badCaptureCollapse : Evidence (.inclusion .capture) BadOpenScope :=
  .inclusionTrans (.var captureLowerEvidence) (.var captureUpperEvidence)

def badTypeCollapseProposition : Proposition (.inclusion .type)
    BadOpenScope :=
  .inclusion (.type .top) (.type .bot)

def badCaptureCollapseProposition : Proposition (.inclusion .capture)
    BadOpenScope :=
  .inclusion (.capture badCapabilityOpened) (.capture .empty)

theorem bad_open_type_assumptions_compose :
    (Evidence.check badOpenContext badTypeCollapse).map
        (fun checked => checked.proposition) =
      some badTypeCollapseProposition := by
  native_decide

theorem bad_open_capture_assumptions_compose :
    (Evidence.check badOpenContext badCaptureCollapse).map
        (fun checked => checked.proposition) =
      some badCaptureCollapseProposition := by
  native_decide

def fabricatedSymbols : SymbolArgs BadScope symbols :=
  symbolArguments .top badCapability

/-- These certificates merely repeat reflexivity at the chosen witnesses;
they cannot prove either bad upper endpoint in the ambient context. -/
def fabricatedEvidence : EvidenceArgs BadScope relations :=
  evidenceArguments
    (.inclusionRefl (.type .top))
    (.inclusionRefl (.type .top))
    (.inclusionRefl (.capture badCapability))
    (.inclusionRefl (.capture badCapability))

theorem fabricated_bad_model_is_rejected :
    (Theory.checkModel badContext (theory badBounds)
      fabricatedSymbols fabricatedEvidence).isNone = true := by
  native_decide

end DOTCaptureToManySortedFC.Acyclic.ObjectEncoding
