import Coercions.Translation.ManySorted.Acyclic.ObjectEncoding

/-!
# Metatheory of the acyclic object encoding

This module records the source-independent structural facts needed by later
DOT elaboration.  Renaming commutes with the fixed two-member encoding, and
opening an object installs one payload binding together with the exact two
symbol and four directed-bound coordinates advertised by `ObjectEncoding`.
-/

namespace DOTCaptureToManySortedFC.Acyclic.ObjectEncoding

open ManySortedFC

namespace Bounds

/-- Rename all four ambient endpoints of an object interface. -/
def rename {source target : Sig} (bounds : Bounds source)
    (rho : Rename source target) : Bounds target where
  typeLower := bounds.typeLower.rename rho
  typeUpper := bounds.typeUpper.rename rho
  captureLower := bounds.captureLower.rename rho
  captureUpper := bounds.captureUpper.rename rho

@[simp]
theorem rename_id {scope : Sig} (bounds : Bounds scope) :
    bounds.rename Rename.id = bounds := by
  cases bounds
  simp [rename]

@[simp]
theorem rename_comp {first second third : Sig} (bounds : Bounds first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (bounds.rename rho₁).rename rho₂ = bounds.rename (rho₁.comp rho₂) := by
  cases bounds
  simp [rename, Ty.rename_comp, Capture.rename_comp]

end Bounds

/-! ## Naturality of the fixed representation -/

private def typeEndpoint {scope : Sig} (type : Ty scope) :
    StaticExpr .type (SymbolScope scope) :=
  .type (type.rename symbolWeakening)

private def captureEndpoint {scope : Sig} (capture : Capture scope) :
    StaticExpr .capture (SymbolScope scope) :=
  .capture (capture.rename symbolWeakening)

private def theoryView {scope : Sig} (bounds : Bounds scope) :
    Theory scope symbols relations :=
  .cons (.inclusion (typeEndpoint bounds.typeLower) alphaSymbol)
    (.cons (.inclusion alphaSymbol (typeEndpoint bounds.typeUpper))
      (.cons (.inclusion (captureEndpoint bounds.captureLower) chiSymbol)
        (.cons (.inclusion chiSymbol
          (captureEndpoint bounds.captureUpper)) .nil)))

private theorem theory_eq_view {scope : Sig} (bounds : Bounds scope) :
    theory bounds = theoryView bounds := rfl

private theorem comp_symbolWeakening {source target : Sig}
    (rho : Rename source target) :
    rho.comp (symbolWeakening (scope := target)) =
      (symbolWeakening (scope := source)).comp
        (rho.liftSymbols symbols) := by
  apply Rename.ext
  intro kind index
  rfl

private theorem alphaSymbol_rename_liftSymbols {source target : Sig}
    (rho : Rename source target) :
    (alphaSymbol (scope := source)).rename (rho.liftSymbols symbols) =
      alphaSymbol (scope := target) := by
  rfl

private theorem chiSymbol_rename_liftSymbols {source target : Sig}
    (rho : Rename source target) :
    (chiSymbol (scope := source)).rename (rho.liftSymbols symbols) =
      chiSymbol (scope := target) := by
  rfl

@[simp]
theorem theory_rename {source target : Sig} (bounds : Bounds source)
    (rho : Rename source target) :
    (theory bounds).rename rho = theory (bounds.rename rho) := by
  rw [theory_eq_view, theory_eq_view]
  simp only [theoryView, Theory.rename, Proposition.rename,
    StaticExpr.rename, typeEndpoint, captureEndpoint, Bounds.rename,
    Ty.rename_comp, Capture.rename_comp]
  rw [comp_symbolWeakening]
  rw [alphaSymbol_rename_liftSymbols, chiSymbol_rename_liftSymbols]

@[simp]
theorem payloadType_rename_liftStatic {source target : Sig}
    (rho : Rename source target) :
    (payloadType (scope := source)).rename
        (rho.liftStatic symbols relations) =
      payloadType (scope := target) := by
  rfl

@[simp]
theorem existentialShape_rename {source target : Sig}
    (bounds : Bounds source) (rho : Rename source target) :
    (existentialShape bounds).rename rho =
      existentialShape (bounds.rename rho) := by
  simp [existentialShape, Ty.rename]

@[simp]
theorem objectType_rename {source target : Sig} (bounds : Bounds source)
    (rho : Rename source target) :
    (objectType bounds).rename rho = objectType (bounds.rename rho) := by
  simp [objectType, Bounds.rename, Ty.rename]

/-! ## The context exposed by one object open -/

/-- Canonical weakening from the ambient scope through the static interface
and its newest payload binder. -/
def payloadWeakening {scope : Sig} : Rename scope (PayloadScope scope) :=
  staticWeakening.comp (Rename.succ (kind := .term))

/-- Context obtained by opening the fixed two-member theory and then adding
its separately represented payload. -/
def openedContext {scope : Sig} (context : Ctx scope)
    (bounds : Bounds scope) : Ctx (PayloadScope scope) :=
  (context.extendTheory (theory bounds)).extendTerm payloadType

/-- Four proof coordinates after weakening below the payload binder. -/
def typeLowerPayloadEvidence {scope : Sig} :
    BVar (PayloadScope scope) (.evidence (.inclusion .type)) :=
  .there typeLowerEvidence

def typeUpperPayloadEvidence {scope : Sig} :
    BVar (PayloadScope scope) (.evidence (.inclusion .type)) :=
  .there typeUpperEvidence

def captureLowerPayloadEvidence {scope : Sig} :
    BVar (PayloadScope scope) (.evidence (.inclusion .capture)) :=
  .there captureLowerEvidence

def captureUpperPayloadEvidence {scope : Sig} :
    BVar (PayloadScope scope) (.evidence (.inclusion .capture)) :=
  .there captureUpperEvidence

/-! Semantic forms of the four exported propositions. -/

def typeLowerPayloadProposition {scope : Sig} (bounds : Bounds scope) :
    Proposition (.inclusion .type) (PayloadScope scope) :=
  .inclusion
    (.type (bounds.typeLower.rename payloadWeakening)) alphaPayload

def typeUpperPayloadProposition {scope : Sig} (bounds : Bounds scope) :
    Proposition (.inclusion .type) (PayloadScope scope) :=
  .inclusion alphaPayload
    (.type (bounds.typeUpper.rename payloadWeakening))

def captureLowerPayloadProposition {scope : Sig} (bounds : Bounds scope) :
    Proposition (.inclusion .capture) (PayloadScope scope) :=
  .inclusion
    (.capture (bounds.captureLower.rename payloadWeakening)) chiPayload

def captureUpperPayloadProposition {scope : Sig} (bounds : Bounds scope) :
    Proposition (.inclusion .capture) (PayloadScope scope) :=
  .inclusion chiPayload
    (.capture (bounds.captureUpper.rename payloadWeakening))

def typeLowerInstalledProposition {scope : Sig}
    (bounds : Bounds scope) :
    Proposition (.inclusion .type) (PayloadScope scope) :=
  (ManySortedTranslation.StaticSlot.exportHead
    (.inclusion (typeEndpoint bounds.typeLower) alphaSymbol)
    [.inclusion .type, .inclusion .capture, .inclusion .capture]).rename
      Rename.succ

def typeUpperInstalledProposition {scope : Sig}
    (bounds : Bounds scope) :
    Proposition (.inclusion .type) (PayloadScope scope) :=
  ((ManySortedTranslation.StaticSlot.exportHead
    (.inclusion alphaSymbol (typeEndpoint bounds.typeUpper))
    [.inclusion .capture, .inclusion .capture]).rename
      (Rename.succ (kind := .evidence (.inclusion .type)))).rename
        (Rename.succ (kind := .term))

def captureLowerInstalledProposition {scope : Sig}
    (bounds : Bounds scope) :
    Proposition (.inclusion .capture) (PayloadScope scope) :=
  (((ManySortedTranslation.StaticSlot.exportHead
    (.inclusion (captureEndpoint bounds.captureLower) chiSymbol)
    [.inclusion .capture]).rename
      (Rename.succ (kind := .evidence (.inclusion .type)))).rename
        (Rename.succ (kind := .evidence (.inclusion .type)))).rename
          (Rename.succ (kind := .term))

def captureUpperInstalledProposition {scope : Sig}
    (bounds : Bounds scope) :
    Proposition (.inclusion .capture) (PayloadScope scope) :=
  ((((ManySortedTranslation.StaticSlot.exportHead
    (.inclusion chiSymbol (captureEndpoint bounds.captureUpper)) []).rename
      (Rename.succ (kind := .evidence (.inclusion .capture)))).rename
        (Rename.succ (kind := .evidence (.inclusion .type)))).rename
          (Rename.succ (kind := .evidence (.inclusion .type)))).rename
            (Rename.succ (kind := .term))

@[simp]
theorem typeLowerInstalledProposition_eq {scope : Sig}
    (bounds : Bounds scope) :
    typeLowerInstalledProposition bounds =
      typeLowerPayloadProposition bounds := by
  simp only [typeLowerInstalledProposition, typeLowerPayloadProposition,
    ManySortedTranslation.StaticSlot.exportHead, typeEndpoint,
    alphaSymbol, alphaPayload, alphaPayloadName, alphaStaticName,
    payloadWeakening, staticWeakening, symbolWeakening,
    Proposition.rename, StaticExpr.rename, Ty.rename_comp]
  rfl

@[simp]
theorem typeUpperInstalledProposition_eq {scope : Sig}
    (bounds : Bounds scope) :
    typeUpperInstalledProposition bounds =
      typeUpperPayloadProposition bounds := by
  simp only [typeUpperInstalledProposition, typeUpperPayloadProposition,
    ManySortedTranslation.StaticSlot.exportHead, typeEndpoint,
    alphaSymbol, alphaPayload, alphaPayloadName, alphaStaticName,
    payloadWeakening, staticWeakening, symbolWeakening,
    Proposition.rename, StaticExpr.rename, Ty.rename_comp]
  rfl

@[simp]
theorem captureLowerInstalledProposition_eq {scope : Sig}
    (bounds : Bounds scope) :
    captureLowerInstalledProposition bounds =
      captureLowerPayloadProposition bounds := by
  simp only [captureLowerInstalledProposition,
    captureLowerPayloadProposition,
    ManySortedTranslation.StaticSlot.exportHead, captureEndpoint,
    chiSymbol, chiPayload, chiPayloadName, chiStaticName,
    payloadWeakening, staticWeakening, symbolWeakening,
    Proposition.rename, StaticExpr.rename, Capture.rename_comp]
  rfl

@[simp]
theorem captureUpperInstalledProposition_eq {scope : Sig}
    (bounds : Bounds scope) :
    captureUpperInstalledProposition bounds =
      captureUpperPayloadProposition bounds := by
  simp only [captureUpperInstalledProposition,
    captureUpperPayloadProposition,
    ManySortedTranslation.StaticSlot.exportHead, captureEndpoint,
    chiSymbol, chiPayload, chiPayloadName, chiStaticName,
    payloadWeakening, staticWeakening, symbolWeakening,
    Proposition.rename, StaticExpr.rename, Capture.rename_comp]
  rfl

/-! ## Exact context lookup -/

@[simp]
theorem lookup_payload {scope : Sig} (context : Ctx scope)
    (bounds : Bounds scope) :
    (openedContext context bounds).lookup payloadTerm =
      Binding.term payloadTypeOpened := by
  rfl

@[simp]
theorem payloadTypeOpened_shape {scope : Sig} :
    payloadTypeOpened (scope := scope) =
      .capturing (.cvar chiPayloadName) (.tvar alphaPayloadName) := by
  rfl

@[simp]
theorem lookup_alpha {scope : Sig} (context : Ctx scope)
    (bounds : Bounds scope) :
    (openedContext context bounds).lookup alphaPayloadName =
      Binding.symbol := by
  rfl

@[simp]
theorem lookup_chi {scope : Sig} (context : Ctx scope)
    (bounds : Bounds scope) :
    (openedContext context bounds).lookup chiPayloadName =
      Binding.symbol := by
  rfl

@[simp]
theorem lookup_typeLower {scope : Sig} (context : Ctx scope)
    (bounds : Bounds scope) :
    (openedContext context bounds).lookup typeLowerPayloadEvidence =
      Binding.evidence (typeLowerPayloadProposition bounds) := by
  rw [← typeLowerInstalledProposition_eq]
  unfold openedContext
  rw [theory_eq_view]
  rfl

@[simp]
theorem lookup_typeUpper {scope : Sig} (context : Ctx scope)
    (bounds : Bounds scope) :
    (openedContext context bounds).lookup typeUpperPayloadEvidence =
      Binding.evidence (typeUpperPayloadProposition bounds) := by
  rw [← typeUpperInstalledProposition_eq]
  unfold openedContext
  rw [theory_eq_view]
  rfl

@[simp]
theorem lookup_captureLower {scope : Sig} (context : Ctx scope)
    (bounds : Bounds scope) :
    (openedContext context bounds).lookup captureLowerPayloadEvidence =
      Binding.evidence (captureLowerPayloadProposition bounds) := by
  rw [← captureLowerInstalledProposition_eq]
  unfold openedContext
  rw [theory_eq_view]
  rfl

@[simp]
theorem lookup_captureUpper {scope : Sig} (context : Ctx scope)
    (bounds : Bounds scope) :
    (openedContext context bounds).lookup captureUpperPayloadEvidence =
      Binding.evidence (captureUpperPayloadProposition bounds) := by
  rw [← captureUpperInstalledProposition_eq]
  unfold openedContext
  rw [theory_eq_view]
  rfl

/-! ## Direct proof terms for later member compilation -/

def provesTypeLower {scope : Sig} (context : Ctx scope)
    (bounds : Bounds scope) :
    Evidence.Proves (openedContext context bounds)
      (.var typeLowerPayloadEvidence)
      (typeLowerPayloadProposition bounds) :=
  .var (lookup_typeLower context bounds)

def provesTypeUpper {scope : Sig} (context : Ctx scope)
    (bounds : Bounds scope) :
    Evidence.Proves (openedContext context bounds)
      (.var typeUpperPayloadEvidence)
      (typeUpperPayloadProposition bounds) :=
  .var (lookup_typeUpper context bounds)

def provesCaptureLower {scope : Sig} (context : Ctx scope)
    (bounds : Bounds scope) :
    Evidence.Proves (openedContext context bounds)
      (.var captureLowerPayloadEvidence)
      (captureLowerPayloadProposition bounds) :=
  .var (lookup_captureLower context bounds)

def provesCaptureUpper {scope : Sig} (context : Ctx scope)
    (bounds : Bounds scope) :
    Evidence.Proves (openedContext context bounds)
      (.var captureUpperPayloadEvidence)
      (captureUpperPayloadProposition bounds) :=
  .var (lookup_captureUpper context bounds)

/-- The payload's explicitly captured context binding justifies the one-way
runtime-root contraction `{payload} ≤ χ`. -/
def provesPayloadRoot {scope : Sig} (context : Ctx scope)
    (bounds : Bounds scope) :
    Evidence.Proves (openedContext context bounds)
      (.captureVariable payloadTerm)
      (.inclusion (.capture (.singleton payloadTerm)) chiPayload) :=
  .captureVariable (lookup_payload context bounds)

end DOTCaptureToManySortedFC.Acyclic.ObjectEncoding
