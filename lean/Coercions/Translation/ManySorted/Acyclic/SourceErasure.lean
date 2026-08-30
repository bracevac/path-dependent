import Coercions.Translation.ManySorted.Acyclic.SelectionTranslation
import Coercions.ManySortedFC.Erasure

/-!
# Direct runtime erasure of acyclic DOT with captures

The source object representation has no runtime record.  An object value
erases directly to its payload, and selecting `x.v` erases to the runtime
variable that already denotes that payload.  Static member names and their
four interval certificates therefore contribute no runtime coordinates.
-/

namespace DOTCaptureToManySortedFC.Acyclic.SourceErasure

namespace Source

export DOTCapture.Acyclic
  (Scope Var Rename Path Ctx Value Term ValueLabel Capture Ty ObjectSig)

end Source

namespace Target

export ManySortedFC (BVar)

end Target

namespace Selection

export DOTCaptureToManySortedFC.Acyclic.SelectionTranslation
  (term)

end Selection

/-! ## Source-to-runtime variable maps -/

/-- Map source variables into an arbitrary runtime scope. -/
abbrev Renaming (source target : Nat) : Type :=
  Source.Var source -> Fin target

namespace Renaming

/-- Precompose a runtime projection with a source renaming. -/
def precomp {source middle target : Nat}
    (rho : Source.Rename source middle) (sigma : Renaming middle target) :
    Renaming source target :=
  fun index => sigma (rho.var index)

/-- Postcompose a source projection with a runtime renaming. -/
def postcomp {source middle target : Nat}
    (rho : Renaming source middle)
    (sigma : ManySortedFC.Runtime.Renaming middle target) :
    Renaming source target :=
  fun index => sigma (rho index)

@[simp]
theorem precomp_id {source target : Nat} (rho : Renaming source target) :
    precomp DOTCapture.Acyclic.Rename.id rho = rho := by
  funext index
  rfl

@[simp]
theorem precomp_comp {first second third target : Nat}
    (rho₁ : Source.Rename first second)
    (rho₂ : Source.Rename second third)
    (sigma : Renaming third target) :
    precomp (rho₁.comp rho₂) sigma =
      precomp rho₁ (precomp rho₂ sigma) := by
  funext index
  rfl

@[simp]
theorem postcomp_id {source target : Nat} (rho : Renaming source target) :
    postcomp rho ManySortedFC.Runtime.Renaming.id = rho := by
  funext index
  rfl

@[simp]
theorem postcomp_comp {source first second third : Nat}
    (rho : Renaming source first)
    (sigma₁ : ManySortedFC.Runtime.Renaming first second)
    (sigma₂ : ManySortedFC.Runtime.Renaming second third) :
    postcomp (postcomp rho sigma₁) sigma₂ =
      postcomp rho (sigma₁.comp sigma₂) := by
  funext index
  rfl

@[simp]
theorem precomp_postcomp {source middle : Nat} {first second : Nat}
    (rho : Source.Rename source middle) (sigma : Renaming middle first)
    (tau : ManySortedFC.Runtime.Renaming first second) :
    postcomp (precomp rho sigma) tau = precomp rho (postcomp sigma tau) := by
  funext index
  rfl

end Renaming

/-! ## Generalized direct erasure -/

/-- Erase the variable-only source path to its runtime coordinate. -/
def erasePathWith {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) :
    Source.Path scope -> Fin runtimeScope
  | .var name => rho name

/-- Erase a source value.  An object package has no runtime wrapper: it is
represented by the erasure of its value-member payload. -/
def eraseValueWith {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) :
    Source.Value scope -> ManySortedFC.Runtime.Tm runtimeScope
  | .var name => .var (rho name)
  | .unit => .unit
  | .object _signature _typeWitness _captureWitness payload =>
      eraseValueWith rho payload

/-- Erase an acyclic source computation.  A primitive value-member selection
is just a read of the receiver's already-separated payload coordinate. -/
def eraseTermWith {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) :
    Source.Term scope -> ManySortedFC.Runtime.Tm runtimeScope
  | .ret value => eraseValueWith rho value
  | .select receiver .v => .var (erasePathWith rho receiver)

/-! ## Exact generalized equations -/

@[simp]
theorem erasePathWith_var {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) (name : Source.Var scope) :
    erasePathWith rho (.var name) = rho name := rfl

@[simp]
theorem eraseValueWith_var {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) (name : Source.Var scope) :
    eraseValueWith rho (.var name) = .var (rho name) := rfl

@[simp]
theorem eraseValueWith_unit {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) :
    eraseValueWith rho (.unit : Source.Value scope) = .unit := rfl

@[simp]
theorem eraseValueWith_object {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) (signature : Source.ObjectSig scope)
    (typeWitness : Source.Ty scope)
    (captureWitness : Source.Capture scope)
    (payload : Source.Value scope) :
    eraseValueWith rho
        (.object signature typeWitness captureWitness payload) =
      eraseValueWith rho payload := rfl

@[simp]
theorem eraseTermWith_ret {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) (value : Source.Value scope) :
    eraseTermWith rho (.ret value) = eraseValueWith rho value := rfl

@[simp]
theorem eraseTermWith_select {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) (receiver : Source.Path scope) :
    eraseTermWith rho (.select receiver .v) =
      .var (erasePathWith rho receiver) := rfl

/-! ## Naturality -/

@[simp]
theorem erasePathWith_sourceRename {source middle runtimeScope : Nat}
    (sigma : Renaming middle runtimeScope)
    (rho : Source.Rename source middle) (path : Source.Path source) :
    erasePathWith sigma (path.rename rho) =
      erasePathWith (Renaming.precomp rho sigma) path := by
  cases path
  rfl

@[simp]
theorem eraseValueWith_sourceRename {source middle runtimeScope : Nat}
    (sigma : Renaming middle runtimeScope)
    (rho : Source.Rename source middle) (value : Source.Value source) :
    eraseValueWith sigma (value.rename rho) =
      eraseValueWith (Renaming.precomp rho sigma) value := by
  induction value with
  | var => rfl
  | unit => rfl
  | object signature typeWitness captureWitness payload induction =>
      simpa [DOTCapture.Acyclic.Value.rename, eraseValueWith] using induction

@[simp]
theorem eraseTermWith_sourceRename {source middle runtimeScope : Nat}
    (sigma : Renaming middle runtimeScope)
    (rho : Source.Rename source middle) (sourceTerm : Source.Term source) :
    eraseTermWith sigma (sourceTerm.rename rho) =
      eraseTermWith (Renaming.precomp rho sigma) sourceTerm := by
  cases sourceTerm with
  | ret value =>
      simp [DOTCapture.Acyclic.Term.rename, eraseTermWith,
        eraseValueWith_sourceRename]
  | select receiver label =>
      cases label
      simp [DOTCapture.Acyclic.Term.rename, eraseTermWith,
        erasePathWith_sourceRename]

@[simp]
theorem erasePathWith_runtimeRename {scope source target : Nat}
    (rho : Renaming scope source)
    (sigma : ManySortedFC.Runtime.Renaming source target)
    (path : Source.Path scope) :
    sigma (erasePathWith rho path) =
      erasePathWith (Renaming.postcomp rho sigma) path := by
  cases path
  rfl

@[simp]
theorem eraseValueWith_runtimeRename {scope source target : Nat}
    (rho : Renaming scope source)
    (sigma : ManySortedFC.Runtime.Renaming source target)
    (value : Source.Value scope) :
    (eraseValueWith rho value).rename sigma =
      eraseValueWith (Renaming.postcomp rho sigma) value := by
  induction value with
  | var => rfl
  | unit => rfl
  | object signature typeWitness captureWitness payload induction =>
      simpa [eraseValueWith] using induction

@[simp]
theorem eraseTermWith_runtimeRename {scope source target : Nat}
    (rho : Renaming scope source)
    (sigma : ManySortedFC.Runtime.Renaming source target)
    (sourceTerm : Source.Term scope) :
    (eraseTermWith rho sourceTerm).rename sigma =
      eraseTermWith (Renaming.postcomp rho sigma) sourceTerm := by
  cases sourceTerm with
  | ret value =>
      simp [eraseTermWith, eraseValueWith_runtimeRename]
  | select receiver label =>
      cases label
      simp [eraseTermWith, ManySortedFC.Runtime.Tm.rename,
        erasePathWith_runtimeRename]

/-! ## Canonical context erasure -/

/-- Every source binding contributes exactly one runtime slot.  Object
expansion adds static names and evidence, but its only runtime binder is the
separate payload. -/
@[simp]
theorem targetTermCount {scope : Source.Scope} (context : Source.Ctx scope) :
    (Layout.sig context).termCount = scope := by
  induction context with
  | nil => rfl
  | extend outer type induction =>
      cases type with
      | top => simp [Layout.sig, induction]
      | bot => simp [Layout.sig, induction]
      | one => simp [Layout.sig, induction]
      | ref => simp [Layout.sig, induction]
      | object => simp [Layout.sig, ObjectEncoding.PayloadScope, induction]
      | capturing captures shape =>
          cases shape <;>
            simp [Layout.sig, ObjectEncoding.PayloadScope, induction]

/-- Canonical variable projection: allocate through `Layout.termVar`, then
forget all target static and evidence coordinates. -/
def compiledRenaming {scope : Source.Scope} (context : Source.Ctx scope) :
    Renaming scope (Layout.sig context).termCount :=
  fun index => ManySortedFC.BVar.toTermIndex (Layout.termVar context index)

@[simp]
theorem compiledRenaming_apply {scope : Source.Scope}
    (context : Source.Ctx scope) (index : Source.Var scope) :
    compiledRenaming context index =
      ManySortedFC.BVar.toTermIndex (Layout.termVar context index) := rfl

/-- Direct erasure of a source value in its canonical translated context. -/
def eraseValue {scope : Source.Scope} (context : Source.Ctx scope)
    (value : Source.Value scope) :
    ManySortedFC.Runtime.Tm (Layout.sig context).termCount :=
  eraseValueWith (compiledRenaming context) value

/-- Direct erasure of a source computation in its canonical translated
context. -/
def eraseTerm {scope : Source.Scope} (context : Source.Ctx scope)
    (sourceTerm : Source.Term scope) :
    ManySortedFC.Runtime.Tm (Layout.sig context).termCount :=
  eraseTermWith (compiledRenaming context) sourceTerm

/-! ## Exact canonical equations -/

@[simp]
theorem eraseValue_var {scope : Source.Scope} (context : Source.Ctx scope)
    (name : Source.Var scope) :
    eraseValue context (.var name) =
      .var (ManySortedFC.BVar.toTermIndex
        (Layout.termVar context name)) := rfl

@[simp]
theorem eraseValue_unit {scope : Source.Scope} (context : Source.Ctx scope) :
    eraseValue context (.unit : Source.Value scope) = .unit := rfl

@[simp]
theorem eraseValue_object {scope : Source.Scope} (context : Source.Ctx scope)
    (signature : Source.ObjectSig scope) (typeWitness : Source.Ty scope)
    (captureWitness : Source.Capture scope)
    (payload : Source.Value scope) :
    eraseValue context
        (.object signature typeWitness captureWitness payload) =
      eraseValue context payload := rfl

@[simp]
theorem eraseTerm_ret {scope : Source.Scope} (context : Source.Ctx scope)
    (value : Source.Value scope) :
    eraseTerm context (.ret value) = eraseValue context value := rfl

@[simp]
theorem eraseTerm_select {scope : Source.Scope} (context : Source.Ctx scope)
    (receiver : Source.Path scope) :
    eraseTerm context (.select receiver .v) =
      .var (ManySortedFC.BVar.toTermIndex
        (Layout.translatePath context receiver)) := by
  cases receiver
  rfl

/-! ## Agreement with primitive selection translation -/

/-- The generated target annotations are all runtime-transparent: selection
erases to its resolved payload variable before relating that coordinate back
to source syntax. -/
@[simp]
theorem generatedSelection_targetErase {scope : Source.Scope}
    {context : Source.Ctx scope}
    {translated : ExposureTranslation.TranslatedContext context}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (resolved : ExposureTranslation.ResolvedExposure translated receiver
      signature) :
    (Selection.term resolved).erase =
      .var (ManySortedFC.BVar.toTermIndex resolved.slot.payload) := by
  rfl

/-- Erasure agreement under any target-to-runtime variable projection.  The
retag and use annotations are transparent, and the resolved payload is the
same coordinate as the source receiver under `Layout.termVar`. -/
theorem generatedSelection_eraseWith {scope : Source.Scope}
    {context : Source.Ctx scope}
    {translated : ExposureTranslation.TranslatedContext context}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (resolved : ExposureTranslation.ResolvedExposure translated receiver
      signature)
    {runtimeScope : Nat}
    (rho : ManySortedFC.Erasure.Renaming (Layout.sig context) runtimeScope) :
    (Selection.term resolved).eraseWith rho =
      eraseTermWith (fun name => rho (Layout.termVar context name))
        (.select receiver .v) := by
  cases receiver with
  | var name =>
      simp only [SelectionTranslation.term, ManySortedFC.Tm.eraseWith,
        ManySortedFC.Adapter.erase, eraseTermWith, erasePathWith]
      rw [resolved.payloadIsPath]
      rfl

/-- Canonical primitive selection translation commutes exactly with direct
source erasure. -/
theorem generatedSelection_erase {scope : Source.Scope}
    {context : Source.Ctx scope}
    {translated : ExposureTranslation.TranslatedContext context}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (resolved : ExposureTranslation.ResolvedExposure translated receiver
      signature) :
    (Selection.term resolved).erase =
      eraseTerm context (.select receiver .v) := by
  simpa [ManySortedFC.Tm.erase, eraseTerm, compiledRenaming,
    ManySortedFC.Erasure.Renaming.identity] using
    generatedSelection_eraseWith resolved
      (ManySortedFC.Erasure.Renaming.identity (Layout.sig context))

/-! ## Regressions -/

namespace Regression

namespace ExposureRegression

export DOTCaptureToManySortedFC.Acyclic.ExposureTranslation.Regression
  (exactContext exactResolved OlderExpandedSourceContext
    olderExpandedContext olderExpandedReceiver olderExpandedResolved)

end ExposureRegression

/-- Captured-DOT object packages have no runtime wrapper of their own. -/
def exactObjectValue : Source.Value 0 :=
  .object
    DOTCaptureToManySortedFC.Acyclic.StaticTranslation.exactSourceSignature
    .one .empty .unit

theorem object_value_erases_to_payload :
    eraseValue (.nil : Source.Ctx 0) exactObjectValue = .unit := by
  rfl

theorem newest_selection_agrees :
    (Selection.term ExposureRegression.exactResolved).erase =
      eraseTerm DOTCaptureToManySortedFC.Acyclic.StaticTranslation.exactSourceContext
        (.select
          DOTCaptureToManySortedFC.Acyclic.StaticTranslation.exactReceiver .v) :=
  generatedSelection_erase ExposureRegression.exactResolved

theorem older_through_object_selection_agrees :
    (Selection.term ExposureRegression.olderExpandedResolved).erase =
      eraseTerm ExposureRegression.OlderExpandedSourceContext
        (.select ExposureRegression.olderExpandedReceiver .v) := by
  exact generatedSelection_erase ExposureRegression.olderExpandedResolved

end Regression

end DOTCaptureToManySortedFC.Acyclic.SourceErasure
