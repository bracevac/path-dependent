import Coercions.Translation.ManySorted.RecursiveObjects.Source
import Coercions.Translation.ManySorted.ModalIntersections.ObjectContract

/-!
# Source-indexed encoding of guarded recursive type members

All source type-member labels are allocated before any recursive body is
translated.  A local type reference becomes a homogeneous recursive self
slot; a local capture reference is first replaced by the explicitly supplied
ambient capture model.  The completed recursive projections are then used as
the type witnesses of the ordinary cumulative `ObjectContract` model.

This is the type-recursive Stage 6A boundary.  Capture members and the unique
representation-capture symbol `C_rep` remain outside the recursive block.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.Encoding

open DOTCaptureToManySortedFC.RecursiveObjects
open DOTCaptureToManySortedFC.Intersections.Encoding
open DOTCaptureToManySortedFC.ModalIntersections

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev StaticSort := ManySortedFC.StaticSort
abbrev BVar := ManySortedFC.BVar
abbrev Rename := ManySortedFC.Rename
abbrev Ty := ManySortedFC.Ty
abbrev Capture := ManySortedFC.Capture
abbrev RecBodies := ManySortedFC.RecBodies
abbrev SymbolArgs := ManySortedFC.SymbolArgs
abbrev Evidence := ManySortedFC.Evidence
abbrev Ctx := ManySortedFC.Ctx

end Target

/-- Failures specific to the recursive source/target boundary. -/
inductive Error : Type where
  | preparation (error : ModalIntersections.Preparation.Error)
  | recursiveCaptureMember (label : Source.Label)
  | recursiveOuterCapture
  | missingTypeDefinition (label : Source.Label)
  | missingCaptureWitness (label : Source.Label)
  | memberAllocationMismatch (label : Source.Label)
  | publicWitnessMisalignment
  | unguardedTargetBlock
  | captureEvidenceCompilation
  | containmentEvidenceCompilation
  | contractedModelRejected
deriving DecidableEq, Repr

/-! ## Homogeneous target allocation -/

/-- Weaken an ambient target scope below a homogeneous suffix of type names. -/
def weakenTypes (scope : Target.Sig) : (count : Nat) ->
    Target.Rename scope (ManySortedFC.TypeScope scope count)
  | 0 => .id
  | count + 1 =>
      (weakenTypes scope count).comp
        (ManySortedFC.Rename.succ (kind := .symbol .type))

/-- The source list head is the newest target self slot.  This is the same
newest-first convention used by `RecBodies.get` and `TypeArgs.get`. -/
def selfMembers (targetScope : Target.Sig) {sourceScope : Source.Sig} :
    (definitions : List (Source.TypeDefinition sourceScope)) ->
      List (MemberName (ManySortedFC.TypeScope targetScope definitions.length))
  | [] => []
  | definition :: remaining =>
      .type definition.label .here ::
        (selfMembers targetScope remaining).map fun member =>
          member.rename (ManySortedFC.Rename.succ
            (kind := .symbol .type))

/-- Locate the recursive slot belonging to a source label. -/
def definitionIndex? {scope : Source.Sig} :
    (definitions : List (Source.TypeDefinition scope)) -> Source.Label ->
      Option (Fin definitions.length)
  | [], _ => none
  | definition :: remaining, label =>
      if definition.label = label then
        some ⟨0, Nat.zero_lt_succ remaining.length⟩
      else
        (definitionIndex? remaining label).map Fin.succ

/-! ## Recursive body translation -/

/-- Translate every body against the complete self allocation.  Capture
members have already been replaced by `captureModel`; type members remain
local and are resolved by `selfMembers`. -/
def compileBodiesFrom {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : ModalIntersections.Layout sourceScope targetScope)
    (captureModel : Source.AmbientCaptureModel sourceScope)
    (allDefinitions : List (Source.TypeDefinition sourceScope)) :
    (remaining : List (Source.TypeDefinition sourceScope)) ->
      Except Error
        (Target.RecBodies targetScope allDefinitions.length remaining.length)
  | [] => .ok .nil
  | definition :: rest => do
      let initial <- compileBodiesFrom layout captureModel allDefinitions rest
      let bodySource := definition.body.realizeLocals captureModel.asLocalModel
      let body <-
        (ModalIntersections.Preparation.Compile.translateType
          (layout.renameTarget (weakenTypes targetScope allDefinitions.length))
          (selfMembers targetScope allDefinitions) bodySource).mapError
            Error.preparation
      pure (.snoc initial body)

/-- Complete simultaneous recursive block. -/
def compileBodies {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : ModalIntersections.Layout sourceScope targetScope)
    (captureModel : Source.AmbientCaptureModel sourceScope)
    (definitions : List (Source.TypeDefinition sourceScope)) :
    Except Error
      (Target.RecBodies targetScope definitions.length definitions.length) :=
  compileBodiesFrom layout captureModel definitions definitions

/-! ## Source-indexed public member witnesses -/

private def findTypeLabel? {scope : Target.Sig}
    (name : Target.BVar scope (.symbol .type)) :
    List (PreparedEntry scope) -> Option Source.Label
  | [] => none
  | .type label candidate _ :: remaining =>
      if candidate = name then some label else findTypeLabel? name remaining
  | .capture _ _ _ :: remaining => findTypeLabel? name remaining

private def findCaptureLabel? {scope : Target.Sig}
    (name : Target.BVar scope (.symbol .capture)) :
    List (PreparedEntry scope) -> Option Source.Label
  | [] => none
  | .capture label candidate _ :: remaining =>
      if candidate = name then some label
      else findCaptureLabel? name remaining
  | .type _ _ _ :: remaining => findCaptureLabel? name remaining

/-- Walk the normalized public symbol spine.  Type entries select the
recursive projection assigned to their source label; capture entries compile
the corresponding explicit ambient witness. -/
def compileMemberSymbolsFrom {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : ModalIntersections.Layout sourceScope targetScope)
    (definitions : List (Source.TypeDefinition sourceScope))
    (captureModel : Source.AmbientCaptureModel sourceScope)
    (bodies : Target.RecBodies targetScope definitions.length
      definitions.length)
    {allSymbols : List Target.StaticSort}
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope targetScope allSymbols))) :
    (symbols : List Target.StaticSort) ->
    (rho : Target.Rename
      (ManySortedFC.SymbolScope targetScope symbols)
      (ManySortedFC.SymbolScope targetScope allSymbols)) ->
      Except Error (Target.SymbolArgs targetScope symbols)
  | [], _ => .ok .nil
  | .type :: remaining, rho => do
      let name := rho.var
        (.here : Target.BVar
          (ManySortedFC.SymbolScope targetScope (.type :: remaining))
          (.symbol .type))
      let label <- match findTypeLabel? name entries with
        | some label => .ok label
        | none => .error (.memberAllocationMismatch 0)
      let index <- match definitionIndex? definitions label with
        | some index => .ok index
        | none => .error (.missingTypeDefinition label)
      let older <- compileMemberSymbolsFrom layout definitions captureModel
        bodies entries remaining
        ((ManySortedFC.Rename.succ
          (scope := ManySortedFC.SymbolScope targetScope remaining)
          (kind := .symbol .type)).comp rho)
      pure (.cons (.type (.recProj bodies index)) older)
  | .capture :: remaining, rho => do
      let name := rho.var
        (.here : Target.BVar
          (ManySortedFC.SymbolScope targetScope (.capture :: remaining))
          (.symbol .capture))
      let label <- match findCaptureLabel? name entries with
        | some label => .ok label
        | none => .error (.memberAllocationMismatch 0)
      let witness <-
        (ModalIntersections.Preparation.translateCapture layout
          (captureModel.witness label)).mapError Error.preparation
      let older <- compileMemberSymbolsFrom layout definitions captureModel
        bodies entries remaining
        ((ManySortedFC.Rename.succ
          (scope := ManySortedFC.SymbolScope targetScope remaining)
          (kind := .symbol .capture)).comp rho)
      pure (.cons (.capture witness) older)

/-- Compile the public member portion of one cumulative object model. -/
def compileMemberSymbols {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : ModalIntersections.Layout sourceScope targetScope)
    (definitions : List (Source.TypeDefinition sourceScope))
    (captureModel : Source.AmbientCaptureModel sourceScope)
    (bodies : Target.RecBodies targetScope definitions.length
      definitions.length)
    (object : ObjectContract.PreparedObject targetScope) :
    Except Error (Target.SymbolArgs targetScope object.memberSymbols) :=
  compileMemberSymbolsFrom layout definitions captureModel bodies
    object.encoding.prepared.entries object.memberSymbols
    ManySortedFC.Rename.id

/-! ## Public-label alignment -/

private def findTypeNameByLabel? {scope : Target.Sig}
    (label : Source.Label) : List (PreparedEntry scope) ->
      Option (Target.BVar scope (.symbol .type))
  | [] => none
  | .type candidate candidateName _ :: remaining =>
      if candidate = label then some candidateName
      else findTypeNameByLabel? label remaining
  | .capture _ _ _ :: remaining => findTypeNameByLabel? label remaining

/-- Witness assigned to one normalized public type label after instantiating
the member-only model. -/
def publicTypeWitness? {targetScope : Target.Sig}
    (object : ObjectContract.PreparedObject targetScope)
    (memberSymbols : Target.SymbolArgs targetScope object.memberSymbols)
    (label : Source.Label) : Option (Target.Ty targetScope) := do
  let name <- findTypeNameByLabel? label object.encoding.prepared.entries
  match (ManySortedFC.StaticSubst.ofSymbolArgs ManySortedFC.Rename.id
      memberSymbols).symbolVar name with
  | .type witness => some witness

/-- Every source definition label is interpreted by its own recursive slot,
independently of canonical public-label order. -/
def PublicWitnessesAligned {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (definitions : List (Source.TypeDefinition sourceScope))
    (bodies : Target.RecBodies targetScope definitions.length
      definitions.length)
    (object : ObjectContract.PreparedObject targetScope)
    (memberSymbols : Target.SymbolArgs targetScope object.memberSymbols) : Prop :=
  forall index : Fin definitions.length,
    publicTypeWitness? object memberSymbols (definitions.get index).label =
      some (.recProj bodies index)

instance publicWitnessesAlignedDecidable {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (definitions : List (Source.TypeDefinition sourceScope))
    (bodies : Target.RecBodies targetScope definitions.length
      definitions.length)
    (object : ObjectContract.PreparedObject targetScope)
    (memberSymbols : Target.SymbolArgs targetScope object.memberSymbols) :
    Decidable (PublicWitnessesAligned definitions bodies object memberSymbols) :=
  by
    unfold PublicWitnessesAligned
    infer_instance

/-! ## Prepared recursive object -/

/-- The source-indexed static half of a recursive package.  The complete
symbol vector is `object.extendSymbols memberSymbols`, so the cumulative
object contract contributes its single `C_rep` exactly once and outside the
homogeneous recursive type block. -/
structure Prepared {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : ModalIntersections.Layout sourceScope targetScope)
    (signature : Source.Signature sourceScope)
    (valid : signature.Valid)
    {context : Source.Ctx sourceScope}
    (realization : Source.Realization context signature) where
  object : ObjectContract.PreparedObject targetScope
  objectPrepared : ObjectContract.prepare layout signature.objectType =
    .ok object
  bodies : Target.RecBodies targetScope signature.typeDefinitions.length
    signature.typeDefinitions.length
  bodiesCompiled : compileBodies layout realization.captures
    signature.typeDefinitions = .ok bodies
  guarded : bodies.headGuarded = true
  memberSymbols : Target.SymbolArgs targetScope object.memberSymbols
  memberSymbolsCompiled : compileMemberSymbols layout signature.typeDefinitions
    realization.captures bodies object = .ok memberSymbols
  publicWitnessesAligned : PublicWitnessesAligned signature.typeDefinitions
    bodies object memberSymbols

namespace Prepared

/-- Complete ambient model, including the one representation-capture
witness owned by `ObjectContract`. -/
def symbols {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    {layout : ModalIntersections.Layout sourceScope targetScope}
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {context : Source.Ctx sourceScope}
    {realization : Source.Realization context signature}
    (prepared : Prepared layout signature valid realization) :
    Target.SymbolArgs targetScope prepared.object.symbols :=
  prepared.object.extendSymbols prepared.memberSymbols

/-- Recursive witness selected by source-list position. -/
def witness {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    {layout : ModalIntersections.Layout sourceScope targetScope}
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {context : Source.Ctx sourceScope}
    {realization : Source.Realization context signature}
    (prepared : Prepared layout signature valid realization)
    (index : Fin signature.typeDefinitions.length) : Target.Ty targetScope :=
  .recProj prepared.bodies index

/-- Simultaneous unfolding of one recursive witness. -/
def unfolding {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    {layout : ModalIntersections.Layout sourceScope targetScope}
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {context : Source.Ctx sourceScope}
    {realization : Source.Realization context signature}
    (prepared : Prepared layout signature valid realization)
    (index : Fin signature.typeDefinitions.length) : Target.Ty targetScope :=
  prepared.bodies.unfoldAt index

end Prepared

/-- Validate the explicit Stage 6A recursion boundary before delegating to
ordinary cumulative preparation. -/
def checkBoundary {scope : Source.Sig} (signature : Source.Signature scope) :
    Except Error Unit := do
  match signature.captureDeclarations.firstRecursiveMember? with
  | some label => .error (.recursiveCaptureMember label)
  | none => pure ()
  if Source.captureAmbientOnly signature.outerCapture then pure ()
  else .error .recursiveOuterCapture

/-- Prepare all source-indexed names and retain target guardedness as an
executable condition.  The target evidence checker repeats this guard when it
checks each `unfoldRec` certificate. -/
def prepare {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : ModalIntersections.Layout sourceScope targetScope)
    (signature : Source.Signature sourceScope)
    (valid : signature.Valid)
    {context : Source.Ctx sourceScope}
    (realization : Source.Realization context signature) :
    Except Error (Prepared layout signature valid realization) := do
  checkBoundary signature
  match objectPrepared : ObjectContract.prepare layout signature.objectType with
  | .error error => .error (.preparation error)
  | .ok object =>
      match bodiesCompiled : compileBodies layout realization.captures
          signature.typeDefinitions with
      | .error error => .error error
      | .ok bodies =>
          if guarded : bodies.headGuarded = true then
            match memberSymbolsCompiled : compileMemberSymbols layout
                signature.typeDefinitions realization.captures bodies object with
            | .error error => .error error
            | .ok memberSymbols =>
                if publicWitnessesAligned : PublicWitnessesAligned
                    signature.typeDefinitions bodies object memberSymbols then
                  .ok
                    { object
                      objectPrepared
                      bodies
                      bodiesCompiled
                      guarded
                      memberSymbols
                      memberSymbolsCompiled
                      publicWitnessesAligned }
                else
                  .error .publicWitnessMisalignment
          else
            .error .unguardedTargetBlock

end DOTCaptureToManySortedFC.RecursiveObjects.Encoding
