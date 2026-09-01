import Coercions.DOT.Captures.ModalIntersections.Erasure
import Coercions.DOT.Captures.ModalIntersections.TypingContext
import Coercions.ManySortedFC.ModalPreservation
import Coercions.Translation.ManySorted.ModalIntersections.ModalProvenanceTransport
import Coercions.Translation.ManySorted.ModalIntersections.PreparationRenaming

/-!
# Compiler-ready contexts for cumulative modal intersections

The recursive compiler carries a source typing environment only as an index.
Its executable state is an independently well-scoped many-sorted context,
the cumulative coordinate layout into that context, and a proof-relevant
accounting of every active modal frame.

This file keeps the layout/context component separate from modal provenance.
That separation makes the runtime projection depend only on stable term
coordinates: static theories and proof-only modal frames are erased without
consulting their certificates.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.CompilerContext

namespace Source

abbrev StaticSort := DOTCapture.ModalIntersections.StaticSort
abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev BVar := DOTCapture.ModalIntersections.BVar
abbrev CaptureMode := DOTCapture.ModalIntersections.CaptureMode
abbrev ModalRequirements := DOTCapture.ModalIntersections.ModalRequirements
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev StaticExpr := DOTCapture.ModalIntersections.StaticExpr
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev ObjectType := DOTCapture.ModalIntersections.ObjectType
abbrev Value := DOTCapture.ModalIntersections.Value
abbrev Term := DOTCapture.ModalIntersections.Term

end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Ctx := ManySortedFC.Ctx
abbrev Ty := ManySortedFC.Ty
abbrev StaticExpr := ManySortedFC.StaticExpr
abbrev Capture := ManySortedFC.Capture
abbrev Theory := ManySortedFC.Theory
abbrev ModalContext := ManySortedFC.ModalContext
abbrev StaticScope := ManySortedFC.StaticScope
abbrev ModalScope := ManySortedFC.ModalScope
abbrev Tm := ManySortedFC.Tm

end Target

namespace SourceErasure

abbrev Renaming := DOTCapture.ModalIntersections.Erasure.Renaming

namespace Renaming

/-- Transport only the runtime codomain of a source-variable projection. -/
def castTarget {source : Source.Sig} {first second : Nat}
    (scopeEquality : first = second) (rho : Renaming source first) :
    Renaming source second :=
  fun sourceVar => Fin.cast scopeEquality (rho sourceVar)

@[simp]
theorem castTarget_rfl {source : Source.Sig} {target : Nat}
    (rho : Renaming source target) :
    castTarget rfl rho = rho := rfl

end Renaming

end SourceErasure

open DOTCaptureToManySortedFC.Intersections.Encoding

/-! Static and evidence weakening changes an intrinsic target variable but
not its erased numeric coordinate.  The value-level formulation avoids
polluting later laws with transports between propositionally equal `Fin`
scopes. -/

private theorem toTermIndex_weakenSymbols_val (scope : Target.Sig)
    (symbols : List ManySortedFC.StaticSort)
    (index : ManySortedFC.BVar scope .term) :
    (ManySortedFC.BVar.toTermIndex
      ((ManySortedFC.Rename.weakenSymbols symbols).var index)).val =
      (ManySortedFC.BVar.toTermIndex index).val := by
  induction symbols with
  | nil => rfl
  | cons sort rest induction =>
      simp only [ManySortedFC.Rename.weakenSymbols,
        ManySortedFC.symbolKinds, ManySortedFC.Rename.weakenMany,
        ManySortedFC.Rename.comp_var, ManySortedFC.Rename.succ_var]
      change
        (ManySortedFC.BVar.toTermIndex
          ((ManySortedFC.Rename.weakenSymbols rest).var index)).val = _
      exact induction

private theorem toTermIndex_weakenEvidence_val (scope : Target.Sig)
    (relations : List ManySortedFC.Relation)
    (index : ManySortedFC.BVar scope .term) :
    (ManySortedFC.BVar.toTermIndex
      ((ManySortedFC.Rename.weakenMany scope
        (ManySortedFC.evidenceKinds relations)).var index)).val =
      (ManySortedFC.BVar.toTermIndex index).val := by
  induction relations with
  | nil => rfl
  | cons relation rest induction =>
      simp only [ManySortedFC.evidenceKinds,
        ManySortedFC.Rename.weakenMany,
        ManySortedFC.Rename.comp_var, ManySortedFC.Rename.succ_var]
      change
        (ManySortedFC.BVar.toTermIndex
          ((ManySortedFC.Rename.weakenMany scope
            (ManySortedFC.evidenceKinds rest)).var index)).val = _
      exact induction

private theorem toTermIndex_weakenStatic_val (scope : Target.Sig)
    (symbols : List ManySortedFC.StaticSort)
    (relations : List ManySortedFC.Relation)
    (index : ManySortedFC.BVar scope .term) :
    (ManySortedFC.BVar.toTermIndex
      ((ManySortedFC.Rename.weakenStatic symbols relations).var index)).val =
      (ManySortedFC.BVar.toTermIndex index).val := by
  simp only [ManySortedFC.Rename.weakenStatic,
    ManySortedFC.Rename.comp_var]
  rw [toTermIndex_weakenEvidence_val,
    toTermIndex_weakenSymbols_val]

private theorem toTermIndex_weakenModal_val (scope : Target.Sig)
    (separationCount : Nat) (modes : List ManySortedFC.CaptureMode)
    (index : ManySortedFC.BVar scope .term) :
    (ManySortedFC.BVar.toTermIndex
      ((ManySortedFC.Rename.weakenModal scope separationCount modes).var
        index)).val =
      (ManySortedFC.BVar.toTermIndex index).val := by
  exact toTermIndex_weakenEvidence_val scope
    (ManySortedFC.modalRelations separationCount modes) index

/-! ## Layout and target-context core -/

/-- The provenance-independent part of compiler readiness.  Keeping this
record explicit prevents proof-only modal bookkeeping from entering source
erasure or stable coordinate allocation. -/
structure Core {sourceScope : Source.Sig}
    (environment : Source.TypingEnv sourceScope)
    (targetScope : Target.Sig) where
  layout : Layout sourceScope targetScope
  target : Target.Ctx targetScope

namespace Core

/-- Canonical total capture map used only to index proof-relevant modal
provenance.  Successfully prepared captures recover their exact translation;
malformed ambient selections map to empty.  The derivation-directed compiler
uses the prepared constructors below before extending its canonical state. -/
def captureMap {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope) :
    Source.Capture sourceScope -> Target.Capture targetScope :=
  Preparation.totalCapture core.layout

end Core

/-! ## Exact preparation artifacts -/

/-- Successful translation of one ordinary source binding in this exact
layout. -/
structure PreparedTerm {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (sourceType : Source.Ty sourceScope) where
  targetType : Target.Ty targetScope
  prepared : Preparation.translateType core.layout sourceType =
    .ok targetType

/-- Successful translation of one capture in this exact layout. -/
structure PreparedCapture {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (sourceCapture : Source.Capture sourceScope) where
  targetCapture : Target.Capture targetScope
  prepared : Preparation.translateCapture core.layout sourceCapture =
    .ok targetCapture

namespace PreparedCapture

@[simp]
theorem captureMap_eq {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {sourceCapture : Source.Capture sourceScope}
    (prepared : PreparedCapture core sourceCapture) :
    core.captureMap sourceCapture = prepared.targetCapture :=
  Preparation.totalCapture_of_prepared core.layout sourceCapture
    prepared.targetCapture prepared.prepared

end PreparedCapture

/-- Successful translation of one sorted static expression in this exact
layout. -/
structure PreparedStaticExpr {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort}
    (sourceExpression : Source.StaticExpr sort sourceScope) where
  targetExpression : Target.StaticExpr (translateSort sort) targetScope
  prepared : Preparation.translateStaticExpr core.layout sourceExpression =
    .ok targetExpression

/-- Successful translation of one lexical true interval in this exact
layout. -/
structure PreparedStatic {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort}
    (interval : DOTCapture.ModalIntersections.Interval sort sourceScope) where
  theory : Target.Theory targetScope [translateSort sort]
    (intervalRelations interval)
  prepared : Preparation.translateInterval core.layout interval = .ok theory

/-- Exact interval and payload-type translations needed when an existential
package is opened. -/
structure PreparedPayload {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort}
    (interval : DOTCapture.ModalIntersections.Interval sort sourceScope)
    (sourcePayload : Source.Ty (sourceScope ▹ .static sort)) where
  theory : Target.Theory targetScope [translateSort sort]
    (intervalRelations interval)
  intervalPrepared :
    Preparation.translateInterval core.layout interval = .ok theory
  targetPayload : Target.Ty
    (Target.StaticScope targetScope [translateSort sort]
      (intervalRelations interval))
  payloadPrepared :
    Preparation.translateType (core.layout.extendStatic interval)
      sourcePayload = .ok targetPayload

/-- A cumulative source object prepared and encoded in this exact layout. -/
structure PreparedObject {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (sourceObject : Source.ObjectType sourceScope) where
  object : Preparation.PreparedObject targetScope
  prepared : Preparation.prepareObject core.layout sourceObject = .ok object

/-- A negative object parameter and dependent result template prepared in
this exact layout. -/
structure PreparedObjectArrow {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (parameter : Source.ObjectType sourceScope)
    (resultTemplate : Source.Ty sourceScope) where
  arrow : Preparation.PreparedObjectArrow targetScope
  prepared : Preparation.prepareObjectArrow core.layout parameter
    resultTemplate = .ok arrow

/-- Successful capture translation for one modal frame in this exact
layout. -/
structure PreparedModal {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    (sourceRequirements : Source.ModalRequirements separationCount modes
      sourceScope) where
  requirements : Target.ModalContext separationCount
    (Preparation.translateModes modes) targetScope
  prepared : Preparation.translateRequirements core.layout
    sourceRequirements = .ok requirements

namespace PreparedModal

/-- The exact prepared modal interface is the canonical pointwise map used by
proof-relevant target provenance. -/
@[simp]
theorem canonicalRequirements {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {separationCount : Nat} {modes : List Source.CaptureMode}
    {sourceRequirements : Source.ModalRequirements separationCount modes
      sourceScope}
    (prepared : PreparedModal core sourceRequirements) :
    mapRequirements core.captureMap sourceRequirements =
      prepared.requirements := by
  calc
    mapRequirements core.captureMap sourceRequirements =
        Preparation.totalRequirements core.layout sourceRequirements :=
      (Preparation.totalRequirements_eq_mapRequirements core.layout
        sourceRequirements).symm
    _ = prepared.requirements :=
      Preparation.totalRequirements_of_prepared core.layout
        sourceRequirements prepared.requirements prepared.prepared

end PreparedModal

/-- A coherent compiler context combines the exact layout/target context with
proof-relevant provenance for every active source lock. -/
structure Ready {sourceScope : Source.Sig}
    (environment : Source.TypingEnv sourceScope)
    (targetScope : Target.Sig) where
  core : Core environment targetScope
  provenance : ActiveProvenance environment.locks core.target core.captureMap

namespace Core

/-- Empty source and target contexts share the unique empty layout. -/
def nil : Core DOTCapture.ModalIntersections.TypingEnv.nil [] where
  layout := Layout.empty
  target := ManySortedFC.Ctx.nil

/-- Stable source variables projected through the many-sorted layout into the
target's erased runtime scope. -/
def runtimeRenaming {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope) :
    SourceErasure.Renaming sourceScope targetScope.termCount :=
  fun sourceVar => ManySortedFC.BVar.toTermIndex
    (core.layout.termVar sourceVar)

/-- Independent source-value erasure consults only the stable runtime
projection, never target annotations or modal certificates. -/
def eraseValue {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (value : Source.Value sourceScope) :
    ManySortedFC.Runtime.Tm targetScope.termCount :=
  DOTCapture.ModalIntersections.Erasure.eraseValueWith
    core.runtimeRenaming value

/-- Independent source-computation erasure consults only the stable runtime
projection. -/
def eraseTerm {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (term : Source.Term sourceScope) :
    ManySortedFC.Runtime.Tm targetScope.termCount :=
  DOTCapture.ModalIntersections.Erasure.eraseTermWith
    core.runtimeRenaming term

/-- Add one ordinary source binding and its independently translated target
type. -/
def extendPlain {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (sourceType : Source.Ty sourceScope) (targetType : Target.Ty targetScope) :
    Core (environment.extendTerm sourceType) (targetScope ▹ .term) where
  layout := core.layout.extendPlain
  target := core.target.extendTerm targetType

/-- Install the exact target theory translated for one lexical source
interval. -/
def extendStatic {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort}
    (interval : DOTCapture.ModalIntersections.Interval sort sourceScope)
    (theory : Target.Theory targetScope [translateSort sort]
      (intervalRelations interval)) :
    Core (environment.extendStatic interval)
      (Target.StaticScope targetScope [translateSort sort]
        (intervalRelations interval)) where
  layout := core.layout.extendStatic interval
  target := core.target.extendTheory theory

/-- Open an existential's translated interval theory and add its one runtime
payload binding. -/
def extendPayload {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort}
    (interval : DOTCapture.ModalIntersections.Interval sort sourceScope)
    (sourcePayload : Source.Ty (sourceScope ▹ .static sort))
    (theory : Target.Theory targetScope [translateSort sort]
      (intervalRelations interval))
    (targetPayload : Target.Ty
      (Target.StaticScope targetScope [translateSort sort]
        (intervalRelations interval))) :
    Core (environment.extendPayload interval sourcePayload)
      (Target.StaticScope targetScope [translateSort sort]
        (intervalRelations interval) ▹ .term) where
  layout := core.layout.extendPayload interval
  target := (core.target.extendTheory theory).extendTerm targetPayload

/-- Open a prepared object's complete names-first theory and install its one
runtime representation as the newest stable source root. -/
def extendObject {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (sourceObject : Source.ObjectType sourceScope)
    (object : Preparation.PreparedObject targetScope) :
    Core (environment.extendTerm sourceObject.formedType)
      (Target.StaticScope targetScope object.encoding.symbols
        object.encoding.relations ▹ .term) where
  layout := core.layout.extendObject object.encoding
  target := (core.target.extendTheory object.encoding.theory).extendTerm
    object.representation

/-- Enter a translated modal evidence block.  This changes neither source
variable scope nor runtime scope. -/
def push {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    (sourceRequirements : Source.ModalRequirements separationCount modes
      sourceScope)
    (targetRequirements : Target.ModalContext separationCount
      (Preparation.translateModes modes) targetScope) :
    Core (environment.push sourceRequirements)
      (Target.ModalScope targetScope separationCount
        (Preparation.translateModes modes)) where
  layout := core.layout.weakenModal separationCount
    (Preparation.translateModes modes)
  target := core.target.extendModal targetRequirements

/-! ## Runtime lift laws -/

/-- Ordinary source and target binders extend the runtime projection in
lockstep. -/
@[simp]
theorem runtimeRenaming_extendPlain {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (sourceType : Source.Ty sourceScope) (targetType : Target.Ty targetScope) :
    (core.extendPlain sourceType targetType).runtimeRenaming =
      core.runtimeRenaming.liftTerm := by
  funext sourceVar
  cases sourceVar <;> rfl

/-- A lexical static theory contributes no runtime coordinate. -/
@[simp]
theorem runtimeRenaming_extendStatic {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort}
    (interval : DOTCapture.ModalIntersections.Interval sort sourceScope)
    (theory : Target.Theory targetScope [translateSort sort]
      (intervalRelations interval)) :
    (core.extendStatic interval theory).runtimeRenaming =
      SourceErasure.Renaming.castTarget
        (ManySortedFC.Sig.termCount_staticScope targetScope
          [translateSort sort] (intervalRelations interval)).symm
        (core.runtimeRenaming.liftStatic sort) := by
  funext sourceVar
  cases sourceVar with
  | there older =>
      cases interval with
      | bounds lower upper =>
          cases lower <;> cases upper <;> rfl

/-- Existential opening forgets the hidden static binder and preserves the
newest payload binder. -/
@[simp]
theorem runtimeRenaming_extendPayload {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort}
    (interval : DOTCapture.ModalIntersections.Interval sort sourceScope)
    (sourcePayload : Source.Ty (sourceScope ▹ .static sort))
    (theory : Target.Theory targetScope [translateSort sort]
      (intervalRelations interval))
    (targetPayload : Target.Ty
      (Target.StaticScope targetScope [translateSort sort]
        (intervalRelations interval))) :
    (core.extendPayload interval sourcePayload theory
        targetPayload).runtimeRenaming =
      SourceErasure.Renaming.castTarget
        (by
          simp only [ManySortedFC.Sig.termCount_extend_term,
            ManySortedFC.Sig.termCount_staticScope,
            Nat.succ_eq_add_one])
        (core.runtimeRenaming.liftPayload sort) := by
  funext sourceVar
  cases sourceVar with
  | here => rfl
  | there older =>
      cases older with
      | there oldest =>
          cases interval with
          | bounds lower upper =>
              cases lower <;> cases upper <;> rfl

/-- Names and evidence opened for an object erase away; its one source root
and one target representation binder are the same newest runtime slot. -/
@[simp]
theorem runtimeRenaming_extendObject {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (sourceObject : Source.ObjectType sourceScope)
    (object : Preparation.PreparedObject targetScope) :
    (core.extendObject sourceObject object).runtimeRenaming =
      SourceErasure.Renaming.castTarget object.one_payload.symm
        core.runtimeRenaming.liftTerm := by
  funext sourceVar
  apply Fin.ext
  cases sourceVar with
  | here => rfl
  | there older =>
      change
        (ManySortedFC.BVar.toTermIndex
          ((ManySortedFC.Rename.weakenStatic object.encoding.symbols
            object.encoding.relations).var
              (core.layout.termVar older))).val + 1 =
        (ManySortedFC.BVar.toTermIndex
          (core.layout.termVar older)).val + 1
      exact congrArg (fun coordinate => coordinate + 1)
        (toTermIndex_weakenStatic_val targetScope
          object.encoding.symbols object.encoding.relations
          (core.layout.termVar older))

/-- Modal evidence is proof-only, so pushing a frame leaves every erased
runtime coordinate unchanged. -/
@[simp]
theorem runtimeRenaming_push {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    (sourceRequirements : Source.ModalRequirements separationCount modes
      sourceScope)
    (targetRequirements : Target.ModalContext separationCount
      (Preparation.translateModes modes) targetScope) :
    (core.push sourceRequirements targetRequirements).runtimeRenaming =
      SourceErasure.Renaming.castTarget
        (ManySortedFC.Sig.termCount_evidenceBlock targetScope
          (ManySortedFC.modalRelations separationCount
            (Preparation.translateModes modes))).symm
        core.runtimeRenaming := by
  funext sourceVar
  apply Fin.ext
  exact toTermIndex_weakenModal_val targetScope separationCount
    (Preparation.translateModes modes) (core.layout.termVar sourceVar)

end Core

/-! ## Canonical prepared context extensions -/

namespace Ready

/-- The empty source environment has no active modal frame. -/
def nil : Ready DOTCapture.ModalIntersections.TypingEnv.nil [] where
  core := Core.nil
  provenance := ActiveProvenance.nil ManySortedFC.Ctx.nil
    (Preparation.totalCapture Layout.empty)

/-- Add an ordinary source binding only after its type has translated in the
exact current layout. -/
noncomputable def extendPlain {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (ready : Ready environment targetScope)
    (sourceType : Source.Ty sourceScope)
    (prepared : PreparedTerm ready.core sourceType) :
    Ready (environment.extendTerm sourceType) (targetScope ▹ .term) := by
  let nextCore := ready.core.extendPlain sourceType prepared.targetType
  let substitution := ManySortedFC.TermStaticSubst.ofRename
    (ManySortedFC.Rename.succ (scope := targetScope) (kind := .term))
  have preserves : substitution.Preserves ready.core.target nextCore.target :=
    ManySortedFC.TermStaticSubst.Preserves.weaken ready.core.target
      (.term prepared.targetType)
  refine { core := nextCore, provenance := ?_ }
  refine ActiveProvenance.renameSource ready.provenance
    (DOTCapture.BinderOnly.Rename.succ (scope := sourceScope) (kind := .term))
    substitution preserves nextCore.captureMap ?_
  intro capture
  change Preparation.totalCapture ready.core.layout.extendPlain
      (capture.rename DOTCapture.BinderOnly.Rename.succ) =
    (Preparation.totalCapture ready.core.layout capture).substitute
      (ManySortedFC.StaticSubst.ofRename ManySortedFC.Rename.succ)
  rw [Preparation.totalCapture_extendPlain]
  rw [ManySortedFC.Capture.substitute_ofRename]

/-- Add one lexical static interval only after its complete target theory has
been prepared in the exact current layout. -/
noncomputable def extendStatic {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (ready : Ready environment targetScope)
    {sort : Source.StaticSort}
    (interval : DOTCapture.ModalIntersections.Interval sort sourceScope)
    (prepared : PreparedStatic ready.core interval) :
    Ready (environment.extendStatic interval)
      (Target.StaticScope targetScope [translateSort sort]
        (intervalRelations interval)) := by
  let nextCore := ready.core.extendStatic interval prepared.theory
  let rho := Layout.staticRename targetScope interval
  let substitution := ManySortedFC.TermStaticSubst.ofRename rho
  have preserves : substitution.Preserves ready.core.target nextCore.target :=
    ManySortedFC.TermStaticSubst.Preserves.weakenTheory ready.core.target
      prepared.theory
  refine { core := nextCore, provenance := ?_ }
  refine ActiveProvenance.renameSource ready.provenance
    (DOTCapture.BinderOnly.Rename.succ (scope := sourceScope)
      (kind := .static sort)) substitution preserves nextCore.captureMap ?_
  intro capture
  change Preparation.totalCapture (ready.core.layout.extendStatic interval)
      (capture.rename DOTCapture.BinderOnly.Rename.succ) =
    (Preparation.totalCapture ready.core.layout capture).substitute
      (ManySortedFC.StaticSubst.ofRename
        (Layout.staticRename targetScope interval))
  rw [Preparation.totalCapture_extendStatic]
  rw [ManySortedFC.Capture.substitute_ofRename]

/-- Open a prepared existential interval and payload in the same two stages as
the source environment: first the hidden static name, then the runtime value. -/
noncomputable def extendPayload {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (ready : Ready environment targetScope)
    {sort : Source.StaticSort}
    (interval : DOTCapture.ModalIntersections.Interval sort sourceScope)
    (sourcePayload : Source.Ty (sourceScope ▹ .static sort))
    (prepared : PreparedPayload ready.core interval sourcePayload) :
    Ready (environment.extendPayload interval sourcePayload)
      (Target.StaticScope targetScope [translateSort sort]
        (intervalRelations interval) ▹ .term) := by
  let staticPrepared : PreparedStatic ready.core interval :=
    { theory := prepared.theory
      prepared := prepared.intervalPrepared }
  let afterStatic := ready.extendStatic interval staticPrepared
  have afterStaticLayout : afterStatic.core.layout =
      ready.core.layout.extendStatic interval := by
    rfl
  let payloadPrepared : PreparedTerm afterStatic.core sourcePayload :=
    { targetType := prepared.targetPayload
      prepared := by
        rw [afterStaticLayout]
        exact prepared.payloadPrepared }
  exact afterStatic.extendPlain sourcePayload payloadPrepared

/-- Open a prepared object theory and install its representation as one stable
runtime root.  Existing modal leaves first cross the proof-only theory and
then the source/target term binder in lockstep. -/
noncomputable def extendObject {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (ready : Ready environment targetScope)
    (sourceObject : Source.ObjectType sourceScope)
    (prepared : PreparedObject ready.core sourceObject) :
    Ready (environment.extendTerm sourceObject.formedType)
      (Target.StaticScope targetScope prepared.object.encoding.symbols
        prepared.object.encoding.relations ▹ .term) := by
  let object := prepared.object
  let namesRename := ManySortedFC.Rename.weakenStatic (scope := targetScope)
    object.encoding.symbols object.encoding.relations
  let namesSubstitution := ManySortedFC.TermStaticSubst.ofRename namesRename
  let namesContext := ready.core.target.extendTheory object.encoding.theory
  have namesPreserves : namesSubstitution.Preserves ready.core.target
      namesContext :=
    ManySortedFC.TermStaticSubst.Preserves.weakenTheory ready.core.target
      object.encoding.theory
  let namesProvenance := ready.provenance.substituteTarget namesSubstitution
    namesPreserves
  let nextCore := ready.core.extendObject sourceObject object
  let termSubstitution := ManySortedFC.TermStaticSubst.ofRename
    (ManySortedFC.Rename.succ
      (scope := Target.StaticScope targetScope object.encoding.symbols
        object.encoding.relations) (kind := .term))
  have termPreserves : termSubstitution.Preserves namesContext
      nextCore.target :=
    ManySortedFC.TermStaticSubst.Preserves.weaken namesContext
      (.term object.representation)
  refine { core := nextCore, provenance := ?_ }
  refine ActiveProvenance.renameSource namesProvenance
    (DOTCapture.BinderOnly.Rename.succ (scope := sourceScope) (kind := .term))
    termSubstitution termPreserves nextCore.captureMap ?_
  intro capture
  change Preparation.totalCapture
      (ready.core.layout.extendObject object.encoding)
      (capture.rename DOTCapture.BinderOnly.Rename.succ) =
    ((Preparation.totalCapture ready.core.layout capture).substitute
      (ManySortedFC.StaticSubst.ofRename namesRename)).substitute
      (ManySortedFC.StaticSubst.ofRename ManySortedFC.Rename.succ)
  rw [Preparation.totalCapture_extendObject,
    ManySortedFC.Capture.substitute_ofRename,
    ManySortedFC.Capture.substitute_ofRename,
    ManySortedFC.Capture.rename_comp]
  rfl

/-- Enter a source lock only after its complete modal interface has prepared.
The target theory is reconstructed canonically from the same successful
source interface so `ActiveProvenance.push` supplies its exact coordinates. -/
noncomputable def push {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (ready : Ready environment targetScope)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    (sourceRequirements : Source.ModalRequirements separationCount modes
      sourceScope)
    (prepared : PreparedModal ready.core sourceRequirements) :
    Ready (environment.push sourceRequirements)
      (Target.ModalScope targetScope separationCount
        (Preparation.translateModes modes)) := by
  cases sourceRequirements with
  | mk separation modeContext =>
      let targetRequirements := prepared.requirements
      have targetRequirementsEquality :
          mapRequirements ready.core.captureMap
              (.mk separation modeContext) = targetRequirements :=
        prepared.canonicalRequirements
      let nextCore := ready.core.push (.mk separation modeContext)
        targetRequirements
      refine { core := nextCore, provenance := ?_ }
      have pushed := ready.provenance.push separation modeContext
      have captureMapEquality :
          Preparation.totalCapture
              (ready.core.layout.weakenModal separationCount
                (Preparation.translateModes modes)) =
            (fun capture =>
              (Preparation.totalCapture ready.core.layout capture).rename
                (ManySortedFC.Rename.weakenModal targetScope separationCount
                  (Preparation.translateModes modes))) := by
        funext capture
        exact Preparation.totalCapture_weakenModal ready.core.layout
          separationCount (Preparation.translateModes modes) capture
      change ActiveProvenance
        (environment.locks.push (.mk separation modeContext))
        (ready.core.target.extendModal
          targetRequirements)
        (Preparation.totalCapture
          (ready.core.layout.weakenModal separationCount
            (Preparation.translateModes modes)))
      rw [captureMapEquality]
      rw [← targetRequirementsEquality]
      simpa only [Core.captureMap] using pushed

end Ready

end DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
