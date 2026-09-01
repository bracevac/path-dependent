import Coercions.DOT.Captures.ModalIntersections.Structural
import Coercions.Translation.ManySorted.ModalIntersections.ModalProvenance

/-!
# Capture preparation under coordinated renaming

Preparation is intentionally partial: malformed member selections are
rejected.  Active modal provenance nevertheless needs a total interpretation
of source captures.  This file supplies the canonical total interpretation
used by compiler-ready contexts and proves that it follows coordinated source
and target weakenings.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections

open DOTCaptureToManySortedFC.Intersections.Encoding

namespace Preparation

@[simp]
theorem totalSeparationContext_eq_mapSeparationContext {count : Nat}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.SeparationContext count sourceScope) :
    totalSeparationContext layout source =
      mapSeparationContext (totalCapture layout) source := by
  induction source with
  | nil => rfl
  | cons rest capture induction =>
      simp [totalSeparationContext, mapSeparationContext, induction]

@[simp]
theorem totalModeContext_eq_mapModeContext
    {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.ModeContext modes sourceScope) :
    totalModeContext layout source =
      mapModeContext (totalCapture layout) source := by
  induction source with
  | nil => rfl
  | cons rest capture induction =>
      simp [totalModeContext, mapModeContext, induction]

@[simp]
theorem totalRequirements_eq_mapRequirements {count : Nat}
    {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.ModalRequirements count modes sourceScope) :
    totalRequirements layout source =
      mapRequirements (totalCapture layout) source := by
  cases source
  simp [totalRequirements, mapRequirements]

namespace Layout

/-- A source renaming and target renaming move every coordinate in two
layouts in lockstep. -/
structure Follows {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    (first : Layout firstSource firstTarget)
    (second : Layout secondSource secondTarget)
    (sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource)
    (targetRename : Target.Rename firstTarget secondTarget) : Prop where
  termVar : forall sourceVar,
    second.termVar (sourceRename.var sourceVar) =
      targetRename.var (first.termVar sourceVar)
  staticSlot : forall {sort} sourceVar,
    second.staticSlot (sourceRename.var sourceVar) =
      (first.staticSlot (sort := sort) sourceVar).rename targetRename
  member : forall path label,
    second.member? (path.rename sourceRename) label =
      (first.member? path label).map fun name => name.rename targetRename
  localType : forall label,
    second.localModel.typeMember? label =
      (first.localModel.typeMember? label).map fun type =>
        type.rename targetRename
  localCapture : forall label,
    second.localModel.captureMember? label =
      (first.localModel.captureMember? label).map fun capture =>
        capture.rename targetRename
  localClassifier : forall label,
    second.localModel.classifierMember? label =
      (first.localModel.classifierMember? label).map fun classifier =>
        classifier.rename targetRename

namespace Follows

def renameTarget {sourceScope : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    (layout : Layout sourceScope firstTarget)
    (rho : Target.Rename firstTarget secondTarget) :
    Follows layout (layout.renameTarget rho)
      DOTCapture.BinderOnly.Rename.id rho where
  termVar := by intro sourceVar; rfl
  staticSlot := by intro sort sourceVar; rfl
  member := by
    intro path label
    simp
  localType := by intro label; rfl
  localCapture := by intro label; rfl
  localClassifier := by intro label; rfl

def extendPlain {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) :
    Follows layout layout.extendPlain
      DOTCapture.BinderOnly.Rename.succ ManySortedFC.Rename.succ where
  termVar := by intro sourceVar; rfl
  staticSlot := by intro sort sourceVar; rfl
  member := by intro path label; cases path; rfl
  localType := by intro label; rfl
  localCapture := by intro label; rfl
  localClassifier := by intro label; rfl

def extendStatic {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) {sort : Source.StaticSort}
    (interval : Source.Interval sort sourceScope) :
    Follows layout (layout.extendStatic interval)
      DOTCapture.BinderOnly.Rename.succ
      (Layout.staticRename targetScope interval) where
  termVar := by intro sourceVar; rfl
  staticSlot := by intro olderSort sourceVar; rfl
  member := by intro path label; cases path; rfl
  localType := by intro label; rfl
  localCapture := by intro label; rfl
  localClassifier := by intro label; rfl

def extendObject {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (encoding : Intersections.Encoding.Encoding targetScope) :
    Follows layout (layout.extendObject encoding)
      DOTCapture.BinderOnly.Rename.succ
      (Layout.objectRename targetScope) where
  termVar := by intro sourceVar; rfl
  staticSlot := by intro sort sourceVar; rfl
  member := by intro path label; cases path; rfl
  localType := by intro label; rfl
  localCapture := by intro label; rfl
  localClassifier := by intro label; rfl

def extendObjectWith {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (symbols : List Target.StaticSort) (relations : List Target.Relation)
    (openedMembers : List (Intersections.Encoding.MemberName
      (Target.StaticScope targetScope symbols relations))) :
    Follows layout
      (layout.extendObjectWith symbols relations openedMembers)
      DOTCapture.BinderOnly.Rename.succ
      (Layout.objectRename targetScope) where
  termVar := by intro sourceVar; rfl
  staticSlot := by intro sort sourceVar; rfl
  member := by intro path label; cases path; rfl
  localType := by intro label; rfl
  localCapture := by intro label; rfl
  localClassifier := by intro label; rfl

end Follows

end Layout

/-- Total classifier interpretation is natural under coordinated source and
target renaming.  As for captures, malformed member selections retain their
canonical ground fallback on both sides. -/
@[simp]
theorem totalClassifier_follows {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    (classifier : Source.ClassifierExpr firstSource) :
    totalClassifier second (classifier.rename sourceRename) =
      (totalClassifier first classifier).rename targetRename := by
  cases classifier with
  | ground kind => rfl
  | ref reference =>
      cases reference with
      | member path label =>
          simp only [DOTCapture.ModalIntersections.ClassifierExpr.rename,
            DOTCapture.ModalIntersections.ClassifierRef.rename,
            totalClassifier]
          rw [show
            second.member? (path.rename sourceRename) label =
              (first.member? path label).map
                (fun name => name.rename targetRename) from
            follows.member path label]
          cases found : first.member? path label with
          | none => rfl
          | some member => cases member <;> rfl
      | localMember label =>
          simp only [DOTCapture.ModalIntersections.ClassifierExpr.rename,
            DOTCapture.ModalIntersections.ClassifierRef.rename,
            totalClassifier]
          rw [follows.localClassifier]
          cases found : first.localModel.classifierMember? label with
          | none => rfl
          | some classifier => rfl

/-- Total capture interpretation is natural under coordinated source and
target renaming.  Member lookup is compared before inspecting the member
sort, so duplicate labels and rejected sort mismatches are preserved. -/
@[simp]
theorem totalCapture_follows {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    (capture : Source.Capture firstSource) :
    totalCapture second (capture.rename sourceRename) =
      (totalCapture first capture).rename targetRename := by
  induction capture with
  | empty => rfl
  | union left right leftInduction rightInduction =>
      simp [DOTCapture.ModalIntersections.Capture.rename, totalCapture,
        ManySortedFC.Capture.rename, leftInduction, rightInduction]
  | project capture classifier captureInduction =>
      simp [DOTCapture.ModalIntersections.Capture.rename, totalCapture,
        ManySortedFC.Capture.rename, captureInduction,
        totalClassifier_follows follows classifier]
  | readOnly capture induction =>
      simp [DOTCapture.ModalIntersections.Capture.rename, totalCapture,
        ManySortedFC.Capture.rename, induction]
  | singleton path =>
      cases path with
      | var sourceVar =>
          simp [DOTCapture.ModalIntersections.Capture.rename,
            DOTCapture.ModalIntersections.Path.rename, totalCapture,
            ManySortedFC.Capture.rename, follows.termVar]
  | ref reference =>
      cases reference with
      | bound sourceVar =>
          simp only [DOTCapture.ModalIntersections.Capture.rename,
            DOTCapture.ModalIntersections.StaticRef.rename, totalCapture,
            ManySortedFC.Capture.rename]
          rw [follows.staticSlot]
          rfl
      | captureMember path label =>
          simp only [DOTCapture.ModalIntersections.Capture.rename,
            DOTCapture.ModalIntersections.StaticRef.rename, totalCapture]
          rw [show
            second.member? (path.rename sourceRename) label =
              (first.member? path label).map
                (fun name => name.rename targetRename) from
            follows.member path label]
          cases found : first.member? path label with
          | none => rfl
          | some member =>
              cases member <;> rfl
      | localCaptureMember label =>
          simp only [DOTCapture.ModalIntersections.Capture.rename,
            DOTCapture.ModalIntersections.StaticRef.rename, totalCapture]
          rw [follows.localCapture]
          cases found : first.localModel.captureMember? label with
          | none => rfl
          | some capture => rfl

@[simp]
theorem totalCapture_renameTarget {sourceScope : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    (layout : Layout sourceScope firstTarget)
    (rho : Target.Rename firstTarget secondTarget)
    (capture : Source.Capture sourceScope) :
    totalCapture (layout.renameTarget rho) capture =
      (totalCapture layout capture).rename rho := by
  simpa using totalCapture_follows
    (Layout.Follows.renameTarget layout rho) capture

@[simp]
theorem totalCapture_extendPlain {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (capture : Source.Capture sourceScope) :
    totalCapture layout.extendPlain
        (capture.rename DOTCapture.BinderOnly.Rename.succ) =
      (totalCapture layout capture).rename ManySortedFC.Rename.succ :=
  totalCapture_follows (Layout.Follows.extendPlain layout) capture

@[simp]
theorem totalCapture_extendStatic {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    {sort : Source.StaticSort}
    (interval : Source.Interval sort sourceScope)
    (capture : Source.Capture sourceScope) :
    totalCapture (layout.extendStatic interval)
        (capture.rename DOTCapture.BinderOnly.Rename.succ) =
      (totalCapture layout capture).rename
        (Layout.staticRename targetScope interval) :=
  totalCapture_follows (Layout.Follows.extendStatic layout interval) capture

@[simp]
theorem totalCapture_extendObject {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (encoding : Intersections.Encoding.Encoding targetScope)
    (capture : Source.Capture sourceScope) :
    totalCapture (layout.extendObject encoding)
        (capture.rename DOTCapture.BinderOnly.Rename.succ) =
      (totalCapture layout capture).rename
        (Layout.objectRename targetScope) :=
  totalCapture_follows (Layout.Follows.extendObject layout encoding) capture

@[simp]
theorem totalCapture_extendObjectWith {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (symbols : List Target.StaticSort) (relations : List Target.Relation)
    (openedMembers : List (Intersections.Encoding.MemberName
      (Target.StaticScope targetScope symbols relations)))
    (capture : Source.Capture sourceScope) :
    totalCapture (layout.extendObjectWith symbols relations openedMembers)
        (capture.rename DOTCapture.BinderOnly.Rename.succ) =
      (totalCapture layout capture).rename
        (Layout.objectRename targetScope) :=
  totalCapture_follows
    (Layout.Follows.extendObjectWith layout symbols relations openedMembers)
    capture

@[simp]
theorem totalCapture_weakenModal {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (separationCount : Nat) (modes : List Target.CaptureMode)
    (capture : Source.Capture sourceScope) :
    totalCapture (layout.weakenModal separationCount modes) capture =
      (totalCapture layout capture).rename
        (ManySortedFC.Rename.weakenModal targetScope separationCount modes) :=
  totalCapture_renameTarget layout _ capture

end Preparation

end DOTCaptureToManySortedFC.ModalIntersections
