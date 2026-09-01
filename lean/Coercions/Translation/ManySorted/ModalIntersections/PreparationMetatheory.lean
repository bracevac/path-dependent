import Coercions.Translation.ManySorted.ModalIntersections.PreparationRenaming
import Coercions.Translation.ManySorted.BinderOnly.LayoutMetatheory

/-!
# Metatheory of cumulative preparation

Successful preparation follows coordinated source and target renamings.  The
statements in this file are deliberately phrased as equalities of partial
computations: malformed source syntax remains rejected on both sides, while a
successful result is identified with the renamed original artifact.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.Preparation

open DOTCaptureToManySortedFC.Intersections.Encoding

def renameMembers {first second : Target.Sig}
    (members : List (MemberName first)) (rho : Target.Rename first second) :
    List (MemberName second) :=
  members.map fun member => member.rename rho

private theorem renameMembers_comp {first second third : Target.Sig}
    (members : List (MemberName first))
    (rho₁ : Target.Rename first second) (rho₂ : Target.Rename second third) :
    renameMembers (renameMembers members rho₁) rho₂ =
      renameMembers members (rho₁.comp rho₂) := by
  induction members with
  | nil => rfl
  | cons member remaining induction =>
      cases member with
      | type label name =>
        change MemberName.type label (rho₂.var (rho₁.var name)) ::
            renameMembers (renameMembers remaining rho₁) rho₂ =
          MemberName.type label ((rho₁.comp rho₂).var name) ::
            renameMembers remaining (rho₁.comp rho₂)
        rw [induction]
        rfl
      | capture label name =>
        change MemberName.capture label (rho₂.var (rho₁.var name)) ::
            renameMembers (renameMembers remaining rho₁) rho₂ =
          MemberName.capture label ((rho₁.comp rho₂).var name) ::
            renameMembers remaining (rho₁.comp rho₂)
        rw [induction]
        rfl

@[simp]
private theorem find?_rename {first second : Target.Sig}
    (members : List (MemberName first))
    (rho : Target.Rename first second) (label : Nat) :
    MemberNames.find? (renameMembers members rho) label =
      (MemberNames.find? members label).map fun member => member.rename rho := by
  induction members with
  | nil => rfl
  | cons member remaining induction =>
      cases member with
      | type memberLabel name =>
          by_cases labelsMatch : memberLabel = label
          · subst memberLabel
            simp [renameMembers, MemberNames.find?, MemberName.rename,
              MemberName.label]
          · simp only [renameMembers, List.map_cons, MemberName.rename,
              MemberNames.find?, MemberName.label, labelsMatch, if_false]
            exact induction
      | capture memberLabel name =>
          by_cases labelsMatch : memberLabel = label
          · subst memberLabel
            simp [renameMembers, MemberNames.find?, MemberName.rename,
              MemberName.label]
          · simp only [renameMembers, List.map_cons, MemberName.rename,
              MemberNames.find?, MemberName.label, labelsMatch, if_false]
            exact induction

private def renameCaptureResult {first second : Target.Sig}
    (rho : Target.Rename first second) :
    Except Error (Target.Capture first) ->
      Except Error (Target.Capture second) :=
  Except.map fun capture => capture.rename rho

private def compileExpectCapture {scope : Target.Sig} (label : Nat) :
    MemberName scope -> Except Error
      (Target.BVar scope (.symbol .capture))
  | .capture _ name => .ok name
  | .type _ _ => .error (.memberSortMismatch label .capture .type)

private def compilePathMember {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (path : Source.Path sourceScope) (label : Nat) :
    Except Error (MemberName targetScope) :=
  match layout.member? path label with
  | some member => .ok member
  | none => .error (.unknownPathMember label)

private def compileLocalMember {scope : Target.Sig}
    (members : List (MemberName scope)) (label : Nat) :
    Except Error (MemberName scope) :=
  match MemberNames.find? members label with
  | some member => .ok member
  | none => .error (.unknownLocalMember label)

private def compileCaptureReference {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.StaticRef .capture sourceScope ->
      Except Error (Target.BVar targetScope (.symbol .capture))
  | .bound name => .ok (layout.staticSlot name).name
  | .captureMember path label => do
      compileExpectCapture label (← compilePathMember layout path label)
  | .localCaptureMember label => do
      compileExpectCapture label (← compileLocalMember members label)

private theorem translateCapture_ref {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (reference : Source.StaticRef .capture sourceScope) :
    Compile.translateCapture layout members (.ref reference) = (do
      pure (.cvar (← compileCaptureReference layout members reference))) := by
  rfl

private def compileExpectType {scope : Target.Sig} (label : Nat) :
    MemberName scope -> Except Error (Target.BVar scope (.symbol .type))
  | .type _ name => .ok name
  | .capture _ _ => .error (.memberSortMismatch label .type .capture)

private def compileTypeReference {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.StaticRef .type sourceScope ->
      Except Error (Target.BVar targetScope (.symbol .type))
  | .bound name => .ok (layout.staticSlot name).name
  | .typeMember path label => do
      compileExpectType label (← compilePathMember layout path label)
  | .localTypeMember label => do
      compileExpectType label (← compileLocalMember members label)

private theorem translateType_ref {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (reference : Source.StaticRef .type sourceScope) :
    Compile.translateType layout members (.ref reference) = (do
      pure (.tvar (← compileTypeReference layout members reference))) := by
  rfl

namespace Compile

private theorem compileTypeReference_follows
    {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    (members : List (MemberName firstTarget))
    (reference : Source.StaticRef .type firstSource) :
    compileTypeReference second (renameMembers members targetRename)
        (reference.rename sourceRename) =
      (compileTypeReference first members reference).map targetRename.var := by
  cases reference with
  | bound sourceVar =>
      simp only [DOTCapture.ModalIntersections.StaticRef.rename,
        compileTypeReference]
      rw [follows.staticSlot]
      rfl
  | typeMember path label =>
      simp only [DOTCapture.ModalIntersections.StaticRef.rename,
        compileTypeReference, compilePathMember, compileExpectType]
      rw [follows.member]
      cases found : first.member? path label with
      | none => rfl
      | some member => cases member <;> rfl
  | localTypeMember label =>
      simp only [DOTCapture.ModalIntersections.StaticRef.rename,
        compileTypeReference, compileLocalMember, compileExpectType]
      rw [find?_rename]
      cases found : MemberNames.find? members label with
      | none => rfl
      | some member => cases member <;> rfl

theorem translateCapture_follows {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    (members : List (MemberName firstTarget))
    (capture : Source.Capture firstSource) :
    translateCapture second (renameMembers members targetRename)
        (capture.rename sourceRename) =
      renameCaptureResult targetRename
        (translateCapture first members capture) := by
  induction capture with
  | empty => rfl
  | union left right leftInduction rightInduction =>
      simp only [DOTCapture.ModalIntersections.Capture.rename]
      change (do
          pure (ManySortedFC.Capture.union
            (← translateCapture second (renameMembers members targetRename)
              (left.rename sourceRename))
            (← translateCapture second (renameMembers members targetRename)
              (right.rename sourceRename)))) =
        (do
          pure (ManySortedFC.Capture.union
            (← translateCapture first members left)
            (← translateCapture first members right))).map fun target =>
              ManySortedFC.Capture.rename target targetRename
      rw [leftInduction, rightInduction]
      cases translateCapture first members left <;>
        cases translateCapture first members right <;> rfl
  | readOnly capture induction =>
      simp only [DOTCapture.ModalIntersections.Capture.rename]
      change (do
          pure (ManySortedFC.Capture.readOnly
            (← translateCapture second (renameMembers members targetRename)
              (capture.rename sourceRename)))) =
        (do
          pure (ManySortedFC.Capture.readOnly
            (← translateCapture first members capture))).map
            fun target => ManySortedFC.Capture.rename target targetRename
      rw [induction]
      cases translateCapture first members capture <;> rfl
  | singleton path =>
      cases path with
      | var sourceVar =>
          simp only [DOTCapture.ModalIntersections.Capture.rename,
            DOTCapture.ModalIntersections.Path.rename]
          change .ok (ManySortedFC.Capture.singleton
              (second.termVar (sourceRename.var sourceVar))) =
            Except.map (fun target =>
              ManySortedFC.Capture.rename target targetRename)
              (.ok (ManySortedFC.Capture.singleton
                (first.termVar sourceVar)))
          rw [follows.termVar]
          rfl
  | ref reference =>
      cases reference with
      | bound sourceVar =>
          simp only [DOTCapture.ModalIntersections.Capture.rename,
            DOTCapture.ModalIntersections.StaticRef.rename]
          change .ok (ManySortedFC.Capture.cvar
              (second.staticSlot (sourceRename.var sourceVar)).name) =
            Except.map (fun target =>
              ManySortedFC.Capture.rename target targetRename)
              (.ok (ManySortedFC.Capture.cvar
                (first.staticSlot sourceVar).name))
          rw [follows.staticSlot]
          rfl
      | captureMember path label =>
          simp only [DOTCapture.ModalIntersections.Capture.rename,
            DOTCapture.ModalIntersections.StaticRef.rename]
          rw [translateCapture_ref, translateCapture_ref]
          simp only [compileCaptureReference, compilePathMember,
            compileExpectCapture, renameCaptureResult]
          rw [follows.member]
          cases found : first.member? path label with
          | none => rfl
          | some member => cases member <;> rfl
      | localCaptureMember label =>
          simp only [DOTCapture.ModalIntersections.Capture.rename,
            DOTCapture.ModalIntersections.StaticRef.rename]
          rw [translateCapture_ref, translateCapture_ref]
          simp only [compileCaptureReference, compileLocalMember,
            compileExpectCapture, renameCaptureResult]
          rw [find?_rename]
          cases found : MemberNames.find? members label with
          | none => rfl
          | some member => cases member <;> rfl

theorem translateSeparationContext_follows
    {count : Nat} {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    (members : List (MemberName firstTarget))
    (context : Source.SeparationContext count firstSource) :
    translateSeparationContext second (renameMembers members targetRename)
        (context.rename sourceRename) =
      (translateSeparationContext first members context).map fun target =>
        ManySortedFC.SeparationContext.rename target targetRename := by
  induction context with
  | nil => rfl
  | cons rest capture induction =>
      simp only [DOTCapture.ModalIntersections.SeparationContext.rename]
      change (do
          pure (ManySortedFC.SeparationContext.cons
            (← translateSeparationContext second
              (renameMembers members targetRename)
              (rest.rename sourceRename))
            (← translateCapture second (renameMembers members targetRename)
              (capture.rename sourceRename)))) =
        (do
          pure (ManySortedFC.SeparationContext.cons
            (← translateSeparationContext first members rest)
            (← translateCapture first members capture))).map fun target =>
              ManySortedFC.SeparationContext.rename target targetRename
      rw [induction follows, translateCapture_follows follows]
      cases translateSeparationContext first members rest <;>
        cases translateCapture first members capture <;> rfl

theorem translateModeContext_follows
    {modes : List Source.CaptureMode}
    {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    (members : List (MemberName firstTarget))
    (context : Source.ModeContext modes firstSource) :
    translateModeContext second (renameMembers members targetRename)
        (context.rename sourceRename) =
      (translateModeContext first members context).map fun target =>
        ManySortedFC.ModeContext.rename target targetRename := by
  induction context with
  | nil => rfl
  | cons rest capture induction =>
      simp only [DOTCapture.ModalIntersections.ModeContext.rename]
      change (do
          pure (ManySortedFC.ModeContext.cons
            (← translateModeContext second
              (renameMembers members targetRename)
              (rest.rename sourceRename))
            (← translateCapture second (renameMembers members targetRename)
              (capture.rename sourceRename)))) =
        (do
          pure (ManySortedFC.ModeContext.cons
            (← translateModeContext first members rest)
            (← translateCapture first members capture))).map fun target =>
              ManySortedFC.ModeContext.rename target targetRename
      rw [induction follows, translateCapture_follows follows]
      cases translateModeContext first members rest <;>
        cases translateCapture first members capture <;> rfl

theorem translateRequirements_follows
    {count : Nat} {modes : List Source.CaptureMode}
    {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    (members : List (MemberName firstTarget))
    (requirements : Source.ModalRequirements count modes firstSource) :
    translateRequirements second (renameMembers members targetRename)
        (requirements.rename sourceRename) =
      (translateRequirements first members requirements).map fun target =>
        ManySortedFC.ModalContext.rename target targetRename := by
  cases requirements with
  | mk separation mode =>
      simp only [DOTCapture.ModalIntersections.ModalRequirements.rename]
      change (do
          pure (ManySortedFC.ModalContext.mk
            (← translateSeparationContext second
              (renameMembers members targetRename)
              (separation.rename sourceRename))
            (← translateModeContext second
              (renameMembers members targetRename)
              (mode.rename sourceRename)))) =
        (do
          pure (ManySortedFC.ModalContext.mk
            (← translateSeparationContext first members separation)
            (← translateModeContext first members mode))).map fun target =>
              ManySortedFC.ModalContext.rename target targetRename
      rw [translateSeparationContext_follows follows,
        translateModeContext_follows follows]
      cases translateSeparationContext first members separation <;>
        cases translateModeContext first members mode <;> rfl

end Compile

/-! ## Ambient modal preparation

The member list is empty outside an object names block, so the general
member-aware theorems specialize directly to compiler layouts.
-/

theorem translateCapture_follows {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    (capture : Source.Capture firstSource) :
    translateCapture second (capture.rename sourceRename) =
      (translateCapture first capture).map fun target =>
        target.rename targetRename := by
  simpa [translateCapture, renameMembers] using
    Compile.translateCapture_follows follows [] capture

theorem translateSeparationContext_follows
    {count : Nat} {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    (context : Source.SeparationContext count firstSource) :
    translateSeparationContext second (context.rename sourceRename) =
      (translateSeparationContext first context).map fun target =>
        target.rename targetRename := by
  simpa [translateSeparationContext, renameMembers] using
    Compile.translateSeparationContext_follows follows [] context

theorem translateModeContext_follows
    {modes : List Source.CaptureMode}
    {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    (context : Source.ModeContext modes firstSource) :
    translateModeContext second (context.rename sourceRename) =
      (translateModeContext first context).map fun target =>
        target.rename targetRename := by
  simpa [translateModeContext, renameMembers] using
    Compile.translateModeContext_follows follows [] context

theorem translateRequirements_follows
    {count : Nat} {modes : List Source.CaptureMode}
    {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    (requirements : Source.ModalRequirements count modes firstSource) :
    translateRequirements second (requirements.rename sourceRename) =
      (translateRequirements first requirements).map fun target =>
        target.rename targetRename := by
  simpa [translateRequirements, renameMembers] using
    Compile.translateRequirements_follows follows [] requirements

namespace Layout.Follows

@[simp]
theorem intervalRelations_rename {firstSource secondSource : Source.Sig}
    {sort : Source.StaticSort} (interval : Source.Interval sort firstSource)
    (rho : DOTCapture.ModalIntersections.Rename firstSource secondSource) :
    intervalRelations (interval.rename rho) = intervalRelations interval := by
  cases interval with
  | bounds lower upper => cases lower <;> cases upper <;> rfl

/-- Lift a target renaming below a source interval whose endpoints have been
renamed.  The cast changes only the proposition-spine index; the endpoint
presence theorem above makes it computationally the ordinary `liftStatic`. -/
def liftStaticFor {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    (rho : Target.Rename firstTarget secondTarget)
    {sort : Source.StaticSort} (interval : Source.Interval sort firstSource)
    (sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource) :
    Target.Rename
      (Target.StaticScope firstTarget [translateSort sort]
        (intervalRelations interval))
      (Target.StaticScope secondTarget [translateSort sort]
        (intervalRelations (interval.rename sourceRename))) :=
  match interval with
  | .bounds .none .none => rho.liftStatic [translateSort sort] []
  | .bounds (.some _) .none =>
      rho.liftStatic [translateSort sort] [.inclusion (translateSort sort)]
  | .bounds .none (.some _) =>
      rho.liftStatic [translateSort sort] [.inclusion (translateSort sort)]
  | .bounds (.some _) (.some _) =>
      rho.liftStatic [translateSort sort]
        [.inclusion (translateSort sort), .inclusion (translateSort sort)]

/-- Coordinated layout movements compose. -/
def comp {firstSource middleSource lastSource : Source.Sig}
    {firstTarget middleTarget lastTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {middle : Layout middleSource middleTarget}
    {last : Layout lastSource lastTarget}
    {firstSourceRename : DOTCapture.ModalIntersections.Rename
      firstSource middleSource}
    {secondSourceRename : DOTCapture.ModalIntersections.Rename
      middleSource lastSource}
    {firstTargetRename : Target.Rename firstTarget middleTarget}
    {secondTargetRename : Target.Rename middleTarget lastTarget}
    (firstFollows : Layout.Follows first middle firstSourceRename
      firstTargetRename)
    (secondFollows : Layout.Follows middle last secondSourceRename
      secondTargetRename) :
    Layout.Follows first last
      (firstSourceRename.comp secondSourceRename)
      (firstTargetRename.comp secondTargetRename) where
  termVar := by
    intro sourceVar
    rw [DOTCapture.BinderOnly.Rename.comp_var,
      secondFollows.termVar, firstFollows.termVar]
    rfl
  staticSlot := by
    intro sort sourceVar
    rw [DOTCapture.BinderOnly.Rename.comp_var,
      secondFollows.staticSlot, firstFollows.staticSlot,
      ManySortedTranslation.StaticSlot.rename_comp]
  member := by
    intro path label
    change last.member?
        ((path.rename firstSourceRename).rename secondSourceRename) label = _
    rw [secondFollows.member, firstFollows.member]
    cases found : first.member? path label with
    | none => rfl
    | some member => cases member <;> rfl

/-- Coordinated renaming remains coherent below one same-shape lexical
interval.  Endpoint syntax is renamed, but the emitted symbol/evidence spine
depends only on endpoint presence. -/
def extendStaticCongr {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    {sort : Source.StaticSort} (interval : Source.Interval sort firstSource) :
    Layout.Follows (first.extendStatic interval)
      (second.extendStatic (interval.rename sourceRename))
      sourceRename.lift
      (liftStaticFor targetRename interval sourceRename) := by
  cases interval with
  | bounds lower upper =>
      cases lower <;> cases upper
      all_goals
        refine
          { termVar := ?_
            staticSlot := ?_
            member := ?_ }
        · intro sourceVar
          cases sourceVar with
          | there older =>
              simp only [DOTCapture.ModalIntersections.Interval.rename,
                DOTCapture.ModalIntersections.Endpoint.rename,
                liftStaticFor, DOTCapture.BinderOnly.Rename.lift_there,
                Layout.extendStatic_term_there, intervalRelations]
              rw [follows.termVar]
              exact DOTCaptureToManySortedFC.BinderOnly.ManySortedRename.weakenStatic_liftStatic_var
                targetRename _ _ _
        · intro otherSort sourceVar
          cases sourceVar with
          | here =>
              simp only [DOTCapture.ModalIntersections.Interval.rename,
                DOTCapture.ModalIntersections.Endpoint.rename,
                liftStaticFor]
              cases sort <;> rfl
          | there older =>
              simp only [DOTCapture.ModalIntersections.Interval.rename,
                DOTCapture.ModalIntersections.Endpoint.rename,
                liftStaticFor]
              change
                ((second.staticSlot (sourceRename.var older)).rename
                    (ManySortedFC.Rename.weakenStatic _ _)) =
                  ((first.staticSlot older).rename
                    (ManySortedFC.Rename.weakenStatic _ _)).rename
                      (targetRename.liftStatic _ _)
              rw [follows.staticSlot,
                ManySortedTranslation.StaticSlot.rename_comp,
                ManySortedTranslation.StaticSlot.rename_comp,
                DOTCaptureToManySortedFC.BinderOnly.ManySortedRename.comp_weakenStatic]
        · intro path label
          cases path with
          | var sourceVar =>
              cases sourceVar with
              | there older =>
                  simp only [DOTCapture.ModalIntersections.Interval.rename,
                    DOTCapture.ModalIntersections.Endpoint.rename,
                    liftStaticFor]
                  change
                    (second.member? (.var (sourceRename.var older)) label).map
                        (fun member => member.rename
                          (ManySortedFC.Rename.weakenStatic _ _)) =
                      ((first.member? (.var older) label).map
                        (fun member => member.rename
                          (ManySortedFC.Rename.weakenStatic _ _))).map
                            (fun member => member.rename
                              (targetRename.liftStatic _ _))
                  rw [show second.member? (.var (sourceRename.var older)) label =
                    (first.member? (.var older) label).map fun member =>
                      member.rename targetRename from
                    follows.member (.var older) label]
                  cases found : first.member? (.var older) label with
                  | none => rfl
                  | some member =>
                      cases member <;>
                        simp only [Option.map_some, MemberName.rename]
                      all_goals
                        rw [DOTCaptureToManySortedFC.BinderOnly.ManySortedRename.weakenStatic_liftStatic_var]

/-- The auxiliary local-member table follows the same static weakening
square as the layout.  This is the list-level fact needed by nested interval
bodies in the member-aware compiler. -/
theorem renameMembers_extendStatic {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    (targetRename : Target.Rename firstTarget secondTarget)
    {sort : Source.StaticSort} (interval : Source.Interval sort firstSource)
    (sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource)
    (members : List (MemberName firstTarget)) :
    renameMembers (renameMembers members targetRename)
        (Layout.staticRename secondTarget (interval.rename sourceRename)) =
      renameMembers
        (renameMembers members (Layout.staticRename firstTarget interval))
        (liftStaticFor targetRename interval sourceRename) := by
  cases interval with
  | bounds lower upper =>
      cases lower <;> cases upper
      all_goals
        simp only [DOTCapture.ModalIntersections.Interval.rename,
          DOTCapture.ModalIntersections.Endpoint.rename, Layout.staticRename,
          intervalRelations, liftStaticFor]
        rw [renameMembers_comp, renameMembers_comp,
          DOTCaptureToManySortedFC.BinderOnly.ManySortedRename.comp_weakenStatic]

end Layout.Follows

def renameIntervalTheory {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    (rho : Target.Rename firstTarget secondTarget)
    {sort : Source.StaticSort} (interval : Source.Interval sort firstSource)
    (sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource) :
    Target.Theory firstTarget [translateSort sort]
        (intervalRelations interval) ->
      Target.Theory secondTarget [translateSort sort]
        (intervalRelations (interval.rename sourceRename)) :=
  match interval with
  | .bounds .none .none => fun theory => theory.rename rho
  | .bounds (.some _) .none => fun theory => theory.rename rho
  | .bounds .none (.some _) => fun theory => theory.rename rho
  | .bounds (.some _) (.some _) => fun theory => theory.rename rho

mutual

private def typeComplexity {scope : Source.Sig} : Source.Ty scope → Nat
  | .top | .bot | .one | .ref _ | .objectArrow _ _ | .object _ => 1
  | .arr domain codomain =>
      typeComplexity domain + typeComplexity codomain + 1
  | .capturing _ shape => typeComplexity shape + 1
  | .forallI interval body | .existsI interval body =>
      intervalComplexity interval + typeComplexity body + 1
  | .modal _ body => typeComplexity body + 1

private def staticExprComplexity {sort : Source.StaticSort}
    {scope : Source.Sig} : Source.StaticExpr sort scope → Nat
  | .type type => typeComplexity type + 1
  | .capture _ => 1

private def endpointComplexity {sort : Source.StaticSort}
    {scope : Source.Sig} :
    DOTCapture.ModalIntersections.Endpoint sort scope → Nat
  | .none => 1
  | .some expression => staticExprComplexity expression + 1

private def intervalComplexity {sort : Source.StaticSort}
    {scope : Source.Sig} : Source.Interval sort scope → Nat
  | .bounds lower upper =>
      endpointComplexity lower + endpointComplexity upper + 1

end

namespace Compile

mutual

theorem translateType_follows {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    (members : List (MemberName firstTarget))
    (type : Source.Ty firstSource) :
    translateType second (renameMembers members targetRename)
        (type.rename sourceRename) =
      (translateType first members type).map fun target =>
        ManySortedFC.Ty.rename target targetRename :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref reference => by
      simp only [DOTCapture.ModalIntersections.Ty.rename]
      rw [translateType_ref, translateType_ref,
        compileTypeReference_follows follows]
      cases compileTypeReference first members reference <;> rfl
  | .arr domain codomain => by
      simp only [DOTCapture.ModalIntersections.Ty.rename]
      change (do
          pure (ManySortedFC.Ty.arr
            (← translateType second (renameMembers members targetRename)
              (domain.rename sourceRename))
            (← translateType second (renameMembers members targetRename)
              (codomain.rename sourceRename)))) =
        (do
          pure (ManySortedFC.Ty.arr
            (← translateType first members domain)
            (← translateType first members codomain))).map fun target =>
              ManySortedFC.Ty.rename target targetRename
      rw [translateType_follows follows members domain,
        translateType_follows follows members codomain]
      cases translateType first members domain <;>
        cases translateType first members codomain <;> rfl
  | .objectArrow parameter resultTemplate => rfl
  | .capturing captures shape => by
      simp only [DOTCapture.ModalIntersections.Ty.rename]
      change (do
          pure (ManySortedFC.Ty.capturing
            (← translateCapture second (renameMembers members targetRename)
              (captures.rename sourceRename))
            (← translateType second (renameMembers members targetRename)
              (shape.rename sourceRename)))) =
        (do
          pure (ManySortedFC.Ty.capturing
            (← translateCapture first members captures)
            (← translateType first members shape))).map fun target =>
              ManySortedFC.Ty.rename target targetRename
      rw [translateCapture_follows follows members captures,
        translateType_follows follows members shape]
      cases translateCapture first members captures <;>
        cases translateType first members shape <;> rfl
  | @DOTCapture.ModalIntersections.Ty.forallI _ sort interval body => by
      have intervalFollows := translateInterval_follows follows members interval
      cases interval with
      | bounds lower upper =>
          cases lower <;> cases upper
          all_goals
            simp only [DOTCapture.ModalIntersections.Ty.rename]
            change (do
                pure (ManySortedFC.Ty.forallT
                  (← translateInterval second
                    (renameMembers members targetRename) _)
                  (← translateType (second.extendStatic _)
                    (renameMembers (renameMembers members targetRename)
                      (Layout.staticRename secondTarget _))
                    (body.rename sourceRename.lift)))) =
              (do
                pure (ManySortedFC.Ty.forallT
                  (← translateInterval first members _)
                  (← translateType (first.extendStatic _)
                    (renameMembers members
                      (Layout.staticRename firstTarget _)) body))).map
                fun target => ManySortedFC.Ty.rename target targetRename
            rw [intervalFollows]
            rw [Layout.Follows.renameMembers_extendStatic]
            rw [translateType_follows
              (Layout.Follows.extendStaticCongr follows _) _ body]
            cases translateInterval first members _ <;>
              cases translateType (first.extendStatic _)
                (renameMembers members (Layout.staticRename firstTarget _))
                body <;> rfl
  | @DOTCapture.ModalIntersections.Ty.existsI _ sort interval body => by
      have intervalFollows := translateInterval_follows follows members interval
      cases interval with
      | bounds lower upper =>
          cases lower <;> cases upper
          all_goals
            simp only [DOTCapture.ModalIntersections.Ty.rename]
            change (do
                pure (ManySortedFC.Ty.existsT
                  (← translateInterval second
                    (renameMembers members targetRename) _)
                  (← translateType (second.extendStatic _)
                    (renameMembers (renameMembers members targetRename)
                      (Layout.staticRename secondTarget _))
                    (body.rename sourceRename.lift)))) =
              (do
                pure (ManySortedFC.Ty.existsT
                  (← translateInterval first members _)
                  (← translateType (first.extendStatic _)
                    (renameMembers members
                      (Layout.staticRename firstTarget _)) body))).map
                fun target => ManySortedFC.Ty.rename target targetRename
            rw [intervalFollows]
            rw [Layout.Follows.renameMembers_extendStatic]
            rw [translateType_follows
              (Layout.Follows.extendStaticCongr follows _) _ body]
            cases translateInterval first members _ <;>
              cases translateType (first.extendStatic _)
                (renameMembers members (Layout.staticRename firstTarget _))
                body <;> rfl
  | .modal requirements body => by
      simp only [DOTCapture.ModalIntersections.Ty.rename]
      change (do
          pure (ManySortedFC.Ty.modal
            (← translateRequirements second
              (renameMembers members targetRename)
              (requirements.rename sourceRename))
            (← translateType second (renameMembers members targetRename)
              (body.rename sourceRename)))) =
        (do
          pure (ManySortedFC.Ty.modal
            (← translateRequirements first members requirements)
            (← translateType first members body))).map fun target =>
              ManySortedFC.Ty.rename target targetRename
      rw [translateRequirements_follows follows members requirements,
        translateType_follows follows members body]
      cases translateRequirements first members requirements <;>
        cases translateType first members body <;> rfl
  | .object object => rfl

termination_by typeComplexity type
decreasing_by
  all_goals
    simp [typeComplexity] <;> omega

theorem translateStaticExpr_follows {sort : Source.StaticSort}
    {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    (members : List (MemberName firstTarget))
    (expression : Source.StaticExpr sort firstSource) :
    translateStaticExpr second (renameMembers members targetRename)
        (expression.rename sourceRename) =
      (translateStaticExpr first members expression).map fun target =>
        ManySortedFC.StaticExpr.rename target targetRename :=
  match expression with
  | .type type => by
      simp only [DOTCapture.ModalIntersections.StaticExpr.rename]
      change (translateType second (renameMembers members targetRename)
          (type.rename sourceRename)).map ManySortedFC.StaticExpr.type =
        ((translateType first members type).map
          ManySortedFC.StaticExpr.type).map fun target =>
            ManySortedFC.StaticExpr.rename target targetRename
      rw [translateType_follows follows members type]
      cases translateType first members type <;> rfl
  | .capture capture => by
      simp only [DOTCapture.ModalIntersections.StaticExpr.rename]
      change (translateCapture second (renameMembers members targetRename)
          (capture.rename sourceRename)).map ManySortedFC.StaticExpr.capture =
        ((translateCapture first members capture).map
          ManySortedFC.StaticExpr.capture).map fun target =>
            ManySortedFC.StaticExpr.rename target targetRename
      rw [translateCapture_follows follows members capture]
      cases translateCapture first members capture <;> rfl

termination_by staticExprComplexity expression
decreasing_by
  all_goals
    simp [staticExprComplexity] <;> omega

theorem translateEndpoint_follows {sort : Source.StaticSort}
    {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    (members : List (MemberName firstTarget))
    (endpoint : DOTCapture.ModalIntersections.Endpoint sort firstSource) :
    match endpoint with
    | .none => True
    | .some expression =>
        translateStaticExpr second (renameMembers members targetRename)
            (expression.rename sourceRename) =
          (translateStaticExpr first members expression).map fun target =>
            ManySortedFC.StaticExpr.rename target targetRename :=
  match endpoint with
  | .none => True.intro
  | .some expression =>
      translateStaticExpr_follows follows members expression

termination_by endpointComplexity endpoint
decreasing_by
  all_goals
    simp [endpointComplexity] <;> omega

theorem translateInterval_follows {sort : Source.StaticSort}
    {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {first : Layout firstSource firstTarget}
    {second : Layout secondSource secondTarget}
    {sourceRename : DOTCapture.ModalIntersections.Rename
      firstSource secondSource}
    {targetRename : Target.Rename firstTarget secondTarget}
    (follows : Layout.Follows first second sourceRename targetRename)
    (members : List (MemberName firstTarget))
    (interval : Source.Interval sort firstSource) :
    translateInterval second (renameMembers members targetRename)
        (interval.rename sourceRename) =
      (translateInterval first members interval).map
        (renameIntervalTheory targetRename interval sourceRename) :=
  match interval with
  | .bounds lower upper => by
      have lowerFollows := translateEndpoint_follows follows members lower
      have upperFollows := translateEndpoint_follows follows members upper
      cases lower with
      | none =>
          cases upper with
          | none => rfl
          | some upper =>
              simp only [DOTCapture.ModalIntersections.Interval.rename,
                DOTCapture.ModalIntersections.Endpoint.rename]
              change (do
                  pure (ManySortedFC.Interval.upperBounded
                    (← translateStaticExpr second
                      (renameMembers members targetRename)
                      (upper.rename sourceRename)))) =
                (do
                  pure (ManySortedFC.Interval.upperBounded
                    (← translateStaticExpr first members upper))).map
                  (renameIntervalTheory targetRename
                    (.bounds .none (.some upper)) sourceRename)
              rw [upperFollows]
              cases translated : translateStaticExpr first members upper with
              | error failure => rfl
              | ok value =>
                  change Except.ok (ManySortedFC.Interval.upperBounded
                      (value.rename targetRename)) =
                    Except.ok ((ManySortedFC.Interval.upperBounded value).rename
                      targetRename)
                  exact congrArg Except.ok
                    (DOTCaptureToManySortedFC.BinderOnly.TargetInterval.upperBounded_rename
                      targetRename value).symm
      | some lower =>
          cases upper with
          | none =>
              simp only [DOTCapture.ModalIntersections.Interval.rename,
                DOTCapture.ModalIntersections.Endpoint.rename]
              change (do
                  pure (ManySortedFC.Interval.lowerBounded
                    (← translateStaticExpr second
                      (renameMembers members targetRename)
                      (lower.rename sourceRename)))) =
                (do
                  pure (ManySortedFC.Interval.lowerBounded
                    (← translateStaticExpr first members lower))).map
                  (renameIntervalTheory targetRename
                    (.bounds (.some lower) .none) sourceRename)
              rw [lowerFollows]
              cases translated : translateStaticExpr first members lower with
              | error failure => rfl
              | ok value =>
                  change Except.ok (ManySortedFC.Interval.lowerBounded
                      (value.rename targetRename)) =
                    Except.ok ((ManySortedFC.Interval.lowerBounded value).rename
                      targetRename)
                  exact congrArg Except.ok
                    (DOTCaptureToManySortedFC.BinderOnly.TargetInterval.lowerBounded_rename
                      targetRename value).symm
          | some upper =>
              simp only [DOTCapture.ModalIntersections.Interval.rename,
                DOTCapture.ModalIntersections.Endpoint.rename]
              change (do
                  pure (ManySortedFC.Interval.between
                    (← translateStaticExpr second
                      (renameMembers members targetRename)
                      (lower.rename sourceRename))
                    (← translateStaticExpr second
                      (renameMembers members targetRename)
                      (upper.rename sourceRename)))) =
                (do
                  pure (ManySortedFC.Interval.between
                    (← translateStaticExpr first members lower)
                    (← translateStaticExpr first members upper))).map
                  (renameIntervalTheory targetRename
                    (.bounds (.some lower) (.some upper)) sourceRename)
              rw [lowerFollows, upperFollows]
              cases lowerTranslated : translateStaticExpr first members lower with
              | error failure => rfl
              | ok lowerValue =>
                  cases upperTranslated :
                      translateStaticExpr first members upper with
                  | error failure => rfl
                  | ok upperValue =>
                      change Except.ok (ManySortedFC.Interval.between
                          (lowerValue.rename targetRename)
                          (upperValue.rename targetRename)) =
                        Except.ok ((ManySortedFC.Interval.between lowerValue
                          upperValue).rename targetRename)
                      exact congrArg Except.ok
                        (DOTCaptureToManySortedFC.BinderOnly.TargetInterval.between_rename
                          targetRename lowerValue upperValue).symm

termination_by intervalComplexity interval
decreasing_by
  all_goals
    simp [intervalComplexity] <;> omega

end

end Compile

namespace Compile

theorem translateType_extendPlain {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (type : Source.Ty sourceScope) :
    translateType layout.extendPlain
        (renameMembers members ManySortedFC.Rename.succ)
        (type.rename DOTCapture.BinderOnly.Rename.succ) =
      (translateType layout members type).map fun target =>
        target.rename ManySortedFC.Rename.succ :=
  translateType_follows (Layout.Follows.extendPlain layout) members type

theorem translateStaticExpr_extendPlain {sort : Source.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (expression : Source.StaticExpr sort sourceScope) :
    translateStaticExpr layout.extendPlain
        (renameMembers members ManySortedFC.Rename.succ)
        (expression.rename DOTCapture.BinderOnly.Rename.succ) =
      (translateStaticExpr layout members expression).map fun target =>
        target.rename ManySortedFC.Rename.succ :=
  translateStaticExpr_follows (Layout.Follows.extendPlain layout) members
    expression

theorem translateType_extendStatic {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) {sort : Source.StaticSort}
    (interval : Source.Interval sort sourceScope)
    (type : Source.Ty sourceScope) :
    translateType (layout.extendStatic interval)
        (renameMembers members (Layout.staticRename targetScope interval))
        (type.rename DOTCapture.BinderOnly.Rename.succ) =
      (translateType layout members type).map fun target =>
        target.rename (Layout.staticRename targetScope interval) :=
  translateType_follows (Layout.Follows.extendStatic layout interval) members
    type

theorem translateStaticExpr_extendStatic {expressionSort sort :
    Source.StaticSort} {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (interval : Source.Interval sort sourceScope)
    (expression : Source.StaticExpr expressionSort sourceScope) :
    translateStaticExpr (layout.extendStatic interval)
        (renameMembers members (Layout.staticRename targetScope interval))
        (expression.rename DOTCapture.BinderOnly.Rename.succ) =
      (translateStaticExpr layout members expression).map fun target =>
        target.rename (Layout.staticRename targetScope interval) :=
  translateStaticExpr_follows
    (Layout.Follows.extendStatic layout interval) members expression

theorem translateType_extendObject {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (encoding : Intersections.Encoding.Encoding targetScope)
    (type : Source.Ty sourceScope) :
    translateType (layout.extendObject encoding)
        (renameMembers members (Layout.objectRename targetScope))
        (type.rename DOTCapture.BinderOnly.Rename.succ) =
      (translateType layout members type).map fun target =>
        target.rename (Layout.objectRename targetScope) :=
  translateType_follows (Layout.Follows.extendObject layout encoding) members
    type

theorem translateStaticExpr_extendObject {sort : Source.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (encoding : Intersections.Encoding.Encoding targetScope)
    (expression : Source.StaticExpr sort sourceScope) :
    translateStaticExpr (layout.extendObject encoding)
        (renameMembers members (Layout.objectRename targetScope))
        (expression.rename DOTCapture.BinderOnly.Rename.succ) =
      (translateStaticExpr layout members expression).map fun target =>
        target.rename (Layout.objectRename targetScope) :=
  translateStaticExpr_follows
    (Layout.Follows.extendObject layout encoding) members expression

theorem translateType_weakenModal {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) (separationCount : Nat)
    (modes : List Target.CaptureMode) (type : Source.Ty sourceScope) :
    translateType (layout.weakenModal separationCount modes)
        (renameMembers members
          (ManySortedFC.Rename.weakenModal targetScope separationCount modes))
        type =
      (translateType layout members type).map fun target =>
        target.rename
          (ManySortedFC.Rename.weakenModal targetScope separationCount modes) := by
  simpa only [DOTCapture.ModalIntersections.Ty.rename_id] using
    translateType_follows
      (Layout.Follows.renameTarget layout
        (ManySortedFC.Rename.weakenModal targetScope separationCount modes))
      members type

theorem translateStaticExpr_weakenModal {sort : Source.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) (separationCount : Nat)
    (modes : List Target.CaptureMode)
    (expression : Source.StaticExpr sort sourceScope) :
    translateStaticExpr (layout.weakenModal separationCount modes)
        (renameMembers members
          (ManySortedFC.Rename.weakenModal targetScope separationCount modes))
        expression =
      (translateStaticExpr layout members expression).map fun target =>
        target.rename
          (ManySortedFC.Rename.weakenModal targetScope separationCount modes) := by
  simpa only [DOTCapture.ModalIntersections.StaticExpr.rename_id] using
    translateStaticExpr_follows
      (Layout.Follows.renameTarget layout
        (ManySortedFC.Rename.weakenModal targetScope separationCount modes))
      members expression

theorem translateType_extendPayload {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) {sort : Source.StaticSort}
    (interval : Source.Interval sort sourceScope)
    (type : Source.Ty sourceScope) :
    translateType (layout.extendPayload interval)
        (renameMembers members ((Layout.staticRename targetScope interval).comp
          ManySortedFC.Rename.succ))
        ((type.rename DOTCapture.BinderOnly.Rename.succ).rename
          DOTCapture.BinderOnly.Rename.succ) =
      (translateType layout members type).map fun target =>
        target.rename ((Layout.staticRename targetScope interval).comp
          ManySortedFC.Rename.succ) := by
  simpa only [Layout.extendPayload,
    DOTCapture.ModalIntersections.Ty.rename_comp] using
      translateType_follows
        ((Layout.Follows.extendStatic layout interval).comp
          (Layout.Follows.extendPlain (layout.extendStatic interval)))
        members type

theorem translateStaticExpr_extendPayload {expressionSort sort :
    Source.StaticSort} {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (interval : Source.Interval sort sourceScope)
    (expression : Source.StaticExpr expressionSort sourceScope) :
    translateStaticExpr (layout.extendPayload interval)
        (renameMembers members ((Layout.staticRename targetScope interval).comp
          ManySortedFC.Rename.succ))
        ((expression.rename DOTCapture.BinderOnly.Rename.succ).rename
          DOTCapture.BinderOnly.Rename.succ) =
      (translateStaticExpr layout members expression).map fun target =>
        target.rename ((Layout.staticRename targetScope interval).comp
          ManySortedFC.Rename.succ) := by
  simpa only [Layout.extendPayload,
    DOTCapture.ModalIntersections.StaticExpr.rename_comp] using
      translateStaticExpr_follows
        ((Layout.Follows.extendStatic layout interval).comp
          (Layout.Follows.extendPlain (layout.extendStatic interval)))
        members expression

end Compile

@[simp]
theorem translateCapture_extendPlain {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (capture : Source.Capture sourceScope) :
    translateCapture layout.extendPlain capture.weaken =
      (translateCapture layout capture).map fun target =>
        target.rename ManySortedFC.Rename.succ :=
  translateCapture_follows (Layout.Follows.extendPlain layout) capture

@[simp]
theorem translateCapture_extendStatic {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    {sort : Source.StaticSort} (interval : Source.Interval sort sourceScope)
    (capture : Source.Capture sourceScope) :
    translateCapture (layout.extendStatic interval) capture.weaken =
      (translateCapture layout capture).map fun target =>
        target.rename (Layout.staticRename targetScope interval) :=
  translateCapture_follows (Layout.Follows.extendStatic layout interval) capture

@[simp]
theorem translateCapture_extendObject {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (encoding : Intersections.Encoding.Encoding targetScope)
    (capture : Source.Capture sourceScope) :
    translateCapture (layout.extendObject encoding) capture.weaken =
      (translateCapture layout capture).map fun target =>
        target.rename (Layout.objectRename targetScope) :=
  translateCapture_follows (Layout.Follows.extendObject layout encoding) capture

@[simp]
theorem translateCapture_weakenModal {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (separationCount : Nat) (modes : List Target.CaptureMode)
    (capture : Source.Capture sourceScope) :
    translateCapture (layout.weakenModal separationCount modes) capture =
      (translateCapture layout capture).map fun target =>
        target.rename
          (ManySortedFC.Rename.weakenModal targetScope separationCount modes) := by
  simpa only [DOTCapture.ModalIntersections.Capture.rename_id] using
    translateCapture_follows
      (Layout.Follows.renameTarget layout
        (ManySortedFC.Rename.weakenModal targetScope separationCount modes))
      capture

/-- Package payload extension is the composition of lexical-static and term
weakening; no special coordinate law is hidden in the compiler. -/
theorem translateCapture_extendPayload {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    {sort : Source.StaticSort} (interval : Source.Interval sort sourceScope)
    (capture : Source.Capture sourceScope) :
    translateCapture (layout.extendPayload interval)
        ((capture.weaken (kind := .static sort)).weaken (kind := .term)) =
      (translateCapture layout capture).map fun target =>
        target.rename ((Layout.staticRename targetScope interval).comp
          ManySortedFC.Rename.succ) := by
  simpa only [Layout.extendPayload,
    DOTCapture.ModalIntersections.Capture.weaken,
    DOTCapture.ModalIntersections.Capture.rename_comp] using
      translateCapture_follows
        ((Layout.Follows.extendStatic layout interval).comp
          (Layout.Follows.extendPlain (layout.extendStatic interval))) capture

/-! ## Same-shape lexical intervals

Endpoint expressions do not participate in coordinate allocation.  Replacing
an endpoint while preserving which sides are present therefore leaves the
extended source-to-target layout literally unchanged.  These equalities are
the alignment facts used by same-shape interval entailment: the available and
required theories may contain different propositions, but their dependent
bodies use exactly the same coordinates.
-/

namespace Layout

theorem extendStatic_lower_eq {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    {sort : Source.StaticSort}
    (first second : Source.StaticExpr sort sourceScope) :
    layout.extendStatic (.bounds (.some first) .none) =
      layout.extendStatic (.bounds (.some second) .none) := by
  apply Layout.ext
  · intro sourceVar
    cases sourceVar <;> rfl
  · intro otherSort sourceVar
    cases sourceVar <;> rfl
  · intro path label
    cases path with
    | var sourceVar => cases sourceVar <;> rfl

theorem extendStatic_upper_eq {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    {sort : Source.StaticSort}
    (first second : Source.StaticExpr sort sourceScope) :
    layout.extendStatic (.bounds .none (.some first)) =
      layout.extendStatic (.bounds .none (.some second)) := by
  apply Layout.ext
  · intro sourceVar
    cases sourceVar <;> rfl
  · intro otherSort sourceVar
    cases sourceVar <;> rfl
  · intro path label
    cases path with
    | var sourceVar => cases sourceVar <;> rfl

theorem extendStatic_between_eq {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    {sort : Source.StaticSort}
    (firstLower firstUpper secondLower secondUpper :
      Source.StaticExpr sort sourceScope) :
    layout.extendStatic (.bounds (.some firstLower) (.some firstUpper)) =
      layout.extendStatic (.bounds (.some secondLower) (.some secondUpper)) := by
  apply Layout.ext
  · intro sourceVar
    cases sourceVar <;> rfl
  · intro otherSort sourceVar
    cases sourceVar <;> rfl
  · intro path label
    cases path with
    | var sourceVar => cases sourceVar <;> rfl

end Layout

theorem translateType_extendStatic_lower_eq
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) {sort : Source.StaticSort}
    (available required : Source.StaticExpr sort sourceScope)
    (body : Source.Ty (sourceScope ▹ .static sort)) :
    translateType (layout.extendStatic (.bounds (.some required) .none)) body =
      translateType
        (layout.extendStatic (.bounds (.some available) .none)) body := by
  rw [Layout.extendStatic_lower_eq layout required available]
  rfl

theorem translateType_extendStatic_upper_eq
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) {sort : Source.StaticSort}
    (available required : Source.StaticExpr sort sourceScope)
    (body : Source.Ty (sourceScope ▹ .static sort)) :
    translateType (layout.extendStatic (.bounds .none (.some required))) body =
      translateType
        (layout.extendStatic (.bounds .none (.some available))) body := by
  rw [Layout.extendStatic_upper_eq layout required available]
  rfl

theorem translateType_extendStatic_between_eq
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) {sort : Source.StaticSort}
    (availableLower availableUpper requiredLower requiredUpper :
      Source.StaticExpr sort sourceScope)
    (body : Source.Ty (sourceScope ▹ .static sort)) :
    translateType
        (layout.extendStatic
          (.bounds (.some requiredLower) (.some requiredUpper))) body =
      translateType
        (layout.extendStatic
          (.bounds (.some availableLower) (.some availableUpper))) body := by
  rw [Layout.extendStatic_between_eq layout requiredLower requiredUpper
    availableLower availableUpper]
  rfl

end DOTCaptureToManySortedFC.ModalIntersections.Preparation
