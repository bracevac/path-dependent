import Coercions.DOT.Captures.ModalIntersections.Syntax
import Coercions.Translation.ManySorted.StaticSlot
import Coercions.Translation.ManySorted.Intersections.Preparation

/-!
# Cumulative source-to-target layouts

The cumulative source has three independent classes of stable coordinates:

* ordinary term variables, which retain one runtime slot;
* lexical static variables, which expand to one target symbol and the
  evidence slots contributed by their true interval; and
* labeled members selected from stable object roots, whose names were
  allocated by the intersection encoding.

This module combines those coordinates without translating types or building
target contexts.  Every extension is therefore determined only by binder
shape and by an already prepared names-first object encoding.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections

namespace Source

abbrev StaticSort := DOTCapture.ModalIntersections.StaticSort
abbrev BinderKind := DOTCapture.ModalIntersections.BinderKind
abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev BVar := DOTCapture.ModalIntersections.BVar
abbrev Path := DOTCapture.ModalIntersections.Path
abbrev Interval := DOTCapture.ModalIntersections.Interval

end Source

namespace Target

abbrev StaticSort := ManySortedFC.StaticSort
abbrev Relation := ManySortedFC.Relation
abbrev CaptureMode := ManySortedFC.CaptureMode
abbrev Sig := ManySortedFC.Sig
abbrev BVar := ManySortedFC.BVar
abbrev Rename := ManySortedFC.Rename
abbrev StaticScope := ManySortedFC.StaticScope
abbrev ModalScope := ManySortedFC.ModalScope

end Target

open DOTCaptureToManySortedFC.Intersections.Encoding

/-- The source and target use distinct syntax types for the same two static
sorts. -/
def translateSort : Source.StaticSort -> Target.StaticSort
  | .type => .type
  | .capture => .capture

/-- Evidence-binder shape contributed by one lexical source interval. -/
def intervalRelations {scope : Source.Sig} {sort : Source.StaticSort} :
    Source.Interval sort scope -> List Target.Relation
  | .bounds .none .none => []
  | .bounds (.some _) .none => [.inclusion (translateSort sort)]
  | .bounds .none (.some _) => [.inclusion (translateSort sort)]
  | .bounds (.some _) (.some _) =>
      [.inclusion (translateSort sort), .inclusion (translateSort sort)]

/-- One cumulative source layout in an independently chosen target scope.

Lexical static references and stable object members deliberately have
different lookup fields.  The former return interval evidence coordinates;
the latter return the shared member identity allocated by an object
encoding. -/
structure Layout (sourceScope : Source.Sig) (targetScope : Target.Sig) where
  termVar : Source.BVar sourceScope .term -> Target.BVar targetScope .term
  staticSlot : {sort : Source.StaticSort} ->
    Source.BVar sourceScope (.static sort) ->
      ManySortedTranslation.StaticSlot targetScope (translateSort sort)
  member? : Source.Path sourceScope -> Nat -> Option (MemberName targetScope)

namespace Layout

/-- Two layouts with the same three coordinate maps are equal. -/
@[ext (iff := false)]
theorem ext {sourceScope : Source.Sig} {targetScope : Target.Sig}
    {first second : Layout sourceScope targetScope}
    (termVar : forall sourceVar,
      first.termVar sourceVar = second.termVar sourceVar)
    (staticSlot : forall {sort} sourceVar,
      first.staticSlot (sort := sort) sourceVar =
        second.staticSlot (sort := sort) sourceVar)
    (member : forall path label,
      first.member? path label = second.member? path label) :
    first = second := by
  cases first with
  | mk firstTerm firstStatic firstMember =>
      cases second with
      | mk secondTerm secondStatic secondMember =>
          congr
          · funext sourceVar
            exact termVar sourceVar
          · funext sort sourceVar
            exact staticSlot sourceVar
          · funext path label
            exact member path label

/-- Rename every target coordinate while keeping the source scope fixed. -/
def renameTarget {sourceScope : Source.Sig} {first second : Target.Sig}
    (layout : Layout sourceScope first) (rho : Target.Rename first second) :
    Layout sourceScope second where
  termVar := fun sourceVar => rho.var (layout.termVar sourceVar)
  staticSlot := fun sourceVar => (layout.staticSlot sourceVar).rename rho
  member? := fun path label =>
    (layout.member? path label).map fun member => member.rename rho

@[simp]
theorem renameTarget_termVar {sourceScope : Source.Sig}
    {first second : Target.Sig} (layout : Layout sourceScope first)
    (rho : Target.Rename first second)
    (sourceVar : Source.BVar sourceScope .term) :
    (layout.renameTarget rho).termVar sourceVar =
      rho.var (layout.termVar sourceVar) := rfl

@[simp]
theorem renameTarget_staticSlot {sourceScope : Source.Sig}
    {first second : Target.Sig} (layout : Layout sourceScope first)
    (rho : Target.Rename first second) {sort : Source.StaticSort}
    (sourceVar : Source.BVar sourceScope (.static sort)) :
    (layout.renameTarget rho).staticSlot sourceVar =
      (layout.staticSlot sourceVar).rename rho := rfl

@[simp]
theorem renameTarget_member {sourceScope : Source.Sig}
    {first second : Target.Sig} (layout : Layout sourceScope first)
    (rho : Target.Rename first second) (path : Source.Path sourceScope)
    (label : Nat) :
    (layout.renameTarget rho).member? path label =
      (layout.member? path label).map fun member => member.rename rho := rfl

@[simp]
theorem renameTarget_id {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope) :
    layout.renameTarget ManySortedFC.Rename.id = layout := by
  apply Layout.ext
  · intro sourceVar
    rfl
  · intro sort sourceVar
    exact ManySortedTranslation.StaticSlot.rename_id
      (layout.staticSlot sourceVar)
  · intro path label
    cases found : layout.member? path label with
    | none => simp only [renameTarget_member, found, Option.map_none]
    | some targetMember =>
        simp only [renameTarget_member, found, Option.map_some]
        cases targetMember <;> rfl

@[simp]
theorem renameTarget_comp {sourceScope : Source.Sig}
    {first second third : Target.Sig} (layout : Layout sourceScope first)
    (rho₁ : Target.Rename first second) (rho₂ : Target.Rename second third) :
    (layout.renameTarget rho₁).renameTarget rho₂ =
      layout.renameTarget (rho₁.comp rho₂) := by
  apply Layout.ext
  · intro sourceVar
    rfl
  · intro sort sourceVar
    exact ManySortedTranslation.StaticSlot.rename_comp
      (layout.staticSlot sourceVar) rho₁ rho₂
  · intro path label
    cases found : layout.member? path label with
    | none => simp only [renameTarget_member, found, Option.map_none]
    | some targetMember =>
        simp only [renameTarget_member, found, Option.map_some]
        cases targetMember <;> rfl

/-! ## Ordinary term extension -/

/-- Extend by an ordinary runtime binder.  It contributes no stable member
names; all older coordinates are weakened once. -/
def extendPlain {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) :
    Layout (sourceScope ▹ .term) (targetScope ▹ .term) where
  termVar := fun
    | .here => .here
    | .there older => .there (layout.termVar older)
  staticSlot := fun
    | .there older => (layout.staticSlot older).weaken
  member? := fun path label =>
    match path with
    | .var .here => none
    | .var (.there older) =>
        (layout.member? (.var older) label).map fun member =>
          member.rename ManySortedFC.Rename.succ

@[simp]
theorem extendPlain_term_here {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope) :
    layout.extendPlain.termVar .here = .here := rfl

@[simp]
theorem extendPlain_term_there {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (sourceVar : Source.BVar sourceScope .term) :
    layout.extendPlain.termVar (.there sourceVar) =
      .there (layout.termVar sourceVar) := rfl

@[simp]
theorem extendPlain_static_there {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    {sort : Source.StaticSort}
    (sourceVar : Source.BVar sourceScope (.static sort)) :
    layout.extendPlain.staticSlot (.there sourceVar) =
      (layout.staticSlot sourceVar).weaken := rfl

@[simp]
theorem extendPlain_member_here {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (label : Nat) :
    layout.extendPlain.member? (.var .here) label = none := rfl

@[simp]
theorem extendPlain_member_there {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (sourceVar : Source.BVar sourceScope .term) (label : Nat) :
    layout.extendPlain.member? (.var (.there sourceVar)) label =
      (layout.member? (.var sourceVar) label).map fun member =>
        member.rename ManySortedFC.Rename.succ := rfl

/-! ## Lexical static extension -/

/-- Target weakening contributed by a one-symbol lexical interval. -/
def staticRename (targetScope : Target.Sig) {sourceScope : Source.Sig}
    {sort : Source.StaticSort} (interval : Source.Interval sort sourceScope) :
    Target.Rename targetScope
      (Target.StaticScope targetScope [translateSort sort]
        (intervalRelations interval)) :=
  ManySortedFC.Rename.weakenStatic [translateSort sort]
    (intervalRelations interval)

/-- Exact target coordinates allocated for the newest lexical static binder.
Only endpoint presence matters at the layout layer. -/
def newestStaticSlot (targetScope : Target.Sig) {sourceScope : Source.Sig}
    {sort : Source.StaticSort} (interval : Source.Interval sort sourceScope) :
    ManySortedTranslation.StaticSlot
      (Target.StaticScope targetScope [translateSort sort]
        (intervalRelations interval)) (translateSort sort) :=
  match interval with
  | .bounds .none .none =>
      ManySortedTranslation.StaticSlot.unconstrained targetScope
        (translateSort sort)
  | .bounds (.some _) .none =>
      { name := .there .here, lower := some .here, upper := none }
  | .bounds .none (.some _) =>
      { name := .there .here, lower := none, upper := some .here }
  | .bounds (.some _) (.some _) =>
      { name := .there (.there .here)
        lower := some .here
        upper := some (.there .here) }

/-- Extend by one lexical type/capture binder and its exact optional interval
evidence slots.  Stable object roots are merely weakened. -/
def extendStatic {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) {sort : Source.StaticSort}
    (interval : Source.Interval sort sourceScope) :
    Layout (sourceScope ▹ .static sort)
      (Target.StaticScope targetScope [translateSort sort]
        (intervalRelations interval)) where
  termVar := fun
    | .there older => (staticRename targetScope interval).var
        (layout.termVar older)
  staticSlot := fun
    | .here => newestStaticSlot targetScope interval
    | .there older => (layout.staticSlot older).rename
        (staticRename targetScope interval)
  member? := fun path label =>
    match path with
    | .var (.there older) =>
        (layout.member? (.var older) label).map fun member =>
          member.rename (staticRename targetScope interval)

@[simp]
theorem extendStatic_term_there {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    {sort : Source.StaticSort} (interval : Source.Interval sort sourceScope)
    (sourceVar : Source.BVar sourceScope .term) :
    (layout.extendStatic interval).termVar (.there sourceVar) =
      (staticRename targetScope interval).var (layout.termVar sourceVar) := rfl

@[simp]
theorem extendStatic_slot_here {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    {sort : Source.StaticSort} (interval : Source.Interval sort sourceScope) :
    (layout.extendStatic interval).staticSlot .here =
      newestStaticSlot targetScope interval := rfl

@[simp]
theorem extendStatic_slot_there {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    {newestSort olderSort : Source.StaticSort}
    (interval : Source.Interval newestSort sourceScope)
    (sourceVar : Source.BVar sourceScope (.static olderSort)) :
    (layout.extendStatic interval).staticSlot (.there sourceVar) =
      (layout.staticSlot sourceVar).rename
        (staticRename targetScope interval) := rfl

@[simp]
theorem extendStatic_member_there {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    {sort : Source.StaticSort} (interval : Source.Interval sort sourceScope)
    (sourceVar : Source.BVar sourceScope .term) (label : Nat) :
    (layout.extendStatic interval).member? (.var (.there sourceVar)) label =
      (layout.member? (.var sourceVar) label).map fun member =>
        member.rename (staticRename targetScope interval) := rfl

/-! ## Package payload extension -/

/-- Opening a lexical existential installs its one-symbol interval theory and
then one runtime payload binder. -/
def extendPayload {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) {sort : Source.StaticSort}
    (interval : Source.Interval sort sourceScope) :
    Layout ((sourceScope ▹ .static sort) ▹ .term)
      (Target.StaticScope targetScope [translateSort sort]
        (intervalRelations interval) ▹ .term) :=
  (layout.extendStatic interval).extendPlain

@[simp]
theorem extendPayload_term_here {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    {sort : Source.StaticSort} (interval : Source.Interval sort sourceScope) :
    (layout.extendPayload interval).termVar .here = .here := rfl

@[simp]
theorem extendPayload_member_here {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    {sort : Source.StaticSort} (interval : Source.Interval sort sourceScope)
    (label : Nat) :
    (layout.extendPayload interval).member? (.var .here) label = none := rfl

/-! ## Stable object extension -/

/-- Ambient target coordinates weakened below a complete names-first theory
and its one runtime representation binder. -/
def objectRename (targetScope : Target.Sig)
    {symbols : List Target.StaticSort} {relations : List Target.Relation} :
    Target.Rename targetScope
      (Target.StaticScope targetScope symbols relations ▹ .term) :=
  (ManySortedFC.Rename.weakenStatic symbols relations).comp
    ManySortedFC.Rename.succ

/-- Open an encoded object theory and install its payload as a stable source
root.  Member lookup reuses the names already allocated by `Encoding`; it
never allocates a second identity. -/
def extendObjectWith {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (symbols : List Target.StaticSort) (relations : List Target.Relation)
    (openedMembers : List
      (MemberName (Target.StaticScope targetScope symbols relations))) :
    Layout (sourceScope ▹ .term)
      (Target.StaticScope targetScope symbols relations ▹ .term) where
  termVar := fun
    | .here => .here
    | .there older =>
        (objectRename targetScope).var (layout.termVar older)
  staticSlot := fun
    | .there older => (layout.staticSlot older).rename
        (objectRename targetScope)
  member? := fun path label =>
    match path with
    | .var .here =>
        (DOTCaptureToManySortedFC.Intersections.Preparation.MemberNames.find?
          openedMembers label).map fun member =>
            member.rename ManySortedFC.Rename.succ
    | .var (.there older) =>
        (layout.member? (.var older) label).map fun member =>
          member.rename (objectRename targetScope)

/-- Historical encoded-object specialization of `extendObjectWith`. -/
def extendObject {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) (encoding : Encoding targetScope) :
    Layout (sourceScope ▹ .term)
      (Target.StaticScope targetScope encoding.symbols encoding.relations ▹
        .term) :=
  layout.extendObjectWith encoding.symbols encoding.relations
    encoding.openedMembers

@[simp]
theorem extendObjectWith_term_here {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (symbols : List Target.StaticSort) (relations : List Target.Relation)
    (openedMembers : List
      (MemberName (Target.StaticScope targetScope symbols relations))) :
    (layout.extendObjectWith symbols relations openedMembers).termVar .here =
      .here := rfl

@[simp]
theorem extendObjectWith_term_there {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (symbols : List Target.StaticSort) (relations : List Target.Relation)
    (openedMembers : List
      (MemberName (Target.StaticScope targetScope symbols relations)))
    (sourceVar : Source.BVar sourceScope .term) :
    (layout.extendObjectWith symbols relations openedMembers).termVar
        (.there sourceVar) =
      (objectRename targetScope).var (layout.termVar sourceVar) := rfl

@[simp]
theorem extendObjectWith_member_here {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (symbols : List Target.StaticSort) (relations : List Target.Relation)
    (openedMembers : List
      (MemberName (Target.StaticScope targetScope symbols relations)))
    (label : Nat) :
    (layout.extendObjectWith symbols relations openedMembers).member?
        (.var .here) label =
      (DOTCaptureToManySortedFC.Intersections.Preparation.MemberNames.find?
        openedMembers label).map fun member =>
          member.rename ManySortedFC.Rename.succ := rfl

@[simp]
theorem extendObject_term_here {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (encoding : Encoding targetScope) :
    (layout.extendObject encoding).termVar .here = .here := rfl

@[simp]
theorem extendObject_term_there {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (encoding : Encoding targetScope)
    (sourceVar : Source.BVar sourceScope .term) :
    (layout.extendObject encoding).termVar (.there sourceVar) =
      (objectRename targetScope).var (layout.termVar sourceVar) := rfl

@[simp]
theorem extendObject_static_there {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (encoding : Encoding targetScope) {sort : Source.StaticSort}
    (sourceVar : Source.BVar sourceScope (.static sort)) :
    (layout.extendObject encoding).staticSlot (.there sourceVar) =
      (layout.staticSlot sourceVar).rename (objectRename targetScope) := rfl

@[simp]
theorem extendObject_member_here {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (encoding : Encoding targetScope) (label : Nat) :
    (layout.extendObject encoding).member? (.var .here) label =
      (DOTCaptureToManySortedFC.Intersections.Preparation.MemberNames.find?
        encoding.openedMembers label).map fun member =>
          member.rename ManySortedFC.Rename.succ := rfl

@[simp]
theorem extendObject_member_there {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (encoding : Encoding targetScope)
    (sourceVar : Source.BVar sourceScope .term) (label : Nat) :
    (layout.extendObject encoding).member? (.var (.there sourceVar)) label =
      (layout.member? (.var sourceVar) label).map fun member =>
        member.rename (objectRename targetScope) := rfl

/-! ## Modal target extension -/

/-- Weaken every coordinate below a target modal evidence block.  Modal
requirements add no source binder, so the source scope is unchanged. -/
def weakenModal {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) (separationCount : Nat)
    (modes : List Target.CaptureMode) :
    Layout sourceScope (Target.ModalScope targetScope separationCount modes) :=
  layout.renameTarget
    (ManySortedFC.Rename.weakenModal targetScope separationCount modes)

@[simp]
theorem weakenModal_termVar {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (separationCount : Nat) (modes : List Target.CaptureMode)
    (sourceVar : Source.BVar sourceScope .term) :
    (layout.weakenModal separationCount modes).termVar sourceVar =
      (ManySortedFC.Rename.weakenModal targetScope separationCount modes).var
        (layout.termVar sourceVar) := rfl

@[simp]
theorem weakenModal_staticSlot {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (separationCount : Nat) (modes : List Target.CaptureMode)
    {sort : Source.StaticSort}
    (sourceVar : Source.BVar sourceScope (.static sort)) :
    (layout.weakenModal separationCount modes).staticSlot sourceVar =
      (layout.staticSlot sourceVar).rename
        (ManySortedFC.Rename.weakenModal targetScope separationCount modes) :=
  rfl

@[simp]
theorem weakenModal_member {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (separationCount : Nat) (modes : List Target.CaptureMode)
    (path : Source.Path sourceScope) (label : Nat) :
    (layout.weakenModal separationCount modes).member? path label =
      (layout.member? path label).map fun member =>
        member.rename
          (ManySortedFC.Rename.weakenModal targetScope separationCount modes) :=
  rfl

/-! ## Empty layout -/

/-- The unique layout between empty source and target scopes. -/
def empty : Layout [] [] where
  termVar := fun sourceVar => nomatch sourceVar
  staticSlot := fun sourceVar => nomatch sourceVar
  member? := fun path _ =>
    match path with
    | .var sourceVar => nomatch sourceVar

end Layout

end DOTCaptureToManySortedFC.ModalIntersections
