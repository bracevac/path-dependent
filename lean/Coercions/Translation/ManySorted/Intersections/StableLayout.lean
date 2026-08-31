import Coercions.Translation.ManySorted.Intersections.Preparation

/-!
# Stable path layouts for normalized intersection signatures

Opening one encoded object extends the target context by its complete static
theory and one runtime payload binder.  The corresponding source variable is
then the sole root for all of that object's labeled static names.  Older roots
are only renamed; they are never reallocated.
-/

namespace DOTCaptureToManySortedFC.Intersections.StableLayout

open Encoding Preparation

namespace Source

abbrev Scope := DOTCapture.Intersections.Source.Scope
abbrev Var := DOTCapture.Intersections.Source.Var
abbrev Path := DOTCapture.Intersections.Source.Path

end Source

namespace Target

open ManySortedFC

abbrev Sig := ManySortedFC.Sig
abbrev BVar := ManySortedFC.BVar
abbrev Rename := ManySortedFC.Rename

end Target

/-- The layout type is shared with bound preparation: both ordinary source
paths and bounds inside later signatures consult the same stable identities. -/
abbrev Layout := Preparation.OuterLayout

namespace Layout

/-- Rename every target coordinate without changing source paths. -/
def rename {sourceScope : Source.Scope} {first second : Target.Sig}
    (layout : Layout sourceScope first) (rho : Target.Rename first second) :
    Layout sourceScope second where
  termVar := fun sourceVar => rho.var (layout.termVar sourceVar)
  member? := fun path label =>
    (layout.member? path label).map fun member => member.rename rho

/-- Extend by an ordinary runtime binder.  The newest path has no static
members, while every older coordinate is weakened once. -/
def extendPlain {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) :
    Layout (sourceScope + 1) (targetScope ▹ .term) where
  termVar := fun
    | .here => .here
    | .there older => .there (layout.termVar older)
  member? := fun path label =>
    match path with
    | .var .here => none
    | .var (.there older) =>
        (layout.member? (.var older) label).map fun member =>
          member.rename ManySortedFC.Rename.succ

/-- Ambient coordinates weakened below a complete theory and its runtime
payload. -/
def objectRename (targetScope : Target.Sig) {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation} :
    Target.Rename targetScope
      (ManySortedFC.StaticScope targetScope symbols relations ▹ .term) :=
  (ManySortedFC.Rename.weakenStatic symbols relations).comp
    ManySortedFC.Rename.succ

/-- Open one encoded signature and install its payload as a stable source
root.  Every newest-path member lookup selects an already allocated name from
the encoding; it performs no fresh-name operation. -/
def extendObject {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) (encoding : Encoding targetScope) :
    Layout (sourceScope + 1)
      (ManySortedFC.StaticScope targetScope encoding.symbols
        encoding.relations ▹ .term) where
  termVar := fun
    | .here => .here
    | .there older =>
        (objectRename targetScope).var (layout.termVar older)
  member? := fun path label =>
    match path with
    | .var .here =>
        (Preparation.MemberNames.find? encoding.openedMembers label).map
          fun member => member.rename ManySortedFC.Rename.succ
    | .var (.there older) =>
        (layout.member? (.var older) label).map fun member =>
          member.rename (objectRename targetScope)

@[simp]
theorem extendPlain_term_here {sourceScope : Source.Scope}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope) :
    (layout.extendPlain).termVar .here = .here := rfl

@[simp]
theorem extendPlain_member_here {sourceScope : Source.Scope}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (label : Nat) :
    (layout.extendPlain).member? (.var .here) label = none := rfl

@[simp]
theorem extendObject_term_here {sourceScope : Source.Scope}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (encoding : Encoding targetScope) :
    (layout.extendObject encoding).termVar .here = .here := rfl

@[simp]
theorem extendObject_member_here {sourceScope : Source.Scope}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (encoding : Encoding targetScope) (label : Nat) :
    (layout.extendObject encoding).member? (.var .here) label =
      (Preparation.MemberNames.find? encoding.openedMembers label).map
        (fun member => member.rename ManySortedFC.Rename.succ) := rfl

/-- A repeated lookup at one stable `(path,label)` is literally functional. -/
theorem member_identity {sourceScope : Source.Scope}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (path : Source.Path sourceScope) (label : Nat)
    {first second : MemberName targetScope}
    (firstFound : layout.member? path label = some first)
    (secondFound : layout.member? path label = some second) : first = second := by
  rw [firstFound] at secondFound
  exact Option.some.inj secondFound

end Layout

end DOTCaptureToManySortedFC.Intersections.StableLayout
