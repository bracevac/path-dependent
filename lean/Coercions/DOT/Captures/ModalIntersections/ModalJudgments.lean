import Coercions.DOT.Captures.ModalIntersections.StaticJudgments

/-!
# Access-only modal judgments for captured intersections

Modal assumptions are a lexical stack of requirement frames over one
unchanged source scope.  They may justify access modes and separation, but
they are deliberately absent from `Disjoint`: a lock cannot manufacture a
freshness fact.

All membership and judgment types live in `Type`, so duplicate captures at
different requirement positions remain distinguishable.
-/

namespace DOTCapture.ModalIntersections

/-! ## Proof-relevant positional membership -/

namespace SeparationContext

/-- One position in a separation context.  Two equal capture expressions at
different positions have different inhabitants of this type. -/
inductive Position {scope : Sig} :
    {count : Nat} → SeparationContext count scope → Type where
  | here {count : Nat} {rest : SeparationContext count scope}
      {capture : Capture scope} : Position (.cons rest capture)
  | there {count : Nat} {rest : SeparationContext count scope}
      {capture : Capture scope} :
      Position rest → Position (.cons rest capture)

namespace Position

/-- The capture stored at a separation-context position. -/
def capture {scope : Sig} {count : Nat}
    {context : SeparationContext count scope} :
    Position context → Capture scope
  | @here _ _ _ capture => capture
  | there older => older.capture

/-- Proof-relevant inequality of two positions.  Both orientations are
represented, and there is intentionally no constructor for one position
against itself. -/
inductive Distinct {scope : Sig} : {count : Nat} →
    {context : SeparationContext count scope} →
    Position context → Position context → Type where
  | hereThere {rest : SeparationContext count scope}
      {capture : Capture scope} (older : Position rest) :
      Distinct (context := .cons rest capture) .here (.there older)
  | thereHere {rest : SeparationContext count scope}
      {capture : Capture scope} (older : Position rest) :
      Distinct (context := .cons rest capture) (.there older) .here
  | thereThere {rest : SeparationContext count scope}
      {capture : Capture scope} {left right : Position rest}
      (distinct : Distinct left right) :
      Distinct (context := .cons rest capture) (.there left) (.there right)

/-- Positional distinctness is symmetric. -/
def Distinct.swap {scope : Sig} {count : Nat}
    {context : SeparationContext count scope}
    {left right : Position context} (distinct : Distinct left right) :
    Distinct right left :=
  match distinct with
  | .hereThere older => .thereHere older
  | .thereHere older => .hereThere older
  | .thereThere inner => .thereThere inner.swap

/-- Rename a position without changing which list entry it denotes. -/
def rename {source target : Sig} {count : Nat}
    {context : SeparationContext count source}
    (position : Position context) (rho : Rename source target) :
    Position (context.rename rho) :=
  match position with
  | .here => .here
  | .there older => .there (older.rename rho)

@[simp]
theorem capture_rename {source target : Sig} {count : Nat}
    {context : SeparationContext count source}
    (position : Position context) (rho : Rename source target) :
    (position.rename rho).capture = position.capture.rename rho := by
  induction position with
  | here => rfl
  | there older induction => exact induction

/-- Renaming preserves positional distinctness. -/
def Distinct.rename {source target : Sig} {count : Nat}
    {context : SeparationContext count source}
    {left right : Position context} (distinct : Distinct left right)
    (rho : Rename source target) :
    Distinct (left.rename rho) (right.rename rho) :=
  match distinct with
  | .hereThere older => .hereThere (older.rename rho)
  | .thereHere older => .thereHere (older.rename rho)
  | .thereThere inner => .thereThere (inner.rename rho)

end Position
end SeparationContext

namespace ModeContext

/-- One positional mode occurrence.  Its mode and capture are both retained
in the indices, so repeated obligations remain proof-relevant. -/
inductive Occurs {scope : Sig} : {modes : List CaptureMode} →
    (context : ModeContext modes scope) →
    CaptureMode → Capture scope → Type where
  | here {modes : List CaptureMode} {mode : CaptureMode}
      {rest : ModeContext modes scope} {capture : Capture scope} :
      Occurs (.cons (mode := mode) rest capture) mode capture
  | there {modes : List CaptureMode} {newestMode mode : CaptureMode}
      {rest : ModeContext modes scope} {newest capture : Capture scope}
      (older : Occurs rest mode capture) :
      Occurs (.cons (mode := newestMode) rest newest) mode capture

namespace Occurs

/-- Rename a mode occurrence without changing its position or mode. -/
def rename {source target : Sig} {modes : List CaptureMode}
    {context : ModeContext modes source} {mode : CaptureMode}
    {capture : Capture source} (occurrence : Occurs context mode capture)
    (rho : Rename source target) :
    Occurs (context.rename rho) mode (capture.rename rho) :=
  match occurrence with
  | .here => .here
  | .there older => .there (older.rename rho)

end Occurs
end ModeContext

/-! ## Active lock assumptions -/

/-- A stack of active modal requirement frames.  Pushing a lock changes the
logical environment, not the heterogeneous term/static scope. -/
inductive ModalAssumptions (scope : Sig) : Type where
  | nil : ModalAssumptions scope
  | push {separationCount : Nat} {modes : List CaptureMode}
      (outer : ModalAssumptions scope)
      (frame : ModalRequirements separationCount modes scope) :
      ModalAssumptions scope

namespace ModalAssumptions

/-- Rename every active frame along one source-scope renaming. -/
def rename {source target : Sig} (assumptions : ModalAssumptions source)
    (rho : Rename source target) : ModalAssumptions target :=
  match assumptions with
  | .nil => .nil
  | .push outer frame => .push (outer.rename rho) (frame.rename rho)

@[simp]
theorem rename_id {scope : Sig} (assumptions : ModalAssumptions scope) :
    assumptions.rename DOTCapture.BinderOnly.Rename.id = assumptions := by
  induction assumptions with
  | nil => rfl
  | push outer frame induction =>
      simp only [rename, induction, ModalRequirements.rename_id]

@[simp]
theorem rename_comp {first second third : Sig}
    (assumptions : ModalAssumptions first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (assumptions.rename rho₁).rename rho₂ =
      assumptions.rename (rho₁.comp rho₂) := by
  induction assumptions with
  | nil => rfl
  | push outer frame induction =>
      simp only [rename, induction, ModalRequirements.rename_comp]

/-- Proof-relevant lookup of an exact frame at any stack depth. -/
inductive Lookup {scope : Sig} {separationCount : Nat}
    {modes : List CaptureMode}
    (frame : ModalRequirements separationCount modes scope) :
    ModalAssumptions scope → Type where
  | here {outer : ModalAssumptions scope} :
      Lookup frame (.push outer frame)
  | there {outer : ModalAssumptions scope}
      {otherSeparationCount : Nat} {otherModes : List CaptureMode}
      {other : ModalRequirements otherSeparationCount otherModes scope}
      (older : Lookup frame outer) : Lookup frame (.push outer other)

namespace Lookup

/-- Frame lookup is stable under source-scope renaming. -/
def rename {source target : Sig} {separationCount : Nat}
    {modes : List CaptureMode}
    {frame : ModalRequirements separationCount modes source}
    {assumptions : ModalAssumptions source}
    (lookup : Lookup frame assumptions) (rho : Rename source target) :
    Lookup (frame.rename rho) (assumptions.rename rho) :=
  match lookup with
  | .here => .here
  | .there older => .there (older.rename rho)

end Lookup
end ModalAssumptions

/-! ## Access-only logical judgments -/

/-- Capture-mode judgment.  Active lock frames can supply mode facts. -/
inductive Mode {scope : Sig} (context : Ctx scope)
    (assumptions : ModalAssumptions scope) :
    Capture scope → CaptureMode → Type where
  | empty (mode : CaptureMode) : Mode context assumptions .empty mode
  | union {left right : Capture scope} {mode : CaptureMode}
      (leftMode : Mode context assumptions left mode)
      (rightMode : Mode context assumptions right mode) :
      Mode context assumptions (.union left right) mode
  | subcapture {lower upper : Capture scope} {mode : CaptureMode}
      (inclusion : CaptureIncludes context lower upper)
      (upperMode : Mode context assumptions upper mode) :
      Mode context assumptions lower mode
  | writable (capture : Capture scope) :
      Mode context assumptions capture .writable
  | readOnly (capture : Capture scope) :
      Mode context assumptions (.readOnly capture) .readOnly
  | lock {separationCount : Nat} {modes : List CaptureMode}
      {separation : SeparationContext separationCount scope}
      {modeContext : ModeContext modes scope}
      {mode : CaptureMode} {capture : Capture scope}
      (frame : ModalAssumptions.Lookup
        (.mk separation modeContext) assumptions)
      (occurrence : ModeContext.Occurs modeContext mode capture) :
      Mode context assumptions capture mode

/-- Structural capture equality available to disjointness transport.  It has
the same capture-specific congruences as target equality evidence and does
not allow transport from mere inclusion. -/
inductive CaptureEquality {scope : Sig} (context : Ctx scope) :
    Capture scope → Capture scope → Type where
  | refl (capture : Capture scope) : CaptureEquality context capture capture
  | symm {left right : Capture scope}
      (equality : CaptureEquality context left right) :
      CaptureEquality context right left
  | trans {first second third : Capture scope}
      (left : CaptureEquality context first second)
      (right : CaptureEquality context second third) :
      CaptureEquality context first third
  | union {left₁ left₂ right₁ right₂ : Capture scope}
      (left : CaptureEquality context left₁ left₂)
      (right : CaptureEquality context right₁ right₂) :
      CaptureEquality context (.union left₁ right₁) (.union left₂ right₂)
  | readOnly {left right : Capture scope}
      (equality : CaptureEquality context left right) :
      CaptureEquality context (.readOnly left) (.readOnly right)

/-- Resource disjointness.  This judgment intentionally has no
`ModalAssumptions` parameter and no read-only or lock constructor. -/
inductive Disjoint {scope : Sig} (context : Ctx scope) :
    Capture scope → Capture scope → Type where
  | empty (capture : Capture scope) : Disjoint context .empty capture
  | symm {left right : Capture scope}
      (disjoint : Disjoint context left right) :
      Disjoint context right left
  | union {left right other : Capture scope}
      (leftDisjoint : Disjoint context left other)
      (rightDisjoint : Disjoint context right other) :
      Disjoint context (.union left right) other
  | equality {replacement original other : Capture scope}
      (equality : CaptureEquality context replacement original)
      (disjoint : Disjoint context original other) :
      Disjoint context replacement other

/-- Access separation.  Unlike disjointness, separation may be supplied by a
lock frame and permits two read-only views of the same capability. -/
inductive Separate {scope : Sig} (context : Ctx scope)
    (assumptions : ModalAssumptions scope) :
    Capture scope → Capture scope → Type where
  | empty (capture : Capture scope) :
      Separate context assumptions .empty capture
  | symm {left right : Capture scope}
      (separate : Separate context assumptions left right) :
      Separate context assumptions right left
  | union {left right other : Capture scope}
      (leftSeparate : Separate context assumptions left other)
      (rightSeparate : Separate context assumptions right other) :
      Separate context assumptions (.union left right) other
  | subcapture {lower upper other : Capture scope}
      (inclusion : CaptureIncludes context lower upper)
      (separation : Separate context assumptions upper other) :
      Separate context assumptions lower other
  | readOnly {left right : Capture scope}
      (leftMode : Mode context assumptions left .readOnly)
      (rightMode : Mode context assumptions right .readOnly) :
      Separate context assumptions left right
  | ofDisjoint {left right : Capture scope}
      (disjoint : Disjoint context left right) :
      Separate context assumptions left right
  | lock {separationCount : Nat} {modes : List CaptureMode}
      {separation : SeparationContext separationCount scope}
      {modeContext : ModeContext modes scope}
      (frame : ModalAssumptions.Lookup
        (.mk separation modeContext) assumptions)
      (left right : SeparationContext.Position separation)
      (distinct : SeparationContext.Position.Distinct left right) :
      Separate context assumptions left.capture right.capture

/-- Satisfaction covers every positional mode occurrence and both
orientations of every distinct separation pair.  This deliberately symmetric
source presentation is equivalent to the target's one canonical orientation,
because `Separate.symm` derives the reverse orientation. -/
inductive Satisfies {scope : Sig} (context : Ctx scope)
    (assumptions : ModalAssumptions scope) :
    {separationCount : Nat} → {modes : List CaptureMode} →
    ModalRequirements separationCount modes scope → Type where
  | mk {separationCount : Nat} {modes : List CaptureMode}
      {separation : SeparationContext separationCount scope}
      {modeContext : ModeContext modes scope}
      (modesCovered : ∀ {mode : CaptureMode} {capture : Capture scope},
        ModeContext.Occurs modeContext mode capture →
          Mode context assumptions capture mode)
      (separationsCovered :
        ∀ (left right : SeparationContext.Position separation),
          SeparationContext.Position.Distinct left right →
            Separate context assumptions left.capture right.capture) :
      Satisfies context assumptions (.mk separation modeContext)

/-! ## Small structural regressions -/

namespace ModalJudgmentExamples

/-- The newest positional occurrence retains the mode stored at that exact
mode-context entry. -/
def headModeExact {scope : Sig} {modes : List CaptureMode}
    {mode : CaptureMode} (rest : ModeContext modes scope)
    (capture : Capture scope) :
    ModeContext.Occurs (.cons (mode := mode) rest capture) mode capture :=
  .here

/-- A writable head cannot be consulted as a read-only assumption. -/
def writableHeadIsNotReadOnly {scope : Sig} (capture : Capture scope) :
    ModeContext.Occurs
        (.cons (mode := .writable) (.nil : ModeContext [] scope) capture)
        .readOnly capture ->
      Empty := by
  intro occurrence
  cases occurrence with
  | there older => cases older

/-- Shared read-only access is separated even when both views contain the
same capabilities. -/
def sharedReadOnlySeparation {scope : Sig} (context : Ctx scope)
    (assumptions : ModalAssumptions scope) (capture : Capture scope) :
    Separate context assumptions (.readOnly capture) (.readOnly capture) :=
  .readOnly (.readOnly capture) (.readOnly capture)

/-- The same disjointness derivation is independent of every active-lock
stack: there is no assumptions argument to inspect or transport. -/
def disjointIgnoresLocks {scope : Sig} {context : Ctx scope}
    {left right : Capture scope} (disjoint : Disjoint context left right)
    (_source _target : ModalAssumptions scope) : Disjoint context left right :=
  disjoint

/-- Lookup reaches through a newer frame without confusing equal captures at
different stack depths. -/
def lookupOuterFrame {scope : Sig} {outerCount newestCount : Nat}
    {outerModes newestModes : List CaptureMode}
    (outerFrame : ModalRequirements outerCount outerModes scope)
    (newestFrame : ModalRequirements newestCount newestModes scope) :
    ModalAssumptions.Lookup outerFrame
      (.push (.push .nil outerFrame) newestFrame) :=
  .there .here

end ModalJudgmentExamples

end DOTCapture.ModalIntersections
