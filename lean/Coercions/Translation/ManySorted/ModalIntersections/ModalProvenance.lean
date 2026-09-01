import Coercions.Translation.ManySorted.ModalIntersections.Preparation
import Coercions.DOT.Captures.ModalIntersections.ModalJudgments
import Coercions.ManySortedFC.TheoryMapValidity

/-!
# Modal proof provenance for the cumulative compiler

The source keeps active modal frames in a proof-relevant stack without
changing its heterogeneous variable scope.  The target instead opens one
explicit evidence block per frame.  This file records the exact positional
correspondence between those two presentations.

The construction is deliberately independent of type- and inclusion-evidence
compilation.  Its only syntax dependency is a supplied translation of source
captures.  Later compiler layers can therefore use the same provenance for
`Mode.lock`, `Separate.lock`, modal elimination, and modal adapters.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections

namespace Source

abbrev CaptureMode := DOTCapture.ModalIntersections.CaptureMode
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev SeparationContext := DOTCapture.ModalIntersections.SeparationContext
abbrev ModeContext := DOTCapture.ModalIntersections.ModeContext
abbrev ModalRequirements := DOTCapture.ModalIntersections.ModalRequirements
abbrev ModalAssumptions := DOTCapture.ModalIntersections.ModalAssumptions

end Source

namespace Target

abbrev Capture := ManySortedFC.Capture
abbrev SeparationContext := ManySortedFC.SeparationContext
abbrev ModeContext := ManySortedFC.ModeContext
abbrev ModalContext := ManySortedFC.ModalContext
abbrev ConstraintRef := ManySortedFC.ConstraintRef
abbrev Evidence := ManySortedFC.Evidence
abbrev EvidenceArgs := ManySortedFC.EvidenceArgs
abbrev Proposition := ManySortedFC.Proposition
abbrev Theory := ManySortedFC.Theory
abbrev Ctx := ManySortedFC.Ctx

end Target

/-! ## Syntax-only modal translation -/

/-- The modal-provenance layer shares Preparation's public mode map. -/
abbrev translateCaptureMode := Preparation.translateMode

/-- The modal-provenance layer shares Preparation's intrinsic mode-list map. -/
abbrev translateCaptureModes := Preparation.translateModes

/-- Map every capture in a separation context without changing positions. -/
def mapSeparationContext {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (capture : Source.Capture sourceScope -> Target.Capture targetScope) :
    {count : Nat} -> Source.SeparationContext count sourceScope ->
      Target.SeparationContext count targetScope
  | 0, .nil => .nil
  | _ + 1, .cons rest newest =>
      .cons (mapSeparationContext capture rest) (capture newest)

/-- Map every capture and mode in a positional mode context. -/
def mapModeContext {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (capture : Source.Capture sourceScope -> Target.Capture targetScope) :
    {modes : List Source.CaptureMode} ->
      Source.ModeContext modes sourceScope ->
      Target.ModeContext (translateCaptureModes modes) targetScope
  | [], .nil => .nil
  | _ :: _, .cons rest newest =>
      .cons (mapModeContext capture rest) (capture newest)

/-- Translate one primitive source modal frame, retaining its exact list
shape and every duplicate capture occurrence. -/
def mapRequirements {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (capture : Source.Capture sourceScope -> Target.Capture targetScope) :
    {separationCount : Nat} -> {modes : List Source.CaptureMode} ->
      Source.ModalRequirements separationCount modes sourceScope ->
      Target.ModalContext separationCount (translateCaptureModes modes)
        targetScope
  | _, _, .mk separation mode =>
      .mk (mapSeparationContext capture separation)
        (mapModeContext capture mode)

/-! ## Intrinsically related references -/

namespace ConstraintRef

/-- Preserve a reference into the left side of an appended relation block. -/
def appendLeft {first second : List ManySortedFC.Relation}
    {relation : ManySortedFC.Relation} :
    Target.ConstraintRef first relation ->
      Target.ConstraintRef (first ++ second) relation
  | .here => .here
  | .there older => .there (appendLeft older)

/-- Weaken a reference below every relation in a newer left prefix. -/
def appendRight (first : List ManySortedFC.Relation)
    {second : List ManySortedFC.Relation}
    {relation : ManySortedFC.Relation} :
    Target.ConstraintRef second relation ->
      Target.ConstraintRef (first ++ second) relation :=
  fun reference =>
    match first with
    | [] => reference
    | _ :: rest => .there (appendRight rest reference)

end ConstraintRef

/-- The target mode proposition corresponding to one proof-relevant source
mode occurrence. -/
def modeReference {sourceScope : Source.Sig}
    {modes : List Source.CaptureMode}
    {context : Source.ModeContext modes sourceScope}
    {mode : Source.CaptureMode} {capture : Source.Capture sourceScope}
    (occurrence : DOTCapture.ModalIntersections.ModeContext.Occurs context
      mode capture) :
    Target.ConstraintRef
      (ManySortedFC.modeRelations (translateCaptureModes modes))
      (.mode (translateCaptureMode mode)) :=
  match occurrence with
  | .here => .here
  | .there older => .there (modeReference older)

/-- Lift a mode occurrence through the separation suffix of a complete modal
theory. -/
def modalModeReference {sourceScope : Source.Sig}
    {separationCount : Nat}
    {modes : List Source.CaptureMode}
    {modeContext : Source.ModeContext modes sourceScope}
    {mode : Source.CaptureMode} {capture : Source.Capture sourceScope}
    (occurrence : DOTCapture.ModalIntersections.ModeContext.Occurs modeContext
      mode capture) :
    Target.ConstraintRef
      (ManySortedFC.modalRelations separationCount
        (translateCaptureModes modes))
      (.mode (translateCaptureMode mode)) :=
  ConstraintRef.appendLeft (second :=
    ManySortedFC.separationRelations separationCount)
    (modeReference occurrence)

/-- A source separation position mapped to the same target list position. -/
def separationPosition {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (capture : Source.Capture sourceScope -> Target.Capture targetScope)
    {count : Nat} {context : Source.SeparationContext count sourceScope} :
    DOTCapture.ModalIntersections.SeparationContext.Position context ->
      ManySortedFC.SeparationPosition
        (mapSeparationContext capture context)
  | .here => .here
  | .there older => .there (separationPosition capture older)

/-- Reference to the proposition emitted between a fixed new head and one
older separation position. -/
def againstReference {sourceScope : Source.Sig}
    {count : Nat} {context : Source.SeparationContext count sourceScope} :
    DOTCapture.ModalIntersections.SeparationContext.Position context ->
      Target.ConstraintRef (List.replicate count .separate) .separate
  | .here => .here
  | .there older => .there (againstReference older)

/-- Whether the target's canonical newest-before-older pair already has the
orientation requested by the source judgment. -/
inductive SeparationOrientation : Type where
  | forward
  | reverse
deriving DecidableEq, Repr

/-- One exact target relation coordinate for a proof-relevant source pair.
The orientation bit says whether `separateSymm` is required after reading the
target assumption. -/
structure SeparationReference {sourceScope : Source.Sig}
    {count : Nat} {context : Source.SeparationContext count sourceScope}
    (left right :
      DOTCapture.ModalIntersections.SeparationContext.Position context) where
  orientation : SeparationOrientation
  reference : Target.ConstraintRef
    (ManySortedFC.separationRelations count) .separate

/-- Compute the canonical unordered-pair slot for every source positional
distinctness proof.  Equal capture expressions at different positions remain
distinct because recursion is on positions, not expression equality. -/
def separationReference {sourceScope : Source.Sig}
    {count : Nat} {context : Source.SeparationContext count sourceScope}
    {left right :
      DOTCapture.ModalIntersections.SeparationContext.Position context}
    (distinct :
      DOTCapture.ModalIntersections.SeparationContext.Position.Distinct
        left right) : SeparationReference left right :=
  match distinct with
  | .hereThere older =>
      { orientation := .forward
        reference := ConstraintRef.appendLeft
          (second := ManySortedFC.separationRelations _)
          (againstReference older) }
  | .thereHere older =>
      { orientation := .reverse
        reference := ConstraintRef.appendLeft
          (second := ManySortedFC.separationRelations _)
          (againstReference older) }
  | .thereThere inner =>
      let older := separationReference inner
      { orientation := older.orientation
        reference := ConstraintRef.appendRight
          (List.replicate _ .separate) older.reference }

/-- Lift a canonical separation-pair reference below the complete mode
prefix of a modal theory. -/
def modalSeparationReference {sourceScope : Source.Sig}
    {count : Nat} {modes : List Source.CaptureMode}
    {context : Source.SeparationContext count sourceScope}
    {left right :
      DOTCapture.ModalIntersections.SeparationContext.Position context}
    (distinct :
      DOTCapture.ModalIntersections.SeparationContext.Position.Distinct
        left right) :
    SeparationOrientation ×
      Target.ConstraintRef
        (ManySortedFC.modalRelations count (translateCaptureModes modes))
        .separate :=
  let reference := separationReference distinct
  ⟨reference.orientation,
    ConstraintRef.appendRight
      (ManySortedFC.modeRelations (translateCaptureModes modes))
      reference.reference⟩

/-! ## Reference soundness -/

/-- Looking up a left reference after theory append recovers the original
left proposition. -/
@[simp]
theorem propositionAt_appendLeft {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {firstRelations secondRelations : List ManySortedFC.Relation}
    (first : Target.Theory scope symbols firstRelations)
    (second : Target.Theory scope symbols secondRelations)
    {relation : ManySortedFC.Relation}
    (reference : Target.ConstraintRef firstRelations relation) :
    (ManySortedFC.Theory.append first second).propositionAt
        (ConstraintRef.appendLeft reference) =
      first.propositionAt reference :=
  match first, reference with
  | .cons _ _, .here => rfl
  | .cons _ rest, .there older =>
      propositionAt_appendLeft rest second older

/-- Looking up a right reference after theory append skips the complete left
theory. -/
@[simp]
theorem propositionAt_appendRight {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {firstRelations secondRelations : List ManySortedFC.Relation}
    (first : Target.Theory scope symbols firstRelations)
    (second : Target.Theory scope symbols secondRelations)
    {relation : ManySortedFC.Relation}
    (reference : Target.ConstraintRef secondRelations relation) :
    (ManySortedFC.Theory.append first second).propositionAt
        (ConstraintRef.appendRight firstRelations reference) =
      second.propositionAt reference :=
  match first with
  | .nil => rfl
  | .cons _ rest => propositionAt_appendRight rest second reference

/-- A mode occurrence points to the proposition for its exact stored capture
and tag. -/
@[simp]
theorem modeReference_proposition {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (captureMap : Source.Capture sourceScope -> Target.Capture targetScope)
    {modes : List Source.CaptureMode}
    {context : Source.ModeContext modes sourceScope}
    {mode : Source.CaptureMode} {capture : Source.Capture sourceScope}
    (occurrence : DOTCapture.ModalIntersections.ModeContext.Occurs context
      mode capture) :
    (mapModeContext captureMap context).toTheory.propositionAt
        (modeReference occurrence) =
      .mode (captureMap capture) := by
  induction occurrence with
  | here => rfl
  | there older induction => exact induction

/-- The same exact mode proposition is retained in a complete modal theory. -/
@[simp]
theorem modalModeReference_proposition {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (captureMap : Source.Capture sourceScope -> Target.Capture targetScope)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    (separation : Source.SeparationContext separationCount sourceScope)
    (modeContext : Source.ModeContext modes sourceScope)
    {mode : Source.CaptureMode} {capture : Source.Capture sourceScope}
    (occurrence : DOTCapture.ModalIntersections.ModeContext.Occurs modeContext
      mode capture) :
    ManySortedFC.Theory.propositionAt
        (mapRequirements captureMap (.mk separation modeContext)).toTheory
        (modalModeReference occurrence) =
      ManySortedFC.Proposition.mode (captureMap capture) := by
  exact (propositionAt_appendLeft _ _ _).trans
    (modeReference_proposition captureMap occurrence)

/-- A fixed newest separation entry is paired with the exact requested older
position. -/
@[simp]
theorem againstReference_proposition {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (captureMap : Source.Capture sourceScope -> Target.Capture targetScope)
    (head : Source.Capture sourceScope)
    {count : Nat} {context : Source.SeparationContext count sourceScope}
    (position :
      DOTCapture.ModalIntersections.SeparationContext.Position context) :
    (ManySortedFC.SeparationContext.against (captureMap head)
        (mapSeparationContext captureMap context)).propositionAt
        (againstReference position) =
      .separate (captureMap head) (captureMap position.capture) := by
  induction position with
  | here => rfl
  | there older induction => exact induction

/-- Proposition endpoint order selected by a canonical pair coordinate. -/
def orientedSeparation {scope : Target.Sig}
    (orientation : SeparationOrientation)
    (left right : Target.Capture scope) : Target.Proposition .separate scope :=
  match orientation with
  | .forward => .separate left right
  | .reverse => .separate right left

/-- Every positional distinctness proof selects the unique canonical target
pair; the orientation records whether its endpoints are already requested in
canonical newest-to-older order. -/
@[simp]
theorem separationReference_proposition {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (captureMap : Source.Capture sourceScope -> Target.Capture targetScope)
    {count : Nat} {context : Source.SeparationContext count sourceScope}
    {left right :
      DOTCapture.ModalIntersections.SeparationContext.Position context}
    (distinct :
      DOTCapture.ModalIntersections.SeparationContext.Position.Distinct
        left right) :
    (mapSeparationContext captureMap context).toTheory.propositionAt
        (separationReference distinct).reference =
      orientedSeparation (separationReference distinct).orientation
        (captureMap left.capture) (captureMap right.capture) := by
  induction distinct with
  | hereThere older =>
      exact (propositionAt_appendLeft _ _ _).trans
        (againstReference_proposition captureMap _ older)
  | thereHere older =>
      exact (propositionAt_appendLeft _ _ _).trans
        (againstReference_proposition captureMap _ older)
  | thereThere inner induction =>
      exact propositionAt_appendRight _ _ _ |>.trans induction

/-- The complete modal theory retains the canonical pair and orientation
below its mode prefix. -/
@[simp]
theorem modalSeparationReference_proposition {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (captureMap : Source.Capture sourceScope -> Target.Capture targetScope)
    {count : Nat} {modes : List Source.CaptureMode}
    (separation : Source.SeparationContext count sourceScope)
    (modeContext : Source.ModeContext modes sourceScope)
    {left right :
      DOTCapture.ModalIntersections.SeparationContext.Position separation}
    (distinct :
      DOTCapture.ModalIntersections.SeparationContext.Position.Distinct
        left right) :
    let located : SeparationOrientation × Target.ConstraintRef
        (ManySortedFC.modalRelations count (translateCaptureModes modes))
        .separate := modalSeparationReference (modes := modes) distinct
    ManySortedFC.Theory.propositionAt
        (mapRequirements captureMap (.mk separation modeContext)).toTheory
        located.2 =
      orientedSeparation located.1
        (captureMap left.capture) (captureMap right.capture) := by
  exact (propositionAt_appendRight _ _ _).trans
    (separationReference_proposition captureMap distinct)

/-! ## Exact current-frame variables -/

/-- Select one assumption from the newest target modal evidence block. -/
def currentFrameEvidence {scope : Target.Sig} {count : Nat}
    {modes : List ManySortedFC.CaptureMode}
    (_requirements : Target.ModalContext count modes scope)
    {relation : ManySortedFC.Relation}
    (reference : Target.ConstraintRef
      (ManySortedFC.modalRelations count modes) relation) :
    Target.Evidence relation (ManySortedFC.ModalScope scope count modes) :=
  .var (reference.toEvidenceBVar scope)

/-- The current-frame variable proves precisely the referenced proposition,
weakened below the complete evidence block. -/
def currentFrameEvidence_proves {scope : Target.Sig}
    (context : Target.Ctx scope) {count : Nat}
    {modes : List ManySortedFC.CaptureMode}
    (requirements : Target.ModalContext count modes scope)
    {relation : ManySortedFC.Relation}
    (reference : Target.ConstraintRef
      (ManySortedFC.modalRelations count modes) relation) :
    ManySortedFC.Evidence.Proves (context.extendModal requirements)
      (currentFrameEvidence requirements reference)
      ((requirements.toTheory.propositionAt reference).rename
        (ManySortedFC.Rename.weakenModal scope count modes)) := by
  apply ManySortedFC.Evidence.Proves.var
  simpa [currentFrameEvidence, ManySortedFC.Ctx.extendModal,
    ManySortedFC.Ctx.extendTheory, ManySortedFC.Rename.weakenModal] using
    (ManySortedFC.Ctx.lookup_extendTheoryEvidence_constraint
      (context.extendSymbols []) requirements.toTheory reference)

/-! ## Canonical target satisfaction blocks -/

/-- A translated mode judgment packaged with its exact certificate typing. -/
structure CompiledMode {scope : Target.Sig} (context : Target.Ctx scope)
    (capture : Target.Capture scope) (mode : ManySortedFC.CaptureMode) where
  evidence : Target.Evidence (.mode mode) scope
  typing : ManySortedFC.Evidence.Proves context evidence (.mode capture)

/-- A translated separation judgment packaged with its exact certificate
typing. -/
structure CompiledSeparate {scope : Target.Sig} (context : Target.Ctx scope)
    (left right : Target.Capture scope) where
  evidence : Target.Evidence .separate scope
  typing : ManySortedFC.Evidence.Proves context evidence
    (.separate left right)

/-- Renaming preserves the endpoint order selected by an orientation. -/
@[simp]
theorem orientedSeparation_rename {source target : Target.Sig}
    (orientation : SeparationOrientation)
    (left right : Target.Capture source) (rho : ManySortedFC.Rename source target) :
    (orientedSeparation orientation left right).rename rho =
      orientedSeparation orientation (left.rename rho) (right.rename rho) := by
  cases orientation <;> rfl

/-- Turn a certificate in canonical pair order into the endpoint order
requested by the source proof. -/
def orientCompiledSeparate {scope : Target.Sig} (context : Target.Ctx scope)
    (orientation : SeparationOrientation) (left right : Target.Capture scope)
    (evidence : Target.Evidence .separate scope)
    (typing : ManySortedFC.Evidence.Proves context evidence
      (orientedSeparation orientation left right)) :
    CompiledSeparate context left right :=
  match orientation with
  | .forward =>
      { evidence := evidence
        typing := typing }
  | .reverse =>
      { evidence := .separateSymm evidence
        typing := .separateSymm typing }

/-- Compile an exact mode occurrence supplied by the newest source lock into
the corresponding variable of the newest target evidence block. -/
def compileCurrentMode {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (targetContext : Target.Ctx targetScope)
    (captureMap : Source.Capture sourceScope -> Target.Capture targetScope)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    (separation : Source.SeparationContext separationCount sourceScope)
    (modeContext : Source.ModeContext modes sourceScope)
    {mode : Source.CaptureMode} {capture : Source.Capture sourceScope}
    (occurrence : DOTCapture.ModalIntersections.ModeContext.Occurs modeContext
      mode capture) :
    CompiledMode
      (targetContext.extendModal
        (mapRequirements captureMap (.mk separation modeContext)))
      ((captureMap capture).rename
        (ManySortedFC.Rename.weakenModal targetScope separationCount
          (translateCaptureModes modes)))
      (translateCaptureMode mode) :=
  let requirements := mapRequirements captureMap (.mk separation modeContext)
  let reference := modalModeReference occurrence
  { evidence := currentFrameEvidence requirements reference
    typing := by
      have exactTyping := currentFrameEvidence_proves targetContext
        requirements reference
      rw [modalModeReference_proposition captureMap separation modeContext
        occurrence] at exactTyping
      exact exactTyping }

/-- Compile an exact pair supplied by the newest source lock.  Reverse source
orientation is represented by one explicit `separateSymm` around the same
canonical target variable. -/
def compileCurrentSeparate {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (targetContext : Target.Ctx targetScope)
    (captureMap : Source.Capture sourceScope -> Target.Capture targetScope)
    {count : Nat} {modes : List Source.CaptureMode}
    (separation : Source.SeparationContext count sourceScope)
    (modeContext : Source.ModeContext modes sourceScope)
    {left right :
      DOTCapture.ModalIntersections.SeparationContext.Position separation}
    (distinct :
      DOTCapture.ModalIntersections.SeparationContext.Position.Distinct
        left right) :
    CompiledSeparate
      (targetContext.extendModal
        (mapRequirements captureMap (.mk separation modeContext)))
      ((captureMap left.capture).rename
        (ManySortedFC.Rename.weakenModal targetScope count
          (translateCaptureModes modes)))
      ((captureMap right.capture).rename
        (ManySortedFC.Rename.weakenModal targetScope count
          (translateCaptureModes modes))) :=
  let requirements := mapRequirements captureMap (.mk separation modeContext)
  let located := modalSeparationReference (modes := modes) distinct
  let evidence := currentFrameEvidence requirements located.2
  let typing : ManySortedFC.Evidence.Proves
      (targetContext.extendModal requirements) evidence
      (orientedSeparation located.1
        ((captureMap left.capture).rename
          (ManySortedFC.Rename.weakenModal targetScope count
            (translateCaptureModes modes)))
        ((captureMap right.capture).rename
          (ManySortedFC.Rename.weakenModal targetScope count
            (translateCaptureModes modes)))) := by
    have exactTyping := currentFrameEvidence_proves targetContext
      requirements located.2
    rw [modalSeparationReference_proposition captureMap separation modeContext
      distinct] at exactTyping
    change ManySortedFC.Evidence.Proves
      (targetContext.extendModal requirements) evidence
      ((orientedSeparation located.1
        (captureMap left.capture) (captureMap right.capture)).rename
          (ManySortedFC.Rename.weakenModal targetScope count
            (translateCaptureModes modes))) at exactTyping
    rw [orientedSeparation_rename] at exactTyping
    exact exactTyping
  orientCompiledSeparate _ located.1 _ _ evidence typing

namespace CompiledMode

/-- Transport a compiled mode leaf along any target substitution that
preserves the target context. -/
noncomputable def substitute {source target : Target.Sig}
    {sourceContext : Target.Ctx source} {targetContext : Target.Ctx target}
    {capture : Target.Capture source} {mode : ManySortedFC.CaptureMode}
    (compiled : CompiledMode sourceContext capture mode)
    (substitution : ManySortedFC.TermStaticSubst source target)
    (preserves : substitution.Preserves sourceContext targetContext) :
    CompiledMode targetContext
      (capture.substitute substitution.static) mode :=
  { evidence := compiled.evidence.substitute substitution
    typing := compiled.typing.substitute substitution preserves }

/-- Weaken a compiled mode leaf below a newly opened modal theory. -/
noncomputable def weakenModal {scope : Target.Sig}
    {context : Target.Ctx scope} {capture : Target.Capture scope}
    {mode : ManySortedFC.CaptureMode}
    (compiled : CompiledMode context capture mode)
    {count : Nat} {modes : List ManySortedFC.CaptureMode}
    (requirements : Target.ModalContext count modes scope) :
    CompiledMode (context.extendModal requirements)
      (capture.rename (ManySortedFC.Rename.weakenModal scope count modes))
      mode := by
  let substitution := ManySortedFC.TermStaticSubst.ofRename
    (ManySortedFC.Rename.weakenModal scope count modes)
  have preserves : substitution.Preserves context
      (context.extendModal requirements) := by
    simpa [substitution, ManySortedFC.Ctx.extendModal,
      ManySortedFC.Rename.weakenModal,
      ManySortedFC.Rename.weakenStatic,
      ManySortedFC.Rename.weakenSymbols] using
      (ManySortedFC.TermStaticSubst.Preserves.weakenTheory context
        requirements.toTheory)
  have transported := compiled.substitute substitution preserves
  simpa [substitution, ManySortedFC.TermStaticSubst.ofRename,
    ManySortedFC.Capture.substitute_ofRename] using transported

end CompiledMode

namespace CompiledSeparate

/-- Transport a compiled separation leaf along any target substitution that
preserves the target context. -/
noncomputable def substitute {source target : Target.Sig}
    {sourceContext : Target.Ctx source} {targetContext : Target.Ctx target}
    {left right : Target.Capture source}
    (compiled : CompiledSeparate sourceContext left right)
    (substitution : ManySortedFC.TermStaticSubst source target)
    (preserves : substitution.Preserves sourceContext targetContext) :
    CompiledSeparate targetContext
      (left.substitute substitution.static)
      (right.substitute substitution.static) :=
  { evidence := compiled.evidence.substitute substitution
    typing := compiled.typing.substitute substitution preserves }

/-- Weaken a compiled separation leaf below a newly opened modal theory. -/
noncomputable def weakenModal {scope : Target.Sig}
    {context : Target.Ctx scope} {left right : Target.Capture scope}
    (compiled : CompiledSeparate context left right)
    {count : Nat} {modes : List ManySortedFC.CaptureMode}
    (requirements : Target.ModalContext count modes scope) :
    CompiledSeparate (context.extendModal requirements)
      (left.rename (ManySortedFC.Rename.weakenModal scope count modes))
      (right.rename (ManySortedFC.Rename.weakenModal scope count modes)) := by
  let substitution := ManySortedFC.TermStaticSubst.ofRename
    (ManySortedFC.Rename.weakenModal scope count modes)
  have preserves : substitution.Preserves context
      (context.extendModal requirements) := by
    simpa [substitution, ManySortedFC.Ctx.extendModal,
      ManySortedFC.Rename.weakenModal,
      ManySortedFC.Rename.weakenStatic,
      ManySortedFC.Rename.weakenSymbols] using
      (ManySortedFC.TermStaticSubst.Preserves.weakenTheory context
        requirements.toTheory)
  have transported := compiled.substitute substitution preserves
  simpa [substitution, ManySortedFC.TermStaticSubst.ofRename,
    ManySortedFC.Capture.substitute_ofRename] using transported

end CompiledSeparate

/-! ## Proof-relevant active-frame stacks -/

/-- Exact modal leaves exported by every active source frame, expressed in
one current target context.  The capture interpretation is deliberately an
explicit parameter: cumulative preparation is partial, so a compiler may
instantiate this kernel-independent carrier only after the captures needed
by its current derivation have translated successfully. -/
structure ActiveProvenance {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (assumptions : Source.ModalAssumptions sourceScope)
    (targetContext : Target.Ctx targetScope)
    (captureMap : Source.Capture sourceScope -> Target.Capture targetScope) where
  modeLock : {separationCount : Nat} -> {modes : List Source.CaptureMode} ->
    {separation : Source.SeparationContext separationCount sourceScope} ->
    {modeContext : Source.ModeContext modes sourceScope} ->
    {mode : Source.CaptureMode} -> {capture : Source.Capture sourceScope} ->
    DOTCapture.ModalIntersections.ModalAssumptions.Lookup
      (.mk separation modeContext) assumptions ->
    DOTCapture.ModalIntersections.ModeContext.Occurs modeContext mode capture ->
    CompiledMode targetContext (captureMap capture)
      (translateCaptureMode mode)
  separateLock : {separationCount : Nat} ->
    {modes : List Source.CaptureMode} ->
    {separation : Source.SeparationContext separationCount sourceScope} ->
    {modeContext : Source.ModeContext modes sourceScope} ->
    (frame : DOTCapture.ModalIntersections.ModalAssumptions.Lookup
      (.mk separation modeContext) assumptions) ->
    (left right :
      DOTCapture.ModalIntersections.SeparationContext.Position separation) ->
    DOTCapture.ModalIntersections.SeparationContext.Position.Distinct
      left right ->
    CompiledSeparate targetContext
      (captureMap left.capture) (captureMap right.capture)

namespace ActiveProvenance

/-- No frame can be looked up in the empty active stack. -/
def nil {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (targetContext : Target.Ctx targetScope)
    (captureMap : Source.Capture sourceScope -> Target.Capture targetScope) :
    ActiveProvenance .nil targetContext captureMap where
  modeLock := fun frame _ => nomatch frame
  separateLock := fun frame _ _ _ => nomatch frame

/-- Transport all active leaves through an arbitrary target substitution.
This is the common operation used by ordinary, static, payload, and object
context extensions once their context-preservation proof is available. -/
noncomputable def substituteTarget {sourceScope : Source.Sig}
    {firstScope secondScope : Target.Sig}
    {assumptions : Source.ModalAssumptions sourceScope}
    {firstContext : Target.Ctx firstScope}
    {secondContext : Target.Ctx secondScope}
    {captureMap : Source.Capture sourceScope -> Target.Capture firstScope}
    (provenance : ActiveProvenance assumptions firstContext captureMap)
    (substitution : ManySortedFC.TermStaticSubst firstScope secondScope)
    (preserves : substitution.Preserves firstContext secondContext) :
    ActiveProvenance assumptions secondContext
      (fun capture => (captureMap capture).substitute substitution.static) where
  modeLock := fun frame occurrence =>
    (provenance.modeLock frame occurrence).substitute substitution preserves
  separateLock := fun frame left right distinct =>
    (provenance.separateLock frame left right distinct).substitute
      substitution preserves

/-- Push one primitive source lock and its canonically mapped target theory.
Newest queries use exact current-frame variables; older queries are weakened
below the new proof block.  Lookup recursion therefore retains the identity
of duplicate frames at different stack depths. -/
noncomputable def push {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    {assumptions : Source.ModalAssumptions sourceScope}
    {targetContext : Target.Ctx targetScope}
    {captureMap : Source.Capture sourceScope -> Target.Capture targetScope}
    (outer : ActiveProvenance assumptions targetContext captureMap)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    (separation : Source.SeparationContext separationCount sourceScope)
    (modeContext : Source.ModeContext modes sourceScope) :
    let requirements := mapRequirements captureMap
      (.mk separation modeContext)
    ActiveProvenance
      (.push assumptions (.mk separation modeContext))
      (targetContext.extendModal requirements)
      (fun capture => (captureMap capture).rename
        (ManySortedFC.Rename.weakenModal targetScope separationCount
          (translateCaptureModes modes))) := by
  let requirements := mapRequirements captureMap (.mk separation modeContext)
  let rho := ManySortedFC.Rename.weakenModal targetScope separationCount
    (translateCaptureModes modes)
  refine { modeLock := ?_, separateLock := ?_ }
  · intro queriedCount queriedModes queriedSeparation queriedModeContext
      queriedMode queriedCapture frame occurrence
    cases frame with
    | here =>
        exact compileCurrentMode targetContext captureMap separation
          modeContext occurrence
    | there older =>
        exact (outer.modeLock older occurrence).weakenModal requirements
  · intro queriedCount queriedModes queriedSeparation queriedModeContext
      frame left right distinct
    cases frame with
    | here =>
        exact compileCurrentSeparate targetContext captureMap separation
          modeContext distinct
    | there older =>
        exact (outer.separateLock older left right distinct).weakenModal
          requirements

end ActiveProvenance

/-- The modal-only leaf interface needed to compile `Satisfies`.  Inclusion,
equality, and ordinary context lookup remain responsibilities of the caller. -/
structure JudgmentCompiler {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (sourceContext : DOTCapture.ModalIntersections.Ctx sourceScope)
    (assumptions : Source.ModalAssumptions sourceScope)
    (targetContext : Target.Ctx targetScope)
    (capture : Source.Capture sourceScope -> Target.Capture targetScope) where
  mode : {sourceCapture : Source.Capture sourceScope} ->
    {sourceMode : Source.CaptureMode} ->
    DOTCapture.ModalIntersections.Mode sourceContext assumptions
      sourceCapture sourceMode ->
      CompiledMode targetContext (capture sourceCapture)
        (translateCaptureMode sourceMode)
  separate : {left right : Source.Capture sourceScope} ->
    DOTCapture.ModalIntersections.Separate sourceContext assumptions
      left right ->
      CompiledSeparate targetContext (capture left) (capture right)

/-- Instantiating a zero-symbol proposition is the identity. -/
@[simp]
theorem instantiateSymbols_nil {scope : Target.Sig}
    {relation : ManySortedFC.Relation}
    (proposition : Target.Proposition relation scope) :
    proposition.instantiateSymbols
        (.nil : ManySortedFC.SymbolArgs scope []) = proposition := by
  unfold ManySortedFC.Proposition.instantiateSymbols
  change proposition.substitute
      (ManySortedFC.StaticSubst.ofRename ManySortedFC.Rename.id) = proposition
  rw [ManySortedFC.Proposition.substitute_ofRename,
    ManySortedFC.Proposition.rename_id]

/-- Append two evidence-argument blocks in relation-list order. -/
def appendEvidenceArgs {scope : Target.Sig}
    {first second : List ManySortedFC.Relation} :
    Target.EvidenceArgs scope first -> Target.EvidenceArgs scope second ->
      Target.EvidenceArgs scope (first ++ second)
  | .nil, right => right
  | .cons newest older, right =>
      .cons newest (appendEvidenceArgs older right)

/-- Satisfaction composes in the same order as `Theory.append`. -/
def appendSatisfaction {scope : Target.Sig} {context : Target.Ctx scope}
    {symbols : List ManySortedFC.StaticSort}
    {arguments : ManySortedFC.SymbolArgs scope symbols}
    {firstRelations secondRelations : List ManySortedFC.Relation}
    {first : Target.Theory scope symbols firstRelations}
    {second : Target.Theory scope symbols secondRelations}
    {firstEvidence : Target.EvidenceArgs scope firstRelations}
    {secondEvidence : Target.EvidenceArgs scope secondRelations}
    (left : ManySortedFC.Theory.SatisfiedBy context arguments first
      firstEvidence)
    (right : ManySortedFC.Theory.SatisfiedBy context arguments second
      secondEvidence) :
    ManySortedFC.Theory.SatisfiedBy context arguments
      (ManySortedFC.Theory.append first second)
      (appendEvidenceArgs firstEvidence secondEvidence) :=
  match left with
  | .nil => right
  | .cons head tail => .cons head (appendSatisfaction tail right)

/-- A proof-carrying evidence block for a zero-symbol target theory. -/
structure CompiledTheorySatisfaction {scope : Target.Sig}
    (context : Target.Ctx scope) {relations : List ManySortedFC.Relation}
    (theory : Target.Theory scope [] relations) where
  evidence : Target.EvidenceArgs scope relations
  typing : ManySortedFC.Theory.SatisfiedBy context
    (.nil : ManySortedFC.SymbolArgs scope []) theory evidence

namespace CompiledTheorySatisfaction

/-- Append two compiled zero-symbol theory models. -/
def append {scope : Target.Sig} {context : Target.Ctx scope}
    {firstRelations secondRelations : List ManySortedFC.Relation}
    {first : Target.Theory scope [] firstRelations}
    {second : Target.Theory scope [] secondRelations}
    (left : CompiledTheorySatisfaction context first)
    (right : CompiledTheorySatisfaction context second) :
    CompiledTheorySatisfaction context
      (ManySortedFC.Theory.append first second) :=
  { evidence := appendEvidenceArgs left.evidence right.evidence
    typing := appendSatisfaction left.typing right.typing }

end CompiledTheorySatisfaction

/-- Compile every mode occurrence in newest-to-oldest order. -/
def compileModeCoverage {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    {sourceContext : DOTCapture.ModalIntersections.Ctx sourceScope}
    {assumptions : Source.ModalAssumptions sourceScope}
    {targetContext : Target.Ctx targetScope}
    {capture : Source.Capture sourceScope -> Target.Capture targetScope}
    (compiler : JudgmentCompiler sourceContext assumptions targetContext
      capture) :
    {modes : List Source.CaptureMode} ->
    (modeContext : Source.ModeContext modes sourceScope) ->
    (covered : forall {mode : Source.CaptureMode}
      {sourceCapture : Source.Capture sourceScope},
      DOTCapture.ModalIntersections.ModeContext.Occurs modeContext mode
        sourceCapture ->
      DOTCapture.ModalIntersections.Mode sourceContext assumptions
        sourceCapture mode) ->
    CompiledTheorySatisfaction targetContext
      (mapModeContext capture modeContext).toTheory
  | [], .nil, _ =>
      { evidence := .nil
        typing := .nil }
  | _ :: _, .cons rest newest, covered =>
      let head := compiler.mode (covered .here)
      let tail := compileModeCoverage compiler rest
        (fun occurrence => covered (.there occurrence))
      { evidence := .cons head.evidence tail.evidence
        typing := .cons (by simpa using head.typing) tail.typing }

/-- Compile the pairs between one new separation head and all older
positions, in exactly the order used by `SeparationContext.against`. -/
def compileAgainstCoverage {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    {sourceContext : DOTCapture.ModalIntersections.Ctx sourceScope}
    {assumptions : Source.ModalAssumptions sourceScope}
    {targetContext : Target.Ctx targetScope}
    {capture : Source.Capture sourceScope -> Target.Capture targetScope}
    (compiler : JudgmentCompiler sourceContext assumptions targetContext
      capture)
    (head : Source.Capture sourceScope) :
    {count : Nat} ->
    (rest : Source.SeparationContext count sourceScope) ->
    (covered : forall
      (position :
        DOTCapture.ModalIntersections.SeparationContext.Position rest),
      DOTCapture.ModalIntersections.Separate sourceContext assumptions
        head position.capture) ->
    CompiledTheorySatisfaction targetContext
      (ManySortedFC.SeparationContext.against (capture head)
        (mapSeparationContext capture rest))
  | 0, .nil, _ =>
      { evidence := .nil
        typing := .nil }
  | _ + 1, .cons older newest, covered =>
      let headProof := compiler.separate (covered .here)
      let tail := compileAgainstCoverage compiler head older
        (fun position => covered (.there position))
      { evidence := .cons headProof.evidence tail.evidence
        typing := .cons (by simpa using headProof.typing) tail.typing }

/-- Compile all canonical unordered separation pairs: newest against every
older position first, followed recursively by the older subcontext. -/
def compileSeparationCoverage {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    {sourceContext : DOTCapture.ModalIntersections.Ctx sourceScope}
    {assumptions : Source.ModalAssumptions sourceScope}
    {targetContext : Target.Ctx targetScope}
    {capture : Source.Capture sourceScope -> Target.Capture targetScope}
    (compiler : JudgmentCompiler sourceContext assumptions targetContext
      capture) :
    {count : Nat} ->
    (separation : Source.SeparationContext count sourceScope) ->
    (covered : forall
      (left right :
        DOTCapture.ModalIntersections.SeparationContext.Position separation),
      DOTCapture.ModalIntersections.SeparationContext.Position.Distinct
        left right ->
      DOTCapture.ModalIntersections.Separate sourceContext assumptions
        left.capture right.capture) ->
    CompiledTheorySatisfaction targetContext
      (mapSeparationContext capture separation).toTheory
  | 0, .nil, _ =>
      { evidence := .nil
        typing := .nil }
  | _ + 1, .cons rest newest, covered =>
      let against := compileAgainstCoverage compiler newest rest
        (fun position =>
          covered .here (.there position) (.hereThere position))
      let older := compileSeparationCoverage compiler rest
        (fun left right distinct =>
          covered (.there left) (.there right) (.thereThere distinct))
      against.append older

/-- Exact target evidence and declarative satisfaction for one source
`Satisfies` derivation. -/
structure CompiledSatisfaction {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (targetContext : Target.Ctx targetScope)
    (capture : Source.Capture sourceScope -> Target.Capture targetScope)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    (requirements : Source.ModalRequirements separationCount modes
      sourceScope) where
  evidence : Target.EvidenceArgs targetScope
    (ManySortedFC.modalRelations separationCount
      (translateCaptureModes modes))
  typing : ManySortedFC.Theory.SatisfiedBy targetContext
    (.nil : ManySortedFC.SymbolArgs targetScope [])
    (mapRequirements capture requirements).toTheory evidence

/-- Compile source satisfaction into the target's canonical mode-prefix then
unordered-separation-pair evidence order. -/
def compileSatisfies {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    {sourceContext : DOTCapture.ModalIntersections.Ctx sourceScope}
    {assumptions : Source.ModalAssumptions sourceScope}
    {targetContext : Target.Ctx targetScope}
    {capture : Source.Capture sourceScope -> Target.Capture targetScope}
    (compiler : JudgmentCompiler sourceContext assumptions targetContext
      capture)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    {requirements : Source.ModalRequirements separationCount modes
      sourceScope}
    (satisfaction : DOTCapture.ModalIntersections.Satisfies sourceContext
      assumptions requirements) :
    CompiledSatisfaction targetContext capture requirements :=
  match satisfaction with
  | @DOTCapture.ModalIntersections.Satisfies.mk _ _ _ _ _ separation
      modeContext modesCovered separationsCovered =>
      let mode := compileModeCoverage compiler modeContext modesCovered
      let separate := compileSeparationCoverage compiler separation
        separationsCovered
      let complete := mode.append separate
      { evidence := complete.evidence
        typing := complete.typing }

end DOTCaptureToManySortedFC.ModalIntersections
