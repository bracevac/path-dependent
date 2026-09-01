import Coercions.ManySortedFC.ModalContext
import Coercions.ManySortedFC.TermTyping
import Coercions.ManySortedFC.TheoryMapValidity

/-!
# Modal evidence confinement

A primitive modal context adds only `Mode` and `Separate` assumptions.  This
module makes the resulting provenance boundary structural: equality,
inclusion, and disjointness certificates can be lowered through the modal
evidence block and therefore cannot depend on any assumption introduced by
the lock.
-/

namespace ManySortedFC

namespace BVar

/-- Remove a proof-only block from an evidence reference whose relation does
not occur in that block. -/
def lowerEvidenceBlock {scope : Sig} {relation : Relation} :
    {relations : List Relation} → relation ∉ relations →
      BVar (Sig.extendMany scope (evidenceKinds relations))
        (.evidence relation) → BVar scope (.evidence relation)
  | [], _, index => index
  | newest :: relations, absent, .here =>
      False.elim (absent (by simp))
  | newest :: relations, absent, .there index =>
      lowerEvidenceBlock (fun membership =>
        absent (List.mem_cons_of_mem newest membership)) index

/-- Lowering and then re-weakening a nonmember evidence reference returns the
same reference. -/
theorem weakenMany_lowerEvidenceBlock {scope : Sig} {relation : Relation} :
    ∀ {relations : List Relation} (absent : relation ∉ relations)
      (index : BVar (Sig.extendMany scope (evidenceKinds relations))
        (.evidence relation)),
      (Rename.weakenMany scope (evidenceKinds relations)).var
          (lowerEvidenceBlock absent index) = index := by
  intro relations
  induction relations with
  | nil =>
      intro absent index
      exact Rename.id_var index
  | cons newest relations induction =>
      intro absent index
      cases index with
      | here => exact False.elim (absent (by simp))
      | there index =>
          change BVar.there
              ((Rename.weakenMany scope (evidenceKinds relations)).var
                (lowerEvidenceBlock _ index)) = BVar.there index
          rw [induction]

end BVar

namespace StaticSubst

/-- Forget the proof-only binders introduced by one modal context. -/
def dropModal (scope : Sig) (separationCount : Nat)
    (modes : List CaptureMode) :
    StaticSubst (ModalScope scope separationCount modes) scope :=
  StaticSubst.id.dropEvidenceBlock
    (modalRelations separationCount modes)

private theorem dropEvidenceBlock_postRename (scope : Sig) :
    ∀ relations : List Relation,
    (StaticSubst.id.dropEvidenceBlock relations).postRename
        (Rename.weakenMany scope (evidenceKinds relations)) =
      StaticSubst.ofRename Rename.id := by
  intro relations
  induction relations with
  | nil =>
      apply StaticSubst.ext
      · intro index
        rfl
      · intro sort index
        change (StaticExpr.symbol index).rename Rename.id =
          StaticExpr.symbol index
        rw [StaticExpr.rename_id]
  | cons relation relations induction =>
      apply StaticSubst.ext
      · intro index
        cases index with
        | there index =>
            simp only [StaticSubst.dropEvidenceBlock,
              StaticSubst.dropEvidence, StaticSubst.postRename,
              evidenceKinds, Rename.weakenMany, Rename.comp_var]
            have point := congrArg
              (fun substitution => substitution.termVar index) induction
            exact congrArg BVar.there point
      · intro sort index
        cases index with
        | there index =>
            simp only [StaticSubst.dropEvidenceBlock,
              StaticSubst.dropEvidence, StaticSubst.postRename,
              evidenceKinds, Rename.weakenMany, Rename.comp_var]
            have point := congrArg
              (fun substitution => substitution.symbolVar index) induction
            change ((StaticSubst.id.dropEvidenceBlock relations).symbolVar
                index).rename
                  (Rename.weakenMany scope (evidenceKinds relations)) =
              StaticExpr.symbol index at point
            simp only [StaticSubst.ofRename, Rename.id_var]
            rw [← StaticExpr.rename_comp, point]
            cases sort <;> rfl

private def weakenMany_dropEvidenceBlock (scope : Sig) :
    ∀ relations : List Relation,
    StaticSubst.Follows
      (Rename.weakenMany scope (evidenceKinds relations))
      (StaticSubst.id.dropEvidenceBlock relations)
      (StaticSubst.ofRename Rename.id)
  | [] => by constructor <;> intros <;> rfl
  | relation :: relations =>
      (weakenMany_dropEvidenceBlock scope relations).dropAfter relation

@[simp]
theorem dropModal_postRename (scope : Sig) (separationCount : Nat)
    (modes : List CaptureMode) :
    (dropModal scope separationCount modes).postRename
        (Rename.weakenModal scope separationCount modes) =
      StaticSubst.ofRename Rename.id := by
  unfold dropModal Rename.weakenModal
  exact dropEvidenceBlock_postRename scope
    (modalRelations separationCount modes)

/-- Weakening into a modal block and then dropping it is the identity static
action on the outer scope. -/
def weakenModal_dropModal (scope : Sig) (separationCount : Nat)
    (modes : List CaptureMode) :
    StaticSubst.Follows
      (Rename.weakenModal scope separationCount modes)
      (dropModal scope separationCount modes)
      (StaticSubst.ofRename Rename.id) :=
  weakenMany_dropEvidenceBlock scope _

end StaticSubst

namespace Capture

theorem substitute_dropModal_rename {scope : Sig}
    (capture : Capture (ModalScope scope separationCount modes)) :
    (capture.substitute
        (StaticSubst.dropModal scope separationCount modes)).rename
          (Rename.weakenModal scope separationCount modes) = capture := by
  rw [Capture.substitute_postRename,
    StaticSubst.dropModal_postRename,
    Capture.substitute_ofRename, Capture.rename_id]

end Capture

namespace Ty

theorem substitute_dropModal_rename {scope : Sig}
    (type : Ty (ModalScope scope separationCount modes)) :
    (type.substitute
        (StaticSubst.dropModal scope separationCount modes)).rename
          (Rename.weakenModal scope separationCount modes) = type := by
  rw [Ty.substitute_postRename, StaticSubst.dropModal_postRename,
    Ty.substitute_ofRename, Ty.rename_id]

end Ty

namespace StaticExpr

/-- Static syntax cannot observe proof binders, so dropping and re-adding a
modal evidence block is the identity. -/
theorem substitute_dropModal_rename {scope : Sig} {sort : StaticSort}
    (expression : StaticExpr sort (ModalScope scope separationCount modes)) :
    (expression.substitute
        (StaticSubst.dropModal scope separationCount modes)).rename
          (Rename.weakenModal scope separationCount modes) = expression := by
  rw [StaticExpr.substitute_postRename,
    StaticSubst.dropModal_postRename,
    StaticExpr.substitute_ofRename, StaticExpr.rename_id]

end StaticExpr

namespace Proposition

theorem substitute_dropModal_rename {scope : Sig} {relation : Relation}
    (proposition : Proposition relation
      (ModalScope scope separationCount modes)) :
    (proposition.substitute
        (StaticSubst.dropModal scope separationCount modes)).rename
          (Rename.weakenModal scope separationCount modes) = proposition := by
  rw [Proposition.substitute_postRename,
    StaticSubst.dropModal_postRename,
    Proposition.substitute_ofRename, Proposition.rename_id]

theorem rename_weakenModal_substitute_dropModal {scope : Sig}
    {relation : Relation} (proposition : Proposition relation scope)
    (separationCount : Nat) (modes : List CaptureMode) :
    (proposition.rename
        (Rename.weakenModal scope separationCount modes)).substitute
          (StaticSubst.dropModal scope separationCount modes) =
      proposition := by
  rw [Proposition.rename_substitute proposition _ _ _
    (StaticSubst.weakenModal_dropModal scope separationCount modes),
    Proposition.substitute_ofRename, Proposition.rename_id]

end Proposition

namespace Evidence

/-- Lower an equality certificate through a modal proof block. -/
def lowerModalEquality {scope : Sig} {sort : StaticSort}
    {separationCount : Nat} {modes : List CaptureMode} :
    Evidence (.equality sort)
        (ModalScope scope separationCount modes) →
      Evidence (.equality sort) scope
  | .var index => .var (index.lowerEvidenceBlock
      (modalRelations_ne_equality separationCount modes sort))
  | .equalityRefl expression =>
      .equalityRefl (expression.substitute
        (StaticSubst.dropModal scope separationCount modes))
  | .equalitySymm evidence => .equalitySymm evidence.lowerModalEquality
  | .equalityTrans first second =>
      .equalityTrans first.lowerModalEquality second.lowerModalEquality
  | .unfoldRec bodies index =>
      .unfoldRec
        (bodies.substitute
          (StaticSubst.dropModal scope separationCount modes))
        index
  | .equalityArrow domain codomain =>
      .equalityArrow domain.lowerModalEquality codomain.lowerModalEquality
  | .equalityCapturing captures shape =>
      .equalityCapturing captures.lowerModalEquality
        shape.lowerModalEquality
  | .equalityCaptureUnion left right =>
      .equalityCaptureUnion left.lowerModalEquality
        right.lowerModalEquality
  | .equalityCaptureReadOnly capture =>
      .equalityCaptureReadOnly capture.lowerModalEquality

/-- Lower an inclusion certificate and every equality subcertificate it may
contain through a modal proof block. -/
def lowerModalInclusion {scope : Sig} {sort : StaticSort}
    {separationCount : Nat} {modes : List CaptureMode} :
    Evidence (.inclusion sort)
        (ModalScope scope separationCount modes) →
      Evidence (.inclusion sort) scope
  | .var index => .var (index.lowerEvidenceBlock
      (modalRelations_ne_inclusion separationCount modes sort))
  | .inclusionRefl expression =>
      .inclusionRefl (expression.substitute
        (StaticSubst.dropModal scope separationCount modes))
  | .inclusionTrans first second =>
      .inclusionTrans first.lowerModalInclusion second.lowerModalInclusion
  | .equalityToInclusion equality =>
      .equalityToInclusion equality.lowerModalEquality
  | .typeTop source => .typeTop (source.substitute
      (StaticSubst.dropModal scope separationCount modes))
  | .typeBottom target => .typeBottom (target.substitute
      (StaticSubst.dropModal scope separationCount modes))
  | .typeArrow domain codomain =>
      .typeArrow domain.lowerModalInclusion codomain.lowerModalInclusion
  | .typeCapturing captures shape =>
      .typeCapturing captures.lowerModalInclusion shape.lowerModalInclusion
  | .captureEmpty target => .captureEmpty (target.substitute
      (StaticSubst.dropModal scope separationCount modes))
  | .captureUnionLeft left right =>
      .captureUnionLeft
        (left.substitute (StaticSubst.dropModal scope separationCount modes))
        (right.substitute (StaticSubst.dropModal scope separationCount modes))
  | .captureUnionRight left right =>
      .captureUnionRight
        (left.substitute (StaticSubst.dropModal scope separationCount modes))
        (right.substitute (StaticSubst.dropModal scope separationCount modes))
  | .captureUnionElim left right =>
      .captureUnionElim left.lowerModalInclusion right.lowerModalInclusion
  | .captureVariable index => .captureVariable
      ((StaticSubst.dropModal scope separationCount modes).termVar index)
  | .captureReadOnly capture => .captureReadOnly (capture.substitute
      (StaticSubst.dropModal scope separationCount modes))
  | .captureReadOnlyMono subcapture =>
      .captureReadOnlyMono subcapture.lowerModalInclusion

/-- Lower a disjointness certificate and every equality subcertificate it
uses through a modal proof block. -/
def lowerModalDisjoint {scope : Sig}
    {separationCount : Nat} {modes : List CaptureMode} :
    Evidence .disjoint (ModalScope scope separationCount modes) →
      Evidence .disjoint scope
  | .var index => .var (index.lowerEvidenceBlock
      (modalRelations_ne_disjoint separationCount modes))
  | .disjointSymm evidence => .disjointSymm evidence.lowerModalDisjoint
  | .disjointUnion left right =>
      .disjointUnion left.lowerModalDisjoint right.lowerModalDisjoint
  | .disjointEmpty capture => .disjointEmpty (capture.substitute
      (StaticSubst.dropModal scope separationCount modes))
  | .disjointEquality equality disjoint =>
      .disjointEquality equality.lowerModalEquality
        disjoint.lowerModalDisjoint

@[simp]
def lowerModalEquality_rename {scope : Sig} {sort : StaticSort}
    {separationCount : Nat} {modes : List CaptureMode}
    (evidence : Evidence (.equality sort)
      (ModalScope scope separationCount modes)) :
    evidence.lowerModalEquality.rename
        (Rename.weakenModal scope separationCount modes) = evidence :=
  match evidence with
  | .var index => by
      simp only [lowerModalEquality, Evidence.rename]
      congr 1
      unfold Rename.weakenModal
      exact BVar.weakenMany_lowerEvidenceBlock _ index
  | .equalityRefl expression => by
      simp only [lowerModalEquality, Evidence.rename,
        StaticExpr.substitute_dropModal_rename]
  | .equalitySymm inner => by
      simp only [lowerModalEquality, Evidence.rename,
        lowerModalEquality_rename inner]
  | .equalityTrans first second => by
      simp only [lowerModalEquality, Evidence.rename,
        lowerModalEquality_rename first, lowerModalEquality_rename second]
  | .unfoldRec bodies index => by
      simp only [lowerModalEquality, Evidence.rename,
        RecBodies.substitute_postRename,
        StaticSubst.dropModal_postRename,
        RecBodies.substitute_ofRename, RecBodies.rename_id]
  | .equalityArrow domain codomain => by
      simp only [lowerModalEquality, Evidence.rename,
        lowerModalEquality_rename domain, lowerModalEquality_rename codomain]
  | .equalityCapturing captures shape => by
      simp only [lowerModalEquality, Evidence.rename,
        lowerModalEquality_rename captures, lowerModalEquality_rename shape]
  | .equalityCaptureUnion left right => by
      simp only [lowerModalEquality, Evidence.rename,
        lowerModalEquality_rename left, lowerModalEquality_rename right]
  | .equalityCaptureReadOnly capture => by
      simp only [lowerModalEquality, Evidence.rename,
        lowerModalEquality_rename capture]

@[simp]
def lowerModalInclusion_rename {scope : Sig} {sort : StaticSort}
    {separationCount : Nat} {modes : List CaptureMode}
    (evidence : Evidence (.inclusion sort)
      (ModalScope scope separationCount modes)) :
    evidence.lowerModalInclusion.rename
        (Rename.weakenModal scope separationCount modes) = evidence :=
  match evidence with
  | .var index => by
      simp only [lowerModalInclusion, Evidence.rename]
      congr 1
      unfold Rename.weakenModal
      exact BVar.weakenMany_lowerEvidenceBlock _ index
  | .inclusionRefl expression => by
      simp only [lowerModalInclusion, Evidence.rename,
        StaticExpr.substitute_dropModal_rename]
  | .inclusionTrans first second => by
      simp only [lowerModalInclusion, Evidence.rename,
        lowerModalInclusion_rename first, lowerModalInclusion_rename second]
  | .equalityToInclusion equality => by
      simp only [lowerModalInclusion, Evidence.rename,
        lowerModalEquality_rename]
  | .typeTop source => by
      simp only [lowerModalInclusion, Evidence.rename,
        Ty.substitute_dropModal_rename]
  | .typeBottom target => by
      simp only [lowerModalInclusion, Evidence.rename,
        Ty.substitute_dropModal_rename]
  | .typeArrow domain codomain => by
      simp only [lowerModalInclusion, Evidence.rename,
        lowerModalInclusion_rename domain, lowerModalInclusion_rename codomain]
  | .typeCapturing captures shape => by
      simp only [lowerModalInclusion, Evidence.rename,
        lowerModalInclusion_rename captures, lowerModalInclusion_rename shape]
  | .captureEmpty target => by
      simp only [lowerModalInclusion, Evidence.rename,
        Capture.substitute_dropModal_rename]
  | .captureUnionLeft left right => by
      simp only [lowerModalInclusion, Evidence.rename,
        Capture.substitute_dropModal_rename]
  | .captureUnionRight left right => by
      simp only [lowerModalInclusion, Evidence.rename,
        Capture.substitute_dropModal_rename]
  | .captureUnionElim left right => by
      simp only [lowerModalInclusion, Evidence.rename,
        lowerModalInclusion_rename left, lowerModalInclusion_rename right]
  | .captureVariable index => by
      simp only [lowerModalInclusion, Evidence.rename]
      have point := congrArg
        (fun substitution => substitution.termVar index)
        (StaticSubst.dropModal_postRename scope separationCount modes)
      exact congrArg Evidence.captureVariable (by
        simpa only [StaticSubst.postRename, StaticSubst.ofRename,
          Rename.id_var] using point)
  | .captureReadOnly capture => by
      simp only [lowerModalInclusion, Evidence.rename,
        Capture.substitute_dropModal_rename]
  | .captureReadOnlyMono subcapture => by
      simp only [lowerModalInclusion, Evidence.rename,
        lowerModalInclusion_rename subcapture]

@[simp]
def lowerModalDisjoint_rename {scope : Sig}
    {separationCount : Nat} {modes : List CaptureMode}
    (evidence : Evidence .disjoint
      (ModalScope scope separationCount modes)) :
    evidence.lowerModalDisjoint.rename
        (Rename.weakenModal scope separationCount modes) = evidence :=
  match evidence with
  | .var index => by
      simp only [lowerModalDisjoint, Evidence.rename]
      congr 1
      unfold Rename.weakenModal
      exact BVar.weakenMany_lowerEvidenceBlock _ index
  | .disjointSymm inner => by
      simp only [lowerModalDisjoint, Evidence.rename,
        lowerModalDisjoint_rename inner]
  | .disjointUnion left right => by
      simp only [lowerModalDisjoint, Evidence.rename,
        lowerModalDisjoint_rename left, lowerModalDisjoint_rename right]
  | .disjointEmpty capture => by
      simp only [lowerModalDisjoint, Evidence.rename,
        Capture.substitute_dropModal_rename]
  | .disjointEquality equality disjoint => by
      simp only [lowerModalDisjoint, Evidence.rename,
        lowerModalEquality_rename, lowerModalDisjoint_rename disjoint]

end Evidence

namespace Ctx

private theorem lookup_extendProofTheory_ambient {scope : Sig}
    (context : Ctx scope) :
    {relations : List Relation} → (theory : Theory scope [] relations) →
      {kind : BinderKind} → (index : BVar scope kind) →
      (context.extendTheory theory).lookup
          ((Rename.weakenMany scope (evidenceKinds relations)).var index) =
        (context.lookup index).rename
          (Rename.weakenMany scope (evidenceKinds relations))
  | [], .nil, _, index => by
      simpa only [Ctx.extendTheory, Ctx.extendSymbols, SymbolScope,
        symbolKinds, Ctx.extendTheoryEvidence, evidenceKinds,
        Rename.weakenMany, Rename.id_var] using
          (Binding.rename_id (context.lookup index)).symm
  | relation :: relations, .cons proposition rest, _, index => by
      change ((context.extendTheory rest).lookup
          ((Rename.weakenMany scope (evidenceKinds relations)).var index)).weaken =
        (context.lookup index).rename
          ((Rename.weakenMany scope (evidenceKinds relations)).comp
            (Rename.succ (kind := .evidence relation)))
      rw [lookup_extendProofTheory_ambient context rest index]
      exact Binding.rename_comp _ _ _

/-- Ambient bindings are merely weakened by modal-context extension. -/
theorem lookup_extendModal_ambient {scope : Sig} (context : Ctx scope)
    {separationCount : Nat} {modes : List CaptureMode}
    (requirements : ModalContext separationCount modes scope)
    {kind : BinderKind} (index : BVar scope kind) :
    (context.extendModal requirements).lookup
        ((Rename.weakenModal scope separationCount modes).var index) =
      (context.lookup index).rename
        (Rename.weakenModal scope separationCount modes) := by
  unfold Ctx.extendModal Rename.weakenModal
  exact lookup_extendProofTheory_ambient context requirements.toTheory index

/-- Looking up a term variable after dropping a modal proof block recovers the
substituted outer binding. -/
theorem lookup_dropModal_term {scope : Sig} (context : Ctx scope)
    {separationCount : Nat} {modes : List CaptureMode}
    (requirements : ModalContext separationCount modes scope)
    (index : BVar (ModalScope scope separationCount modes) .term) :
    context.lookup
        ((StaticSubst.dropModal scope separationCount modes).termVar index) =
      ((context.extendModal requirements).lookup index).substitute
        (StaticSubst.dropModal scope separationCount modes) := by
  let lower :=
    (StaticSubst.dropModal scope separationCount modes).termVar index
  have reweakened :
      (Rename.weakenModal scope separationCount modes).var lower = index := by
    have point := congrArg
      (fun substitution => substitution.termVar index)
      (StaticSubst.dropModal_postRename scope separationCount modes)
    exact point
  have lookup := lookup_extendModal_ambient context requirements lower
  rw [reweakened] at lookup
  calc
    context.lookup lower =
        (context.lookup lower).substitute
          (StaticSubst.ofRename Rename.id) := by
      rw [Binding.substitute_ofRename, Binding.rename_id]
    _ = ((context.lookup lower).rename
          (Rename.weakenModal scope separationCount modes)).substitute
            (StaticSubst.dropModal scope separationCount modes) :=
      (Binding.rename_substitute (context.lookup lower)
        (Rename.weakenModal scope separationCount modes)
        (StaticSubst.dropModal scope separationCount modes)
        (StaticSubst.ofRename Rename.id)
        (StaticSubst.weakenModal_dropModal scope separationCount modes)).symm
    _ = ((context.extendModal requirements).lookup index).substitute
          (StaticSubst.dropModal scope separationCount modes) := by
      rw [lookup]

end Ctx

namespace Evidence.Proves

private def lowerModalVar {scope : Sig} {context : Ctx scope}
    {separationCount : Nat} {modes : List CaptureMode}
    {requirements : ModalContext separationCount modes scope}
    {relation : Relation}
    (absent : relation ∉ modalRelations separationCount modes)
    {index : BVar (ModalScope scope separationCount modes)
      (.evidence relation)}
    {proposition : Proposition relation
      (ModalScope scope separationCount modes)}
    (binding : (context.extendModal requirements).lookup index =
      Binding.evidence proposition) :
    Evidence.Proves context
      (.var (index.lowerEvidenceBlock absent))
      (proposition.substitute
        (StaticSubst.dropModal scope separationCount modes)) := by
  let lower := index.lowerEvidenceBlock absent
  have reweakened :
      (Rename.weakenModal scope separationCount modes).var lower = index :=
    BVar.weakenMany_lowerEvidenceBlock absent index
  have lookup := Ctx.lookup_extendModal_ambient context requirements lower
  rw [reweakened] at lookup
  apply Evidence.Proves.var
  calc
    context.lookup lower =
        (context.lookup lower).substitute
          (StaticSubst.ofRename Rename.id) := by
      rw [Binding.substitute_ofRename, Binding.rename_id]
    _ = ((context.lookup lower).rename
          (Rename.weakenModal scope separationCount modes)).substitute
            (StaticSubst.dropModal scope separationCount modes) :=
      (Binding.rename_substitute (context.lookup lower)
        (Rename.weakenModal scope separationCount modes)
        (StaticSubst.dropModal scope separationCount modes)
        (StaticSubst.ofRename Rename.id)
        (StaticSubst.weakenModal_dropModal scope separationCount modes)).symm
    _ = (Binding.evidence proposition).substitute
          (StaticSubst.dropModal scope separationCount modes) := by
      rw [← lookup, binding]
    _ = Binding.evidence (proposition.substitute
          (StaticSubst.dropModal scope separationCount modes)) := rfl

/-- Checked equality derivations under a lock lower to checked derivations in
the unchanged outer context. -/
noncomputable def lowerModalEquality {scope : Sig} {context : Ctx scope}
    {separationCount : Nat} {modes : List CaptureMode}
    {requirements : ModalContext separationCount modes scope}
    {sort : StaticSort}
    {evidence : Evidence (.equality sort)
      (ModalScope scope separationCount modes)}
    {proposition : Proposition (.equality sort)
      (ModalScope scope separationCount modes)}
    (typing : Evidence.Proves (context.extendModal requirements)
      evidence proposition) :
    Evidence.Proves context evidence.lowerModalEquality
      (proposition.substitute
        (StaticSubst.dropModal scope separationCount modes)) :=
  match typing with
  | .var binding => by
      simpa [Evidence.lowerModalEquality] using
        (lowerModalVar
          (modalRelations_ne_equality separationCount modes sort) binding)
  | .equalityRefl expression => by
      simpa [Evidence.lowerModalEquality, Proposition.substitute] using
        (Evidence.Proves.equalityRefl (context := context)
          (expression.substitute
            (StaticSubst.dropModal scope separationCount modes)))
  | .equalitySymm inner => by
      simpa [Evidence.lowerModalEquality, Proposition.substitute] using
        Evidence.Proves.equalitySymm (lowerModalEquality inner)
  | .equalityTrans first second => by
      simpa [Evidence.lowerModalEquality, Proposition.substitute] using
        Evidence.Proves.equalityTrans (lowerModalEquality first)
          (lowerModalEquality second)
  | .unfoldRec guarded => by
      simpa [Evidence.lowerModalEquality, Proposition.substitute,
        StaticExpr.substitute, Ty.substitute,
        RecBodies.unfoldAt_substitute] using
        (Evidence.Proves.unfoldRec (context := context)
          (by simpa using guarded))
  | .equalityArrow domain codomain => by
      simpa [Evidence.lowerModalEquality, Proposition.substitute,
        StaticExpr.substitute, Ty.substitute] using
        Evidence.Proves.equalityArrow (lowerModalEquality domain)
          (lowerModalEquality codomain)
  | .equalityCapturing captures shape => by
      simpa [Evidence.lowerModalEquality, Proposition.substitute,
        StaticExpr.substitute, Ty.substitute] using
        Evidence.Proves.equalityCapturing (lowerModalEquality captures)
          (lowerModalEquality shape)
  | .equalityCaptureUnion left right => by
      simpa [Evidence.lowerModalEquality, Proposition.substitute,
        StaticExpr.substitute, Capture.substitute] using
        Evidence.Proves.equalityCaptureUnion (lowerModalEquality left)
          (lowerModalEquality right)
  | .equalityCaptureReadOnly capture => by
      simpa [Evidence.lowerModalEquality, Proposition.substitute,
        StaticExpr.substitute, Capture.substitute] using
        Evidence.Proves.equalityCaptureReadOnly (lowerModalEquality capture)

/-- Checked inclusion derivations under a lock lower to checked derivations in
the unchanged outer context.  Equality premises are lowered recursively. -/
noncomputable def lowerModalInclusion {scope : Sig} {context : Ctx scope}
    {separationCount : Nat} {modes : List CaptureMode}
    {requirements : ModalContext separationCount modes scope}
    {sort : StaticSort}
    {evidence : Evidence (.inclusion sort)
      (ModalScope scope separationCount modes)}
    {proposition : Proposition (.inclusion sort)
      (ModalScope scope separationCount modes)}
    (typing : Evidence.Proves (context.extendModal requirements)
      evidence proposition) :
    Evidence.Proves context evidence.lowerModalInclusion
      (proposition.substitute
        (StaticSubst.dropModal scope separationCount modes)) :=
  match typing with
  | .var binding => by
      simpa [Evidence.lowerModalInclusion] using
        (lowerModalVar
          (modalRelations_ne_inclusion separationCount modes sort) binding)
  | .inclusionRefl expression => by
      simpa [Evidence.lowerModalInclusion, Proposition.substitute] using
        (Evidence.Proves.inclusionRefl (context := context)
          (expression.substitute
            (StaticSubst.dropModal scope separationCount modes)))
  | .inclusionTrans first second => by
      simpa [Evidence.lowerModalInclusion, Proposition.substitute] using
        Evidence.Proves.inclusionTrans (lowerModalInclusion first)
          (lowerModalInclusion second)
  | .equalityToInclusion equality => by
      simpa [Evidence.lowerModalInclusion, Proposition.substitute] using
        Evidence.Proves.equalityToInclusion (lowerModalEquality equality)
  | .typeTop source => by
      simpa [Evidence.lowerModalInclusion, Proposition.substitute,
        StaticExpr.substitute, Ty.substitute] using
        (Evidence.Proves.typeTop (context := context)
          (source.substitute
            (StaticSubst.dropModal scope separationCount modes)))
  | .typeBottom target => by
      simpa [Evidence.lowerModalInclusion, Proposition.substitute,
        StaticExpr.substitute, Ty.substitute] using
        (Evidence.Proves.typeBottom (context := context)
          (target.substitute
            (StaticSubst.dropModal scope separationCount modes)))
  | .typeArrow domain codomain => by
      simpa [Evidence.lowerModalInclusion, Proposition.substitute,
        StaticExpr.substitute, Ty.substitute] using
        Evidence.Proves.typeArrow (lowerModalInclusion domain)
          (lowerModalInclusion codomain)
  | .typeCapturing captures shape => by
      simpa [Evidence.lowerModalInclusion, Proposition.substitute,
        StaticExpr.substitute, Ty.substitute] using
        Evidence.Proves.typeCapturing (lowerModalInclusion captures)
          (lowerModalInclusion shape)
  | .captureEmpty target => by
      simpa [Evidence.lowerModalInclusion, Proposition.substitute,
        StaticExpr.substitute] using
        (Evidence.Proves.captureEmpty (context := context)
          (target.substitute
            (StaticSubst.dropModal scope separationCount modes)))
  | .captureUnionLeft left right => by
      simpa [Evidence.lowerModalInclusion, Proposition.substitute,
        StaticExpr.substitute, Capture.substitute] using
        (Evidence.Proves.captureUnionLeft (context := context)
          (left.substitute
            (StaticSubst.dropModal scope separationCount modes))
          (right.substitute
            (StaticSubst.dropModal scope separationCount modes)))
  | .captureUnionRight left right => by
      simpa [Evidence.lowerModalInclusion, Proposition.substitute,
        StaticExpr.substitute, Capture.substitute] using
        (Evidence.Proves.captureUnionRight (context := context)
          (left.substitute
            (StaticSubst.dropModal scope separationCount modes))
          (right.substitute
            (StaticSubst.dropModal scope separationCount modes)))
  | .captureUnionElim left right => by
      simpa [Evidence.lowerModalInclusion, Proposition.substitute,
        StaticExpr.substitute, Capture.substitute] using
        Evidence.Proves.captureUnionElim (lowerModalInclusion left)
          (lowerModalInclusion right)
  | .captureVariable binding => by
      simpa [Evidence.lowerModalInclusion, Proposition.substitute,
        StaticExpr.substitute, Capture.substitute] using
        (Evidence.Proves.captureVariable (by
        rw [Ctx.lookup_dropModal_term context requirements, binding]
        rfl))
  | .captureReadOnly capture => by
      simpa [Evidence.lowerModalInclusion, Proposition.substitute,
        StaticExpr.substitute, Capture.substitute] using
        (Evidence.Proves.captureReadOnly (context := context)
          (capture.substitute
            (StaticSubst.dropModal scope separationCount modes)))
  | .captureReadOnlyMono subcapture => by
      simpa [Evidence.lowerModalInclusion, Proposition.substitute,
        StaticExpr.substitute, Capture.substitute] using
        Evidence.Proves.captureReadOnlyMono
          (lowerModalInclusion subcapture)

/-- Checked disjointness derivations under a lock lower to checked
derivations in the unchanged outer context. -/
noncomputable def lowerModalDisjoint {scope : Sig} {context : Ctx scope}
    {separationCount : Nat} {modes : List CaptureMode}
    {requirements : ModalContext separationCount modes scope}
    {evidence : Evidence .disjoint
      (ModalScope scope separationCount modes)}
    {proposition : Proposition .disjoint
      (ModalScope scope separationCount modes)}
    (typing : Evidence.Proves (context.extendModal requirements)
      evidence proposition) :
    Evidence.Proves context evidence.lowerModalDisjoint
      (proposition.substitute
        (StaticSubst.dropModal scope separationCount modes)) :=
  match typing with
  | .var binding => by
      simpa [Evidence.lowerModalDisjoint] using
        (lowerModalVar
          (modalRelations_ne_disjoint separationCount modes) binding)
  | .disjointSymm inner => by
      simpa [Evidence.lowerModalDisjoint, Proposition.substitute] using
        Evidence.Proves.disjointSymm (lowerModalDisjoint inner)
  | .disjointUnion left right => by
      simpa [Evidence.lowerModalDisjoint, Proposition.substitute,
        Capture.substitute] using
        Evidence.Proves.disjointUnion (lowerModalDisjoint left)
          (lowerModalDisjoint right)
  | .disjointEmpty capture => by
      simpa [Evidence.lowerModalDisjoint, Proposition.substitute] using
        (Evidence.Proves.disjointEmpty (context := context)
          (capture.substitute
            (StaticSubst.dropModal scope separationCount modes)))
  | .disjointEquality equality disjoint => by
      simpa [Evidence.lowerModalDisjoint, Proposition.substitute] using
        Evidence.Proves.disjointEquality (lowerModalEquality equality)
          (lowerModalDisjoint disjoint)

end Evidence.Proves

namespace Evidence.Proves

/-- Exact provenance package for a checked disjointness derivation under a
modal lock.  Both the certificate and proposition are weakenings of an outer
checked derivation. -/
structure DisjointModalOrigin {scope : Sig} (context : Ctx scope)
    {separationCount : Nat} {modes : List CaptureMode}
    (requirements : ModalContext separationCount modes scope)
    (evidence : Evidence .disjoint
      (ModalScope scope separationCount modes))
    (proposition : Proposition .disjoint
      (ModalScope scope separationCount modes)) where
  outerEvidence : Evidence .disjoint scope
  outerProposition : Proposition .disjoint scope
  typing : Evidence.Proves context outerEvidence outerProposition
  evidenceOrigin : outerEvidence.rename
    (Rename.weakenModal scope separationCount modes) = evidence
  propositionOrigin : outerProposition.rename
    (Rename.weakenModal scope separationCount modes) = proposition

/-- Every checked disjointness proof under a primitive lock has an exact
checked origin in the outer context. -/
noncomputable def disjoint_modalOrigin {scope : Sig} {context : Ctx scope}
    {separationCount : Nat} {modes : List CaptureMode}
    {requirements : ModalContext separationCount modes scope}
    {evidence : Evidence .disjoint
      (ModalScope scope separationCount modes)}
    {proposition : Proposition .disjoint
      (ModalScope scope separationCount modes)}
    (typing : Evidence.Proves (context.extendModal requirements)
      evidence proposition) :
    DisjointModalOrigin context requirements evidence proposition where
  outerEvidence := evidence.lowerModalDisjoint
  outerProposition := proposition.substitute
    (StaticSubst.dropModal scope separationCount modes)
  typing := typing.lowerModalDisjoint
  evidenceOrigin := Evidence.lowerModalDisjoint_rename evidence
  propositionOrigin := Proposition.substitute_dropModal_rename proposition

end Evidence.Proves

namespace BVar

/-- Decisive closed-world regression: a modal lock alone cannot introduce a
primitive disjointness reference.  Any closed disjointness proof must use a
proper constructor such as `disjointEmpty`, never a generated assumption. -/
theorem no_closed_modal_disjoint_reference (separationCount : Nat)
    (modes : List CaptureMode) :
    ¬ Nonempty (BVar (ModalScope [] separationCount modes)
      (.evidence .disjoint)) := by
  rintro ⟨index⟩
  have lowered : BVar [] (.evidence .disjoint) :=
    index.lowerEvidenceBlock
      (modalRelations_ne_disjoint separationCount modes)
  nomatch lowered

end BVar

namespace Tm

/-- Unlock evidence is checked in the unchanged outer context; entering the
lock is not part of satisfaction. -/
def unlock_satisfaction_outer {scope : Sig} {context : Ctx scope}
    {separationCount : Nat} {modes : List CaptureMode}
    {requirements : ModalContext separationCount modes scope}
    {term : Tm scope}
    {evidenceArguments : EvidenceArgs scope
      (modalRelations separationCount modes)}
    {use : Capture scope} {result : Ty scope}
    (typing : HasType context
      (.unlock requirements term evidenceArguments) use result) :
    requirements.SatisfiedBy context evidenceArguments :=
  Tm.unlock_satisfaction typing

end Tm

end ManySortedFC
