import Coercions.ManySortedFC.Dynamics
import Coercions.ManySortedFC.TermTyping
import Coercions.ManySortedFC.TheoryMapValidity

/-!
# Static-substitution preservation and primitive modal beta

The modal beta rule eliminates a proof-only modal scope.  This module records
the general typing-preservation infrastructure needed to justify that
elimination: evidence-aware static substitutions preserve contexts, adapters,
and terms.  The final modal theorem retains the lock's explicit capture
certificate through `Tm.use`, so the exact immediate-use index is preserved.
-/

namespace ManySortedFC

/-! ## Weakening followed by static substitution -/

@[simp]
theorem Capture.weaken_substitute_lift {source target : Sig}
    (capture : Capture source) (substitution : StaticSubst source target)
    (kind : BinderKind) :
    capture.weaken.substitute (substitution.lift kind) =
      (capture.substitute substitution).weaken := by
  unfold Capture.weaken
  rw [Capture.rename_substitute capture Rename.succ
    (substitution.lift kind) (substitution.postRename Rename.succ)
    (StaticSubst.Follows.weaken substitution kind)]
  exact (Capture.substitute_postRename capture substitution Rename.succ).symm

@[simp]
theorem Ty.weaken_substitute_lift {source target : Sig}
    (type : Ty source) (substitution : StaticSubst source target)
    (kind : BinderKind) :
    type.weaken.substitute (substitution.lift kind) =
      (type.substitute substitution).weaken := by
  unfold Ty.weaken
  rw [Ty.rename_substitute type Rename.succ
    (substitution.lift kind) (substitution.postRename Rename.succ)
    (StaticSubst.Follows.weaken substitution kind)]
  exact (Ty.substitute_postRename type substitution Rename.succ).symm

@[simp]
theorem Ty.weaken_substitute_liftTerm {source target : Sig}
    (type : Ty source) (substitution : StaticSubst source target) :
    type.weaken.substitute substitution.liftTerm =
      (type.substitute substitution).weaken :=
  Ty.weaken_substitute_lift type substitution .term

@[simp]
theorem Capture.weaken_substitute_liftTerm {source target : Sig}
    (capture : Capture source) (substitution : StaticSubst source target) :
    capture.weaken.substitute substitution.liftTerm =
      (capture.substitute substitution).weaken :=
  Capture.weaken_substitute_lift capture substitution .term

@[simp]
theorem Proposition.weaken_substitute_lift {source target : Sig}
    {relation : Relation} (proposition : Proposition relation source)
    (substitution : StaticSubst source target) (kind : BinderKind) :
    (proposition.rename Rename.succ).substitute (substitution.lift kind) =
      (proposition.substitute substitution).rename Rename.succ := by
  rw [Proposition.rename_substitute proposition Rename.succ
    (substitution.lift kind) (substitution.postRename Rename.succ)
    (StaticSubst.Follows.weaken substitution kind)]
  exact (Proposition.substitute_postRename proposition substitution
    Rename.succ).symm

@[simp]
theorem Proposition.weakenMany_substitute_liftMany {source target : Sig}
    {relation : Relation} (proposition : Proposition relation source)
    (substitution : StaticSubst source target) :
  ∀ kinds : Sig,
      (proposition.rename (Rename.weakenMany source kinds)).substitute
          (substitution.liftMany kinds) =
        (proposition.substitute substitution).rename
          (Rename.weakenMany target kinds)
  | [] => by
      simp only [Rename.weakenMany, StaticSubst.liftMany]
      calc
        (proposition.rename Rename.id).substitute substitution =
            proposition.substitute substitution :=
          congrArg (fun current => current.substitute substitution)
            (Proposition.rename_id proposition)
        _ = (proposition.substitute substitution).rename Rename.id :=
          (Proposition.rename_id _).symm
  | kind :: rest => by
      simp only [Rename.weakenMany, StaticSubst.liftMany]
      calc
        (proposition.rename
            ((Rename.weakenMany source rest).comp Rename.succ)).substitute
              ((substitution.liftMany rest).lift kind) =
            ((proposition.rename
              (Rename.weakenMany source rest)).rename Rename.succ).substitute
                ((substitution.liftMany rest).lift kind) := by
              rw [Proposition.rename_comp]
        _ = ((proposition.rename
              (Rename.weakenMany source rest)).substitute
                (substitution.liftMany rest)).rename Rename.succ :=
              Proposition.weaken_substitute_lift _ _ _
        _ = ((proposition.substitute substitution).rename
              (Rename.weakenMany target rest)).rename Rename.succ := by
              rw [Proposition.weakenMany_substitute_liftMany proposition
                substitution rest]
        _ = (proposition.substitute substitution).rename
              ((Rename.weakenMany target rest).comp Rename.succ) :=
              Proposition.rename_comp _ _ _

@[simp]
theorem Capture.weakenMany_substitute_liftMany {source target : Sig}
    (capture : Capture source) (substitution : StaticSubst source target) :
  ∀ kinds : Sig,
      (capture.rename (Rename.weakenMany source kinds)).substitute
          (substitution.liftMany kinds) =
        (capture.substitute substitution).rename
          (Rename.weakenMany target kinds)
  | [] => by
      simp only [Rename.weakenMany, StaticSubst.liftMany]
      calc
        (capture.rename Rename.id).substitute substitution =
            capture.substitute substitution :=
          congrArg (fun current => current.substitute substitution)
            (Capture.rename_id capture)
        _ = (capture.substitute substitution).rename Rename.id :=
          (Capture.rename_id _).symm
  | kind :: rest => by
      simp only [Rename.weakenMany, StaticSubst.liftMany]
      calc
        (capture.rename
            ((Rename.weakenMany source rest).comp Rename.succ)).substitute
              ((substitution.liftMany rest).lift kind) =
            ((capture.rename
              (Rename.weakenMany source rest)).rename Rename.succ).substitute
                ((substitution.liftMany rest).lift kind) := by
              rw [Capture.rename_comp]
        _ = ((capture.rename
              (Rename.weakenMany source rest)).substitute
                (substitution.liftMany rest)).rename Rename.succ :=
              Capture.weaken_substitute_lift _ _ _
        _ = ((capture.substitute substitution).rename
              (Rename.weakenMany target rest)).rename Rename.succ := by
              rw [Capture.weakenMany_substitute_liftMany capture
                substitution rest]
        _ = (capture.substitute substitution).rename
              ((Rename.weakenMany target rest).comp Rename.succ) :=
              Capture.rename_comp _ _ _

@[simp]
theorem Ty.weakenMany_substitute_liftMany {source target : Sig}
    (type : Ty source) (substitution : StaticSubst source target) :
  ∀ kinds : Sig,
      (type.rename (Rename.weakenMany source kinds)).substitute
          (substitution.liftMany kinds) =
        (type.substitute substitution).rename
          (Rename.weakenMany target kinds)
  | [] => by
      simp only [Rename.weakenMany, StaticSubst.liftMany]
      calc
        (type.rename Rename.id).substitute substitution =
            type.substitute substitution :=
          congrArg (fun current => current.substitute substitution)
            (Ty.rename_id type)
        _ = (type.substitute substitution).rename Rename.id :=
          (Ty.rename_id _).symm
  | kind :: rest => by
      simp only [Rename.weakenMany, StaticSubst.liftMany]
      calc
        (type.rename
            ((Rename.weakenMany source rest).comp Rename.succ)).substitute
              ((substitution.liftMany rest).lift kind) =
            ((type.rename
              (Rename.weakenMany source rest)).rename Rename.succ).substitute
                ((substitution.liftMany rest).lift kind) := by
              rw [Ty.rename_comp]
        _ = ((type.rename
              (Rename.weakenMany source rest)).substitute
                (substitution.liftMany rest)).rename Rename.succ :=
              Ty.weaken_substitute_lift _ _ _
        _ = ((type.substitute substitution).rename
              (Rename.weakenMany target rest)).rename Rename.succ := by
              rw [Ty.weakenMany_substitute_liftMany type substitution rest]
        _ = (type.substitute substitution).rename
              ((Rename.weakenMany target rest).comp Rename.succ) :=
              Ty.rename_comp _ _ _

@[simp]
theorem Ty.weakenStatic_substitute_liftStatic {source target : Sig}
    (type : Ty source) (substitution : StaticSubst source target)
    (symbols : List StaticSort) (relations : List Relation) :
    (type.rename (Rename.weakenStatic symbols relations)).substitute
        (substitution.liftStatic symbols relations) =
      (type.substitute substitution).rename
        (Rename.weakenStatic symbols relations) := by
  unfold Rename.weakenStatic Rename.weakenSymbols
    StaticSubst.liftStatic StaticSubst.liftSymbols
    StaticSubst.liftEvidenceBlock
  calc
    (type.rename
        ((Rename.weakenMany source (symbolKinds symbols)).comp
          (Rename.weakenMany (SymbolScope source symbols)
            (evidenceKinds relations)))).substitute
      ((substitution.liftMany (symbolKinds symbols)).liftMany
        (evidenceKinds relations)) =
      ((type.rename (Rename.weakenMany source
        (symbolKinds symbols))).rename
          (Rename.weakenMany (SymbolScope source symbols)
            (evidenceKinds relations))).substitute
        ((substitution.liftMany (symbolKinds symbols)).liftMany
          (evidenceKinds relations)) := by rw [Ty.rename_comp]
    _ = ((type.rename (Rename.weakenMany source
          (symbolKinds symbols))).substitute
            (substitution.liftMany (symbolKinds symbols))).rename
          (Rename.weakenMany (SymbolScope target symbols)
            (evidenceKinds relations)) :=
      Ty.weakenMany_substitute_liftMany _ _ _
    _ = (((type.substitute substitution).rename
          (Rename.weakenMany target (symbolKinds symbols))).rename
            (Rename.weakenMany (SymbolScope target symbols)
              (evidenceKinds relations))) := by
      rw [Ty.weakenMany_substitute_liftMany]
    _ = (type.substitute substitution).rename
          ((Rename.weakenMany target (symbolKinds symbols)).comp
            (Rename.weakenMany (SymbolScope target symbols)
              (evidenceKinds relations))) := Ty.rename_comp _ _ _

@[simp]
theorem Capture.weakenStatic_substitute_liftStatic {source target : Sig}
    (capture : Capture source) (substitution : StaticSubst source target)
    (symbols : List StaticSort) (relations : List Relation) :
    (capture.rename (Rename.weakenStatic symbols relations)).substitute
        (substitution.liftStatic symbols relations) =
      (capture.substitute substitution).rename
        (Rename.weakenStatic symbols relations) := by
  unfold Rename.weakenStatic Rename.weakenSymbols
    StaticSubst.liftStatic StaticSubst.liftSymbols
    StaticSubst.liftEvidenceBlock
  calc
    (capture.rename
        ((Rename.weakenMany source (symbolKinds symbols)).comp
          (Rename.weakenMany (SymbolScope source symbols)
            (evidenceKinds relations)))).substitute
      ((substitution.liftMany (symbolKinds symbols)).liftMany
        (evidenceKinds relations)) =
      ((capture.rename (Rename.weakenMany source
        (symbolKinds symbols))).rename
          (Rename.weakenMany (SymbolScope source symbols)
            (evidenceKinds relations))).substitute
        ((substitution.liftMany (symbolKinds symbols)).liftMany
          (evidenceKinds relations)) := by rw [Capture.rename_comp]
    _ = ((capture.rename (Rename.weakenMany source
          (symbolKinds symbols))).substitute
            (substitution.liftMany (symbolKinds symbols))).rename
          (Rename.weakenMany (SymbolScope target symbols)
            (evidenceKinds relations)) :=
      Capture.weakenMany_substitute_liftMany _ _ _
    _ = (((capture.substitute substitution).rename
          (Rename.weakenMany target (symbolKinds symbols))).rename
            (Rename.weakenMany (SymbolScope target symbols)
              (evidenceKinds relations))) := by
      rw [Capture.weakenMany_substitute_liftMany]
    _ = (capture.substitute substitution).rename
          ((Rename.weakenMany target (symbolKinds symbols)).comp
            (Rename.weakenMany (SymbolScope target symbols)
              (evidenceKinds relations))) := Capture.rename_comp _ _ _

@[simp]
theorem Binding.weaken_substitute_lift {source target : Sig}
    {kind newest : BinderKind} (binding : Binding source kind)
    (substitution : StaticSubst source target) :
    binding.weaken.substitute (substitution.lift newest) =
      (binding.substitute substitution).weaken := by
  cases binding with
  | term type =>
      exact congrArg Binding.term
        (Ty.weaken_substitute_lift type substitution newest)
  | symbol => rfl
  | evidence proposition =>
      exact congrArg Binding.evidence
        (Proposition.weaken_substitute_lift proposition substitution newest)

@[simp]
theorem Binding.evidenceProposition_weaken_substitute_lift
    {source target : Sig} {relation : Relation}
    (binding : Binding source (.evidence relation))
    (substitution : StaticSubst source target) (newest : BinderKind) :
    (binding.weaken.evidenceProposition.substitute
        (substitution.lift newest)) =
      (binding.evidenceProposition.substitute substitution).rename
        Rename.succ := by
  cases binding with
  | evidence proposition =>
      exact Proposition.weaken_substitute_lift proposition substitution newest

/-! ## Structural weakening of evidence typing -/

@[simp]
theorem Evidence.substitute_ofRename {source target : Sig}
    {relation : Relation} (evidence : Evidence relation source)
    (rho : Rename source target) :
    evidence.substitute (TermStaticSubst.ofRename rho) =
      evidence.rename rho := by
  induction evidence generalizing target <;>
    simp_all only [Evidence.substitute, Evidence.rename,
      TermStaticSubst.ofRename,
      Ty.substitute_ofRename, StaticExpr.substitute_ofRename,
      Capture.substitute_ofRename]
  all_goals rfl

namespace TermStaticSubst.Preserves

noncomputable def identity {scope : Sig} (context : Ctx scope) :
    (TermStaticSubst.id (scope := scope)).Preserves context context := by
  constructor
  · intro index
    change context.lookup index =
      (context.lookup index).substitute StaticSubst.id
    rw [show StaticSubst.id (scope := scope) =
      StaticSubst.ofRename Rename.id by rfl]
    rw [Binding.substitute_ofRename, Binding.rename_id]
  · intro relation index
    apply Evidence.Proves.var
    change context.lookup index = Binding.evidence
      ((context.lookup index).evidenceProposition.substitute StaticSubst.id)
    rw [show StaticSubst.id (scope := scope) =
      StaticSubst.ofRename Rename.id by rfl]
    rw [Proposition.substitute_ofRename, Proposition.rename_id]
    cases context.lookup index
    rfl

/-- A structural weakening preserves every ambient term and evidence binding. -/
noncomputable def weaken {scope : Sig} (context : Ctx scope)
    {kind : BinderKind} (binding : Binding scope kind) :
    (TermStaticSubst.ofRename
      (Rename.succ (scope := scope) (kind := kind))).Preserves context
        (context.extend binding) := by
  constructor
  · intro index
    change (context.extend binding).lookup (.there index) =
      (context.lookup index).substitute (StaticSubst.ofRename Rename.succ)
    rw [Binding.substitute_ofRename]
    rfl
  · intro relation index
    change Evidence.Proves (context.extend binding)
      (.var (.there index))
      ((context.lookup index).evidenceProposition.substitute
        (StaticSubst.ofRename Rename.succ))
    apply Evidence.Proves.var
    rw [Ctx.lookup_there]
    cases h : context.lookup index with
    | evidence proposition =>
        simp [Binding.weaken, Binding.rename,
          Binding.evidenceProposition,
          Proposition.substitute_ofRename]

end TermStaticSubst.Preserves

/-! ## Static substitutions that preserve type and capture constructors

General static substitutions may replace a type variable by a capturing,
arrow, or modal type, and may replace a capture variable by the syntactic
empty capture.  Such substitutions do not commute with the capture-index
operations used by `Tm.HasType`.  Modal beta uses a much narrower action: it
replaces proof variables while leaving every static symbol a symbol. -/

namespace StaticSubst

structure Structural {source target : Sig}
    (substitution : StaticSubst source target) : Prop where
  symbolVar : ∀ {sort : StaticSort}
      (index : BVar source (.symbol sort)),
    ∃ targetIndex : BVar target (.symbol sort),
      substitution.symbolVar index = StaticExpr.symbol targetIndex

namespace Structural

def id {scope : Sig} : Structural (StaticSubst.id (scope := scope)) := by
  constructor
  intro sort index
  exact ⟨index, rfl⟩

def lift {source target : Sig} {substitution : StaticSubst source target}
    (structural : substitution.Structural) (kind : BinderKind) :
    (substitution.lift kind).Structural := by
  constructor
  intro sort index
  cases kind with
  | term =>
      cases index with
      | there index =>
          obtain ⟨targetIndex, equality⟩ := structural.symbolVar index
          exact ⟨.there targetIndex, by
            change (substitution.symbolVar index).weaken = _
            rw [equality]
            cases sort <;> rfl⟩
  | symbol newest =>
      cases index with
      | here => exact ⟨.here, rfl⟩
      | there index =>
          obtain ⟨targetIndex, equality⟩ := structural.symbolVar index
          exact ⟨.there targetIndex, by
            change (substitution.symbolVar index).weaken = _
            rw [equality]
            cases sort <;> rfl⟩
  | evidence relation =>
      cases index with
      | there index =>
          obtain ⟨targetIndex, equality⟩ := structural.symbolVar index
          exact ⟨.there targetIndex, by
            change (substitution.symbolVar index).weaken = _
            rw [equality]
            cases sort <;> rfl⟩

def liftMany {source target : Sig}
    {substitution : StaticSubst source target}
    (structural : substitution.Structural) : ∀ kinds : Sig,
    (substitution.liftMany kinds).Structural
  | [] => structural
  | kind :: rest => (structural.liftMany rest).lift kind

def liftStatic {source target : Sig}
    {substitution : StaticSubst source target}
    (structural : substitution.Structural) (symbols : List StaticSort)
    (relations : List Relation) :
    (substitution.liftStatic symbols relations).Structural := by
  unfold StaticSubst.liftStatic StaticSubst.liftSymbols
    StaticSubst.liftEvidenceBlock
  exact (structural.liftMany (symbolKinds symbols)).liftMany
    (evidenceKinds relations)

def liftModal {source target : Sig}
    {substitution : StaticSubst source target}
    (structural : substitution.Structural) (separationCount : Nat)
    (modes : List CaptureMode) :
    (substitution.liftModal separationCount modes).Structural := by
  unfold StaticSubst.liftModal StaticSubst.liftEvidenceBlock
  exact structural.liftMany _

def dropEvidence {source target : Sig}
    {substitution : StaticSubst source target}
    (structural : substitution.Structural) (relation : Relation) :
    (substitution.dropEvidence relation).Structural := by
  constructor
  intro sort index
  cases index with
  | there index => exact structural.symbolVar index

end Structural

@[simp]
theorem comp_assoc {first second third fourth : Sig}
    (one : StaticSubst first second) (two : StaticSubst second third)
    (three : StaticSubst third fourth) :
    (one.comp two).comp three = one.comp (two.comp three) := by
  apply StaticSubst.ext
  · intro index
    rfl
  · intro sort index
    exact StaticExpr.substitute_comp (one.symbolVar index) two three

theorem dropEvidence_eq_comp {source target : Sig}
    (substitution : StaticSubst source target) (relation : Relation) :
    substitution.dropEvidence relation =
      (StaticSubst.id.dropEvidence relation).comp substitution := by
  apply StaticSubst.ext
  · intro index
    cases index
    rfl
  · intro sort index
    cases index with
    | there index =>
        simp only [StaticSubst.dropEvidence, StaticSubst.comp,
          StaticSubst.id]
        rw [StaticExpr.symbol_substitute]

theorem dropEvidenceBlock_eq_comp {source target : Sig}
    (substitution : StaticSubst source target) : ∀ relations : List Relation,
    substitution.dropEvidenceBlock relations =
      (StaticSubst.id.dropEvidenceBlock relations).comp substitution
  | [] => by
      apply StaticSubst.ext
      · intro index
        rfl
      · intro sort index
        simp only [StaticSubst.dropEvidenceBlock, StaticSubst.comp,
          StaticSubst.id]
        rw [StaticExpr.symbol_substitute]
  | relation :: relations => by
      let sourceDrop : StaticSubst
          (Sig.extendMany source (evidenceKinds relations)) source :=
        StaticSubst.id.dropEvidenceBlock relations
      have induction := dropEvidenceBlock_eq_comp substitution relations
      calc
        substitution.dropEvidenceBlock (relation :: relations) =
            (substitution.dropEvidenceBlock relations).dropEvidence
              relation := rfl
        _ = (StaticSubst.id.dropEvidence relation).comp
              (substitution.dropEvidenceBlock relations) :=
            dropEvidence_eq_comp _ _
        _ = (StaticSubst.id.dropEvidence relation).comp
              (sourceDrop.comp substitution) := by
            rw [show substitution.dropEvidenceBlock relations =
              sourceDrop.comp substitution from induction]
        _ = ((StaticSubst.id.dropEvidence relation).comp sourceDrop).comp
              substitution := (StaticSubst.comp_assoc _ _ _).symm
        _ = (sourceDrop.dropEvidence relation).comp substitution := by
            rw [dropEvidence_eq_comp sourceDrop relation]

/-- Lifting through a proof-only block and then removing that block commutes
with any ambient static substitution. -/
theorem liftEvidenceBlock_comp_dropEvidenceBlock
    {source target : Sig} (substitution : StaticSubst source target) :
    ∀ relations : List Relation,
    (substitution.liftEvidenceBlock relations).comp
        (StaticSubst.id.dropEvidenceBlock relations) =
      (StaticSubst.id.dropEvidenceBlock relations).comp substitution
  | [] => by
      apply StaticSubst.ext
      · intro index
        rfl
      · intro sort index
        change (substitution.symbolVar index).substitute StaticSubst.id =
          (StaticExpr.symbol index).substitute substitution
        rw [show StaticSubst.id = StaticSubst.ofRename Rename.id by rfl,
          StaticExpr.substitute_ofRename, StaticExpr.rename_id,
          StaticExpr.symbol_substitute]
  | relation :: relations => by
      apply StaticSubst.ext
      · intro index
        cases index with
        | there index =>
            have point := congrArg
              (fun current => current.termVar index)
              (liftEvidenceBlock_comp_dropEvidenceBlock substitution
                relations)
            exact point
      · intro sort index
        cases index with
        | there index =>
            have point := congrArg
              (fun current => current.symbolVar index)
              (liftEvidenceBlock_comp_dropEvidenceBlock substitution
                relations)
            change (((substitution.liftEvidenceBlock relations).symbolVar
                index).rename Rename.succ).substitute
                  ((StaticSubst.id.dropEvidenceBlock relations).dropEvidence
                    relation) =
              ((StaticSubst.id.dropEvidenceBlock relations).symbolVar
                index).substitute substitution
            rw [StaticExpr.rename_substitute _ Rename.succ _ _
              (StaticSubst.Follows.dropEvidence
                (StaticSubst.id.dropEvidenceBlock relations) relation)]
            exact point

@[simp]
theorem liftModal_comp_dropModal {source target : Sig}
    (substitution : StaticSubst source target)
    (separationCount : Nat) (modes : List CaptureMode) :
    (substitution.liftModal separationCount modes).comp
        (StaticSubst.id.dropEvidenceBlock
          (modalRelations separationCount modes)) =
      (StaticSubst.id.dropEvidenceBlock
        (modalRelations separationCount modes)).comp substitution := by
  unfold StaticSubst.liftModal StaticSubst.liftEvidenceBlock
  exact liftEvidenceBlock_comp_dropEvidenceBlock substitution _

theorem staticOfSymbolArgs_naturality {source target : Sig}
    (substitution : TermStaticSubst source target)
    {symbols : List StaticSort} (arguments : SymbolArgs source symbols)
    (relations : List Relation) :
    (StaticSubst.staticOfSymbolArgs Rename.id arguments relations).comp
        substitution.static =
      (substitution.static.liftStatic symbols relations).comp
        (StaticSubst.staticOfSymbolArgs Rename.id
          (arguments.substitute substitution) relations) := by
  let sourceDrop : StaticSubst (StaticScope source symbols relations)
      (SymbolScope source symbols) :=
    StaticSubst.id.dropEvidenceBlock relations
  let targetDrop : StaticSubst (StaticScope target symbols relations)
      (SymbolScope target symbols) :=
    StaticSubst.id.dropEvidenceBlock relations
  let sourceSymbols : StaticSubst (SymbolScope source symbols) source :=
    StaticSubst.ofSymbolArgs Rename.id arguments
  let targetSymbols : StaticSubst (SymbolScope target symbols) target :=
    StaticSubst.ofSymbolArgs Rename.id
      (arguments.substitute substitution)
  calc
    (StaticSubst.staticOfSymbolArgs Rename.id arguments relations).comp
        substitution.static =
      (sourceDrop.comp sourceSymbols).comp substitution.static := by
        unfold StaticSubst.staticOfSymbolArgs
        rw [dropEvidenceBlock_eq_comp]
    _ = sourceDrop.comp (sourceSymbols.comp substitution.static) :=
      StaticSubst.comp_assoc _ _ _
    _ = sourceDrop.comp
        ((substitution.static.liftSymbols symbols).comp targetSymbols) := by
      rw [StaticSubst.instantiateSymbols_naturality substitution arguments]
    _ = (sourceDrop.comp
        (substitution.static.liftSymbols symbols)).comp targetSymbols :=
      (StaticSubst.comp_assoc _ _ _).symm
    _ = ((substitution.static.liftSymbols symbols).liftEvidenceBlock
        relations).comp (targetDrop.comp targetSymbols) := by
      rw [← StaticSubst.comp_assoc,
        ← liftEvidenceBlock_comp_dropEvidenceBlock]
    _ = (substitution.static.liftStatic symbols relations).comp
        (StaticSubst.staticOfSymbolArgs Rename.id
          (arguments.substitute substitution) relations) := by
      unfold StaticSubst.liftStatic StaticSubst.staticOfSymbolArgs
      rw [dropEvidenceBlock_eq_comp]

end StaticSubst

namespace Ty

@[simp]
theorem instantiateStatic_substitute {source target : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (body : Ty (StaticScope source symbols relations))
    (arguments : SymbolArgs source symbols)
    (substitution : TermStaticSubst source target) :
    (body.instantiateStatic arguments).substitute substitution.static =
      (body.substitute
        (substitution.static.liftStatic symbols relations)).instantiateStatic
          (arguments.substitute substitution) := by
  unfold Ty.instantiateStatic
  rw [Ty.substitute_comp, Ty.substitute_comp,
    StaticSubst.staticOfSymbolArgs_naturality]

end Ty

namespace TermStaticSubst

/-- The static part of evidence-only modal instantiation preserves every
type and capture constructor. -/
def fromEvidenceArgs_structural {scope : Sig} :
    {relations : List Relation} →
    (arguments : EvidenceArgs scope relations) →
    StaticSubst.Structural
      (TermStaticSubst.fromEvidenceArgs TermStaticSubst.id arguments).static
  | [], .nil => StaticSubst.Structural.id
  | _ :: _, .cons _ older =>
      (fromEvidenceArgs_structural older).dropEvidence _

end TermStaticSubst

namespace SeparationContext

@[simp]
theorem weakenMany_substitute_liftMany {source target : Sig}
    {count : Nat} (context : SeparationContext count source)
    (substitution : StaticSubst source target) (kinds : Sig) :
    (context.rename (Rename.weakenMany source kinds)).substitute
        (substitution.liftMany kinds) =
      (context.substitute substitution).rename
        (Rename.weakenMany target kinds) := by
  induction context with
  | nil => rfl
  | cons rest capture induction =>
      simp only [SeparationContext.rename, SeparationContext.substitute]
      rw [induction,
        Capture.weakenMany_substitute_liftMany capture substitution kinds]

end SeparationContext

namespace ModeContext

@[simp]
theorem weakenMany_substitute_liftMany {source target : Sig}
    {modes : List CaptureMode} (context : ModeContext modes source)
    (substitution : StaticSubst source target) (kinds : Sig) :
    (context.rename (Rename.weakenMany source kinds)).substitute
        (substitution.liftMany kinds) =
      (context.substitute substitution).rename
        (Rename.weakenMany target kinds) := by
  induction context with
  | nil => rfl
  | cons rest capture induction =>
      simp only [ModeContext.rename, ModeContext.substitute]
      rw [induction,
        Capture.weakenMany_substitute_liftMany capture substitution kinds]

end ModeContext

namespace ModalContext

@[simp]
theorem weakenModal_substitute_liftModal {source target : Sig}
    {separationCount : Nat} {modes : List CaptureMode}
    (context : ModalContext separationCount modes source)
    (substitution : StaticSubst source target)
    (availableSeparationCount : Nat)
    (availableModes : List CaptureMode) :
    (context.rename
        (Rename.weakenModal source availableSeparationCount
          availableModes)).substitute
      (substitution.liftModal availableSeparationCount availableModes) =
    (context.substitute substitution).rename
      (Rename.weakenModal target availableSeparationCount
        availableModes) := by
  cases context with
  | mk separation mode =>
      simp only [ModalContext.rename, ModalContext.substitute,
        Rename.weakenModal, StaticSubst.liftModal,
        StaticSubst.liftEvidenceBlock]
      rw [SeparationContext.weakenMany_substitute_liftMany,
        ModeContext.weakenMany_substitute_liftMany]

end ModalContext

namespace Ty

@[simp]
theorem outerCapture_substitute_structural {source target : Sig}
    (type : Ty source) (substitution : StaticSubst source target)
    (structural : substitution.Structural) :
    (type.substitute substitution).outerCapture =
      type.outerCapture.substitute substitution := by
  cases type with
  | tvar index =>
      obtain ⟨targetIndex, equality⟩ := structural.symbolVar index
      simp [Ty.substitute, equality, StaticExpr.symbol, Ty.outerCapture,
        Capture.substitute]
  | capturing captures shape => rfl
  | top | bot | one | arr | modal | forallT | existsT => rfl

@[simp]
theorem stripCapture_substitute_structural {source target : Sig}
    (type : Ty source) (substitution : StaticSubst source target)
    (structural : substitution.Structural) :
    (type.substitute substitution).stripCapture =
      type.stripCapture.substitute substitution := by
  cases type with
  | tvar index =>
      obtain ⟨targetIndex, equality⟩ := structural.symbolVar index
      simp [Ty.substitute, equality, StaticExpr.symbol, Ty.stripCapture]
  | capturing captures shape => rfl
  | top | bot | one | arr | modal | forallT | existsT => rfl

@[simp]
theorem precise_substitute_structural {source target : Sig}
    (capability : BVar source .term) (type : Ty source)
    (substitution : StaticSubst source target)
    (structural : substitution.Structural) :
    (Ty.precise capability type).substitute substitution =
      Ty.precise (substitution.termVar capability)
        (type.substitute substitution) := by
  cases type with
  | tvar index =>
      obtain ⟨targetIndex, equality⟩ := structural.symbolVar index
      simp [Ty.precise, Ty.substitute, equality, StaticExpr.symbol]
  | capturing captures shape => rfl
  | top | bot | one | arr | modal | forallT | existsT => rfl

@[simp]
theorem closeModal_substitute {source target : Sig}
    {separationCount : Nat} {modes : List CaptureMode}
    (type : Ty (ModalScope source separationCount modes))
    (substitution : StaticSubst source target) :
    (type.substitute
        (substitution.liftModal separationCount modes)).closeModal =
      type.closeModal.substitute substitution := by
  unfold Ty.closeModal
  rw [Ty.substitute_comp, Ty.substitute_comp,
    StaticSubst.liftModal_comp_dropModal]

end Ty

namespace Capture

@[simp]
theorem sequence_substitute_structural {source target : Sig}
    (immediate following : Capture source)
    (substitution : StaticSubst source target)
    (structural : substitution.Structural) :
    (immediate.sequence following).substitute substitution =
      (immediate.substitute substitution).sequence
        (following.substitute substitution) := by
  cases immediate with
  | cvar index =>
      obtain ⟨targetIndex, equality⟩ := structural.symbolVar index
      simp [Capture.sequence, Capture.substitute, equality,
        StaticExpr.symbol]
  | empty | union | readOnly | singleton => rfl

end Capture

namespace Tm.IsValue

theorem substituteStatic {source target : Sig} {term : Tm source}
    (value : Tm.IsValue term)
    (substitution : TermStaticSubst source target) :
    Tm.IsValue (term.substituteStatic substitution) := by
  induction value generalizing target with
  | var => exact .var
  | unit => exact .unit
  | lam => exact .lam
  | adapt _ induction => exact .adapt (induction substitution)
  | lock => exact .lock
  | @slam scope symbols relations theory closure body captures
      bodyValue induction =>
      exact .slam (induction
        (substitution.liftStatic symbols relations))
  | pack _ induction => exact .pack (induction substitution)

end Tm.IsValue

namespace TermStaticSubst

@[simp]
theorem lift_static {source target : Sig}
    (substitution : TermStaticSubst source target) (kind : BinderKind) :
    (substitution.lift kind).static = substitution.static.lift kind := by
  cases kind <;> rfl

@[simp]
theorem liftTerm_static {source target : Sig}
    (substitution : TermStaticSubst source target) :
    substitution.liftTerm.static = substitution.static.liftTerm := rfl

@[simp]
theorem liftSymbol_static {source target : Sig}
    (substitution : TermStaticSubst source target) (sort : StaticSort) :
    (substitution.liftSymbol sort).static =
      substitution.static.liftSymbol sort := rfl

@[simp]
theorem liftEvidence_static {source target : Sig}
    (substitution : TermStaticSubst source target) (relation : Relation) :
    (substitution.liftEvidence relation).static =
      substitution.static.liftEvidence relation := rfl

@[simp]
theorem liftMany_static {source target : Sig}
    (substitution : TermStaticSubst source target) : ∀ kinds : Sig,
    (substitution.liftMany kinds).static =
      substitution.static.liftMany kinds
  | [] => rfl
  | kind :: rest => by
      simp only [TermStaticSubst.liftMany, StaticSubst.liftMany,
        lift_static, liftMany_static]

@[simp]
theorem liftStatic_static {source target : Sig}
    (substitution : TermStaticSubst source target)
    (symbols : List StaticSort) (relations : List Relation) :
    (substitution.liftStatic symbols relations).static =
      substitution.static.liftStatic symbols relations := by
  unfold TermStaticSubst.liftStatic StaticSubst.liftStatic
    StaticSubst.liftSymbols StaticSubst.liftEvidenceBlock
  simp only [liftMany_static]

@[simp]
theorem liftModal_static {source target : Sig}
    (substitution : TermStaticSubst source target)
    (separationCount : Nat) (modes : List CaptureMode) :
    (substitution.liftModal separationCount modes).static =
      substitution.static.liftModal separationCount modes := by
  unfold TermStaticSubst.liftModal StaticSubst.liftModal
    StaticSubst.liftEvidenceBlock
  exact liftMany_static _ _

end TermStaticSubst

namespace Evidence.Proves

/-- Evidence typing is stable under one structural context weakening. -/
noncomputable def weaken {scope : Sig} {context : Ctx scope}
    {relation : Relation} {evidence : Evidence relation scope}
    {proposition : Proposition relation scope}
    (typing : Evidence.Proves context evidence proposition)
    {kind : BinderKind} (binding : Binding scope kind) :
    Evidence.Proves (context.extend binding) evidence.weaken
      (proposition.rename Rename.succ) := by
  have result := Evidence.Proves.substitute typing
    (TermStaticSubst.ofRename Rename.succ)
    (TermStaticSubst.Preserves.weaken context binding)
  rw [Evidence.substitute_ofRename] at result
  change Evidence.Proves (context.extend binding)
    (evidence.rename Rename.succ)
    (proposition.substitute (StaticSubst.ofRename Rename.succ)) at result
  rw [Proposition.substitute_ofRename] at result
  exact result

end Evidence.Proves

namespace TermStaticSubst.Preserves

/-- Preserve one fresh ordinary term binding. -/
noncomputable def liftTerm {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {substitution : TermStaticSubst source target}
    (preserves : substitution.Preserves sourceContext targetContext)
    (type : Ty source) :
    substitution.liftTerm.Preserves
      (sourceContext.extendTerm type)
      (targetContext.extendTerm (type.substitute substitution.static)) := by
  constructor
  · intro index
    cases index with
    | here =>
        change Binding.term
            ((type.substitute substitution.static).weaken) =
          Binding.term
            (type.weaken.substitute substitution.static.liftTerm)
        exact congrArg Binding.term
          (Ty.weaken_substitute_lift type substitution.static .term).symm
    | there index =>
        change (targetContext.lookup
            (substitution.static.termVar index)).weaken =
          ((sourceContext.lookup index).weaken).substitute
            substitution.static.liftTerm
        calc
          (targetContext.lookup
              (substitution.static.termVar index)).weaken =
              ((sourceContext.lookup index).substitute
                substitution.static).weaken :=
            congrArg Binding.weaken (preserves.term index)
          _ = ((sourceContext.lookup index).weaken).substitute
                substitution.static.liftTerm :=
            (Binding.weaken_substitute_lift
              (sourceContext.lookup index) substitution.static).symm
  · intro relation index
    cases index with
    | there index =>
        have induction := (preserves.evidence index).weaken
          (Binding.term (type.substitute substitution.static))
        change Evidence.Proves
          (targetContext.extend
            (Binding.term (type.substitute substitution.static)))
          (substitution.evidenceVar index).weaken
          ((Binding.evidenceProposition
            ((sourceContext.lookup index).weaken)).substitute
              substitution.static.liftTerm)
        change Evidence.Proves
          (targetContext.extend
            (Binding.term (type.substitute substitution.static)))
          (substitution.evidenceVar index).weaken
          ((Binding.evidenceProposition
            ((sourceContext.lookup index).weaken)).substitute
              (substitution.static.lift .term))
        rw [Binding.evidenceProposition_weaken_substitute_lift
          (sourceContext.lookup index) substitution.static .term]
        exact induction

/-- Preserve one fresh generative static symbol. -/
noncomputable def liftSymbol {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {substitution : TermStaticSubst source target}
    (preserves : substitution.Preserves sourceContext targetContext)
    (sort : StaticSort) :
    (substitution.liftSymbol sort).Preserves
      (sourceContext.extendSymbol sort) (targetContext.extendSymbol sort) := by
  constructor
  · intro index
    cases index with
    | there index =>
        change (targetContext.lookup
            (substitution.static.termVar index)).weaken =
          ((sourceContext.lookup index).weaken).substitute
            (substitution.static.liftSymbol sort)
        calc
          (targetContext.lookup
              (substitution.static.termVar index)).weaken =
              ((sourceContext.lookup index).substitute
                substitution.static).weaken :=
            congrArg Binding.weaken (preserves.term index)
          _ = ((sourceContext.lookup index).weaken).substitute
                (substitution.static.liftSymbol sort) :=
            (Binding.weaken_substitute_lift
              (sourceContext.lookup index) substitution.static).symm
  · intro relation index
    cases index with
    | there index =>
        have induction := (preserves.evidence index).weaken
          (Binding.symbol : Binding target (.symbol sort))
        change Evidence.Proves
          (targetContext.extend
            (Binding.symbol : Binding target (.symbol sort)))
          (substitution.evidenceVar index).weaken
          ((Binding.evidenceProposition
            ((sourceContext.lookup index).weaken)).substitute
              (substitution.static.liftSymbol sort))
        change Evidence.Proves
          (targetContext.extend
            (Binding.symbol : Binding target (.symbol sort)))
          (substitution.evidenceVar index).weaken
          ((Binding.evidenceProposition
            ((sourceContext.lookup index).weaken)).substitute
              (substitution.static.lift (.symbol sort)))
        rw [Binding.evidenceProposition_weaken_substitute_lift
          (sourceContext.lookup index) substitution.static (.symbol sort)]
        exact induction

/-- Preserve one fresh proof binder whose target proposition is the static
substitution of its source proposition. -/
noncomputable def liftEvidence {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {substitution : TermStaticSubst source target}
    (preserves : substitution.Preserves sourceContext targetContext)
    {relation : Relation} (proposition : Proposition relation source) :
    (substitution.liftEvidence relation).Preserves
      (sourceContext.extendEvidence proposition)
      (targetContext.extendEvidence
        (proposition.substitute substitution.static)) := by
  constructor
  · intro index
    cases index with
    | there index =>
        change (targetContext.lookup
            (substitution.static.termVar index)).weaken =
          ((sourceContext.lookup index).weaken).substitute
            (substitution.static.liftEvidence relation)
        calc
          (targetContext.lookup
              (substitution.static.termVar index)).weaken =
              ((sourceContext.lookup index).substitute
                substitution.static).weaken :=
            congrArg Binding.weaken (preserves.term index)
          _ = ((sourceContext.lookup index).weaken).substitute
                (substitution.static.liftEvidence relation) :=
            (Binding.weaken_substitute_lift
              (sourceContext.lookup index) substitution.static).symm
  · intro other index
    cases index with
    | here =>
        apply Evidence.Proves.var
        change Binding.evidence
            ((proposition.substitute substitution.static).rename Rename.succ) =
          Binding.evidence
            ((proposition.rename Rename.succ).substitute
              (substitution.static.liftEvidence relation))
        exact congrArg Binding.evidence
          (Proposition.weaken_substitute_lift proposition
            substitution.static (.evidence relation)).symm
    | there index =>
        have induction := (preserves.evidence index).weaken
          (Binding.evidence
            (proposition.substitute substitution.static))
        change Evidence.Proves
          (targetContext.extend
            (Binding.evidence
              (proposition.substitute substitution.static)))
          (substitution.evidenceVar index).weaken
          ((Binding.evidenceProposition
            ((sourceContext.lookup index).weaken)).substitute
              (substitution.static.liftEvidence relation))
        change Evidence.Proves
          (targetContext.extend
            (Binding.evidence
              (proposition.substitute substitution.static)))
          (substitution.evidenceVar index).weaken
          ((Binding.evidenceProposition
            ((sourceContext.lookup index).weaken)).substitute
              (substitution.static.lift (.evidence relation)))
        rw [Binding.evidenceProposition_weaken_substitute_lift
          (sourceContext.lookup index) substitution.static
            (.evidence relation)]
        exact induction

/-- Preserve a heterogeneous block of fresh static symbols. -/
noncomputable def liftSymbols {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {substitution : TermStaticSubst source target}
    (preserves : substitution.Preserves sourceContext targetContext) :
    ∀ symbols : List StaticSort,
      (substitution.liftMany (symbolKinds symbols)).Preserves
        (sourceContext.extendSymbols symbols)
        (targetContext.extendSymbols symbols)
  | [] => preserves
  | sort :: rest => (liftSymbols preserves rest).liftSymbol sort

/-- Preserve the complete names-first scope opened by a local theory. -/
noncomputable def liftTheory {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {substitution : TermStaticSubst source target}
    (preserves : substitution.Preserves sourceContext targetContext) :
    ∀ {symbols : List StaticSort} {relations : List Relation}
      (theory : Theory source symbols relations),
      (substitution.liftStatic symbols relations).Preserves
        (sourceContext.extendTheory theory)
        (targetContext.extendTheory
          (theory.substitute substitution.static))
  | symbols, [], .nil => by
      simpa [Ctx.extendTheory, TermStaticSubst.liftStatic] using
        preserves.liftSymbols symbols
  | symbols, relation :: relations, .cons proposition rest => by
      let previous := liftTheory preserves rest
      let sourceProposition := proposition.rename
        (Rename.weakenMany (SymbolScope source symbols)
          (evidenceKinds relations))
      have extended := previous.liftEvidence sourceProposition
      have propositionEq :
          sourceProposition.substitute
              (substitution.liftStatic symbols relations).static =
            (proposition.substitute
                (substitution.static.liftSymbols symbols)).rename
              (Rename.weakenMany (SymbolScope target symbols)
                (evidenceKinds relations)) := by
        simp only [sourceProposition, TermStaticSubst.liftStatic_static,
          StaticSubst.liftStatic, StaticSubst.liftEvidenceBlock]
        exact Proposition.weakenMany_substitute_liftMany proposition
          (substitution.static.liftSymbols symbols) _
      rw [propositionEq] at extended
      simpa [Ctx.extendTheory, Ctx.extendTheoryEvidence, Theory.substitute,
        TermStaticSubst.liftStatic, TermStaticSubst.liftMany,
        sourceProposition] using extended

/-- Preserve the proof-only theory generated by one primitive modal context. -/
noncomputable def liftModal {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {substitution : TermStaticSubst source target}
    (preserves : substitution.Preserves sourceContext targetContext)
    {separationCount : Nat} {modes : List CaptureMode}
    (requirements : ModalContext separationCount modes source) :
    (substitution.liftModal separationCount modes).Preserves
      (sourceContext.extendModal requirements)
      (targetContext.extendModal
        (requirements.substitute substitution.static)) := by
  have result := preserves.liftTheory requirements.toTheory
  simpa [Ctx.extendModal, TermStaticSubst.liftModal,
    TermStaticSubst.liftStatic, ModalContext.toTheory_substitute] using result

/-- External satisfaction supplies exactly the proof-variable substitution
used by primitive modal beta.  The generated modal assumptions are not
available while their replacements are checked. -/
noncomputable def instantiateModal {scope : Sig} {context : Ctx scope}
    {separationCount : Nat} {modes : List CaptureMode}
    {requirements : ModalContext separationCount modes scope}
    {evidenceArguments : EvidenceArgs scope
      (modalRelations separationCount modes)}
    (satisfaction : Theory.SatisfiedBy context
      (.nil : SymbolArgs scope []) requirements.toTheory evidenceArguments) :
    TermStaticSubst.Preserves (context.extendModal requirements) context
      (TermStaticSubst.fromEvidenceArgs TermStaticSubst.id
        evidenceArguments) := by
  let base : TermStaticSubst scope scope := TermStaticSubst.id
  have baseEq : base.static =
      StaticSubst.fromSymbolArgs (StaticSubst.ofRename Rename.id)
        (.nil : SymbolArgs scope []) := by
    rfl
  have sourceSatisfaction : Theory.SatisfiedBy context
      (.nil : SymbolArgs scope []) (requirements.toTheory.rename Rename.id)
      evidenceArguments := by
    simpa using satisfaction
  simpa [Ctx.extendModal, base] using
    (TermStaticSubst.Preserves.fromTheoryEvidence
      (source := scope) (target := scope) (symbols := [])
      (rho := Rename.id) (symbolContext := context)
      (arguments := (.nil : SymbolArgs scope [])) (base := base)
      baseEq (identity context) requirements.toTheory evidenceArguments
      sourceSatisfaction)

end TermStaticSubst.Preserves

namespace TheoryMorphism.Validates

noncomputable def substitute {source target : Sig}
    {symbols : List StaticSort} {allRelations relations : List Relation}
    {sourceContext : Ctx (StaticScope source symbols allRelations)}
    {targetContext : Ctx (StaticScope target symbols allRelations)}
    {targetTheory : Theory source symbols relations}
    {evidence : EvidenceArgs
      (StaticScope source symbols allRelations) relations}
    (typing : TheoryMorphism.Validates sourceContext targetTheory evidence)
    (substitution : TermStaticSubst source target)
    (liftedPreserves : TermStaticSubst.Preserves sourceContext targetContext
      (substitution.liftStatic symbols allRelations)) :
    TheoryMorphism.Validates targetContext
      (targetTheory.substitute substitution.static)
      (evidence.substitute
        (substitution.liftStatic symbols allRelations)) := by
  induction typing with
  | nil => exact .nil
  | @cons relation relations proposition rest newest older head tail
      induction =>
      have substituted := Evidence.Proves.substitute head
        (substitution.liftStatic symbols allRelations) liftedPreserves
      rw [TermStaticSubst.liftStatic_static] at substituted
      change Evidence.Proves targetContext
        (newest.substitute
          (substitution.liftStatic symbols allRelations))
        ((proposition.rename
          (Rename.weakenMany (SymbolScope source symbols)
            (evidenceKinds allRelations))).substitute
              ((substitution.static.liftSymbols symbols).liftMany
                (evidenceKinds allRelations))) at substituted
      rw [Proposition.weakenMany_substitute_liftMany proposition
        (substitution.static.liftSymbols symbols)
        (evidenceKinds allRelations)] at substituted
      exact .cons substituted induction

end TheoryMorphism.Validates

namespace TheoryMorphism.HasType

noncomputable def substitute {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {substitution : TermStaticSubst source target}
    {symbols : List StaticSort} {relations : List Relation}
    {sourceTheory targetTheory : Theory source symbols relations}
    {morphism : TheoryMorphism sourceTheory targetTheory}
    (typing : TheoryMorphism.HasType sourceContext morphism)
    (preserves : substitution.Preserves sourceContext targetContext) :
    TheoryMorphism.HasType targetContext
      (morphism.substitute substitution) := by
  exact TheoryMorphism.Validates.substitute typing substitution
    (preserves.liftTheory sourceTheory)

end TheoryMorphism.HasType

namespace ModalTheoryMap.HasType

noncomputable def substitute {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {substitution : TermStaticSubst source target}
    {requiredSeparationCount availableSeparationCount : Nat}
    {requiredModes availableModes : List CaptureMode}
    {available : ModalContext availableSeparationCount availableModes source}
    {required : ModalContext requiredSeparationCount requiredModes source}
    {mapping : ModalTheoryMap source availableSeparationCount availableModes
      requiredSeparationCount requiredModes}
    (typing : ModalTheoryMap.HasType sourceContext available required mapping)
    (liftedPreserves : TermStaticSubst.Preserves
      (sourceContext.extendModal available)
      (targetContext.extendModal
        (available.substitute substitution.static))
      (substitution.liftModal availableSeparationCount availableModes)) :
    ModalTheoryMap.HasType targetContext
      (available.substitute substitution.static)
      (required.substitute substitution.static)
      (mapping.substitute substitution) := by
  have result := Theory.SatisfiedBy.substitute typing
    (substitution.liftModal availableSeparationCount availableModes)
    liftedPreserves
  have theoryEq :
      Theory.substitute
          (TheoryMap.openedTarget available.toTheory required.toTheory)
          (substitution.liftModal availableSeparationCount
            availableModes).static =
        TheoryMap.openedTarget
          (available.substitute substitution.static).toTheory
          (required.substitute substitution.static).toTheory := by
    have sourceRename :
        Rename.weakenStatic (scope := source) []
            (modalRelations availableSeparationCount availableModes) =
          Rename.weakenModal source availableSeparationCount
            availableModes := by
      unfold Rename.weakenStatic Rename.weakenSymbols Rename.weakenModal
      simp only [symbolKinds, Rename.weakenMany]
      exact Rename.id_comp _
    have targetRename :
        Rename.weakenStatic (scope := target) []
            (modalRelations availableSeparationCount availableModes) =
          Rename.weakenModal target availableSeparationCount
            availableModes := by
      unfold Rename.weakenStatic Rename.weakenSymbols Rename.weakenModal
      simp only [symbolKinds, Rename.weakenMany]
      exact Rename.id_comp _
    unfold TheoryMap.openedTarget
    rw [sourceRename, targetRename,
      TermStaticSubst.liftModal_static]
    rw [ModalContext.toTheory_rename,
      ModalContext.toTheory_substitute,
      ModalContext.toTheory_rename]
    exact congrArg ModalContext.toTheory
      (ModalContext.weakenModal_substitute_liftModal required
        substitution.static availableSeparationCount availableModes)
  rw [theoryEq] at result
  change Theory.SatisfiedBy
    (targetContext.extendTheory
      (available.substitute substitution.static).toTheory)
    (.nil : SymbolArgs (ModalScope target availableSeparationCount
      availableModes) [])
    (TheoryMap.openedTarget
      (available.substitute substitution.static).toTheory
      (required.substitute substitution.static).toTheory)
    (mapping.evidence.substitute
      (substitution.liftModal availableSeparationCount availableModes))
    at result
  change Theory.SatisfiedBy
    (targetContext.extendTheory
      (available.substitute substitution.static).toTheory)
    (.nil : SymbolArgs (ModalScope target availableSeparationCount
      availableModes) [])
    (TheoryMap.openedTarget
      (available.substitute substitution.static).toTheory
      (required.substitute substitution.static).toTheory)
    (mapping.evidence.substitute
      (substitution.liftModal availableSeparationCount availableModes))
  exact result

end ModalTheoryMap.HasType

namespace Adapter.HasType

/-- Static substitution preserves adapter typing for the sufficient
symbol-preserving class used by modal evidence instantiation.  Arbitrary
symbol replacement is intentionally excluded because it can change the outer
constructor inspected by capture accounting. -/
noncomputable def substitute {sourceScope : Sig}
    {sourceContext : Ctx sourceScope} {adapter : Adapter sourceScope}
    {sourceType targetType : Ty sourceScope}
    (typing : Adapter.HasType sourceContext adapter sourceType targetType) :
    ∀ {targetScope : Sig} {targetContext : Ctx targetScope}
      (substitution : TermStaticSubst sourceScope targetScope),
      substitution.Preserves sourceContext targetContext →
      substitution.static.Structural →
      Adapter.HasType targetContext (adapter.substitute substitution)
        (sourceType.substitute substitution.static)
        (targetType.substitute substitution.static) := by
  induction typing with
  | identity type =>
      intro targetScope targetContext substitution preserves structural
      exact .identity _
  | cast evidenceTyping =>
      intro targetScope targetContext substitution preserves structural
      exact .cast (Evidence.Proves.substitute evidenceTyping substitution
        preserves)
  | @retagCapture scope context source targetCapture targetShape captures
      shape capturesTyping shapeTyping =>
      intro targetScope targetContext substitution preserves structural
      have substitutedCaptures := Evidence.Proves.substitute capturesTyping
        substitution preserves
      have substitutedShape := Evidence.Proves.substitute shapeTyping
        substitution preserves
      apply Adapter.HasType.retagCapture
      · simpa only [StaticExpr.substitute, Proposition.substitute,
          Ty.outerCapture_substitute_structural source substitution.static
            structural] using substitutedCaptures
      · simpa only [StaticExpr.substitute, Proposition.substitute,
          Ty.stripCapture_substitute_structural source substitution.static
            structural] using substitutedShape
  | forgetEmptyCapture shape =>
      intro targetScope targetContext substitution preserves structural
      exact .forgetEmptyCapture _
  | captured capturesTyping shapeTyping induction =>
      intro targetScope targetContext substitution preserves structural
      exact .captured
        (Evidence.Proves.substitute capturesTyping substitution preserves)
        (induction substitution preserves structural)
  | compose firstTyping secondTyping firstInduction secondInduction =>
      intro targetScope targetContext substitution preserves structural
      exact .compose
        (firstInduction substitution preserves structural)
        (secondInduction substitution preserves structural)
  | function domainTyping codomainTyping domainInduction codomainInduction =>
      intro targetScope targetContext substitution preserves structural
      exact .function
        (domainInduction substitution preserves structural)
        (codomainInduction substitution preserves structural)
  | @modal scope context sourceCount targetCount sourceModes targetModes
      sourceRequirements targetRequirements requirements result
      sourceResult targetResult requirementsTyping resultTyping induction =>
      intro targetScope targetContext substitution preserves structural
      have requirementsSubstituted := requirementsTyping.substitute
        (preserves.liftModal targetRequirements)
      have liftedStructural :
          StaticSubst.Structural
            (substitution.liftModal targetCount targetModes).static := by
        rw [TermStaticSubst.liftModal_static]
        exact structural.liftModal targetCount targetModes
      have resultSubstituted := induction
        (substitution.liftModal targetCount targetModes)
        (preserves.liftModal targetRequirements)
        liftedStructural
      simpa only [Adapter.substitute, Ty.substitute,
        TermStaticSubst.liftModal_static,
        Ty.closeModal_substitute] using
        (Adapter.HasType.modal requirementsSubstituted resultSubstituted)
  | @forallT scope context symbols relations theory body sourceBody targetBody
      bodyTyping induction =>
      intro targetScope targetContext substitution preserves structural
      have liftedStructural :
          (substitution.liftStatic symbols relations).static.Structural := by
        rw [TermStaticSubst.liftStatic_static]
        exact structural.liftStatic symbols relations
      simpa only [TermStaticSubst.liftStatic_static] using
        (Adapter.HasType.forallT (induction
          (substitution.liftStatic symbols relations)
          (preserves.liftTheory theory)
          liftedStructural))
  | @existsT scope context symbols relations theory payload sourcePayload
      targetPayload payloadTyping induction =>
      intro targetScope targetContext substitution preserves structural
      have liftedStructural :
          (substitution.liftStatic symbols relations).static.Structural := by
        rw [TermStaticSubst.liftStatic_static]
        exact structural.liftStatic symbols relations
      simpa only [TermStaticSubst.liftStatic_static] using
        (Adapter.HasType.existsT (induction
          (substitution.liftStatic symbols relations)
          (preserves.liftTheory theory)
          liftedStructural))
  | @forallMorphism scope context symbols relations sourceTheory targetTheory
      constraints body sourceBody targetBody constraintsTyping bodyTyping
      induction =>
      intro targetScope targetContext substitution preserves structural
      have liftedStructural :
          (substitution.liftStatic symbols relations).static.Structural := by
        rw [TermStaticSubst.liftStatic_static]
        exact structural.liftStatic symbols relations
      simpa only [TermStaticSubst.liftStatic_static] using
        (Adapter.HasType.forallMorphism
          (constraintsTyping.substitute preserves)
          (induction (substitution.liftStatic symbols relations)
            (preserves.liftTheory targetTheory)
            liftedStructural))
  | @existsMorphism scope context symbols relations sourceTheory targetTheory
      constraints payload sourcePayload targetPayload constraintsTyping
      payloadTyping induction =>
      intro targetScope targetContext substitution preserves structural
      have liftedStructural :
          (substitution.liftStatic symbols relations).static.Structural := by
        rw [TermStaticSubst.liftStatic_static]
        exact structural.liftStatic symbols relations
      simpa only [TermStaticSubst.liftStatic_static] using
        (Adapter.HasType.existsMorphism
          (constraintsTyping.substitute preserves)
          (induction (substitution.liftStatic symbols relations)
            (preserves.liftTheory sourceTheory)
            liftedStructural))

end Adapter.HasType

namespace Tm.HasType

/-- Static substitution preserves annotated term typing for a sufficient
symbol-preserving class containing modal evidence instantiation.  Arbitrary
symbol replacement is intentionally excluded. -/
noncomputable def substituteStatic {sourceScope : Sig}
    {sourceContext : Ctx sourceScope} {term : Tm sourceScope}
    {use : Capture sourceScope} {type : Ty sourceScope}
    (typing : _root_.ManySortedFC.Tm.HasType sourceContext term use type) :
    ∀ {targetScope : Sig} {targetContext : Ctx targetScope}
      (substitution : TermStaticSubst sourceScope targetScope),
      substitution.Preserves sourceContext targetContext →
      substitution.static.Structural →
      _root_.ManySortedFC.Tm.HasType targetContext
        (term.substituteStatic substitution)
        (use.substitute substitution.static)
        (type.substitute substitution.static) := by
  induction typing with
  | @var scope context index =>
      intro targetScope targetContext substitution preserves structural
      have result := _root_.ManySortedFC.Tm.HasType.var
        (context := targetContext)
        (substitution.static.termVar index)
      have lookup := preserves.term index
      cases h : context.lookup index with
      | term boundType =>
          rw [h] at lookup
          rw [lookup] at result
          simpa only [h, Tm.substituteStatic, Capture.substitute,
            Binding.substitute, Binding.termType,
            Ty.precise_substitute_structural index boundType
              substitution.static structural] using result
  | unit =>
      intro targetScope targetContext substitution preserves structural
      exact .unit
  | @lam scope context domain codomain closure body captures bodyUse
      bodyTyping capturesTyping bodyInduction =>
      intro targetScope targetContext substitution preserves structural
      have liftedStructural :
          StaticSubst.Structural substitution.liftTerm.static := by
        exact structural.lift .term
      have bodySubstituted := bodyInduction substitution.liftTerm
        (preserves.liftTerm domain) liftedStructural
      have capturesSubstituted := Evidence.Proves.substitute capturesTyping
        substitution.liftTerm (preserves.liftTerm domain)
      have bodyExact : _root_.ManySortedFC.Tm.HasType
          (targetContext.extendTerm (domain.substitute substitution.static))
          (body.substituteStatic substitution.liftTerm)
          (bodyUse.substitute substitution.liftTerm.static)
          (codomain.substitute substitution.static).weaken := by
        simpa only [TermStaticSubst.liftTerm_static,
          Ty.weaken_substitute_liftTerm] using bodySubstituted
      have capturesExact : Evidence.Proves
          (targetContext.extendTerm (domain.substitute substitution.static))
          (captures.substitute substitution.liftTerm)
          (.inclusion
            (.capture (bodyUse.substitute substitution.liftTerm.static))
          (.capture (.union
              (closure.substitute substitution.static).weaken
              (.singleton .here)))) := by
        simpa only [Proposition.substitute, StaticExpr.substitute,
          Capture.substitute, TermStaticSubst.liftTerm_static,
          Capture.weaken_substitute_liftTerm] using
          capturesSubstituted
      exact _root_.ManySortedFC.Tm.HasType.lam bodyExact capturesExact
  | @app scope context function argument functionType domain codomain
      functionUse argumentUse functionTyping functionShape argumentTyping
      functionInduction argumentInduction =>
      intro targetScope targetContext substitution preserves structural
      have shape := congrArg
        (fun current => current.substitute substitution.static) functionShape
      have targetShape :
          (functionType.substitute substitution.static).stripCapture =
            .arr (domain.substitute substitution.static)
              (codomain.substitute substitution.static) := by
        simpa only [Ty.stripCapture_substitute_structural functionType
          substitution.static structural, Ty.substitute] using shape
      have result := _root_.ManySortedFC.Tm.HasType.app
        (functionInduction substitution preserves structural) targetShape
        (argumentInduction substitution preserves structural)
      change _root_.ManySortedFC.Tm.HasType targetContext
        ((function.substituteStatic substitution).app
          (argument.substituteStatic substitution))
        ((functionUse.sequence
          (argumentUse.sequence
            (.union functionType.outerCapture domain.outerCapture))).substitute
              substitution.static)
        (codomain.substitute substitution.static)
      rw [Capture.sequence_substitute_structural functionUse _ _ structural,
        Capture.sequence_substitute_structural argumentUse _ _ structural,
        Capture.substitute,
        ← Ty.outerCapture_substitute_structural functionType _ structural,
        ← Ty.outerCapture_substitute_structural domain _ structural]
      exact result
  | @let' scope context result boundType bodyOuterUse rhsUse rhs body bodyUse
      discharge rhsTyping bodyTyping dischargeTyping rhsInduction
      bodyInduction =>
      intro targetScope targetContext substitution preserves structural
      have liftedStructural :
          StaticSubst.Structural substitution.liftTerm.static := by
        exact structural.lift .term
      have bodySubstituted := bodyInduction substitution.liftTerm
        (preserves.liftTerm boundType) liftedStructural
      have dischargeSubstituted := Evidence.Proves.substitute
        dischargeTyping substitution.liftTerm (preserves.liftTerm boundType)
      have bodyExact : _root_.ManySortedFC.Tm.HasType
          (targetContext.extendTerm (boundType.substitute substitution.static))
          (body.substituteStatic substitution.liftTerm)
          (bodyUse.substitute substitution.liftTerm.static)
          (result.substitute substitution.static).weaken := by
        simpa only [TermStaticSubst.liftTerm_static,
          Ty.weaken_substitute_liftTerm] using bodySubstituted
      have dischargeExact : Evidence.Proves
          (targetContext.extendTerm (boundType.substitute substitution.static))
          (discharge.substitute substitution.liftTerm)
          (.inclusion
            (.capture (bodyUse.substitute substitution.liftTerm.static))
            (.capture
              (bodyOuterUse.substitute substitution.static).weaken)) := by
        simpa only [Proposition.substitute, StaticExpr.substitute,
          TermStaticSubst.liftTerm_static,
          Capture.weaken_substitute_liftTerm] using dischargeSubstituted
      exact _root_.ManySortedFC.Tm.HasType.let'
        (rhsInduction substitution preserves structural)
        bodyExact dischargeExact
  | adapt termValue termTyping adapterTyping induction =>
      intro targetScope targetContext substitution preserves structural
      exact .adapt (termValue.substituteStatic substitution)
        (induction substitution preserves structural)
        (adapterTyping.substitute substitution preserves structural)
  | @lock scope context separationCount modes requirements result closure
      body captures bodyUse bodyTyping capturesTyping induction =>
      intro targetScope targetContext substitution preserves structural
      have liftedStructural : StaticSubst.Structural
          (substitution.liftModal separationCount modes).static := by
        rw [TermStaticSubst.liftModal_static]
        exact structural.liftModal separationCount modes
      have liftedPreserves := preserves.liftModal requirements
      have bodySubstituted := induction
        (substitution.liftModal separationCount modes) liftedPreserves
        liftedStructural
      have capturesSubstituted := Evidence.Proves.substitute capturesTyping
        (substitution.liftModal separationCount modes) liftedPreserves
      have bodyExact : _root_.ManySortedFC.Tm.HasType
          (targetContext.extendModal
            (requirements.substitute substitution.static))
          (body.substituteStatic
            (substitution.liftModal separationCount modes))
          (bodyUse.substitute
            (substitution.liftModal separationCount modes).static)
          ((result.substitute substitution.static).rename
            (Rename.weakenModal targetScope separationCount modes)) := by
        simpa only [TermStaticSubst.liftModal_static,
          Rename.weakenModal, StaticSubst.liftModal,
          StaticSubst.liftEvidenceBlock,
          Ty.weakenMany_substitute_liftMany] using bodySubstituted
      have capturesExact : Evidence.Proves
          (targetContext.extendModal
            (requirements.substitute substitution.static))
          (captures.substitute
            (substitution.liftModal separationCount modes))
          (.inclusion
            (.capture (bodyUse.substitute
              (substitution.liftModal separationCount modes).static))
            (.capture ((closure.substitute substitution.static).rename
              (Rename.weakenModal targetScope separationCount modes)))) := by
        simpa only [Proposition.substitute, StaticExpr.substitute,
          TermStaticSubst.liftModal_static, Rename.weakenModal,
          StaticSubst.liftModal, StaticSubst.liftEvidenceBlock,
          Capture.weakenMany_substitute_liftMany] using
          capturesSubstituted
      exact _root_.ManySortedFC.Tm.HasType.lock bodyExact capturesExact
  | @unlock scope context separationCount modes requirements term
      evidenceArguments termUse termType result termTyping termShape
      satisfaction induction =>
      intro targetScope targetContext substitution preserves structural
      have shape := congrArg
        (fun current => current.substitute substitution.static) termShape
      have targetShape :
          (termType.substitute substitution.static).stripCapture =
            .modal (requirements.substitute substitution.static)
              (result.substitute substitution.static) := by
        simpa only [Ty.stripCapture_substitute_structural termType
          substitution.static structural, Ty.substitute] using shape
      have satisfactionSubstituted := Theory.SatisfiedBy.substitute
        satisfaction substitution preserves
      have satisfactionExact : Theory.SatisfiedBy targetContext
          (.nil : SymbolArgs targetScope [])
          (requirements.substitute substitution.static).toTheory
          (evidenceArguments.substitute substitution) := by
        simpa only [SymbolArgs.substitute,
          ModalContext.toTheory_substitute] using satisfactionSubstituted
      have constructed := _root_.ManySortedFC.Tm.HasType.unlock
        (induction substitution preserves structural) targetShape
        satisfactionExact
      change _root_.ManySortedFC.Tm.HasType targetContext
        (.unlock (requirements.substitute substitution.static)
          (term.substituteStatic substitution)
          (evidenceArguments.substitute substitution))
        ((termUse.sequence termType.outerCapture).substitute
          substitution.static)
        (result.substitute substitution.static)
      rw [Capture.sequence_substitute_structural termUse _ _ structural,
        ← Ty.outerCapture_substitute_structural termType _ structural]
      exact constructed
  | @slam scope context symbols relations theory closure body bodyType
      captures bodyValue bodyTyping capturesTyping induction =>
      intro targetScope targetContext substitution preserves structural
      have liftedStructural : StaticSubst.Structural
          (substitution.liftStatic symbols relations).static := by
        rw [TermStaticSubst.liftStatic_static]
        exact structural.liftStatic symbols relations
      have liftedPreserves := preserves.liftTheory theory
      have bodySubstituted := induction
        (substitution.liftStatic symbols relations) liftedPreserves
        liftedStructural
      have capturesSubstituted := Evidence.Proves.substitute capturesTyping
        (substitution.liftStatic symbols relations) liftedPreserves
      have bodyOuterEq :
          (bodyType.substitute
            (substitution.liftStatic symbols relations).static).outerCapture =
            bodyType.outerCapture.substitute
              (substitution.liftStatic symbols relations).static :=
        Ty.outerCapture_substitute_structural bodyType
          (substitution.liftStatic symbols relations).static
          liftedStructural
      have closureEq :
          (closure.rename (Rename.weakenStatic symbols relations)).substitute
              (substitution.liftStatic symbols relations).static =
            (closure.substitute substitution.static).rename
              (Rename.weakenStatic symbols relations) := by
        rw [TermStaticSubst.liftStatic_static,
          Capture.weakenStatic_substitute_liftStatic]
      have capturesExact : Evidence.Proves
          (targetContext.extendTheory (theory.substitute substitution.static))
          (captures.substitute (substitution.liftStatic symbols relations))
          (.inclusion
            (.capture (bodyType.substitute
              (substitution.liftStatic symbols relations).static).outerCapture)
            (.capture ((closure.substitute substitution.static).rename
              (Rename.weakenStatic symbols relations)))) := by
        simpa only [Proposition.substitute, StaticExpr.substitute,
          bodyOuterEq, closureEq] using
          capturesSubstituted
      simpa only [Tm.substituteStatic, Ty.substitute, Capture.substitute,
        TermStaticSubst.liftStatic_static] using
        (_root_.ManySortedFC.Tm.HasType.slam
          (bodyValue.substituteStatic
            (substitution.liftStatic symbols relations))
          bodySubstituted capturesExact)
  | @sapp scope context symbols relations theory function functionType
      functionUse bodyType symbolArguments evidenceArguments functionTyping
      functionShape satisfaction induction =>
      intro targetScope targetContext substitution preserves structural
      have shape := congrArg
        (fun current => current.substitute substitution.static) functionShape
      have targetShape :
          (functionType.substitute substitution.static).stripCapture =
            .forallT (theory.substitute substitution.static)
              (bodyType.substitute
                (substitution.static.liftStatic symbols relations)) := by
        simpa only [Ty.stripCapture_substitute_structural functionType
          substitution.static structural, Ty.substitute] using shape
      have satisfactionSubstituted := Theory.SatisfiedBy.substitute
        satisfaction substitution preserves
      have constructed := _root_.ManySortedFC.Tm.HasType.sapp
        (induction substitution preserves structural) targetShape
        satisfactionSubstituted
      change _root_.ManySortedFC.Tm.HasType targetContext
        (.sapp (theory.substitute substitution.static)
          (function.substituteStatic substitution)
          (symbolArguments.substitute substitution)
          (evidenceArguments.substitute substitution))
        ((functionUse.sequence functionType.outerCapture).substitute
          substitution.static)
        ((bodyType.instantiateStatic symbolArguments).substitute
          substitution.static)
      rw [Capture.sequence_substitute_structural functionUse _ _ structural,
        ← Ty.outerCapture_substitute_structural functionType _ structural,
        Ty.instantiateStatic_substitute]
      exact constructed
  | @pack scope context symbols relations theory payloadType closure
      symbolArguments evidenceArguments payload captures satisfaction
      payloadValue payloadTyping capturesTyping induction =>
      intro targetScope targetContext substitution preserves structural
      have satisfactionSubstituted := Theory.SatisfiedBy.substitute
        satisfaction substitution preserves
      have payloadSubstituted := induction substitution preserves structural
      have capturesSubstituted := Evidence.Proves.substitute capturesTyping
        substitution preserves
      have payloadExact : _root_.ManySortedFC.Tm.HasType targetContext
          (payload.substituteStatic substitution) .empty
          ((payloadType.substitute
            (substitution.static.liftStatic symbols relations)).instantiateStatic
              (symbolArguments.substitute substitution)) := by
        simpa only [Capture.substitute,
          Ty.instantiateStatic_substitute] using payloadSubstituted
      have payloadOuterEq :
          ((payloadType.substitute
            (substitution.static.liftStatic symbols relations)).instantiateStatic
                (symbolArguments.substitute substitution)).outerCapture =
            Capture.substitute
              (payloadType.instantiateStatic symbolArguments).outerCapture
              substitution.static := by
        rw [← Ty.instantiateStatic_substitute payloadType symbolArguments
          substitution]
        exact Ty.outerCapture_substitute_structural
          (payloadType.instantiateStatic symbolArguments)
          substitution.static structural
      have capturesExact : Evidence.Proves targetContext
          (captures.substitute substitution)
          (.inclusion
            (.capture ((payloadType.substitute
              (substitution.static.liftStatic symbols relations)).instantiateStatic
                  (symbolArguments.substitute substitution)).outerCapture)
            (.capture (closure.substitute substitution.static))) := by
        simpa only [Proposition.substitute, StaticExpr.substitute,
          payloadOuterEq] using capturesSubstituted
      simpa only [Tm.substituteStatic, Ty.substitute, Capture.substitute,
        TermStaticSubst.liftStatic_static] using
        (_root_.ManySortedFC.Tm.HasType.pack satisfactionSubstituted
          (payloadValue.substituteStatic substitution) payloadExact
          capturesExact)
  | @«open» scope context symbols relations theory payloadType result
      bodyOuterUse packageUse packageType package body bodyUse discharge
      packageTyping packageShape bodyTyping dischargeTyping packageInduction
      bodyInduction =>
      intro targetScope targetContext substitution preserves structural
      have packageShapeSubstituted := congrArg
        (fun current => current.substitute substitution.static) packageShape
      have targetPackageShape :
          (packageType.substitute substitution.static).stripCapture =
            .existsT (theory.substitute substitution.static)
              (payloadType.substitute
                (substitution.static.liftStatic symbols relations)) := by
        simpa only [Ty.stripCapture_substitute_structural packageType
          substitution.static structural, Ty.substitute] using
          packageShapeSubstituted
      have staticStructural : StaticSubst.Structural
          (substitution.liftStatic symbols relations).static := by
        rw [TermStaticSubst.liftStatic_static]
        exact structural.liftStatic symbols relations
      have bodyStructural : StaticSubst.Structural
          ((substitution.liftStatic symbols relations).liftTerm).static := by
        exact staticStructural.lift .term
      have theoryPreserves := preserves.liftTheory theory
      have bodyPreserves := theoryPreserves.liftTerm payloadType
      have bodySubstituted := bodyInduction
        ((substitution.liftStatic symbols relations).liftTerm)
        bodyPreserves bodyStructural
      have dischargeSubstituted := Evidence.Proves.substitute dischargeTyping
        ((substitution.liftStatic symbols relations).liftTerm) bodyPreserves
      have bodyExact : _root_.ManySortedFC.Tm.HasType
          ((targetContext.extendTheory
            (theory.substitute substitution.static)).extendTerm
              (payloadType.substitute
                (substitution.static.liftStatic symbols relations)))
          (body.substituteStatic
            ((substitution.liftStatic symbols relations).liftTerm))
          (bodyUse.substitute
            ((substitution.liftStatic symbols relations).liftTerm).static)
          (((result.substitute substitution.static).rename
            (Rename.weakenStatic symbols relations)).weaken) := by
        simpa only [TermStaticSubst.liftStatic_static,
          TermStaticSubst.liftTerm_static,
          Ty.weaken_substitute_liftTerm,
          Ty.weakenStatic_substitute_liftStatic] using bodySubstituted
      have bodyOuterWeakenEq :
          ((bodyOuterUse.rename
            (Rename.weakenStatic symbols relations)).weaken).substitute
              ((substitution.liftStatic symbols relations).liftTerm).static =
            (((bodyOuterUse.substitute substitution.static).rename
              (Rename.weakenStatic symbols relations)).weaken) := by
        rw [TermStaticSubst.liftTerm_static,
          Capture.weaken_substitute_liftTerm,
          TermStaticSubst.liftStatic_static,
          Capture.weakenStatic_substitute_liftStatic]
      have dischargeExact : Evidence.Proves
          ((targetContext.extendTheory
            (theory.substitute substitution.static)).extendTerm
              (payloadType.substitute
                (substitution.static.liftStatic symbols relations)))
          (discharge.substitute
            ((substitution.liftStatic symbols relations).liftTerm))
          (.inclusion
            (.capture (bodyUse.substitute
              ((substitution.liftStatic symbols relations).liftTerm).static))
            (.capture (.union
              (((bodyOuterUse.substitute substitution.static).rename
                (Rename.weakenStatic symbols relations)).weaken)
              (.singleton .here)))) := by
        simp only [Proposition.substitute, StaticExpr.substitute,
          Capture.substitute] at dischargeSubstituted
        rw [bodyOuterWeakenEq] at dischargeSubstituted
        simpa only [TermStaticSubst.liftTerm_static,
          TermStaticSubst.liftStatic_static,
          StaticSubst.liftTerm] using dischargeSubstituted
      have constructed := _root_.ManySortedFC.Tm.HasType.«open»
        (packageInduction substitution preserves structural)
        targetPackageShape bodyExact dischargeExact
      have useEq :
          (packageUse.sequence
            (.union packageType.outerCapture bodyOuterUse)).substitute
              substitution.static =
            (packageUse.substitute substitution.static).sequence
              (.union
                (packageType.substitute substitution.static).outerCapture
                (bodyOuterUse.substitute substitution.static)) := by
        rw [Capture.sequence_substitute_structural packageUse _ _ structural,
          Capture.substitute,
          ← Ty.outerCapture_substitute_structural packageType _ structural]
      rw [useEq]
      simpa only [Tm.substituteStatic, Ty.substitute, Capture.substitute,
        TermStaticSubst.liftStatic_static] using constructed
  | use termTyping inclusionTyping induction =>
      intro targetScope targetContext substitution preserves structural
      exact .use (induction substitution preserves structural)
        (Evidence.Proves.substitute inclusionTyping substitution preserves)

end Tm.HasType

/-! ## Exact modal evidence instantiation -/

namespace Ty

/-- Eliminating the evidence binders introduced by a modal lock cancels the
corresponding weakening of an ambient result type. -/
theorem weakenModal_instantiateModal {scope : Sig}
    {separationCount : Nat} {modes : List CaptureMode}
    (type : Ty scope)
    (arguments : EvidenceArgs scope
      (modalRelations separationCount modes)) :
    (type.rename
      (Rename.weakenModal scope separationCount modes)).substitute
        (TermStaticSubst.fromEvidenceArgs TermStaticSubst.id arguments).static =
      type := by
  have follows : StaticSubst.Follows
      (Rename.weakenModal scope separationCount modes)
      (TermStaticSubst.fromEvidenceArgs TermStaticSubst.id arguments).static
      TermStaticSubst.id.static := by
    simpa only [Rename.weakenModal] using
      (StaticSubst.Follows.fromEvidenceArgs TermStaticSubst.id arguments)
  rw [Ty.rename_substitute type _ _ _ follows]
  change type.substitute StaticSubst.id = type
  rw [show StaticSubst.id (scope := scope) =
      StaticSubst.ofRename Rename.id by rfl,
    Ty.substitute_ofRename, Ty.rename_id]

end Ty

namespace Capture

/-- Modal evidence instantiation likewise cancels weakening of an ambient
capture annotation. -/
theorem weakenModal_instantiateModal {scope : Sig}
    {separationCount : Nat} {modes : List CaptureMode}
    (capture : Capture scope)
    (arguments : EvidenceArgs scope
      (modalRelations separationCount modes)) :
    (capture.rename
      (Rename.weakenModal scope separationCount modes)).substitute
        (TermStaticSubst.fromEvidenceArgs TermStaticSubst.id arguments).static =
      capture := by
  have follows : StaticSubst.Follows
      (Rename.weakenModal scope separationCount modes)
      (TermStaticSubst.fromEvidenceArgs TermStaticSubst.id arguments).static
      TermStaticSubst.id.static := by
    simpa only [Rename.weakenModal] using
      (StaticSubst.Follows.fromEvidenceArgs TermStaticSubst.id arguments)
  rw [Capture.rename_substitute capture _ _ _ follows]
  change capture.substitute StaticSubst.id = capture
  rw [show StaticSubst.id (scope := scope) =
      StaticSubst.ofRename Rename.id by rfl,
    Capture.substitute_ofRename, Capture.rename_id]

end Capture

namespace Tm.HasType

/-- Primitive modal beta preserves the exact ambient result and immediate-use
indices.  The lock's latent-use certificate is instantiated with the external
evidence and retained as an explicit `Tm.use` node in the reduct. -/
noncomputable def modalBeta {scope : Sig} {context : Ctx scope}
    {separationCount : Nat} {modes : List CaptureMode}
    {requirements : ModalContext separationCount modes scope}
    {result : Ty scope} {closure : Capture scope}
    {body : Tm (ModalScope scope separationCount modes)}
    {captures : Evidence (.inclusion .capture)
      (ModalScope scope separationCount modes)}
    {bodyUse : Capture (ModalScope scope separationCount modes)}
    {evidenceArguments : EvidenceArgs scope
      (modalRelations separationCount modes)}
    (bodyTyping : _root_.ManySortedFC.Tm.HasType
      (context.extendModal requirements) body bodyUse
      (result.rename
        (Rename.weakenModal scope separationCount modes)))
    (capturesTyping : Evidence.Proves
      (context.extendModal requirements) captures
      (.inclusion (.capture bodyUse)
        (.capture (closure.rename
          (Rename.weakenModal scope separationCount modes)))))
    (satisfaction : Theory.SatisfiedBy context
      (.nil : SymbolArgs scope []) requirements.toTheory
      evidenceArguments) :
    _root_.ManySortedFC.Tm.HasType context
      (.use (body.instantiateModal evidenceArguments)
        (captures.substitute
          (TermStaticSubst.fromEvidenceArgs TermStaticSubst.id
            evidenceArguments)))
      closure result := by
  let substitution := TermStaticSubst.fromEvidenceArgs
    TermStaticSubst.id evidenceArguments
  have preserves : substitution.Preserves
      (context.extendModal requirements) context :=
    TermStaticSubst.Preserves.instantiateModal satisfaction
  have structural : substitution.static.Structural :=
    TermStaticSubst.fromEvidenceArgs_structural evidenceArguments
  have bodySubstituted := bodyTyping.substituteStatic substitution
    preserves structural
  have bodyExact : _root_.ManySortedFC.Tm.HasType context
      (body.instantiateModal evidenceArguments)
      (bodyUse.substitute substitution.static) result := by
    simpa only [Tm.instantiateModal, substitution,
      Ty.weakenModal_instantiateModal result evidenceArguments] using
      bodySubstituted
  have capturesSubstituted := Evidence.Proves.substitute capturesTyping
    substitution preserves
  have capturesExact : Evidence.Proves context
      (captures.substitute substitution)
      (.inclusion (.capture (bodyUse.substitute substitution.static))
        (.capture closure)) := by
    simpa only [Proposition.substitute, StaticExpr.substitute,
      substitution,
      Capture.weakenModal_instantiateModal closure evidenceArguments] using
      capturesSubstituted
  exact .use bodyExact capturesExact

/-- Subject reduction for the primitive beta redex itself.  Inverting the
redex derivation recovers the lock body and its capture certificate; `modalBeta`
then checks the exact reduct produced by `ModalStep.beta` at the same indices. -/
noncomputable def modalBeta_subjectReduction {scope : Sig}
    {context : Ctx scope} {separationCount : Nat}
    {modes : List CaptureMode}
    {requirements : ModalContext separationCount modes scope}
    {result : Ty scope} {closure : Capture scope}
    {body : Tm (ModalScope scope separationCount modes)}
    {captures : Evidence (.inclusion .capture)
      (ModalScope scope separationCount modes)}
    {evidenceArguments : EvidenceArgs scope
      (modalRelations separationCount modes)}
    {use : Capture scope} {type : Ty scope}
    (typing : _root_.ManySortedFC.Tm.HasType context
      (.unlock requirements
        (.lock requirements result closure body captures)
        evidenceArguments)
      use type) :
    _root_.ManySortedFC.Tm.HasType context
      (.use (body.instantiateModal evidenceArguments)
        (captures.substitute
          (TermStaticSubst.fromEvidenceArgs TermStaticSubst.id
            evidenceArguments)))
      use type := by
  cases typing with
  | unlock lockTyping shape satisfaction =>
      cases lockTyping with
      | lock bodyTyping capturesTyping =>
          cases shape
          exact modalBeta bodyTyping capturesTyping satisfaction

end Tm.HasType

end ManySortedFC
