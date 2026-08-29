import DotToFCsub.BridgeMetatheory
import FCsub.RuntimeSubstitution
import DotFC.Source.Runtime

/-!
# Erased operational correspondence for the DOT-to-FCsub bridge

Source erasure and FCsub erasure use distinct intrinsically scoped runtime
languages. This module gives the structural embedding between them, proves
that it commutes with substitution and reduction, and closes the source-step
side of the Milestone-3 commuting diagram.
-/

namespace DotToFCsub.RuntimeEmbedding

/-- A mapping between the ordinary term variables of a DOT scope and an FCsub
scope. Static FCsub binders are invisible to this map. -/
abbrev VarMap (source : DotFC.Sig) (target : FCsub.Sig) :=
  DotFC.BVar source .term → FCsub.BVar target .term

namespace VarMap

/-- Lift a cross-calculus variable map below one runtime term binder. -/
def lift {source : DotFC.Sig} {target : FCsub.Sig}
    (mapping : VarMap source target) :
    VarMap (source ▹ .term) (target ▹ .term)
  | .here => .here
  | .there older => .there (mapping older)

end VarMap

/-- Homomorphic embedding of source runtime syntax into FCsub runtime syntax.
Source objects and target units are the same erased runtime payload. -/
def embedWith {source : DotFC.Sig} {target : FCsub.Sig}
    (mapping : VarMap source target) :
    DotFC.Source.Runtime.Tm source → FCsub.Runtime.Tm target
  | .var index => .var (mapping index)
  | .lam body => .lam (embedWith mapping.lift body)
  | .obj => .unit
  | .app function argument =>
      .app (embedWith mapping function) (embedWith mapping argument)
  | .let' rhs body =>
      .let' (embedWith mapping rhs) (embedWith mapping.lift body)

/-- Embedding commutes with a pair of compatible source/target renamings. -/
theorem embedWith_rename {source₁ source₂ : DotFC.Sig}
    {target₁ target₂ : FCsub.Sig}
    (term : DotFC.Source.Runtime.Tm source₁)
    (mapping₁ : VarMap source₁ target₁)
    (mapping₂ : VarMap source₂ target₂)
    (sourceRename : DotFC.Rename source₁ source₂)
    (targetRename : FCsub.Rename target₁ target₂)
    (compatible : ∀ index,
      mapping₂ (sourceRename.var index) =
        targetRename.var (mapping₁ index)) :
    embedWith mapping₂ (term.rename sourceRename) =
      (embedWith mapping₁ term).rename targetRename := by
  induction term generalizing target₁ source₂ target₂ with
  | var index =>
      simp only [DotFC.Source.Runtime.Tm.rename, embedWith,
        FCsub.Runtime.Tm.rename]
      rw [compatible]
  | lam body induction =>
      simp only [DotFC.Source.Runtime.Tm.rename, embedWith,
        FCsub.Runtime.Tm.rename]
      congr 1
      apply induction
      intro index
      cases index with
      | here => rfl
      | there older =>
          exact congrArg FCsub.BVar.there (compatible older)
  | obj => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [DotFC.Source.Runtime.Tm.rename, embedWith,
        FCsub.Runtime.Tm.rename]
      rw [functionInduction mapping₁ mapping₂ sourceRename targetRename
          compatible,
        argumentInduction mapping₁ mapping₂ sourceRename targetRename
          compatible]
  | let' rhs body rhsInduction bodyInduction =>
      simp only [DotFC.Source.Runtime.Tm.rename, embedWith,
        FCsub.Runtime.Tm.rename]
      rw [rhsInduction mapping₁ mapping₂ sourceRename targetRename compatible]
      congr 1
      apply bodyInduction
      intro index
      cases index with
      | here => rfl
      | there older =>
          exact congrArg FCsub.BVar.there (compatible older)

/-- Embedding and weakening below an ordinary runtime binder commute. -/
@[simp]
theorem embedWith_weaken {source : DotFC.Sig} {target : FCsub.Sig}
    (mapping : VarMap source target) (term : DotFC.Source.Runtime.Tm source) :
    embedWith mapping.lift (term.weaken (kind := .term)) =
      (embedWith mapping term).weaken (kind := .term) := by
  apply embedWith_rename term mapping mapping.lift DotFC.Rename.succ
    FCsub.Rename.succ
  intro index
  rfl

/-- Embedding commutes with compatible simultaneous substitutions. -/
theorem embedWith_subst {source₁ source₂ : DotFC.Sig}
    {target₁ target₂ : FCsub.Sig}
    (term : DotFC.Source.Runtime.Tm source₁)
    (mapping₁ : VarMap source₁ target₁)
    (mapping₂ : VarMap source₂ target₂)
    (sourceSubst : DotFC.Source.Runtime.Subst source₁ source₂)
    (targetSubst : FCsub.Runtime.Subst target₁ target₂)
    (compatible : ∀ index,
      embedWith mapping₂ (sourceSubst.var index) =
        targetSubst.var (mapping₁ index)) :
    embedWith mapping₂ (term.subst sourceSubst) =
      (embedWith mapping₁ term).subst targetSubst := by
  induction term generalizing target₁ source₂ target₂ with
  | var index => exact compatible index
  | lam body induction =>
      simp only [DotFC.Source.Runtime.Tm.subst, embedWith,
        FCsub.Runtime.Tm.subst]
      congr 1
      apply induction
      intro index
      cases index with
      | here => rfl
      | there older =>
          simpa only [DotFC.Source.Runtime.Subst.lift_there,
            FCsub.Runtime.Subst.lift, embedWith_weaken] using
            congrArg FCsub.Runtime.Tm.weaken (compatible older)
  | obj => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [DotFC.Source.Runtime.Tm.subst, embedWith,
        FCsub.Runtime.Tm.subst]
      rw [functionInduction mapping₁ mapping₂ sourceSubst targetSubst compatible,
        argumentInduction mapping₁ mapping₂ sourceSubst targetSubst compatible]
  | let' rhs body rhsInduction bodyInduction =>
      simp only [DotFC.Source.Runtime.Tm.subst, embedWith,
        FCsub.Runtime.Tm.subst]
      rw [rhsInduction mapping₁ mapping₂ sourceSubst targetSubst compatible]
      congr 1
      apply bodyInduction
      intro index
      cases index with
      | here => rfl
      | there older =>
          simpa only [DotFC.Source.Runtime.Subst.lift_there,
            FCsub.Runtime.Subst.lift, embedWith_weaken] using
            congrArg FCsub.Runtime.Tm.weaken (compatible older)

/-- Embedding commutes with opening the newest runtime binder. -/
@[simp]
theorem embedWith_open {source : DotFC.Sig} {target : FCsub.Sig}
    (mapping : VarMap source target)
    (body : DotFC.Source.Runtime.Tm (source ▹ .term))
    (replacement : DotFC.Source.Runtime.Tm source) :
    embedWith mapping (body.open replacement) =
      (embedWith mapping.lift body).open (embedWith mapping replacement) := by
  apply embedWith_subst body mapping.lift mapping
    (DotFC.Source.Runtime.Subst.openAt replacement)
    (FCsub.Runtime.Subst.openAt (embedWith mapping replacement))
  intro index
  cases index <;> rfl

/-- The canonical variable map selected by the translated source context. -/
def contextMap {source : DotFC.Sig} (context : DotFC.Source.Ctx source) :
    VarMap source (DotToFCsub.Elaboration.TargetSig context) :=
  DotToFCsub.Layout.termVar (DotFC.Explicit.Ctx.ofSource context)

/-- Embed a source runtime term in the layout induced by its ambient context. -/
def embed {source : DotFC.Sig} (context : DotFC.Source.Ctx source)
    (term : DotFC.Source.Runtime.Tm source) :
    FCsub.Runtime.Tm (DotToFCsub.Elaboration.TargetSig context) :=
  embedWith (contextMap context) term

/-- Source runtime values remain values after embedding. -/
theorem value_embedWith {source : DotFC.Sig} {target : FCsub.Sig}
    {term : DotFC.Source.Runtime.Tm source}
    (mapping : VarMap source target)
    (value : DotFC.Source.Runtime.IsValue term) :
    FCsub.Runtime.IsValue (embedWith mapping term) := by
  cases value with
  | lam => exact .lam
  | obj => exact .unit

/-- Every source runtime step becomes exactly one FCsub runtime step. -/
theorem step_embedWith {source : DotFC.Sig} {target : FCsub.Sig}
    {term reduct : DotFC.Source.Runtime.Tm source}
    (mapping : VarMap source target)
    (step : DotFC.Source.Runtime.Step term reduct) :
    FCsub.Runtime.Step (embedWith mapping term) (embedWith mapping reduct) := by
  induction step with
  | appFunction step induction =>
      exact .appFunction induction
  | appArgument functionValue step induction =>
      exact .appArgument (value_embedWith mapping functionValue) induction
  | beta argumentValue =>
      simpa only [embedWith, embedWith_open] using
        (FCsub.Runtime.Step.beta (value_embedWith mapping argumentValue))
  | letRhs step induction =>
      exact .letRhs induction
  | zeta rhsValue =>
      simpa only [embedWith, embedWith_open] using
        (FCsub.Runtime.Step.zeta (value_embedWith mapping rhsValue))

/-- Source runtime multisteps embed homomorphically. -/
theorem steps_embedWith {source : DotFC.Sig} {target : FCsub.Sig}
    {term reduct : DotFC.Source.Runtime.Tm source}
    (mapping : VarMap source target)
    (steps : DotFC.Source.Runtime.Steps term reduct) :
    FCsub.Runtime.Steps (embedWith mapping term) (embedWith mapping reduct) := by
  induction steps with
  | refl => exact .refl
  | tail steps step induction =>
      exact .tail induction (step_embedWith mapping step)

end DotToFCsub.RuntimeEmbedding

namespace DotToFCsub.Elaboration

open FCsub

/-! ## Agreement with derivation-directed erasure -/

/-- A plain source binder induces exactly one ordinary target runtime binder. -/
@[simp]
theorem contextMap_snoc_top {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source) :
    RuntimeEmbedding.contextMap (context.snoc .top) =
      (RuntimeEmbedding.contextMap context).lift := by
  funext index
  cases index <;> rfl

@[simp]
theorem contextMap_snoc_bot {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source) :
    RuntimeEmbedding.contextMap (context.snoc .bot) =
      (RuntimeEmbedding.contextMap context).lift := by
  funext index
  cases index <;> rfl

@[simp]
theorem contextMap_snoc_all {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source) (domain : DotFC.Source.Ty source)
    (codomain : DotFC.Source.Ty (source ▹ .term)) :
    RuntimeEmbedding.contextMap (context.snoc (.all domain codomain)) =
      (RuntimeEmbedding.contextMap context).lift := by
  funext index
  cases index <;> rfl

@[simp]
theorem contextMap_snoc_selection {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source)
    (path : DotFC.BVar source .term) (label : DotFC.Source.Name) :
    RuntimeEmbedding.contextMap (context.snoc (.sel path label)) =
      (RuntimeEmbedding.contextMap context).lift := by
  funext index
  cases index <;> rfl

/-- Dropping a direct member binder's static telescope turns its canonical
runtime-variable layout into the ordinary lifted source-variable layout. -/
theorem sourceRuntime_member_context {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source) (label : DotFC.Source.Name)
    (lower upper : DotFC.Source.Ty source)
    (term : DotFC.Source.Runtime.Tm (source ▹ .term)) :
    (RuntimeEmbedding.embed
        (context.snoc (.member label lower upper)) term).subst
        (FCsub.Runtime.Subst.dropPayload
          MemberEncoding.names MemberEncoding.constraints) =
      RuntimeEmbedding.embedWith
        (RuntimeEmbedding.contextMap context).lift term := by
  have embedded := RuntimeEmbedding.embedWith_subst term
    (RuntimeEmbedding.contextMap
      (context.snoc (.member label lower upper)))
    (RuntimeEmbedding.contextMap context).lift
    DotFC.Source.Runtime.Subst.id
    (FCsub.Runtime.Subst.dropPayload
      MemberEncoding.names MemberEncoding.constraints)
    (by
      intro index
      cases index with
      | here => rfl
      | there older =>
          have point := congrArg
            (fun substitution => substitution.var
              (RuntimeEmbedding.contextMap context older))
            (FCsub.Runtime.Subst.ofRename_weakenPayload_comp_dropPayload
              (scope := TargetSig context)
              MemberEncoding.names MemberEncoding.constraints)
          simpa [FCsub.Runtime.Subst.comp, FCsub.Runtime.Subst.ofRename,
            FCsub.Runtime.Subst.id, RuntimeEmbedding.contextMap,
            DotFC.Explicit.Ctx.ofSource, DotFC.Explicit.Ctx.extendTerm,
            Layout.termVar, Layout.extendRename] using point.symm)
  simpa [RuntimeEmbedding.embed] using embedded.symm

/-- The derivation-directed source erasure is exactly the structural embedding
of the source program's own runtime erasure. -/
theorem sourceRuntime_eq_embed {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    (derivation : DotFC.Source.HasTy context term type) :
    sourceRuntime derivation = RuntimeEmbedding.embed context term.erase := by
  induction derivation with
  | var binding => rfl
  | @lam source context domain body codomain domainWf bodyTyping induction =>
      cases domain with
      | top =>
          simpa [sourceRuntime, RuntimeEmbedding.embed,
            RuntimeEmbedding.embedWith] using
            congrArg FCsub.Runtime.Tm.lam induction
      | bot =>
          simpa [sourceRuntime, RuntimeEmbedding.embed,
            RuntimeEmbedding.embedWith] using
            congrArg FCsub.Runtime.Tm.lam induction
      | all nested result =>
          simpa [sourceRuntime, RuntimeEmbedding.embed,
            RuntimeEmbedding.embedWith] using
            congrArg FCsub.Runtime.Tm.lam induction
      | sel path label =>
          simpa [sourceRuntime, RuntimeEmbedding.embed,
            RuntimeEmbedding.embedWith] using
            congrArg FCsub.Runtime.Tm.lam induction
      | member label lower upper =>
          simp only [sourceRuntime, DotFC.Source.Tm.erase,
            RuntimeEmbedding.embed, RuntimeEmbedding.embedWith]
          rw [induction]
          exact congrArg FCsub.Runtime.Tm.lam
            (sourceRuntime_member_context context label lower upper body.erase)
  | obj witnessWf => rfl
  | app functionTyping argumentTyping resultWf functionInduction
      argumentInduction =>
      simp only [sourceRuntime, DotFC.Source.Tm.erase,
        RuntimeEmbedding.embed, RuntimeEmbedding.embedWith]
      rw [sourceRuntime_variable functionTyping]
      rfl
  | @let' source context rhs body bound result rhsTyping bodyTyping resultWf
      rhsInduction bodyInduction =>
      cases bound with
      | top =>
          simp only [sourceRuntime, DotFC.Source.Tm.erase,
            RuntimeEmbedding.embed, RuntimeEmbedding.embedWith]
          rw [rhsInduction, bodyInduction]
          simp [RuntimeEmbedding.embed] <;> rfl
      | bot =>
          simp only [sourceRuntime, DotFC.Source.Tm.erase,
            RuntimeEmbedding.embed, RuntimeEmbedding.embedWith]
          rw [rhsInduction, bodyInduction]
          simp [RuntimeEmbedding.embed] <;> rfl
      | all domain codomain =>
          simp only [sourceRuntime, DotFC.Source.Tm.erase,
            RuntimeEmbedding.embed, RuntimeEmbedding.embedWith]
          rw [rhsInduction, bodyInduction]
          simp [RuntimeEmbedding.embed] <;> rfl
      | sel path label =>
          simp only [sourceRuntime, DotFC.Source.Tm.erase,
            RuntimeEmbedding.embed, RuntimeEmbedding.embedWith]
          rw [rhsInduction, bodyInduction]
          simp [RuntimeEmbedding.embed] <;> rfl
      | member label lower upper =>
          simp only [sourceRuntime, DotFC.Source.Tm.erase,
            RuntimeEmbedding.embed, RuntimeEmbedding.embedWith]
          rw [rhsInduction, bodyInduction]
          exact congrArg
            (FCsub.Runtime.Tm.let'
              (RuntimeEmbedding.embedWith
                (RuntimeEmbedding.contextMap context) rhs.erase))
            (sourceRuntime_member_context context label lower upper body.erase)
  | sub termTyping subtyping targetWf induction =>
      simpa [sourceRuntime] using induction

/-- Checked executable compilation also exposes exact source-step
correspondence, without requiring callers to unpack the checker result. -/
theorem BReady.sourceStep {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {derivation : DotFC.Source.HasTy context term type}
    (ready : BReady derivation)
    {reduct : DotFC.Source.Runtime.Tm source}
    (step : DotFC.Source.Runtime.Step term.erase reduct) :
    ∃ target : FCsub.Tm (TargetSig context),
      TermTranslates derivation target ∧
      FCsub.Runtime.Step target.erase
        (RuntimeEmbedding.embed context reduct) := by
  obtain ⟨_, _, target, _, _, compilation, _⟩ := ready
  refine ⟨target, compilation, ?_⟩
  rw [term_erasure derivation compilation, sourceRuntime_eq_embed]
  exact RuntimeEmbedding.step_embedWith
    (RuntimeEmbedding.contextMap context) step

/-- Checked executable compilation preserves every finite source execution. -/
theorem BReady.sourceSteps {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {derivation : DotFC.Source.HasTy context term type}
    (ready : BReady derivation)
    {reduct : DotFC.Source.Runtime.Tm source}
    (steps : DotFC.Source.Runtime.Steps term.erase reduct) :
    ∃ target : FCsub.Tm (TargetSig context),
      TermTranslates derivation target ∧
      FCsub.Runtime.Steps target.erase
        (RuntimeEmbedding.embed context reduct) := by
  obtain ⟨_, _, target, _, _, compilation, _⟩ := ready
  refine ⟨target, compilation, ?_⟩
  rw [term_erasure derivation compilation, sourceRuntime_eq_embed]
  exact RuntimeEmbedding.steps_embedWith
    (RuntimeEmbedding.contextMap context) steps

end DotToFCsub.Elaboration

namespace DotToFCsub.BridgeMetatheory

open DotToFCsub.Elaboration

/-- One source runtime step commutes exactly with compiled FCsub erasure. -/
theorem Compiled.sourceStep {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {derivation : DotFC.Source.HasTy context term type}
    (compiled : Compiled derivation)
    {reduct : DotFC.Source.Runtime.Tm source}
    (step : DotFC.Source.Runtime.Step term.erase reduct) :
    FCsub.Runtime.Step compiled.target.erase
      (RuntimeEmbedding.embed context reduct) := by
  rw [compiled.erasure, sourceRuntime_eq_embed]
  exact RuntimeEmbedding.step_embedWith
    (RuntimeEmbedding.contextMap context) step

/-- Source runtime multisteps commute exactly with compiled FCsub erasure. -/
theorem Compiled.sourceSteps {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {derivation : DotFC.Source.HasTy context term type}
    (compiled : Compiled derivation)
    {reduct : DotFC.Source.Runtime.Tm source}
    (steps : DotFC.Source.Runtime.Steps term.erase reduct) :
    FCsub.Runtime.Steps compiled.target.erase
      (RuntimeEmbedding.embed context reduct) := by
  rw [compiled.erasure, sourceRuntime_eq_embed]
  exact RuntimeEmbedding.steps_embedWith
    (RuntimeEmbedding.contextMap context) steps

end DotToFCsub.BridgeMetatheory
