import FCsub.Dynamics
import FCsub.Erasure
import FCsub.RuntimeMetatheory
import FCsub.RuntimeSubstitution

/-!
# Erasure metatheory

Erasure preserves values and commutes with every operational substitution.
The substitution theorem is deliberately stated for the full four-sort
annotated substitution, even though its runtime projection retains only the
ordinary term component.
-/

namespace FCsub

namespace Tm

/-- Erasure is natural in a heterogeneous renaming. -/
@[simp]
theorem erase_rename {source target : Sig} (term : Tm source)
    (rho : Rename source target) :
    (term.rename rho).erase = term.erase.rename rho := by
  induction term generalizing target with
  | unit => rfl
  | var index => rfl
  | lam domain body induction =>
      simp only [Tm.rename, erase, Runtime.Tm.rename, induction]
  | app function argument functionInduction argumentInduction =>
      simp only [Tm.rename, erase, Runtime.Tm.rename,
        functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp only [Tm.rename, erase, Runtime.Tm.rename,
        rhsInduction, bodyInduction]
  | cast term evidence induction =>
      simp only [Tm.rename, erase, induction]
  | pack telescope payloadType witnesses evidence payload induction =>
      simp only [Tm.rename, erase, induction]
  | «open» telescope payloadType scrutinee body scrutineeInduction
      bodyInduction =>
      simp only [Tm.rename, erase, Runtime.Tm.rename,
        scrutineeInduction, bodyInduction, Runtime.Tm.rename_subst,
        Runtime.Tm.subst_rename,
        Runtime.Subst.preRename_liftPayload_dropPayload]
  | slam telescope body induction =>
      simp only [Tm.rename, erase, induction, Runtime.Tm.rename_subst,
        Runtime.Tm.subst_rename,
        Runtime.Subst.preRename_liftStatic_dropStatic]
  | sapp telescope function witnesses evidence induction =>
      simp only [Tm.rename, erase, induction]
  | newtype witness body induction =>
      simp only [Tm.rename, erase, induction, Runtime.Tm.rename_subst,
        Runtime.Tm.subst_rename,
        Runtime.Subst.preRename_liftNewtype_dropNewtype]

@[simp]
theorem erase_weaken {scope : Sig} {kind : BinderKind} (term : Tm scope) :
    (term.weaken (kind := kind)).erase = term.erase.weaken := by
  exact erase_rename term Rename.succ

end Tm

namespace Subst

/-- Runtime projection of a four-sort annotated substitution. -/
def eraseRuntime {source target : Sig} (substitution : Subst source target) :
    Runtime.Subst source target where
  var := fun index => (substitution.termVar index).erase

@[simp]
theorem eraseRuntime_id {scope : Sig} :
    eraseRuntime (Subst.id (scope := scope)) = Runtime.Subst.id := by
  apply Runtime.Subst.ext
  intro index
  rfl

@[simp]
theorem eraseRuntime_ofRename {source target : Sig}
    (rho : Rename source target) :
    eraseRuntime (Subst.ofRename rho) = Runtime.Subst.ofRename rho := by
  apply Runtime.Subst.ext
  intro index
  rfl

@[simp]
theorem eraseRuntime_lift {source target : Sig}
    (substitution : Subst source target) (kind : BinderKind) :
    eraseRuntime (substitution.lift kind) =
      (eraseRuntime substitution).liftKind kind := by
  apply Runtime.Subst.ext
  intro index
  cases kind with
  | term =>
      cases index with
      | here => rfl
      | there index => exact Tm.erase_weaken (substitution.termVar index)
  | type =>
      cases index with
      | there index => exact Tm.erase_weaken (substitution.termVar index)
  | evidence relation =>
      cases relation <;> cases index with
      | there index => exact Tm.erase_weaken (substitution.termVar index)

@[simp]
theorem eraseRuntime_liftTerm {source target : Sig}
    (substitution : Subst source target) :
    eraseRuntime substitution.liftTerm = (eraseRuntime substitution).lift := by
  simpa [Subst.lift, Runtime.Subst.liftKind] using
    eraseRuntime_lift substitution .term

@[simp]
theorem eraseRuntime_liftN {source target : Sig}
    (substitution : Subst source target) (kind : BinderKind)
    (count : Nat) :
    eraseRuntime (substitution.liftN kind count) =
      (eraseRuntime substitution).liftN kind count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      change eraseRuntime ((substitution.liftN kind count).lift kind) =
        ((eraseRuntime substitution).liftN kind count).liftKind kind
      calc
        _ = (eraseRuntime (substitution.liftN kind count)).liftKind kind :=
          eraseRuntime_lift _ _
        _ = _ := congrArg (fun current => current.liftKind kind) induction

@[simp]
theorem eraseRuntime_liftTypes {source target : Sig}
    (substitution : Subst source target) (names : Nat) :
    eraseRuntime (substitution.liftTypes names) =
      (eraseRuntime substitution).liftTypes names := by
  exact eraseRuntime_liftN substitution .type names

@[simp]
theorem eraseRuntime_liftStatic {source target : Sig}
    (substitution : Subst source target) (names constraints : Nat) :
    eraseRuntime (substitution.liftStatic names constraints) =
      (eraseRuntime substitution).liftStatic names constraints := by
  simp [Subst.liftStatic, Runtime.Subst.liftStatic]

@[simp]
theorem eraseRuntime_liftPayload {source target : Sig}
    (substitution : Subst source target) (names constraints : Nat) :
    eraseRuntime (substitution.liftPayload names constraints) =
      (eraseRuntime substitution).liftPayload names constraints := by
  simp [Subst.liftPayload, Runtime.Subst.liftPayload]

@[simp]
theorem eraseRuntime_liftNewtype {source target : Sig}
    (substitution : Subst source target) :
    eraseRuntime substitution.liftNewtype =
      (eraseRuntime substitution).liftNewtype := by
  change eraseRuntime ((substitution.lift .type).lift
      (.evidence .equality)) =
    ((eraseRuntime substitution).liftKind .type).liftKind
      (.evidence .equality)
  rw [eraseRuntime_lift, eraseRuntime_lift]

/-- Static arguments affect only erased fields.  On runtime variables their
only effect is to remove the complete static suffix. -/
@[simp]
theorem eraseRuntime_fromStaticArgs {source target : Sig}
    (base : Subst source target) {names constraints : Nat}
    (types : TypeArgs target names) (evidence : LeArgs target constraints) :
    eraseRuntime (Subst.fromStaticArgs base types evidence) =
      (Runtime.Subst.dropStatic (scope := source) names constraints).comp
        (eraseRuntime base) := by
  induction constraints with
  | zero =>
      cases evidence
      induction names with
      | zero =>
          cases types
          simp [Subst.fromStaticArgs, Subst.fromInclusionArgs,
            Subst.fromTypeArgs, Runtime.Subst.dropStatic,
            Runtime.Subst.dropTypes]
      | succ names induction =>
          cases types with
          | snoc initial replacement =>
              apply Runtime.Subst.ext
              intro index
              cases index with
              | there index =>
                  have point := congrArg (fun current => current.var index)
                    (induction initial)
                  simpa [Subst.fromStaticArgs, Subst.fromInclusionArgs,
                    Subst.fromTypeArgs, Subst.instantiateType,
                    eraseRuntime, Runtime.Subst.dropStatic,
                    Runtime.Subst.dropTypes, Runtime.Subst.comp] using point
  | succ constraints induction =>
      cases evidence with
      | snoc initial replacement =>
          apply Runtime.Subst.ext
          intro index
          cases index with
          | there index =>
              have point := congrArg (fun current => current.var index)
                (induction initial)
              simpa [Subst.fromStaticArgs, Subst.fromInclusionArgs,
                Subst.instantiateInclusion, eraseRuntime,
                Runtime.Subst.dropStatic, Runtime.Subst.comp] using point

@[simp]
theorem eraseRuntime_instantiateTerm {scope : Sig}
    (replacement : Tm scope) :
    eraseRuntime (Subst.id.instantiateTerm replacement) =
      Runtime.Subst.openAt replacement.erase := by
  apply Runtime.Subst.ext
  intro index
  cases index <;> rfl

@[simp]
theorem eraseRuntime_instantiateStatic {scope : Sig}
    {names constraints : Nat} (types : TypeArgs scope names)
    (evidence : LeArgs scope constraints) :
    eraseRuntime (Subst.fromStaticArgs Subst.id types evidence) =
      Runtime.Subst.dropStatic names constraints := by
  rw [eraseRuntime_fromStaticArgs, eraseRuntime_id,
    Runtime.Subst.comp_id]

@[simp]
theorem eraseRuntime_instantiatePayload {scope : Sig}
    {names constraints : Nat} (types : TypeArgs scope names)
    (evidence : LeArgs scope constraints) (payload : Tm scope) :
    eraseRuntime
        ((Subst.fromStaticArgs Subst.id types evidence).instantiateTerm
          payload) =
      (Runtime.Subst.dropPayload names constraints).comp
        (Runtime.Subst.openAt payload.erase) := by
  apply Runtime.Subst.ext
  intro index
  cases index with
  | here => rfl
  | there index =>
      have staticPoint := congrArg (fun current => current.var index)
        (eraseRuntime_instantiateStatic types evidence)
      change ((Subst.fromStaticArgs Subst.id types evidence).termVar
          index).erase =
        (Runtime.Subst.dropStatic names constraints).var index at staticPoint
      change ((Subst.fromStaticArgs Subst.id types evidence).termVar
          index).erase =
        ((Runtime.Subst.dropStatic names constraints).var index).weaken.subst
          (Runtime.Subst.openAt payload.erase)
      rw [staticPoint]
      simp only [Runtime.Tm.weaken, Runtime.Tm.rename_subst]
      have dropOpen : Runtime.Subst.preRename Rename.succ
          (Runtime.Subst.openAt payload.erase) = Runtime.Subst.id := by
        apply Runtime.Subst.ext
        intro inner
        rfl
      rw [dropOpen, Runtime.Tm.subst_id]

@[simp]
theorem eraseRuntime_instantiateNewtype {scope : Sig}
    (witness : Ty scope) :
    eraseRuntime
        ((Subst.id.instantiateType witness).instantiateEquality
          (.refl witness)) = Runtime.Subst.dropNewtype := by
  apply Runtime.Subst.ext
  intro index
  cases index with
  | there index => cases index <;> rfl

end Subst

namespace TelMor

/-- Telescope morphisms have no runtime term fields.  Reinterpreting a
target payload scope and then erasing the source payload scope is exactly
the direct target payload drop. -/
@[simp]
theorem eraseRuntime_payloadSubstitution_comp_dropPayload {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints)
    (payloadEvidence : LeCo
      (StaticScope scope sourceNames sourceConstraints)) :
    (morphism.payloadSubstitution payloadEvidence).eraseRuntime.comp
        (Runtime.Subst.dropPayload sourceNames sourceConstraints) =
      Runtime.Subst.dropPayload targetNames targetConstraints := by
  let openedMorphism :=
    morphism.rename (Rename.weakenStatic sourceNames sourceConstraints)
  let targetRealization :=
    openedMorphism.apply
      (TelMor.assumptions scope sourceNames sourceConstraints)
  let targetTypes := targetRealization.types.weaken (kind := .term)
  let targetEvidence := targetRealization.evidence.weaken (kind := .term)
  let ambient : Subst scope
      (PayloadScope scope sourceNames sourceConstraints) :=
    Subst.ofRename (Rename.weakenPayload sourceNames sourceConstraints)
  let staticSubstitution :=
    Subst.fromStaticArgs ambient targetTypes targetEvidence
  change (staticSubstitution.instantiateTerm
      (.cast (.var .here) payloadEvidence.weaken)).eraseRuntime.comp
        (Runtime.Subst.dropPayload sourceNames sourceConstraints) =
      Runtime.Subst.dropPayload targetNames targetConstraints
  apply Runtime.Subst.ext
  intro index
  cases index with
  | here => rfl
  | there index =>
      have staticPoint := congrArg (fun current => current.var index)
        (Subst.eraseRuntime_fromStaticArgs ambient targetTypes targetEvidence)
      change (staticSubstitution.termVar index).erase =
        ((Runtime.Subst.dropStatic targetNames targetConstraints).var
          index).subst ambient.eraseRuntime at staticPoint
      change (staticSubstitution.termVar index).erase.subst
          (Runtime.Subst.dropPayload sourceNames sourceConstraints) =
        ((Runtime.Subst.dropStatic targetNames targetConstraints).var
          index).weaken
      rw [staticPoint, Runtime.Tm.subst_comp]
      have ambientErasure : ambient.eraseRuntime =
          Runtime.Subst.ofRename
            (Rename.weakenPayload sourceNames sourceConstraints) := by
        exact Subst.eraseRuntime_ofRename _
      rw [ambientErasure,
        Runtime.Subst.ofRename_weakenPayload_comp_dropPayload]
      exact Runtime.Tm.subst_ofRename _ Rename.succ

end TelMor

namespace Tm

/-- Erasure commutes with the full annotated substitution action. -/
@[simp]
theorem erase_substitute {source target : Sig} (term : Tm source)
    (substitution : Subst source target) :
    (term.substitute substitution).erase =
      term.erase.subst substitution.eraseRuntime := by
  induction term generalizing target with
  | unit => rfl
  | var index => rfl
  | lam domain body induction =>
      simp only [Tm.substitute, erase, Runtime.Tm.subst,
        induction, Subst.eraseRuntime_liftTerm]
  | app function argument functionInduction argumentInduction =>
      simp only [Tm.substitute, erase, Runtime.Tm.subst,
        functionInduction, argumentInduction]
  | let' rhs body rhsInduction bodyInduction =>
      simp only [Tm.substitute, erase, Runtime.Tm.subst,
        rhsInduction, bodyInduction, Subst.eraseRuntime_liftTerm]
  | cast term evidence induction =>
      simp only [Tm.substitute, erase, induction]
  | pack telescope payloadType witnesses evidence payload induction =>
      simp only [Tm.substitute, erase, induction]
  | «open» telescope payloadType scrutinee body scrutineeInduction
      bodyInduction =>
      simp only [Tm.substitute, erase, Runtime.Tm.subst,
        scrutineeInduction, bodyInduction,
        Subst.eraseRuntime_liftPayload, Runtime.Tm.subst_comp,
        Runtime.Subst.liftPayload_comp_dropPayload]
  | slam telescope body induction =>
      simp only [Tm.substitute, erase, induction,
        Subst.eraseRuntime_liftStatic, Runtime.Tm.subst_comp,
        Runtime.Subst.liftStatic_comp_dropStatic]
  | sapp telescope function witnesses evidence induction =>
      simp only [Tm.substitute, erase, induction]
  | newtype witness body induction =>
      simp only [Tm.substitute, erase, induction,
        Subst.eraseRuntime_liftNewtype, Runtime.Tm.subst_comp,
        Runtime.Subst.liftNewtype_comp_dropNewtype]

/-! ## Operational instantiation corollaries -/

@[simp]
theorem erase_instantiateTerm {scope : Sig} (body : Tm (scope ▹ .term))
    (replacement : Tm scope) :
    (body.instantiateTerm replacement).erase =
      body.erase.open replacement.erase := by
  simp [Tm.instantiateTerm, Runtime.Tm.open]

@[simp]
theorem erase_instantiateStatic {scope : Sig} {names constraints : Nat}
    (body : Tm (StaticScope scope names constraints))
    (types : TypeArgs scope names) (evidence : LeArgs scope constraints) :
    (body.instantiateStatic types evidence).erase =
      body.erase.subst (Runtime.Subst.dropStatic names constraints) := by
  simp [Tm.instantiateStatic]

@[simp]
theorem erase_instantiatePayload {scope : Sig} {names constraints : Nat}
    (body : Tm (PayloadScope scope names constraints))
    (types : TypeArgs scope names) (evidence : LeArgs scope constraints)
    (payload : Tm scope) :
    (body.instantiatePayload types evidence payload).erase =
      (body.erase.subst
        (Runtime.Subst.dropPayload names constraints)).open payload.erase := by
  simp [Tm.instantiatePayload, Runtime.Tm.open, Runtime.Tm.subst_comp]

@[simp]
theorem erase_instantiateNewtype {scope : Sig}
    (body : Tm (NewtypeScope scope)) (witness : Ty scope) :
    (body.instantiateNewtype witness).erase =
      body.erase.subst Runtime.Subst.dropNewtype := by
  simp [Tm.instantiateNewtype]

end Tm

namespace Runtime.IsValue

/-- Runtime substitutions preserve the two runtime value forms. -/
theorem substitute {source target : Sig} {term : Runtime.Tm source}
    (value : Runtime.IsValue term) (substitution : Runtime.Subst source target) :
    Runtime.IsValue (term.subst substitution) := by
  cases value with
  | lam => exact .lam
  | unit => exact .unit

end Runtime.IsValue

namespace Tm.IsValue

/-- Every value admitted by the typing-layer value restriction erases to a
runtime value. -/
theorem erase {scope : Sig} {term : Tm scope} (value : Tm.IsValue term) :
    Runtime.IsValue term.erase := by
  induction value with
  | unit => exact .unit
  | lam => exact .lam
  | cast termValue induction => exact induction
  | pack payloadValue induction => exact induction
  | slam bodyValue induction =>
      exact induction.substitute (Runtime.Subst.dropStatic _ _)

end Tm.IsValue

namespace Tm.IsRuntimeValue

/-- Every operational annotated value erases to a runtime value. -/
theorem erase {scope : Sig} {term : Tm scope}
    (value : Tm.IsRuntimeValue term) : Runtime.IsValue term.erase := by
  induction value with
  | unit => exact .unit
  | lam => exact .lam
  | cast termValue inert induction => exact induction
  | pack payloadValue induction => exact induction
  | slam bodyValue =>
      exact bodyValue.erase.substitute (Runtime.Subst.dropStatic _ _)

end Tm.IsRuntimeValue

end FCsub
