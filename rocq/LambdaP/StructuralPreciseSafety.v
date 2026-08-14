From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Store Cont State Machine Progress
  StructuralMachineInvariant StructuralPreciseStore
  StructuralPreciseCanonical StructuralPreciseProgress
  StructuralPrecisePreservation.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** The two exact-store properties consumed by progress and preservation at
    one machine state. *)
Record Store_PreciseStructSafetyWorld {n : nat}
    (G : Ctx n) (s : Store n) : Prop := {
  store_precise_struct_safety_world_head :
    Store_StructPreciseSingletonHeadPushback G s;
  store_precise_struct_safety_world_function :
    Store_StructExactFunctionPushback G s
}.

(** Store-typing-indexed laws supplying those properties at every exact
    store. *)
Record Store_PreciseStructSafetyLaws : Prop := {
  store_precise_struct_safety_laws_head :
    forall {n : nat} {G : Ctx n} {s : Store n},
      Store_StructPreciseTy G s ->
      Store_StructPreciseSingletonHeadPushback G s;
  store_precise_struct_safety_laws_function :
    forall {n : nat} {G : Ctx n} {s : Store n},
      Store_StructPreciseTy G s ->
      Store_StructExactFunctionPushback G s
}.

Theorem Store_PreciseStructSafetyLaws_world {n : nat} {G : Ctx n}
    {s : Store n} (Hlaws : Store_PreciseStructSafetyLaws)
    (Hstore : Store_StructPreciseTy G s) :
    Store_PreciseStructSafetyWorld G s.
Proof.
  constructor.
  - exact (store_precise_struct_safety_laws_head Hlaws Hstore).
  - exact (store_precise_struct_safety_laws_function Hlaws Hstore).
Qed.

(** Preservation-carrying progress for one exact structural state. *)
Inductive State_PreciseStructSafetyOutcome {n : nat}
    (G : Ctx n) (source : State n) (T : Ty n) : Prop :=
| state_precise_struct_safety_outcome_final :
    State_IsFinal source ->
    State_PreciseStructSafetyOutcome G source T
| state_precise_struct_safety_outcome_step {m : nat}
    (target : State m) :
    State_Step source target ->
    PreciseStructPreserve G target T ->
    State_PreciseStructSafetyOutcome G source T.

Arguments state_precise_struct_safety_outcome_final {n G source T} _.
Arguments state_precise_struct_safety_outcome_step
  {n G source T m} target _ _.

Theorem State_PreciseStructSafetyOutcome_progress {n : nat}
    {G : Ctx n} {source : State n} {T : Ty n}
    (H : State_PreciseStructSafetyOutcome G source T) :
    State_Progress source.
Proof.
  destruct H.
  - exact (state_progress_final H).
  - exact (state_progress_step target H).
Qed.

(** Conditional one-step safety for a precisely typed state. *)
Theorem State_PreciseStructTy_one_step_safety {n : nat}
    {G : Ctx n} {source : State n} {T : Ty n}
    (Hworld : Store_PreciseStructSafetyWorld G (state_store source))
    (Ht : State_PreciseStructTy G source T) :
    State_PreciseStructSafetyOutcome G source T.
Proof.
  destruct source as [s K t].
  destruct (State_PreciseStructTy_progress
    (store_precise_struct_safety_world_head Hworld) Ht)
    as [Hfinal | m target Hstep].
  - exact (state_precise_struct_safety_outcome_final Hfinal).
  - eapply state_precise_struct_safety_outcome_step.
    + exact Hstep.
    + exact (State_Step_precise_preservation_of_exactPushback
        (store_precise_struct_safety_world_function Hworld) Hstep Ht).
Qed.

(** One-step safety discharged directly by store-indexed laws. *)
Theorem State_PreciseStructTy_one_step_safety_of_laws {n : nat}
    {G : Ctx n} {source : State n} {T : Ty n}
    (Hlaws : Store_PreciseStructSafetyLaws)
    (Ht : State_PreciseStructTy G source T) :
    State_PreciseStructSafetyOutcome G source T.
Proof.
  destruct Ht as [S0 Hstore Hcont Hterm].
  apply State_PreciseStructTy_one_step_safety.
  - exact (Store_PreciseStructSafetyLaws_world Hlaws Hstore).
  - eapply state_precise_struct_ty_ok; eassumption.
Qed.

(** Reflexive-transitive allocation growth, weakening the observed result
    type at every appended context entry. *)
Inductive State_PreciseStructExtension : forall {n m : nat},
    Ctx n -> Ty n -> Ctx m -> Ty m -> Prop :=
| state_precise_struct_extension_refl {n : nat}
    (G : Ctx n) (T : Ty n) :
    State_PreciseStructExtension G T G T
| state_precise_struct_extension_snoc {n m : nat}
    {G : Ctx n} {T : Ty n} {D : Ctx m} {U : Ty m} :
    State_PreciseStructExtension G T D U ->
    forall S0 : Ty m,
      State_PreciseStructExtension G T
        (ctx_snoc D S0) (Ty_weaken U).

Arguments state_precise_struct_extension_refl {n} G T.
Arguments state_precise_struct_extension_snoc
  {n m G T D U} _ S0.

Theorem State_PreciseStructExtension_trans {n m l : nat}
    {G : Ctx n} {T : Ty n} {D : Ctx m} {U : Ty m}
    {X : Ctx l} {V : Ty l}
    (H1 : State_PreciseStructExtension G T D U)
    (H2 : State_PreciseStructExtension D U X V) :
    State_PreciseStructExtension G T X V.
Proof.
  induction H2.
  - exact H1.
  - apply state_precise_struct_extension_snoc.
    exact (IHState_PreciseStructExtension H1).
Qed.

(** Expose the target context, target type, and one-step extension witness
    carried by precise preservation. *)
Theorem PreciseStructPreserve_to_extension {n m : nat}
    {G : Ctx n} {target : State m} {T : Ty n}
    (H : PreciseStructPreserve G target T) :
    exists (D : Ctx m) (U : Ty m),
      State_PreciseStructExtension G T D U /\
      State_PreciseStructTy D target U.
Proof.
  destruct H.
  - exists G, T. split.
    + apply state_precise_struct_extension_refl.
    + exact H.
  - exists (ctx_snoc G P), (Ty_weaken T). split.
    + apply state_precise_struct_extension_snoc.
      apply state_precise_struct_extension_refl.
    + exact H.
Qed.

(** Reflexive-transitive machine execution across possibly different
    intrinsic scope indices. *)
Inductive State_PreciseSteps : forall {n m : nat},
    State n -> State m -> Prop :=
| state_precise_steps_refl {n : nat} (source : State n) :
    State_PreciseSteps source source
| state_precise_steps_tail {n j m : nat}
    (source : State n) (middle : State j) (target : State m) :
    State_Step source middle ->
    State_PreciseSteps middle target ->
    State_PreciseSteps source target.

Arguments state_precise_steps_refl {n} source.
Arguments state_precise_steps_tail {n j m} source middle target _ _.

(** Finite executions compose. *)
Theorem State_PreciseSteps_trans {n j m : nat}
    {source : State n} {middle : State j} {target : State m}
    (H1 : State_PreciseSteps source middle)
    (H2 : State_PreciseSteps middle target) :
    State_PreciseSteps source target.
Proof.
  induction H1.
  - exact H2.
  - eapply state_precise_steps_tail.
    + exact H.
    + exact (IHState_PreciseSteps H2).
Qed.

(** Finite execution preserves exact structural typing with an explicit
    context-extension witness. *)
Theorem State_PreciseSteps_preservation {n m : nat}
    {G : Ctx n} {source : State n} {target : State m} {T : Ty n}
    (Hsteps : State_PreciseSteps source target)
    (Ht : State_PreciseStructTy G source T)
    (Hworld : forall {j : nat} {D : Ctx j} {u : State j} {U : Ty j},
      State_PreciseSteps source u ->
      State_PreciseStructTy D u U ->
      Store_PreciseStructSafetyWorld D (state_store u)) :
    exists (D : Ctx m) (U : Ty m),
      State_PreciseStructExtension G T D U /\
      State_PreciseStructTy D target U.
Proof.
  induction Hsteps in G, T, Ht, Hworld |- *.
  - exists G, T. split.
    + apply state_precise_struct_extension_refl.
    + exact Ht.
  - pose proof (Hworld n G source T
      (state_precise_steps_refl source) Ht) as Hw.
    pose proof (State_Step_precise_preservation_of_exactPushback
      (store_precise_struct_safety_world_function Hw) H Ht) as Hpreserve.
    destruct (PreciseStructPreserve_to_extension Hpreserve)
      as (D & U & Hext & Hmiddle).
    assert (Hworld' : forall {l : nat} {X : Ctx l}
        {u : State l} {V : Ty l},
      State_PreciseSteps middle u ->
      State_PreciseStructTy X u V ->
      Store_PreciseStructSafetyWorld X (state_store u)).
    { intros l X u V Hreach Htyped.
      exact (Hworld l X u V
        (state_precise_steps_tail source middle u H Hreach) Htyped). }
    destruct (IHHsteps D U Hmiddle Hworld')
      as (X & V & Hext' & Htarget).
    exists X, V. split.
    + exact (State_PreciseStructExtension_trans Hext Hext').
    + exact Htarget.
Qed.

(** Every finite-run endpoint is precisely typed and final or can take a
    preservation-carrying step. *)
Theorem State_PreciseSteps_safety {n m : nat}
    {G : Ctx n} {source : State n} {target : State m} {T : Ty n}
    (Hsteps : State_PreciseSteps source target)
    (Ht : State_PreciseStructTy G source T)
    (Hworld : forall {j : nat} {D : Ctx j} {u : State j} {U : Ty j},
      State_PreciseSteps source u ->
      State_PreciseStructTy D u U ->
      Store_PreciseStructSafetyWorld D (state_store u)) :
    exists (D : Ctx m) (U : Ty m),
      State_PreciseStructExtension G T D U /\
      State_PreciseStructTy D target U /\
      State_PreciseStructSafetyOutcome D target U.
Proof.
  destruct (State_PreciseSteps_preservation Hsteps Ht Hworld)
    as (D & U & Hext & Htarget).
  pose proof (Hworld m D target U Hsteps Htarget) as Hw.
  exists D, U. repeat split.
  - exact Hext.
  - exact Htarget.
  - exact (State_PreciseStructTy_one_step_safety Hw Htarget).
Qed.

(** Explicit finite-run non-stuckness. *)
Theorem State_PreciseSteps_nonstuck {n m : nat}
    {G : Ctx n} {source : State n} {target : State m} {T : Ty n}
    (Hsteps : State_PreciseSteps source target)
    (Ht : State_PreciseStructTy G source T)
    (Hworld : forall {j : nat} {D : Ctx j} {u : State j} {U : Ty j},
      State_PreciseSteps source u ->
      State_PreciseStructTy D u U ->
      Store_PreciseStructSafetyWorld D (state_store u)) :
    State_Progress target.
Proof.
  destruct (State_PreciseSteps_safety Hsteps Ht Hworld)
    as (D & U & Hext & Htarget & Houtcome).
  exact (State_PreciseStructSafetyOutcome_progress Houtcome).
Qed.

(** Finite-run preservation from exact-store-indexed laws. *)
Theorem State_PreciseSteps_preservation_of_laws {n m : nat}
    {G : Ctx n} {source : State n} {target : State m} {T : Ty n}
    (Hlaws : Store_PreciseStructSafetyLaws)
    (Hsteps : State_PreciseSteps source target)
    (Ht : State_PreciseStructTy G source T) :
    exists (D : Ctx m) (U : Ty m),
      State_PreciseStructExtension G T D U /\
      State_PreciseStructTy D target U.
Proof.
  apply (State_PreciseSteps_preservation Hsteps Ht).
  intros j D u U Hreach Htyped.
  destruct Htyped as [S0 Hstore Hcont Hterm].
  exact (Store_PreciseStructSafetyLaws_world Hlaws Hstore).
Qed.

(** Complete finite-run exact safety from the realization-shaped laws. *)
Theorem State_PreciseSteps_safety_of_laws {n m : nat}
    {G : Ctx n} {source : State n} {target : State m} {T : Ty n}
    (Hlaws : Store_PreciseStructSafetyLaws)
    (Hsteps : State_PreciseSteps source target)
    (Ht : State_PreciseStructTy G source T) :
    exists (D : Ctx m) (U : Ty m),
      State_PreciseStructExtension G T D U /\
      State_PreciseStructTy D target U /\
      State_PreciseStructSafetyOutcome D target U.
Proof.
  apply (State_PreciseSteps_safety Hsteps Ht).
  intros j D u U Hreach Htyped.
  destruct Htyped as [S0 Hstore Hcont Hterm].
  exact (Store_PreciseStructSafetyLaws_world Hlaws Hstore).
Qed.

(** Finite-run non-stuckness from the unconditional store laws. *)
Theorem State_PreciseSteps_nonstuck_of_laws {n m : nat}
    {G : Ctx n} {source : State n} {target : State m} {T : Ty n}
    (Hlaws : Store_PreciseStructSafetyLaws)
    (Hsteps : State_PreciseSteps source target)
    (Ht : State_PreciseStructTy G source T) :
    State_Progress target.
Proof.
  apply (State_PreciseSteps_nonstuck Hsteps Ht).
  intros j D u U Hreach Htyped.
  destruct Htyped as [S0 Hstore Hcont Hterm].
  exact (Store_PreciseStructSafetyLaws_world Hlaws Hstore).
Qed.

Print Assumptions Store_PreciseStructSafetyLaws_world.
Print Assumptions State_PreciseStructSafetyOutcome_progress.
Print Assumptions State_PreciseStructTy_one_step_safety.
Print Assumptions State_PreciseStructTy_one_step_safety_of_laws.
Print Assumptions State_PreciseStructExtension_trans.
Print Assumptions PreciseStructPreserve_to_extension.
Print Assumptions State_PreciseSteps_trans.
Print Assumptions State_PreciseSteps_preservation.
Print Assumptions State_PreciseSteps_safety.
Print Assumptions State_PreciseSteps_nonstuck.
Print Assumptions State_PreciseSteps_preservation_of_laws.
Print Assumptions State_PreciseSteps_safety_of_laws.
Print Assumptions State_PreciseSteps_nonstuck_of_laws.
