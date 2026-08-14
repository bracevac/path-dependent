From PathDependent.LambdaP Require Import
  FinFun Syntax Context Store Cont State Machine PathReduction
  RuntimeConversion ScopedRuntimeEq StructuralRuntimeTyping
  StructuralTermTyping StructuralRuntimeLemmas StructuralMachineInvariant.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** First-order observations used to invert recursive term constructors
    without dependent equality principles. *)
Definition tm_abs_domain_payload {n : nat} (t : Tm n) : option (Ty n) :=
  match t with
  | tm_abs A _ => Some A
  | _ => None
  end.

Definition tm_abs_body_payload {n : nat} (t : Tm n) : option (Tm (S n)) :=
  match t with
  | tm_abs _ body => Some body
  | _ => None
  end.

Definition tm_app_function_payload {n : nat} (t : Tm n) : option (Path n) :=
  match t with
  | tm_app p _ => Some p
  | _ => None
  end.

Definition tm_app_argument_payload {n : nat} (t : Tm n) : option (Path n) :=
  match t with
  | tm_app _ q => Some q
  | _ => None
  end.

(** Structural checking of an abstraction exposes its introduction type
    and the full structural subtype suffix to the observed type. *)
Theorem Tm_StructCheck_abs_inversion_of_eq {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {v : Tm n} {T : Ty n}
    (H : Tm_StructCheck G R v T) :
    forall (A : Ty n) (body : Tm (S n)), v = tm_abs A body ->
      exists B,
        Tm_StructCheck (ctx_snoc G A) (Path_ScopedLift R) body B /\
        Tau_StructWf G R (tau_ty A) /\
        Tau_StructSub G R (tau_ty (ty_fun A B)) (tau_ty T).
Proof.
  induction H; intros domain body0 Heq; try discriminate Heq.
  - pose proof (f_equal tm_abs_domain_payload Heq) as Edomain.
    pose proof (f_equal tm_abs_body_payload Heq) as Ebody.
    cbn [tm_abs_domain_payload] in Edomain.
    cbn [tm_abs_body_payload] in Ebody.
    injection Edomain as Edomain'. injection Ebody as Ebody'.
    subst domain. subst body0. exists T. repeat split.
    + exact H.
    + exact H0.
    + apply tau_struct_sub_refl.
  - destruct (IHTm_StructCheck domain body0 Heq)
      as (B & Hbody & Hdomain & Hbase).
    exists B. repeat split.
    + exact Hbody.
    + exact Hdomain.
    + eapply tau_struct_sub_trans; eassumption.
Qed.

Theorem Tm_StructCheck_abs_inversion {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {A : Ty n}
    {body : Tm (S n)} {T : Ty n}
    (H : Tm_StructCheck G R (tm_abs A body) T) :
    exists B,
      Tm_StructCheck (ctx_snoc G A) (Path_ScopedLift R) body B /\
      Tau_StructWf G R (tau_ty A) /\
      Tau_StructSub G R (tau_ty (ty_fun A B)) (tau_ty T).
Proof.
  exact (@Tm_StructCheck_abs_inversion_of_eq n G R (tm_abs A body) T
    H A body eq_refl).
Qed.

(** Application inversion retains both introduction premises.  Its final
    component transports any checked reduct through trailing subsumption. *)
Theorem Tm_StructCheck_app_inversion_of_eq {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {u : Tm n} {T : Ty n}
    (H : Tm_StructCheck G R u T) :
    forall (p q : Path n), u = tm_app p q ->
      exists (S0 : Ty n) (U : Ty (S n)),
        Tm_StructCheck G R (tm_path p) (ty_fun S0 U) /\
        Tm_StructCheck G R (tm_path q) S0 /\
        (forall t : Tm n,
          Tm_StructCheck G R t (Ty_open U q) ->
          Tm_StructCheck G R t T).
Proof.
  induction H; intros function argument Heq; try discriminate Heq.
  - pose proof (f_equal tm_app_function_payload Heq) as Efunction.
    pose proof (f_equal tm_app_argument_payload Heq) as Eargument.
    cbn [tm_app_function_payload] in Efunction.
    cbn [tm_app_argument_payload] in Eargument.
    injection Efunction as Efunction'. injection Eargument as Eargument'.
    subst function. subst argument.
    exists S0, T. repeat split.
    + exact H.
    + exact H0.
    + intros result Hresult. exact Hresult.
  - destruct (IHTm_StructCheck function argument Heq)
      as (S1 & U & Hfunction & Hargument & post).
    exists S1, U. repeat split.
    + exact Hfunction.
    + exact Hargument.
    + intros result Hresult. eapply tm_struct_check_sub.
      * exact (post result Hresult).
      * exact H0.
      * exact H1.
Qed.

Theorem Tm_StructCheck_app_inversion {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {p q : Path n} {T : Ty n}
    (H : Tm_StructCheck G R (tm_app p q) T) :
    exists (S0 : Ty n) (U : Ty (S n)),
      Tm_StructCheck G R (tm_path p) (ty_fun S0 U) /\
      Tm_StructCheck G R (tm_path q) S0 /\
      (forall t : Tm n,
        Tm_StructCheck G R t (Ty_open U q) ->
        Tm_StructCheck G R t T).
Proof.
  exact (@Tm_StructCheck_app_inversion_of_eq n G R (tm_app p q) T
    H p q eq_refl).
Qed.

(** Store checking is available in the scope where a cell is looked up;
    older derivations are weakened with the runtime relation. *)
Theorem Store_StructTy_lookup_checked {n : nat} {G : Ctx n}
    {s : Store n} (H : Store_StructTy G s) (x : Fin.t n) :
    exists (v : Tm n) (T : Ty n),
      Store_Binds s x v /\ Ctx_Binds G x T /\
      Tm_StructCheck G (Path_RuntimeEq s) v T.
Proof.
  induction H.
  - exact (Fin.elim0 x).
  - refine (@Fin.cases' n x
      (fun x => exists (u : Tm (S n)) (U : Ty (S n)),
        Store_Binds (store_val s v Hv) x u /\
        Ctx_Binds (ctx_snoc G T) x U /\
        Tm_StructCheck (ctx_snoc G T)
          (Path_RuntimeEq (store_val s v Hv)) u U) _ _).
    + exists (Tm_weaken v), (Ty_weaken T). repeat split.
      * apply store_binds_here.
      * apply binds_here.
      * exact (Tm_StructCheck_weaken_runtime H0 T (v := v) Hv).
    + intro y. destruct (IHStore_StructTy y)
        as (u & U & Hu & HU & Hcheck).
      exists (Tm_weaken u), (Ty_weaken U). repeat split.
      * now apply store_binds_there.
      * now apply binds_there.
      * exact (Tm_StructCheck_weaken_runtime Hcheck T (v := v) Hv).
Qed.

(** Concrete store binding inversion for a structurally checked store. *)
Theorem Store_StructTy_of_store_binds_checked {n : nat} {G : Ctx n}
    {s : Store n} {x : Fin.t n} {v : Tm n}
    (H : Store_StructTy G s) (Hb : Store_Binds s x v) :
    exists T, Ctx_Binds G x T /\
      Tm_StructCheck G (Path_RuntimeEq s) v T.
Proof.
  destruct (Store_StructTy_lookup_checked H x)
    as (u & T & Hu & HT & Hcheck).
  pose proof (Store_Binds_unique Hu Hb) as E. subst u.
  now exists T.
Qed.

(** The minimal local relation between a resolving call-site signature and
    the syntax-directed signature of its stored abstraction. *)
Definition Store_StructAppCompatibility {n : nat}
    (G : Ctx n) (s : Store n) : Prop :=
  forall (p q : Path n) (x y : Fin.t n)
    (S0 A X : Ty n) (U B : Ty (S n)) (body : Tm (S n)),
    Store_StructTy G s ->
    Path_reduce p s x ->
    Path_reduce q s y ->
    Store_Binds s x (tm_abs A body) ->
    Ctx_Binds G x X ->
    Tau_StructSub G (Path_RuntimeEq s)
      (tau_ty (ty_fun A B)) (tau_ty X) ->
    Tm_StructCheck G (Path_RuntimeEq s)
      (tm_path p) (ty_fun S0 U) ->
    Tm_StructCheck G (Path_RuntimeEq s) (tm_path q) S0 ->
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty S0) (tau_ty A) /\
      (forall t : Tm n,
        Tm_StructCheck G (Path_RuntimeEq s) t
          (Ty_rename B (FinFun.openAt y)) ->
        Tm_StructCheck G (Path_RuntimeEq s) t (Ty_open U q)).

(** Lookup recovers the closure body.  Domain compatibility and checked
    variable opening then type the concrete reduct. *)
Theorem Store_StructTy_open_application {n : nat} {G : Ctx n}
    {s : Store n} {p q : Path n} {x y : Fin.t n}
    {S0 : Ty n} {U : Ty (S n)} {A : Ty n} {body : Tm (S n)}
    (Hstore : Store_StructTy G s)
    (Hcompat : Store_StructAppCompatibility G s)
    (Hp : Path_reduce p s x) (Hq : Path_reduce q s y)
    (Hbind : Store_Binds s x (tm_abs A body))
    (Hfunction : Tm_StructCheck G (Path_RuntimeEq s)
      (tm_path p) (ty_fun S0 U))
    (Hargument : Tm_StructCheck G (Path_RuntimeEq s)
      (tm_path q) S0) :
    Tm_StructCheck G (Path_RuntimeEq s)
      (Tm_open body y) (Ty_open U q).
Proof.
  destruct (Store_StructTy_of_store_binds_checked Hstore Hbind)
    as (X & Hcontext & Hpublic).
  destruct (Tm_StructCheck_abs_inversion Hpublic)
    as (B & Hbody & Hdomain_wf & Hactual_public).
  destruct (Hcompat p q x y S0 A X U B body Hstore Hp Hq Hbind
    Hcontext Hactual_public Hfunction Hargument) as [Hdomain Hresult].
  pose proof (Tm_StructCheck_reduce_path Hq Hargument) as Hargument_at_S.
  assert (Hargument_at_A : Tm_StructCheck G (Path_RuntimeEq s)
      (tm_path (path_var y)) A).
  { eapply tm_struct_check_sub; eassumption. }
  pose proof (Tm_StructCheck_open_var_of_path_term Hbody
    (Path_RuntimeEq_isEquivCongr s) Hargument_at_A) as Hopened.
  exact (Hresult (Tm_open body y) Hopened).
Qed.

(** Conditional preservation of application reduction. *)
Theorem StructPreserve_app {n : nat} {G : Ctx n} {s : Store n}
    {K : Tm_Cont n} {p q : Path n} {x y : Fin.t n}
    {A : Ty n} {body : Tm (S n)} {T : Ty n}
    (Hcompat : Store_StructAppCompatibility G s)
    (Hp : Path_reduce p s x) (Hq : Path_reduce q s y)
    (Hbind : Store_Binds s x (tm_abs A body))
    (H : State_StructTy G (mk_state s K (tm_app p q)) T) :
    StructPreserve G (mk_state s K (Tm_open body y)) T.
Proof.
  destruct H as [Input Hstore Hcont Happ].
  destruct (Tm_StructCheck_app_inversion Happ)
    as (S0 & U & Hfunction & Hargument & post).
  pose proof (Store_StructTy_open_application Hstore Hcompat Hp Hq Hbind
    Hfunction Hargument) as Hopened.
  apply struct_preserve_same. eapply state_struct_ty_ok.
  - exact Hstore.
  - exact Hcont.
  - exact (post (Tm_open body y) Hopened).
Qed.

(** Package the application case of machine-step preservation. *)
Local Lemma State_Step_struct_app_preservation_general
    {n m : nat} {source : State n} {target : State m}
    (step : State_Step source target) :
    forall (G : Ctx n) (s : Store n) (K : Tm_Cont n)
      (p q : Path n) (T : Ty n),
      source = mk_state s K (tm_app p q) ->
      Store_StructAppCompatibility G s ->
      State_StructTy G (mk_state s K (tm_app p q)) T ->
      StructPreserve G target T.
Proof.
  destruct step as
    [scope op_store op_cont op_p op_q x y A body Hp Hq Hbind
    |scope op_store op_cont path x Hreduce Hnotvar
    |scope op_store op_cont bound body
    |scope op_store op_cont body x
    |scope op_store op_cont body value Hvalue
    |scope op_store op_cont term annotation];
    intros G call_store call_cont call_p call_q result_type
      Esource Hcompat Hstate.
  - pose proof (f_equal state_store Esource) as Estore.
    pose proof (f_equal state_cont Esource) as Econt.
    pose proof (f_equal
      (fun st => tm_app_function_payload (state_term st)) Esource)
      as Efunction.
    pose proof (f_equal
      (fun st => tm_app_argument_payload (state_term st)) Esource)
      as Eargument.
    cbn in Estore, Econt, Efunction, Eargument.
    injection Efunction as Efunction'.
    injection Eargument as Eargument'.
    rewrite <- Estore in Hcompat, Hstate.
    rewrite <- Econt in Hstate.
    rewrite <- Efunction' in Hstate.
    rewrite <- Eargument' in Hstate.
    exact (StructPreserve_app Hcompat Hp Hq Hbind Hstate).
  - pose proof (f_equal state_term Esource) as Eterm.
    discriminate Eterm.
  - pose proof (f_equal state_term Esource) as Eterm.
    discriminate Eterm.
  - pose proof (f_equal state_term Esource) as Eterm.
    discriminate Eterm.
  - pose proof (f_equal state_term Esource) as Eterm.
    cbn in Eterm. destruct Hvalue; discriminate Eterm.
  - pose proof (f_equal state_term Esource) as Eterm.
    discriminate Eterm.
Qed.

Theorem State_Step_struct_app_preservation {n : nat} {G : Ctx n}
    {s : Store n} {K : Tm_Cont n} {p q : Path n}
    {target : State n} {T : Ty n}
    (Hcompat : Store_StructAppCompatibility G s)
    (step : State_Step (mk_state s K (tm_app p q)) target)
    (H : State_StructTy G (mk_state s K (tm_app p q)) T) :
    StructPreserve G target T.
Proof.
  exact (@State_Step_struct_app_preservation_general n n
    (mk_state s K (tm_app p q)) target step
    G s K p q T eq_refl Hcompat H).
Qed.

Print Assumptions Tm_StructCheck_abs_inversion.
Print Assumptions Tm_StructCheck_app_inversion.
Print Assumptions Store_StructTy_lookup_checked.
Print Assumptions Store_StructTy_open_application.
Print Assumptions StructPreserve_app.
Print Assumptions State_Step_struct_app_preservation.
