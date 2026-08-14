From Equations Require Import Equations.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Renaming Store Cont State PathReduction Machine
  PreciseStore PathFunctionality TypingInversion Lookup PathPreservation
  PathProgress Progress Canonical.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Ltac contradict_pair_head :=
  lazymatch goal with
  | Hpath : Path_Ty ?G ?p (tau_ty (ty_pair ?First ?label ?member)),
    Hsub : Tau_Sub ?G (tau_ty (ty_single ?p))
      (tau_ty (ty_fun ?S ?T)) |- _ =>
      let Hbad := fresh "Hbad" in
      pose proof (Tau_Sub_mayHead Hsub
        (tau_may_head_single G p (ty_pair First label member)
          (head_pair label) Hpath
          (tau_may_head_pair G First label member))) as Hbad;
      inversion Hbad
  end.

Ltac contradict_nested_pair_head x :=
  lazymatch goal with
  | Hbind : Ctx_Binds ?G x (ty_pair ?First ?label ?member),
    Hpath : Path_Ty ?G ?p (tau_ty (ty_single (path_var x))),
    Hsub : Tau_Sub ?G (tau_ty (ty_single ?p))
      (tau_ty (ty_fun ?S ?T)) |- _ =>
      let Hx := fresh "Hx" in
      let Hxhead := fresh "Hxhead" in
      let Hphead := fresh "Hphead" in
      let Hbad := fresh "Hbad" in
      pose proof (path_ty_var G x (ty_pair First label member) Hbind) as Hx;
      pose proof (tau_may_head_single G (path_var x)
        (ty_pair First label member) (head_pair label) Hx
        (tau_may_head_pair G First label member)) as Hxhead;
      pose proof (tau_may_head_single G p (ty_single (path_var x))
        (head_pair label) Hpath Hxhead) as Hphead;
      pose proof (Tau_Sub_mayHead Hsub Hphead) as Hbad;
      inversion Hbad
  end.

Theorem Path_reduce_fun_value_precise
    {n : nat} {G : Ctx n} {s : Store n} {p : Path n} {x : Fin.t n}
    {S0 : Ty n} {T : Ty (S n)}
    (Hs : Store_PreciseTy G s)
    (Hr : Path_reduce p s x)
    (Ht : Tm_Ty G (tm_path p) (ty_fun S0 T)) :
    exists (A : Ty n) (body : Tm (S n)),
      Store_Binds s x (tm_abs A body).
Proof.
  destruct (@Tm_Ty_path_inversion n G (tm_path p) (ty_fun S0 T)
    Ht p eq_refl) as (U & Hp & Hsub & Hwf).
  destruct (Path_lookup_type_shape Hs (Path_reduce_toLookup Hr) Hp)
    as [Hbind | Heq].
  - destruct (Store_PreciseTy_of_ctx_binds Hs Hbind)
      as (v & Hv & Hprecise).
    dependent elimination Hprecise.
    + eexists _, _. exact Hv.
    + contradict_pair_head.
    + contradict_pair_head.
  - subst U.
    destruct (Ctx_Binds_exists G x) as [P HP].
    destruct (Store_PreciseTy_of_ctx_binds Hs HP)
      as (v & Hv & Hprecise).
    dependent elimination Hprecise.
    + eexists _, _. exact Hv.
    + contradict_nested_pair_head x.
    + contradict_nested_pair_head x.
Qed.

Theorem State_progress_precise
    {n : nat} {G : Ctx n} {s : Store n} {K : Tm_Cont n}
    {t : Tm n} {S0 R : Ty n}
    (Hs : Store_PreciseTy G s)
    (Hk : Tm_Cont_Ty G S0 K R)
    (Ht : Tm_Ty G t S0) :
    State_Progress (mk_state s K t).
Proof.
  destruct t as [n p | n A body | n k y a d | n p q | n u body | n u A].
  - destruct (@Tm_Ty_path_inversion n G (tm_path p) S0 Ht p eq_refl)
      as (U & Hp & Hsub & Hwf).
    destruct (Path_reduce_progress_precise Hs Hp) as [x Hr].
    destruct p as [x0 | p | p label].
    + exact (State_Progress_path_var (Store_PreciseTy_toTy Hs) x0 K).
    + apply (State_Progress_path Hr). intro Hvar. inversion Hvar.
    + apply (State_Progress_path Hr). intro Hvar. inversion Hvar.
  - exact (State_Progress_value (value_abs A body) s K).
  - exact (State_Progress_value (@value_pair n k y a d) s K).
  - destruct (Tm_Ty_app_inversion Ht) as (A & B & Hp & Hq).
    destruct (@Tm_Ty_path_inversion n G (tm_path p) (ty_fun A B)
      Hp p eq_refl) as (P & Hpp & Hpsub & Hpwf).
    destruct (@Tm_Ty_path_inversion n G (tm_path q) A
      Hq q eq_refl) as (Q & Hpq & Hqsub & Hqwf).
    destruct (Path_reduce_progress_precise Hs Hpp) as [x Hrp].
    destruct (Path_reduce_progress_precise Hs Hpq) as [z Hrq].
    destruct (Path_reduce_fun_value_precise Hs Hrp Hp)
      as (A' & function_body & Hv).
    exact (State_Progress_app Hrp Hrq Hv).
  - exact (State_Progress_let_term s K u body).
  - exact (State_Progress_typed s K u A).
Qed.

Local Definition State_Ty_components
    {n : nat} {G : Ctx n} {st : State n} {T : Ty n}
    (H : State_Ty G st T) :
    exists S0,
      Tm_Cont_Ty G S0 (state_cont st) T /\
      Tm_Ty G (state_term st) S0.
Proof.
  destruct H. exists S0. now split.
Defined.

Theorem State_Ty_progress_of_precise_store
    {n : nat} {G : Ctx n} {s : Store n} {K : Tm_Cont n}
    {t : Tm n} {R : Ty n}
    (H : State_Ty G (mk_state s K t) R)
    (Hs : Store_PreciseTy G s) :
    State_Progress (mk_state s K t).
Proof.
  destruct (State_Ty_components H) as [S0 [Hk Ht]].
  exact (State_progress_precise Hs Hk Ht).
Qed.

Print Assumptions Path_reduce_fun_value_precise.
Print Assumptions State_progress_precise.
Print Assumptions State_Ty_progress_of_precise_store.
