From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Renaming Store PreciseStore.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** An ordinary typing of a value factors through the type assigned directly
    by its introduction rule. *)
Theorem Tm_Ty_value_inversion
    {n : nat} {G : Ctx n} {v : Tm n} {T : Ty n}
    (H : Tm_Ty G v T) (Hv : Tm_IsValue v) :
    exists P,
      Tm_PreciseTy G v P /\
      Tau_Sub G (tau_ty P) (tau_ty T).
Proof.
  induction H as
      [n G p T Hp
      |n G S t T Ht IH Hwf
      |n G p q S T Hp IHp Hq IHq
      |n G y z S T a Hy Hz
      |n G y S T A Hy Hwf
      |n G s S T t Hs IHs Hwf Ht IHt
      |n G t T Ht IH Hwf
      |n G t S T Ht IH Hsub Hwf].
  - inversion Hv.
  - exists (ty_fun S T). split.
    + exact (precise_ty_abs G S t T Ht Hwf).
    + apply sub_refl.
  - inversion Hv.
  - eexists. split.
    + exact (precise_ty_pair G y z S T a Hy Hz).
    + apply sub_refl.
  - eexists. split.
    + exact (precise_ty_tpair G y S T A Hy Hwf).
    + apply sub_refl.
  - inversion Hv.
  - inversion Hv.
  - destruct (IH Hv) as [P [Hp HPT]].
    exists P. split.
    + exact Hp.
    + eapply sub_trans; eassumption.
Qed.

Print Assumptions Tm_Ty_value_inversion.
