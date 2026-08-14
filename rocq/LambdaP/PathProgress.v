From Equations Require Import Equations.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Renaming Store PathReduction Lookup
  PreciseStore PathFunctionality TypingInversion PathPreservation.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Proper signatures require a concrete lookup result; abstract interval
    signatures carry no term-level progress obligation. *)
Local Definition Path_Lookupable {n : nat} (s : Store n) (p : Path n)
    {k : Kind} (d : Tau n k) : Prop :=
  match d with
  | tau_ty _ => exists x, Path_lookup p s x
  | tau_intv _ _ => True
  end.

Local Lemma Path_lookupable_fst
    {n : nat} {G : Ctx n} {s : Store n} {p : Path n}
    {S0 : Ty n} {a : Name} {k : Kind} {d : Tau (S n) k}
    (Hs : Store_PreciseTy G s)
    (Hp : Path_Ty G p (tau_ty (ty_pair S0 a d)))
    (IH : Path_Lookupable s p (tau_ty (ty_pair S0 a d))) :
    Path_Lookupable s (path_fst p) (tau_ty S0).
Proof.
  cbn [Path_Lookupable] in IH |- *.
  destruct IH as [x Hx].
  destruct (Path_lookup_type_shape Hs Hx Hp) as [Hbind | Heq].
  - destruct (Store_PreciseTy_of_ctx_binds Hs Hbind)
      as (v & Hv & Hprecise).
    dependent elimination Hprecise.
    + eexists. eapply path_lookup_fst; eassumption.
    + eexists. eapply path_lookup_fst; eassumption.
  - discriminate Heq.
Qed.

Local Lemma Path_lookupable_sel_r
    {n : nat} {G : Ctx n} {s : Store n} {p : Path n}
    {S0 : Ty n} {a : Name} {k : Kind} {d : Tau (S n) k}
    (Hs : Store_PreciseTy G s)
    (Hp : Path_Ty G p (tau_ty (ty_pair S0 a d)))
    (IH : Path_Lookupable s p (tau_ty (ty_pair S0 a d))) :
    Path_Lookupable s (path_sel p a) (Tau_open d (path_fst p)).
Proof.
  dependent elimination d.
  - cbn [Path_Lookupable] in IH |- *.
    destruct IH as [x Hx].
    destruct (Path_lookup_type_shape Hs Hx Hp) as [Hbind | Heq].
    + destruct (Store_PreciseTy_of_ctx_binds Hs Hbind)
        as (v & Hv & Hprecise).
      dependent elimination Hprecise.
      eexists. eapply path_lookup_sel_hit; eassumption.
    + discriminate Heq.
  - cbn [Path_Lookupable]. exact I.
Qed.

Local Lemma Path_lookupable_sel_l
    {n : nat} {G : Ctx n} {s : Store n} {p : Path n}
    {S0 : Ty n} {a b : Name} {k k' : Kind}
    {d : Tau n k} {d' : Tau (S n) k'}
    (Hs : Store_PreciseTy G s)
    (Hp : Path_Ty G p (tau_ty (ty_pair S0 b d')))
    (Htail : Path_Ty G (path_sel (path_fst p) a) d)
    (Hneq : a <> b)
    (IHp : Path_Lookupable s p (tau_ty (ty_pair S0 b d')))
    (IHtail : Path_Lookupable s (path_sel (path_fst p) a) d) :
    Path_Lookupable s (path_sel p a) d.
Proof.
  dependent elimination d.
  - cbn [Path_Lookupable] in IHp, IHtail |- *.
    destruct IHp as [x Hx]. destruct IHtail as [z Hz].
    destruct (Path_lookup_type_shape Hs Hx Hp) as [Hbind | Heq].
    + destruct (Store_PreciseTy_of_ctx_binds Hs Hbind)
        as (v & Hv & Hprecise).
      dependent elimination Hprecise.
      * exists z. eapply path_lookup_sel_miss; eassumption.
      * exists z. eapply path_lookup_sel_miss; eassumption.
    + discriminate Heq.
  - cbn [Path_Lookupable]. exact I.
Qed.

Local Lemma Path_lookupable_precise
    {n : nat} {G : Ctx n} {s : Store n}
    {k : Kind} {p : Path n} {d : Tau n k}
    (Hs : Store_PreciseTy G s) (Hp : Path_Ty G p d) :
    Path_Lookupable s p d.
Proof.
  induction Hp.
  - cbn [Path_Lookupable]. eexists. apply path_lookup_var.
  - eapply Path_lookupable_fst; [exact Hs | eassumption |].
    exact (IHHp s Hs).
  - eapply Path_lookupable_sel_r; [exact Hs | eassumption |].
    exact (IHHp s Hs).
  - eapply Path_lookupable_sel_l;
      [exact Hs | eassumption | eassumption | eassumption |
       exact (IHHp1 s Hs) | exact (IHHp2 s Hs)].
Qed.

Theorem Path_lookup_progress_precise
    {n : nat} {G : Ctx n} {s : Store n}
    {p : Path n} {T : Ty n}
    (Hs : Store_PreciseTy G s) (Hp : Path_Ty G p (tau_ty T)) :
    exists x, Path_lookup p s x.
Proof. exact (Path_lookupable_precise Hs Hp). Qed.

Theorem Path_reduce_progress_precise
    {n : nat} {G : Ctx n} {s : Store n}
    {p : Path n} {T : Ty n}
    (Hs : Store_PreciseTy G s) (Hp : Path_Ty G p (tau_ty T)) :
    exists x, Path_reduce p s x.
Proof.
  destruct (Path_lookup_progress_precise Hs Hp) as [x Hx].
  exists x. exact (Path_lookup_toReduce Hx).
Qed.

Print Assumptions Path_lookup_progress_precise.
Print Assumptions Path_reduce_progress_precise.
