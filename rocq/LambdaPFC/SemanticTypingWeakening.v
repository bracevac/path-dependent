From Equations Require Import Equations.
From Stdlib Require Import Lists.List.
From PathDependent.LambdaPFC Require Import
  FinFun Syntax Runtime RuntimeEquality Valuation SemanticEvidence
  SemanticTyping SemanticWeakening.

Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Normalized evidence for an old value survives allocation. *)
Definition value_evidence_weaken {n : nat} {sigma : Store n}
    {term : Tm n} {T : Ty n}
    (evidence : ValueEvidence sigma term T)
    (v : Tm n) (value : Tm_IsValue v) :
    ValueEvidence (StoreVal sigma v value) (tm_weaken term) (ty_weaken T).
Proof.
  destruct evidence.
  - cbn [tm_weaken]. simp tm_rename.
    exact (ValueEv_abs (body_closure_weaken b (v := v) value)
      (coercion_weaken c (v := v) value)).
  - cbn [tm_weaken]. simp tm_rename def_rename.
    refine (ValueEv_pair _).
    pose proof (coercion_weaken c (v := v) value) as weakened.
    unfold tau_weaken in weakened.
    rewrite !tau_rename_equation_1, ty_rename_equation_4,
      !ty_rename_equation_5 in weakened.
    rewrite tau_rename_equation_1, ty_rename_equation_5 in weakened.
    simp path_rename in weakened.
    rewrite <- path_weaken_rename in weakened.
    exact weakened.
  - cbn [tm_weaken]. simp tm_rename def_rename.
    refine (ValueEv_tpair _).
    pose proof (coercion_weaken c (v := v) value) as weakened.
    unfold ty_weaken, tau_weaken in weakened |- *.
    rewrite tau_rename_equation_1, ty_rename_equation_4,
      ty_rename_equation_5 in weakened.
    simp path_rename in weakened.
    rewrite tau_rename_rename, <- comp_weaken in weakened.
    rewrite tau_rename_equation_1 in weakened.
    rewrite <- tau_rename_equation_2, tau_rename_rename.
    exact weakened.
Defined.

(** Continuation evidence survives allocation. *)
Fixpoint cont_evidence_weaken {n : nat} {sigma : Store n}
    {S T : Ty n} {cont : TmCont n}
    (evidence : ContEvidence sigma S cont T)
    (v : Tm n) (value : Tm_IsValue v) {struct evidence} :
    ContEvidence (StoreVal sigma v value) (ty_weaken S)
      (cont_weaken cont) (ty_weaken T).
Proof.
  destruct evidence.
  - cbn [cont_weaken cont_rename]. exact ContEv_hole.
  - cbn [cont_weaken cont_rename].
    refine (ContEv_cons
      (cont_evidence_weaken _ _ _ _ _ evidence v value) _
      (coercion_weaken c (v := v) value)).
    pose proof (body_closure_weaken b (v := v) value) as closure.
    rewrite <- ty_weaken_rename in closure.
    exact closure.
Defined.

Print Assumptions value_evidence_weaken.
Print Assumptions cont_evidence_weaken.
