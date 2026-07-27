import LambdaP.Soundness.Den

/-!
Path-evaluation lemmas: determinism, and congruence of evaluation under
replacement of a co-evaluating prefix. The congruence lemma is what makes
`T.open q` and `T.open (var ℓ)` semantically interchangeable when `q ⇓ ℓ`
— paths in types are only ever *resolved* through the store, never
evaluated as programs, so replacing a prefix by any co-evaluating path is
invisible to every store consultation.
-/

namespace LambdaP

/-- Path evaluation is deterministic. -/
theorem PathEval.deterministic {h : Heap} {p : Path 0} {m1 m2 : Nat}
    (h1 : PathEval h p m1) (h2 : PathEval h p m2) : m1 = m2 := by
  induction h1 generalizing m2 with
  | var =>
    cases h2 with
    | var => rfl
  | fst_tm _ hl1 ih =>
    cases h2 with
    | fst_tm h2' hl2 =>
      cases ih h2'
      cases Option.some.inj (hl1.symm.trans hl2)
      rfl
    | fst_ty h2' hl2 =>
      cases ih h2'
      cases Option.some.inj (hl1.symm.trans hl2)
  | fst_ty _ hl1 ih =>
    cases h2 with
    | fst_tm h2' hl2 =>
      cases ih h2'
      cases Option.some.inj (hl1.symm.trans hl2)
    | fst_ty h2' hl2 =>
      cases ih h2'
      cases Option.some.inj (hl1.symm.trans hl2)
      rfl
  | sel _ hl1 ih =>
    cases h2 with
    | sel h2' hl2 =>
      cases ih h2'
      cases Option.some.inj (hl1.symm.trans hl2)
      rfl

/-- Evaluation of an opened path only depends on the target of the opening
path: if `q` and `q'` co-evaluate, then `p[q/x]` and `p[q'/x]` co-evaluate.
Structural in `p` because evaluation consults the prefix only through its
target. -/
theorem PathEval.open_congr {h : Heap} {q q' : Path 0} {ℓq : Nat}
    (hq : PathEval h q ℓq) (hq' : PathEval h q' ℓq) :
    ∀ {p : Path 1} {m : Nat},
      PathEval h (p.subst (Subst.openPath q)) m ->
      PathEval h (p.subst (Subst.openPath q')) m := by
  intro p
  induction p with
  | var x =>
    intro m he
    cases x with
    | bound b =>
      cases b with
      | here =>
        have : m = ℓq := PathEval.deterministic he hq
        subst this
        exact hq'
      | there b => exact nomatch b
    | free n => exact he
  | fst p ih =>
    intro m he
    cases he with
    | fst_tm he' hl => exact .fst_tm (ih he') hl
    | fst_ty he' hl => exact .fst_ty (ih he') hl
  | sel p a ih =>
    intro m he
    cases he with
    | sel he' hl => exact .sel (ih he') hl

end LambdaP
