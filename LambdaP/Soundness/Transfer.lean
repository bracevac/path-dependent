import LambdaP.Soundness.PathLemmas
import LambdaP.Soundness.Den

/-!
The semantic transfer lemma behind `Sub.repl`: co-evaluating closed paths
induce the same denotations through type openings. The arrow/pair clauses
of `Den` store syntactic subtyping facts; those transfer by *syntactic*
`repl` instances (the rule pays for its own closure case), while path
positions transfer by evaluation congruence. The binder-swap algebra
handles the two-openings composition in pair member positions.
-/

namespace LambdaP

/-! ### Binder swap -/

/-- Swaps the two innermost binders. -/
def Rename.swap {s : Sig} : Rename (s+2) (s+2) where
  var := fun
    | .here => .there .here
    | .there .here => .here
    | .there (.there x) => .there (.there x)

@[simp]
theorem Ty.structSize_rename {T : Ty s1} {f : Rename s1 s2} :
    (T.rename f).structSize = T.structSize := by
  induction T generalizing s2 <;> simp [Ty.rename, Ty.structSize, *]

/-- Filling the outer slot with `r`, then the remaining slot with `q`,
equals swapping, filling with `q`, then filling with `r`. Stated in the
substitution spelling that `Den`'s clauses expose after simplification. -/
theorem Ty.openlift_open {T : Ty (s+2)} {r q : Path s} :
    (T.subst (Subst.openPath r).lift).subst (Subst.openPath q)
      = ((T.rename Rename.swap).subst (Subst.openPath q).lift).subst (Subst.openPath r) := by
  have wo : ∀ (u v : Path s),
      (u.rename Rename.succ).subst (Subst.openPath v) = u :=
    fun u v => Path.weaken_open
  simp only [Ty.subst_comp, Ty.rename_subst_comm]
  congr 1
  apply Subst.funext
  intro x
  cases x with
  | here =>
    show q = (q.rename Rename.succ).subst (Subst.openPath r)
    exact (wo q r).symm
  | there y =>
    cases y with
    | here =>
      show (r.rename Rename.succ).subst (Subst.openPath q) = r
      exact wo r q
    | there z => rfl

/-- Opening a swap-renamed type with a weakened path fills the outer slot. -/
theorem Ty.swap_open_weaken {T : Ty (s+2)} {r : Path s} :
    (T.rename Rename.swap).open (r.rename Rename.succ)
      = T.subst (Subst.openPath r).lift := by
  simp only [Ty.open, Ty.rename_subst_comm]
  congr 1
  apply Subst.funext
  intro x
  match x with
  | .here => rfl
  | .there .here => rfl
  | .there (.there x) => rfl

/-! ### Mutual singleton subtyping from co-evaluation -/

/-- Co-evaluating wellformed closed paths are mutually-aliased singletons. -/
theorem PathEval.mutual_singles {Θ : Sto} {h : Heap} (hh : HeapTyped Θ h)
    {p q : Path 0} {m : Nat}
    (hp : PathEval h p m) (hq : PathEval h q m)
    (hwp : Path.Wf Θ .empty p) (hwq : Path.Wf Θ .empty q) :
    Sub Θ .empty (.ty (.single p)) (.ty (.single q)) ∧
    Sub Θ .empty (.ty (.single q)) (.ty (.single p)) :=
  ⟨.trans (hp.to_sub hh) (.symm hwq (hq.to_sub hh)),
   .trans (hq.to_sub hh) (.symm hwp (hp.to_sub hh))⟩

/-! ### The transfer lemma -/

/-- Leaf transfer: singleton clauses. -/
private theorem Den.oc_single {Θ : Sto} {Ξ : SemSto} {h : Heap}
    {p q : Path 0} {m : Nat} (hp : PathEval h p m) (hq : PathEval h q m)
    {P : Path 1} {n : Nat} {ℓ : Nat}
    (hd : Den Θ Ξ h n ((Ty.single P).open p) ℓ) :
    Den Θ Ξ h n ((Ty.single P).open q) ℓ := by
  simp only [Ty.open, Ty.subst, Den] at hd ⊢
  exact PathEval.open_congr hp hq hd

/-- Leaf transfer: type-selection clauses. -/
private theorem Den.oc_tsel {Θ : Sto} {Ξ : SemSto} {h : Heap}
    {p q : Path 0} {m : Nat} (hp : PathEval h p m) (hq : PathEval h q m)
    {P : Path 1} {A : Name} {n : Nat} {ℓ : Nat}
    (hd : Den Θ Ξ h n ((Ty.tsel P A).open p) ℓ) :
    Den Θ Ξ h n ((Ty.tsel P A).open q) ℓ := by
  simp only [Ty.open, Ty.subst, Den] at hd ⊢
  obtain ⟨m1, ℓ1, W, hev, hlk, hΞ⟩ := hd
  exact ⟨m1, ℓ1, W, PathEval.open_congr hp hq hev, hlk, hΞ⟩

/-- Semantic transfer: co-evaluating wellformed closed paths induce the
same denotations through openings, at every level. -/
theorem Den.open_coeval {Θ : Sto} {Ξ : SemSto} {h : Heap}
    (hh : HeapTyped Θ h) (_hok : SemStoOk Θ Ξ h) :
    ∀ (sz : Nat) (T : Ty 1), T.structSize ≤ sz ->
    ∀ {p q : Path 0} {m : Nat},
      PathEval h p m -> PathEval h q m ->
      Path.Wf Θ .empty p -> Path.Wf Θ .empty q ->
      ∀ n ℓ, Den Θ Ξ h n (T.open p) ℓ -> Den Θ Ξ h n (T.open q) ℓ := by
  intro sz
  induction sz with
  | zero =>
    intro T hsz p q m hp hq hwp hwq n ℓ hd
    match T with
    | .top => simp only [Ty.open, Ty.subst, Den]
    | .bot => simp only [Ty.open, Ty.subst, Den] at hd
    | .single P => exact Den.oc_single hp hq hd
    | .tsel P A => exact Den.oc_tsel hp hq hd
    | .arrow S T => simp [Ty.structSize] at hsz
    | .pairTm S a T => simp [Ty.structSize] at hsz
    | .pairTy S A T1 T2 => simp [Ty.structSize] at hsz
  | succ sz ih =>
    intro T hsz p q m hp hq hwp hwq n ℓ hd
    obtain ⟨hs_pq, hs_qp⟩ := PathEval.mutual_singles hh hp hq hwp hwq
    match T with
    | .top => simp only [Ty.open, Ty.subst, Den]
    | .bot => simp only [Ty.open, Ty.subst, Den] at hd
    | .single P => exact Den.oc_single hp hq hd
    | .tsel P A => exact Den.oc_tsel hp hq hd
    | .arrow S T =>
      simp only [Ty.structSize] at hsz
      simp only [Ty.open, Ty.subst, Den] at hd ⊢
      obtain ⟨T0, t, T1, hlk, hwf0, hty, hdom, hcod⟩ := hd
      -- domain: S.open q <: S.open p <: T0, via a closed repl instance
      have hrepl_qp : Sub Θ .empty (.ty (Ty.open S q)) (.ty (Ty.open S p)) :=
        Sub.repl hwq hwp hs_qp hs_pq
      -- codomain: narrow to the q-domain, then a pushed repl instance
      have hnarrow := hcod.narrow hrepl_qp
      have hreplT : Sub Θ (Ctx.empty.push (Ty.open S q))
          (.ty ((T.rename Rename.swap).open (p.rename Rename.succ)))
          (.ty ((T.rename Rename.swap).open (q.rename Rename.succ))) :=
        Sub.repl hwp.weaken hwq.weaken hs_pq.weaken hs_qp.weaken
      rw [Ty.swap_open_weaken, Ty.swap_open_weaken] at hreplT
      exact ⟨T0, t, T1, hlk, hwf0, hty,
        .trans hrepl_qp hdom, .trans hnarrow hreplT⟩
    | .pairTm S a T =>
      simp only [Ty.structSize] at hsz
      simp only [Ty.open, Ty.subst, Den] at hd ⊢
      obtain ⟨ℓ1, ℓ2, hlk, hsub1, hcomp, hmem⟩ := hd
      have hrepl_pq : Sub Θ .empty (.ty (Ty.open S p)) (.ty (Ty.open S q)) :=
        Sub.repl hwp hwq hs_pq hs_qp
      refine ⟨ℓ1, ℓ2, hlk, .trans hsub1 hrepl_pq, ?_, ?_⟩
      · intro k
        exact ih S (by omega) hp hq hwp hwq k ℓ1 (hcomp k)
      · intro q' hq' k
        have hV := hmem q' hq' k
        rw [Ty.openlift_open] at hV ⊢
        exact ih _ (by simp; omega) hp hq hwp hwq k ℓ2 hV
    | .pairTy S A T1 T2 =>
      simp only [Ty.structSize] at hsz
      simp only [Ty.open, Ty.subst, Den] at hd ⊢
      obtain ⟨ℓ1, W, hlk, hsub1, hcomp, hsand⟩ := hd
      have hrepl_pq : Sub Θ .empty (.ty (Ty.open S p)) (.ty (Ty.open S q)) :=
        Sub.repl hwp hwq hs_pq hs_qp
      refine ⟨ℓ1, W, hlk, .trans hsub1 hrepl_pq, ?_, ?_⟩
      · intro k
        exact ih S (by omega) hp hq hwp hwq k ℓ1 (hcomp k)
      · cases n with
        | zero => trivial
        | succ n0 =>
          intro q' hq' y
          constructor
          · intro hy
            rw [Ty.openlift_open] at hy
            have hy' := ih _ (by simp; omega) hq hp hwq hwp n0 y hy
            simp only [Ty.open] at hy'
            rw [← Ty.openlift_open] at hy'
            exact (hsand q' hq' y).1 hy'
          · intro hΞy
            have hy := (hsand q' hq' y).2 hΞy
            rw [Ty.openlift_open] at hy ⊢
            exact ih _ (by simp; omega) hp hq hwp hwq n0 y hy

end LambdaP
