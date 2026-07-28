import LambdaP.Soundness.Bridge

/-!
Support for the syntactic collapse: the transfer motive, realized
closing substitutions over `PT`, their extension at binders, and the
replacement transfer for `PT` (the store-side mirror of
`Den.open_coeval`, with `Inv.open_repl` carrying the lower fields).
-/

namespace LambdaP

/-- The transfer reading of a subtyping conclusion, by shape. -/
def SubPT (Θ : Sto) : Tau 0 -> Tau 0 -> Prop
| .ty U1, .ty U2 => ∀ ℓ, PT Θ U1 ℓ -> PT Θ U2 ℓ
| .intv S1 T1, .intv S2 T2 =>
    (∀ ℓ, PT Θ S2 ℓ -> PT Θ S1 ℓ) ∧
    (∀ ℓ, PT Θ T1 ℓ -> PT Θ T2 ℓ)
| _, _ => False

/-- Closing substitutions realized over the functional interpretation. -/
structure PTSubst (Θ : Sto) (σ : Subst s 0) (Γ : Ctx s) : Prop where
  conforms : SubstTyping Θ σ Γ .empty
  realized : ∀ {x T}, Ctx.LookupVar Γ x T ->
    ∃ m, Chains Θ (σ.var x) m ∧ PT Θ (T.subst σ) m

/-- The identity substitution realizes the empty context. -/
theorem PTSubst.empty {Θ : Sto} : PTSubst Θ Subst.id .empty := by
  constructor
  · constructor
    · intro x T hx
      exact absurd hx (fun hx => nomatch hx)
    · intro x
      exact nomatch x
  · intro x T hx
    exact nomatch hx

/-- Extension at a binder with a resolving, conforming, inhabited path. -/
theorem PTSubst.extend {Θ : Sto} {σ : Subst s 0} {Γ : Ctx s} {S : Ty s}
    {q : Path 0} {ℓq : Nat}
    (hσ : PTSubst Θ σ Γ)
    (hq : Chains Θ q ℓq) (hqwf : Path.Wf Θ .empty q)
    (hqsub : Sub Θ .empty (.ty (.single q)) (.ty (S.subst σ)))
    (hqpt : PT Θ (S.subst σ) ℓq) :
    PTSubst Θ (σ.lift.comp (Subst.openPath q)) (Γ.push S) := by
  constructor
  · exact SubstTyping.comp hσ.conforms.lift (SubstTyping.openPath hqwf hqsub)
  · intro x T hx
    cases hx with
    | here =>
      refine ⟨ℓq, hq, ?_⟩
      rw [Ty.weaken_subst_extend]
      exact hqpt
    | there hx' =>
      obtain ⟨m, hch, hpt⟩ := hσ.realized hx'
      refine ⟨m, ?_, ?_⟩
      · show Chains Θ (((σ.var _).rename Rename.succ).subst (Subst.openPath q)) m
        rw [Path.rename_succ_subst_open]
        exact hch
      · rw [Ty.weaken_subst_extend]
        exact hpt

/-- Replacement transfer for the functional interpretation: co-chaining
closed paths induce the same possible types through openings. -/
theorem PT.open_cochain {Θ : Sto} {h : Heap} (_hh : HeapTyped Θ h) :
    ∀ (sz : Nat) (T : Ty 1), T.structSize ≤ sz ->
    ∀ {p q : Path 0} {ℓ0 : Nat},
      Chains Θ p ℓ0 -> Chains Θ q ℓ0 ->
      ∀ ℓ, PT Θ (T.open p) ℓ -> PT Θ (T.open q) ℓ := by
  intro sz
  induction sz with
  | zero =>
    intro T hsz p q ℓ0 hp hq ℓ hd
    match T with
    | .top => simp only [Ty.open, Ty.subst, PT]
    | .bot => simp only [Ty.open, Ty.subst, PT] at hd
    | .single P =>
      simp only [Ty.open, Ty.subst, PT] at hd ⊢
      exact Chains.open_congr hp hq hd
    | .tsel P A =>
      simp only [Ty.open, Ty.subst, PT] at hd ⊢
      obtain ⟨m, ℓ1, W, hc, hl, hiW⟩ := hd
      exact ⟨m, ℓ1, W, Chains.open_congr hp hq hc, hl, hiW⟩
    | .arrow S T => simp [Ty.structSize] at hsz
    | .pairTm S a T => simp [Ty.structSize] at hsz
    | .pairTy S A T1 T2 => simp [Ty.structSize] at hsz
  | succ sz ih =>
    intro T hsz p q ℓ0 hp hq ℓ hd
    match T with
    | .top => simp only [Ty.open, Ty.subst, PT]
    | .bot => simp only [Ty.open, Ty.subst, PT] at hd
    | .single P =>
      simp only [Ty.open, Ty.subst, PT] at hd ⊢
      exact Chains.open_congr hp hq hd
    | .tsel P A =>
      simp only [Ty.open, Ty.subst, PT] at hd ⊢
      obtain ⟨m, ℓ1, W, hc, hl, hiW⟩ := hd
      exact ⟨m, ℓ1, W, Chains.open_congr hp hq hc, hl, hiW⟩
    | .arrow S T =>
      simp only [Ty.structSize] at hsz
      simp only [Ty.open, Ty.subst, PT] at hd ⊢
      obtain ⟨T0, T1, hl, hdom, hcod⟩ := hd
      refine ⟨T0, T1, hl, ?_, ?_⟩
      · exact .trans ((Sub.repl hq.wf hp.wf (hq.mutual_sub hp) (hp.mutual_sub hq))) hdom
      · have hn := hcod.narrow (Sub.repl hq.wf hp.wf (hq.mutual_sub hp) (hp.mutual_sub hq))
        exact .trans hn (Sub.repl_push hp hq)
    | .pairTm S a T =>
      simp only [Ty.structSize] at hsz
      simp only [Ty.open, Ty.subst, PT] at hd ⊢
      obtain ⟨ℓ1, ℓ2, hl, hs1, hcomp, hmem⟩ := hd
      refine ⟨ℓ1, ℓ2, hl,
        .trans hs1 (Sub.repl hp.wf hq.wf (hp.mutual_sub hq) (hq.mutual_sub hp)),
        ih S (by omega) hp hq ℓ1 hcomp, ?_⟩
      intro q' hq'
      have hV := hmem q' hq'
      rw [Ty.openlift_open] at hV ⊢
      exact ih _ (by simp; omega) hp hq ℓ2 hV
    | .pairTy S A T1 T2 =>
      simp only [Ty.structSize] at hsz
      simp only [Ty.open, Ty.subst, PT] at hd ⊢
      obtain ⟨ℓ1, W, hl, hs1, hcomp, hsand⟩ := hd
      refine ⟨ℓ1, W, hl,
        .trans hs1 (Sub.repl hp.wf hq.wf (hp.mutual_sub hq) (hq.mutual_sub hp)),
        ih S (by omega) hp hq ℓ1 hcomp, ?_⟩
      intro q' hq'
      obtain ⟨hlo, hhi⟩ := hsand q' hq'
      constructor
      · intro y hy
        rw [Ty.openlift_open] at hy
        have hy' : Inv Θ y
            (((T1.rename Rename.swap).subst (Subst.openPath q').lift).subst
              (Subst.openPath p)) :=
          .open_repl hy hq hp
        rw [← Ty.openlift_open] at hy'
        exact hlo y hy'
      · intro y hy
        have hz := hhi y hy
        rw [Ty.openlift_open] at hz ⊢
        exact ih _ (by simp; omega) hp hq y hz

end LambdaP
