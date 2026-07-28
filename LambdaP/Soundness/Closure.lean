import LambdaP.Soundness.DenLemmas
import LambdaP.Soundness.Transfer

/-!
The closure lemma: subtyping is sound for the denotation, per level,
under semantically realized closing substitutions — jointly with path
progress (wellformed paths evaluate). The index discipline is ECOOP'17's:
selections dereference one level up, sandwiches sit at the predecessor,
IHs are invoked at shifted levels (never weakened), and the store tie
(`SemStoOk`) supplies facts at every level.
-/

namespace LambdaP

/-- A closing substitution that is syntactically conforming and whose
images evaluate into the limit denotations of their declared types
(the analog of ECOOP'17's `R_env` towers at all levels). -/
structure SemSubst (Θ : Sto) (Ξ : SemSto) (h : Heap) (σ : Subst s 0)
    (Γ : Ctx s) : Prop where
  conforms : SubstTyping Θ σ Γ .empty
  realized : ∀ {x : BVar s} {T : Ty s}, Ctx.LookupVar Γ x T ->
    ∃ m, PathEval h (σ.var x) m ∧ DenAll Θ Ξ h (T.subst σ) m

/-- The per-level semantic reading of a subtyping conclusion, by shape.
Mixed shapes are unreachable (no rule concludes them); making them `False`
lets the transitivity case eliminate them without a separate shape lemma. -/
def SubDen (Θ : Sto) (Ξ : SemSto) (h : Heap) : Tau 0 -> Tau 0 -> Prop
| .ty U1, .ty U2 => ∀ n ℓ, Den Θ Ξ h n U1 ℓ -> Den Θ Ξ h n U2 ℓ
| .intv S1 T1, .intv S2 T2 =>
    (∀ n ℓ, Den Θ Ξ h n S2 ℓ -> Den Θ Ξ h n S1 ℓ) ∧
    (∀ n ℓ, Den Θ Ξ h n T1 ℓ -> Den Θ Ξ h n T2 ℓ)
| _, _ => False

/-- Conforming substitutions compose. -/
theorem SubstTyping.comp {Θ : Sto} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3}
    {Γ : Ctx s1} {Δ : Ctx s2} {E : Ctx s3}
    (h1 : SubstTyping Θ σ1 Γ Δ) (h2 : SubstTyping Θ σ2 Δ E) :
    SubstTyping Θ (σ1.comp σ2) Γ E := by
  constructor
  · intro x T hx
    have := (h1.conforms hx).subst h2
    simp only [Tau.subst, Ty.subst, Ty.subst_comp] at this ⊢
    exact this
  · intro x
    exact (h1.wf x).subst h2

/-- Weakening then closing through an extended substitution collapses to
the base substitution. -/
theorem Ty.weaken_subst_extend {S : Ty s} {σ : Subst s 0} {q : Path 0} :
    S.weaken.subst (σ.lift.comp (Subst.openPath q)) = S.subst σ := by
  rw [← Ty.subst_comp, Ty.weaken_subst_comm]
  exact Ty.weaken_open

/-- `Path.weaken_open`, spelled on the `rename`-normal form that
substitution lifting produces. -/
theorem Path.rename_succ_subst_open {p q : Path 0} :
    (p.rename Rename.succ).subst (Subst.openPath q) = p :=
  Path.weaken_open

/-- Extending a semantically realized closing substitution at a binder
with an evaluated, conforming path. -/
theorem SemSubst.extend {Θ : Sto} {Ξ : SemSto} {h : Heap} {σ : Subst s 0}
    {Γ : Ctx s} {S : Ty s} {q : Path 0} {ℓq : Nat}
    (hσ : SemSubst Θ Ξ h σ Γ)
    (hq : PathEval h q ℓq) (hqwf : Path.Wf Θ .empty q)
    (hqsub : Sub Θ .empty (.ty (.single q)) (.ty (S.subst σ)))
    (hqden : DenAll Θ Ξ h (S.subst σ) ℓq) :
    SemSubst Θ Ξ h (σ.lift.comp (Subst.openPath q)) (Γ.push S) := by
  constructor
  · exact SubstTyping.comp hσ.conforms.lift (SubstTyping.openPath hqwf hqsub)
  · intro x T hx
    cases hx with
    | here =>
      refine ⟨ℓq, hq, ?_⟩
      rw [Ty.weaken_subst_extend]
      exact hqden
    | there hx' =>
      obtain ⟨m, hev, hden⟩ := hσ.realized hx'
      refine ⟨m, ?_, ?_⟩
      · show PathEval h (((σ.var _).rename Rename.succ).subst (Subst.openPath q)) m
        rw [Path.rename_succ_subst_open]
        exact hev
      · rw [Ty.weaken_subst_extend]
        exact hden

/-- Subtyping is sound for the denotation under realized closing
substitutions, per level. Proven by the joint induction with path
progress (wellformed paths evaluate) as the second motive. -/
theorem Sub.den {Θ : Sto} {Γ : Ctx s} {τ1 τ2 : Tau s} (hs : Sub Θ Γ τ1 τ2) :
    ∀ {Ξ : SemSto} {h : Heap} {σ : Subst s 0},
      HeapTyped Θ h -> SemStoOk Θ Ξ h -> SemSubst Θ Ξ h σ Γ ->
      SubDen Θ Ξ h (τ1.subst σ) (τ2.subst σ) := by
  induction hs using Sub.rec
    (motive_2 := fun {s} Θ Γ p _ =>
      ∀ {Ξ : SemSto} {h : Heap} {σ : Subst s 0},
        HeapTyped Θ h -> SemStoOk Θ Ξ h -> SemSubst Θ Ξ h σ Γ ->
        ∃ m, PathEval h (p.subst σ) m)
  · rename_i τ
    intro Ξ hp σ hh hok hσ
    cases hτ : τ.subst σ with
    | ty U => exact fun n ℓ hd => hd
    | intv S T => exact ⟨fun n ℓ hd => hd, fun n ℓ hd => hd⟩
  · rename_i τ1 τ2 τ3 h1 h2 ih1 ih2
    intro Ξ hp σ hh hok hσ
    have ih1 := ih1 hh hok hσ
    have ih2 := ih2 hh hok hσ
    rcases hτ1 : τ1.subst σ with U1 | ⟨S1, T1⟩ <;>
      rcases hτ2 : τ2.subst σ with U2 | ⟨S2, T2⟩ <;>
      rcases hτ3 : τ3.subst σ with U3 | ⟨S3, T3⟩ <;>
      rw [hτ1, hτ2] at ih1 <;> rw [hτ2, hτ3] at ih2 <;>
      simp only [SubDen] at ih1 ih2 ⊢ <;>
      first
      | exact fun n ℓ hd => ih2 n ℓ (ih1 n ℓ hd)
      | exact ih1.elim
      | exact ih2.elim
      | exact ⟨fun n ℓ hd => ih1.1 n ℓ (ih2.1 n ℓ hd),
               fun n ℓ hd => ih2.2 n ℓ (ih1.2 n ℓ hd)⟩
  · intro Ξ hp σ hh hok hσ n ℓ hd
    simp [Ty.subst, Den] at hd
  · intro Ξ hp σ hh hok hσ n ℓ _
    simp [Ty.subst, Den]
  · rename_i hx
    intro Ξ hp σ hh hok hσ n ℓ hd
    obtain ⟨m, hev, hden⟩ := hσ.realized hx
    simp only [Ty.subst, Den] at hd
    cases PathEval.deterministic hd hev
    exact hden n
  · rename_i hl
    intro Ξ hp σ hh hok hσ n ℓ hd
    simp only [Ty.subst, Den] at hd
    cases hd
    have := (hh.den_precise hok hl) n
    simpa only [Tau.subst, Ty.fromClosed_subst, Ty.fromClosed_zero] using this
  · rename_i hw h1 ihw ih1
    intro Ξ hp σ hh hok hσ n ℓ hd
    simp only [Ty.subst, Den] at hd ⊢
    obtain ⟨m, hev⟩ := ihw hh hok hσ
    have hq := ih1 hh hok hσ n m (by simp only [Ty.subst, Den]; exact hev)
    simp only [Ty.subst, Den] at hq
    cases PathEval.deterministic hq hd
    exact hev
  · rename_i h1 ih1
    intro Ξ hp σ hh hok hσ n ℓ hd
    simp only [Ty.subst, Den] at hd
    cases hd with
    | fst_tm hev hlk =>
      have ih := ih1 hh hok hσ n _ (by simp only [Ty.subst, Den]; exact hev)
      simp only [Ty.subst, Den] at ih
      obtain ⟨ℓ1', ℓ2', hlk', hsubS, hS, hOp⟩ := ih
      have heq := Option.some.inj (hlk'.symm.trans hlk)
      injection heq with _ hy1 _ hy2
      injection hy1 with hy1
      subst hy1
      exact hS n
    | fst_ty hev hlk =>
      have ih := ih1 hh hok hσ n _ (by simp only [Ty.subst, Den]; exact hev)
      simp only [Ty.subst, Den] at ih
      obtain ⟨ℓ1', ℓ2', hlk', -, -, -⟩ := ih
      cases Option.some.inj (hlk'.symm.trans hlk)
  · rename_i h1 ih1
    intro Ξ hp σ hh hok hσ n ℓ hd
    simp only [Ty.subst, Den] at hd
    cases hd with
    | fst_ty hev hlk =>
      have ih := ih1 hh hok hσ n _ (by simp only [Ty.subst, Den]; exact hev)
      simp only [Ty.subst, Den] at ih
      obtain ⟨ℓ1', W', hlk', hsubS, hS, hsand⟩ := ih
      have heq := Option.some.inj (hlk'.symm.trans hlk)
      injection heq with _ hy1 _ _
      injection hy1 with hy1
      subst hy1
      exact hS n
    | fst_tm hev hlk =>
      have ih := ih1 hh hok hσ n _ (by simp only [Ty.subst, Den]; exact hev)
      simp only [Ty.subst, Den] at ih
      obtain ⟨ℓ1', W', hlk', -, -, -⟩ := ih
      cases Option.some.inj (hlk'.symm.trans hlk)
  · rename_i h1 ih1
    intro Ξ hp σ hh hok hσ n ℓ hd
    simp only [Ty.subst, Den] at hd
    cases hd with
    | sel hev hlk =>
      have ih := ih1 hh hok hσ n _ (by simp only [Ty.subst, Den]; exact hev)
      simp only [Ty.subst, Den] at ih
      obtain ⟨ℓ1', ℓ2', hlk', hsubS, hS, hOp⟩ := ih
      have heq := Option.some.inj (hlk'.symm.trans hlk)
      injection heq with _ hy1 _ hy2
      injection hy1 with hy1
      injection hy2 with hy2
      subst hy1; subst hy2
      have hres := hOp _ (PathEval.fst_tm hev hlk') n
      rw [← Ty.open_subst_comm]
      exact hres
    | sel_skip_tm hev hlk hne hin =>
      have ih := ih1 hh hok hσ n _ (by simp only [Ty.subst, Den]; exact hev)
      simp only [Ty.subst, Den] at ih
      obtain ⟨ℓ1', ℓ2', hlk', -, -, -⟩ := ih
      have heq := Option.some.inj (hlk.symm.trans hlk')
      injection heq with _ _ hab _
      exact absurd hab.symm hne
    | sel_skip_ty hev hlk hin =>
      have ih := ih1 hh hok hσ n _ (by simp only [Ty.subst, Den]; exact hev)
      simp only [Ty.subst, Den] at ih
      obtain ⟨ℓ1', ℓ2', hlk', -, -, -⟩ := ih
      cases Option.some.inj (hlk.symm.trans hlk')
  · rename_i h1 h2u ih1 ih2u
    intro Ξ hp σ hh hok hσ n ℓ hd
    simp only [Ty.subst, Den] at hd
    obtain ⟨m, ℓ1, W, hev, hlk, hΞ⟩ := hd
    have ih := ih1 hh hok hσ (n+1) m (by simp only [Ty.subst, Den]; exact hev)
    simp only [Ty.subst, Den] at ih
    obtain ⟨ℓ1', W', hlk', hsubS, hS, hsand⟩ := ih
    have heq := Option.some.inj (hlk'.symm.trans hlk)
    injection heq with _ hy1 _ hW
    injection hy1 with hy1
    subst hy1; subst hW
    have hres := (hsand _ (PathEval.fst_ty hev hlk') ℓ).2 hΞ
    rw [← Ty.open_subst_comm]
    exact hres
  · rename_i hw h1 h2u ihw ih1 ih2u
    intro Ξ hp σ hh hok hσ n ℓ hd
    obtain ⟨m, hev⟩ := ihw hh hok hσ
    have ih := ih1 hh hok hσ (n+1) m (by simp only [Ty.subst, Den]; exact hev)
    simp only [Ty.subst, Den] at ih
    obtain ⟨ℓ1, W, hlk, hsubS, hS, hsand⟩ := ih
    simp only [Ty.subst, Den]
    refine ⟨m, ℓ1, W, hev, hlk, ?_⟩
    refine (hsand _ (PathEval.fst_ty hev hlk) ℓ).1 ?_
    rw [← Ty.open_subst_comm] at hd
    exact hd
  · rename_i h1 h2 ih1u ih2u
    intro Ξ hp σ hh hok hσ n ℓ hd
    simp only [Ty.subst, Den] at hd ⊢
    obtain ⟨T0, t, T1x, hlk, hwf0, hty, hdom, hcod⟩ := hd
    have h1σ := h1.subst hσ.conforms
    simp only [Tau.subst] at h1σ
    have h2σ := h2.subst hσ.conforms.lift
    simp only [Tau.subst] at h2σ
    exact ⟨T0, t, T1x, hlk, hwf0, hty, .trans h1σ hdom,
           .trans (Sub.narrow hcod h1σ) h2σ⟩
  · rename_i s' Θ' Γ' S S' T T' a h1 h2 ih1 ih2
    intro Ξ hp σ hh hok hσ n ℓ hd
    simp only [Ty.subst, Den] at hd ⊢
    obtain ⟨ℓ1, ℓ2, hlk, hsubS, hS, hOp⟩ := hd
    have h1σ := h1.subst hσ.conforms
    simp only [Tau.subst] at h1σ
    have hq1 : ℓ1 < Θ'.length := by
      obtain ⟨-, -, -, -, hb⟩ := hh.lookup_heap hlk
      have hlt := (List.getElem?_eq_some_iff.mp hlk).1
      rw [hh.1]
      exact Nat.lt_trans hb.1 hlt
    refine ⟨ℓ1, ℓ2, hlk, .trans hsubS h1σ,
            fun k => ih1 hh hok hσ k ℓ1 (hS k), ?_⟩
    intro q hq k
    have hqwf := PathEval.to_wf hh hq hq1
    have hqsub := Sub.trans (hq.to_sub hh) hsubS
    have hσq := SemSubst.extend hσ hq hqwf hqsub hS
    have ih := ih2 hh hok hσq
    rw [show ((Tau.ty T).subst ((σ.lift).comp (Subst.openPath q)))
          = .ty ((T.subst σ.lift).open q) from by
        simp only [Tau.subst]; rw [← Ty.subst_comp]; rfl,
       show ((Tau.ty T').subst ((σ.lift).comp (Subst.openPath q)))
          = .ty ((T'.subst σ.lift).open q) from by
        simp only [Tau.subst]; rw [← Ty.subst_comp]; rfl] at ih
    exact ih k ℓ2 (hOp q hq k)
  · rename_i s' Θ' Γ' S S' T1 T2 T1' T2' A h1 h2 ih1 ih2
    intro Ξ hp σ hh hok hσ n ℓ hd
    simp only [Ty.subst, Den] at hd ⊢
    obtain ⟨ℓ1, W, hlk, hsubS, hS, hsand⟩ := hd
    have h1σ := h1.subst hσ.conforms
    simp only [Tau.subst] at h1σ
    have hq1 : ℓ1 < Θ'.length := by
      obtain ⟨-, -, -, -, hb⟩ := hh.lookup_heap hlk
      have hlt := (List.getElem?_eq_some_iff.mp hlk).1
      rw [hh.1]
      exact Nat.lt_trans hb.1 hlt
    refine ⟨ℓ1, W, hlk, .trans hsubS h1σ,
            fun k => ih1 hh hok hσ k ℓ1 (hS k), ?_⟩
    cases n with
    | zero => trivial
    | succ n0 =>
      intro q hq y
      have hqwf := PathEval.to_wf hh hq hq1
      have hqsub := Sub.trans (hq.to_sub hh) hsubS
      have hσq := SemSubst.extend hσ hq hqwf hqsub hS
      have ih := ih2 hh hok hσq
      rw [show ((Tau.intv T1 T2).subst ((σ.lift).comp (Subst.openPath q)))
            = .intv ((T1.subst σ.lift).open q) ((T2.subst σ.lift).open q) from by
          simp only [Tau.subst]; rw [← Ty.subst_comp, ← Ty.subst_comp]; rfl,
         show ((Tau.intv T1' T2').subst ((σ.lift).comp (Subst.openPath q)))
            = .intv ((T1'.subst σ.lift).open q) ((T2'.subst σ.lift).open q) from by
          simp only [Tau.subst]; rw [← Ty.subst_comp, ← Ty.subst_comp]; rfl] at ih
      constructor
      · intro hy
        exact (hsand q hq y).1 (ih.1 n0 y hy)
      · intro hy
        exact ih.2 n0 y ((hsand q hq y).2 hy)
  · rename_i h1 h2 h3u ih1 ih2 ih3u
    intro Ξ hp σ hh hok hσ
    exact ⟨fun n ℓ hd => ih1 hh hok hσ n ℓ hd,
           fun n ℓ hd => ih2 hh hok hσ n ℓ hd⟩
  · -- repl: semantic transfer through co-evaluating openings
    rename_i hwp hwq h1 h2 ihwp ihwq ih1 ih2
    intro Ξ hp σ hh hok hσ n ℓ hd
    obtain ⟨mp, hevp⟩ := ihwp hh hok hσ
    have hq' := ih1 hh hok hσ 0 mp (by simp only [Ty.subst, Den]; exact hevp)
    simp only [Ty.subst, Den] at hq'
    have hwp' := hwp.subst hσ.conforms
    have hwq' := hwq.subst hσ.conforms
    rw [← Ty.open_subst_comm] at hd
    rw [← Ty.open_subst_comm]
    exact Den.open_coeval hh hok _ _ (Nat.le_refl _) hevp hq' hwp' hwq' n ℓ hd
  · -- skip_tm
    rename_i h1 hne ih1
    intro Ξ hp σ hh hok hσ n ℓcand hd
    simp only [Ty.subst, Den] at hd ⊢
    cases hd with
    | sel hev hlk =>
      have ih := ih1 hh hok hσ 0 _ (by simp only [Ty.subst, Den]; exact hev)
      simp only [Ty.subst, Den] at ih
      obtain ⟨ℓ1', ℓ2', hlk', -, -, -⟩ := ih
      have heq := Option.some.inj (hlk.symm.trans hlk')
      injection heq with _ _ hab _
      exact absurd hab hne
    | sel_skip_tm hev hlk hne' hin => exact hin
    | sel_skip_ty hev hlk hin =>
      have ih := ih1 hh hok hσ 0 _ (by simp only [Ty.subst, Den]; exact hev)
      simp only [Ty.subst, Den] at ih
      obtain ⟨ℓ1', ℓ2', hlk', -, -, -⟩ := ih
      cases Option.some.inj (hlk.symm.trans hlk')
  · -- skip_ty
    rename_i h1 ih1
    intro Ξ hp σ hh hok hσ n ℓcand hd
    simp only [Ty.subst, Den] at hd ⊢
    cases hd with
    | sel hev hlk =>
      have ih := ih1 hh hok hσ 0 _ (by simp only [Ty.subst, Den]; exact hev)
      simp only [Ty.subst, Den] at ih
      obtain ⟨ℓ1', W', hlk', -, -, -⟩ := ih
      cases Option.some.inj (hlk.symm.trans hlk')
    | sel_skip_tm hev hlk hne' hin =>
      have ih := ih1 hh hok hσ 0 _ (by simp only [Ty.subst, Den]; exact hev)
      simp only [Ty.subst, Den] at ih
      obtain ⟨ℓ1', W', hlk', -, -, -⟩ := ih
      cases Option.some.inj (hlk.symm.trans hlk')
    | sel_skip_ty hev hlk hin => exact hin
  · rename_i x T hx
    intro Ξ hp σ hh hok hσ
    obtain ⟨m, hev, -⟩ := hσ.realized hx
    exact ⟨m, hev⟩
  · intro Ξ hp σ hh hok hσ
    exact ⟨_, .var⟩
  · intros
    rename_i h1 hsub ih1 ihsub Ξx hpx σx hh hok hσ
    obtain ⟨mid, hev⟩ := ih1 hh hok hσ
    have ih := ihsub hh hok hσ 0 mid (by simp only [Ty.subst, Den]; exact hev)
    simp only [Ty.subst, Den] at ih
    obtain ⟨ℓ1, ℓ2, hlk, -, -, -⟩ := ih
    exact ⟨ℓ1, .fst_tm hev hlk⟩
  · intros
    rename_i h1 hsub ih1 ihsub Ξx hpx σx hh hok hσ
    obtain ⟨mid, hev⟩ := ih1 hh hok hσ
    have ih := ihsub hh hok hσ 0 mid (by simp only [Ty.subst, Den]; exact hev)
    simp only [Ty.subst, Den] at ih
    obtain ⟨ℓ1, W, hlk, -, -, -⟩ := ih
    exact ⟨ℓ1, .fst_ty hev hlk⟩
  · intros
    rename_i h1 hsub ih1 ihsub Ξx hpx σx hh hok hσ
    obtain ⟨mid, hev⟩ := ih1 hh hok hσ
    have ih := ihsub hh hok hσ 0 mid (by simp only [Ty.subst, Den]; exact hev)
    simp only [Ty.subst, Den] at ih
    obtain ⟨ℓ1, ℓ2, hlk, -, -, -⟩ := ih
    exact ⟨ℓ2, .sel hev hlk⟩
  · intros
    rename_i h1 hsub hne ih1 ihsub Ξx hpx σx hh hok hσ
    obtain ⟨m, hin⟩ := ih1 hh hok hσ
    exact PathEval.sel_from_skip hin
  · intros
    rename_i h1 hsub ih1 ihsub Ξx hpx σx hh hok hσ
    obtain ⟨m, hin⟩ := ih1 hh hok hσ
    exact PathEval.sel_from_skip hin

/-- Wellformed paths evaluate, under realized closing substitutions. -/
theorem Path.Wf.den_eval {Θ : Sto} {Γ : Ctx s} {p : Path s} (hw : Path.Wf Θ Γ p) :
    ∀ {Ξ : SemSto} {h : Heap} {σ : Subst s 0},
      HeapTyped Θ h -> SemStoOk Θ Ξ h -> SemSubst Θ Ξ h σ Γ ->
      ∃ m, PathEval h (p.subst σ) m := by
  induction hw using Path.Wf.rec (motive_1 := fun _ _ _ _ _ => True)
  all_goals try (intros; exact trivial)
  · rename_i hx
    intro Ξ hp σ hh hok hσ
    obtain ⟨m, hev, -⟩ := hσ.realized hx
    exact ⟨m, hev⟩
  · intro Ξ hp σ hh hok hσ
    exact ⟨_, .var⟩
  · intros
    rename_i h1 hsub ih1 ihT Ξx hpx σx hh hok hσ
    obtain ⟨mid, hev⟩ := ih1 hh hok hσ
    have ih := Sub.den hsub hh hok hσ 0 mid (by simp only [Ty.subst, Den]; exact hev)
    simp only [Ty.subst, Den] at ih
    obtain ⟨ℓ1, ℓ2, hlk, -, -, -⟩ := ih
    exact ⟨ℓ1, .fst_tm hev hlk⟩
  · intros
    rename_i h1 hsub ih1 ihT Ξx hpx σx hh hok hσ
    obtain ⟨mid, hev⟩ := ih1 hh hok hσ
    have ih := Sub.den hsub hh hok hσ 0 mid (by simp only [Ty.subst, Den]; exact hev)
    simp only [Ty.subst, Den] at ih
    obtain ⟨ℓ1, W, hlk, -, -, -⟩ := ih
    exact ⟨ℓ1, .fst_ty hev hlk⟩
  · intros
    rename_i h1 hsub ih1 ihT Ξx hpx σx hh hok hσ
    obtain ⟨mid, hev⟩ := ih1 hh hok hσ
    have ih := Sub.den hsub hh hok hσ 0 mid (by simp only [Ty.subst, Den]; exact hev)
    simp only [Ty.subst, Den] at ih
    obtain ⟨ℓ1, ℓ2, hlk, -, -, -⟩ := ih
    exact ⟨ℓ2, .sel hev hlk⟩
  · intros
    rename_i h1 hsub hne ih1 ihT Ξx hpx σx hh hok hσ
    obtain ⟨m, hin⟩ := ih1 hh hok hσ
    exact PathEval.sel_from_skip hin
  · intros
    rename_i h1 hsub ih1 ihT Ξx hpx σx hh hok hσ
    obtain ⟨m, hin⟩ := ih1 hh hok hσ
    exact PathEval.sel_from_skip hin

end LambdaP
