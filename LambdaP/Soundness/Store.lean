import LambdaP.Lemmas.Subst

/-!
Store correspondence: connects big-step path evaluation with subtyping.

The central fact is `PathEval.to_sub`: in a well-typed heap, a path is a
mutual subtype (via `Sub.symm`) of the location it evaluates to. This is
the syntactic counterpart of "path reduction is built into type equality"
from the paper, and it hinges on stored values having *precise* singleton
pair types.
-/

namespace LambdaP

/-- Nothing is bound in the empty context. -/
theorem Ctx.LookupVar.empty_elim {x : BVar 0} {T : Ty 0}
    (h : Ctx.LookupVar .empty x T) : False :=
  nomatch h

/-- At scope 0, the closed-type embedding is the identity. -/
theorem Ty.fromClosed_zero {T : Ty 0} : (T.fromClosed : Ty 0) = T := by
  rw [Ty.fromClosed, ← Rename.fromZero_unique Rename.id, Ty.rename_id]

/-- In a well-typed heap, every stored value has a recorded precise type,
and value and type mention only earlier locations. -/
theorem HeapTyped.lookup_heap {Θ : Sto} {h : Heap} (hh : HeapTyped Θ h)
    {ℓ : Nat} {v : Tm 0} (hl : Heap.Lookup h ℓ v) :
    ∃ T, Sto.Lookup Θ ℓ T ∧ Val.PreciseTy Θ v T
      ∧ T.LocsBelow ℓ ∧ v.LocsBelow ℓ := by
  obtain ⟨hlen, hmap⟩ := hh
  have hlt : ℓ < h.length := (List.getElem?_eq_some_iff.mp hl).1
  have hltΘ : ℓ < Θ.length := by rw [hlen]; exact hlt
  have hT : Sto.Lookup Θ ℓ Θ[ℓ] := List.getElem?_eq_getElem hltΘ
  obtain ⟨hTb, v', hv', hvb, hpre⟩ := hmap hT
  have hveq : v' = v := Option.some.inj (hv'.symm.trans hl)
  subst hveq
  exact ⟨Θ[ℓ], hT, hpre, hTb, hvb⟩

/-- A typed heap is bounded (acyclic). -/
theorem HeapTyped.bounded {Θ : Sto} {h : Heap} (hh : HeapTyped Θ h) :
    Heap.Bounded h := by
  intro ℓ v hl
  obtain ⟨-, -, -, -, hvb⟩ := hh.lookup_heap hl
  exact hvb

/-- Heap path evaluation resolves through the store typing, provided the
target is recorded (the bare-location case needs the entry; every
composite case supplies its own from the heap lookup). -/
theorem PathEval.to_chains {Θ : Sto} {h : Heap} (hh : HeapTyped Θ h)
    {p : Path 0} {ℓ : Nat} (he : PathEval h p ℓ)
    (hend : ∃ T, Sto.Lookup Θ ℓ T) : Chains Θ p ℓ := by
  induction he with
  | var => obtain ⟨T, hT⟩ := hend; exact .loc hT
  | fst_tm hp hl ih =>
    obtain ⟨T, hΘ, hpre, -, -⟩ := hh.lookup_heap hl
    cases hpre with
    | pair_tm _ _ => exact .fst_tm (ih ⟨_, hΘ⟩) hΘ
  | fst_ty hp hl ih =>
    obtain ⟨T, hΘ, hpre, -, -⟩ := hh.lookup_heap hl
    cases hpre with
    | pair_ty _ _ => exact .fst_ty (ih ⟨_, hΘ⟩) hΘ
  | sel hp hl ih =>
    obtain ⟨T, hΘ, hpre, -, -⟩ := hh.lookup_heap hl
    cases hpre with
    | pair_tm _ _ => exact .sel (ih ⟨_, hΘ⟩) hΘ
  | sel_skip_tm hp hl hne _ ihp ihin =>
    obtain ⟨T, hΘ, hpre, -, -⟩ := hh.lookup_heap hl
    cases hpre with
    | pair_tm _ _ => exact .sel_skip_tm (ihp ⟨_, hΘ⟩) hΘ hne (ihin hend)
  | sel_skip_ty hp hl _ ihp ihin =>
    obtain ⟨T, hΘ, hpre, -, -⟩ := hh.lookup_heap hl
    cases hpre with
    | pair_ty _ _ => exact .sel_skip_ty (ihp ⟨_, hΘ⟩) hΘ (ihin hend)

/-- A path is a subtype of (the singleton of) the location it evaluates to.
By `Sub.symm`, they are mutual subtypes. -/
theorem PathEval.to_sub {Θ : Sto} {h : Heap} (hh : HeapTyped Θ h)
    {p : Path 0} {ℓ : Nat} (he : PathEval h p ℓ) :
    Sub Θ .empty (.ty (.single p)) (.ty (.single (.var (.free ℓ)))) := by
  induction he with
  | var => exact .refl
  | fst_tm _ hl ih =>
    obtain ⟨T, hΘ, hpre, -, -⟩ := hh.lookup_heap hl
    cases hpre with
    | pair_tm _ _ =>
      have hloc := Sub.var_free (Θ := Θ) (Γ := Ctx.empty) hΘ
      rw [Ty.fromClosed_zero] at hloc
      exact .fst_tm (.trans ih hloc)
  | fst_ty _ hl ih =>
    obtain ⟨T, hΘ, hpre, -, -⟩ := hh.lookup_heap hl
    cases hpre with
    | pair_ty _ _ =>
      have hloc := Sub.var_free (Θ := Θ) (Γ := Ctx.empty) hΘ
      rw [Ty.fromClosed_zero] at hloc
      exact .fst_ty (.trans ih hloc)
  | sel hp hl ih =>
    obtain ⟨T, hΘ, hpre, -, -⟩ := hh.lookup_heap hl
    cases hpre with
    | pair_tm _ _ => exact Sub.sel_tm_loc (hp.to_chains hh ⟨_, hΘ⟩) hΘ
  | sel_skip_tm hp hl hne _ ihp ihin =>
    obtain ⟨T, hΘ, hpre, -, -⟩ := hh.lookup_heap hl
    cases hpre with
    | pair_tm _ _ =>
      exact .trans (Sub.skip_tm_loc (hp.to_chains hh ⟨_, hΘ⟩) hΘ hne) ihin
  | sel_skip_ty hp hl _ ihp ihin =>
    obtain ⟨T, hΘ, hpre, -, -⟩ := hh.lookup_heap hl
    cases hpre with
    | pair_ty _ _ =>
      exact .trans (Sub.skip_ty_loc (hp.to_chains hh ⟨_, hΘ⟩) hΘ) ihin

/-- Inversion for path typing: a typed path is wellformed and its singleton
is below the ascribed type. -/
theorem HasType.path_inv {Θ} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : HasType Θ Γ t T) :
    ∀ {q : Path s}, t = .path q -> Path.Wf Θ Γ q ∧ Sub Θ Γ (.ty (.single q)) (.ty T) := by
  induction h with
  | path hp =>
    intro q hq
    cases hq
    exact ⟨hp, .refl⟩
  | sub _ hsub _ ih =>
    intro q hq
    obtain ⟨hwf, hs⟩ := ih hq
    exact ⟨hwf, .trans hs hsub⟩
  | abs _ _ _ => intro _ hq; cases hq
  | app _ _ _ _ => intro _ hq; cases hq
  | pair_tm _ _ => intro _ hq; cases hq
  | pair_ty _ _ => intro _ hq; cases hq
  | letin _ _ _ _ _ => intro _ hq; cases hq
  | typed _ _ _ => intro _ hq; cases hq

/- Regularity (the type of a well-typed term is wellformed) is deferred:
its `app` case opens the codomain with a possibly location-rooted
argument, which needs the realized (post-pushback) substitution layer.
Unconsumed; re-derive after the runtime substitution lemma lands. -/

end LambdaP
