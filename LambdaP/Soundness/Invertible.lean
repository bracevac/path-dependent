import LambdaP.Soundness.Tight

/-!
Invertible possible types (the ⊢##-analogue): which types a heap
location can be assigned by runtime subtyping chains. Closure
constructors carry tight residues at the empty context and general
residues under binders; `open_repl` closes under replacement of
co-chaining paths. Read-off lemmas peel constructors down to the
precise store entry.
-/

namespace LambdaP

/-- Possible types of a location. -/
inductive Inv (Θ : Sto) : Nat -> Ty 0 -> Prop where
| precise :
  Sto.Lookup Θ ℓ T ->
  Inv Θ ℓ T
| sngl :
  Chains Θ q ℓ ->
  Inv Θ ℓ (.single q)
| top :
  Inv Θ ℓ .top
| arrow_sub :
  Inv Θ ℓ (.arrow T0 T1) ->
  TightSub Θ (.ty S) (.ty T0) ->
  Sub Θ (Ctx.empty.push S) (.ty T1) (.ty T) ->
  Inv Θ ℓ (.arrow S T)
| pair_tm_sub :
  Inv Θ ℓ (.pairTm S a T) ->
  TightSub Θ (.ty S) (.ty S') ->
  Sub Θ (Ctx.empty.push S) (.ty T) (.ty T') ->
  Inv Θ ℓ (.pairTm S' a T')
| pair_ty_sub :
  Inv Θ ℓ (.pairTy S A T1 T2) ->
  TightSub Θ (.ty S) (.ty S') ->
  Sub Θ (Ctx.empty.push S) (.intv T1 T2) (.intv T1' T2') ->
  Inv Θ ℓ (.pairTy S' A T1' T2')
| tsel_intro :
  Chains Θ q m ->
  Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A W.weaken W.weaken) ->
  Inv Θ ℓ W ->
  Inv Θ ℓ (.tsel q A)
| open_repl :
  Inv Θ ℓ (Ty.open T p) ->
  Chains Θ p ℓ0 ->
  Chains Θ q ℓ0 ->
  Inv Θ ℓ (Ty.open T q)

/-! ### Shape decomposition of opened types -/

theorem Ty.open_eq_arrow {T : Ty 1} {q : Path 0} {S : Ty 0} {B : Ty 1}
    (he : T.open q = .arrow S B) :
    ∃ S0 B0, T = .arrow S0 B0 ∧ S = S0.open q ∧
      B = B0.subst (Subst.openPath q).lift := by
  cases T with
  | arrow S0 B0 =>
    simp only [Ty.open, Ty.subst] at he
    injection he with hs h1 h2
    exact ⟨S0, B0, rfl, h1.symm, h2.symm⟩
  | top => cases he
  | bot => cases he
  | pairTm _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTy _ _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | single p => simp only [Ty.open, Ty.subst] at he; cases he
  | tsel p A => simp only [Ty.open, Ty.subst] at he; cases he

theorem Ty.open_eq_pairTm {T : Ty 1} {q : Path 0} {S : Ty 0} {a : Name} {B : Ty 1}
    (he : T.open q = .pairTm S a B) :
    ∃ S0 B0, T = .pairTm S0 a B0 ∧ S = S0.open q ∧
      B = B0.subst (Subst.openPath q).lift := by
  cases T with
  | pairTm S0 a0 B0 =>
    simp only [Ty.open, Ty.subst] at he
    injection he with hs h1 h2 h3
    subst h2
    exact ⟨S0, B0, rfl, h1.symm, h3.symm⟩
  | top => cases he
  | bot => cases he
  | arrow _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTy _ _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | single p => simp only [Ty.open, Ty.subst] at he; cases he
  | tsel p A => simp only [Ty.open, Ty.subst] at he; cases he

theorem Ty.open_eq_pairTy {T : Ty 1} {q : Path 0} {S : Ty 0} {A : Name} {B1 B2 : Ty 1}
    (he : T.open q = .pairTy S A B1 B2) :
    ∃ S0 C1 C2, T = .pairTy S0 A C1 C2 ∧ S = S0.open q ∧
      B1 = C1.subst (Subst.openPath q).lift ∧
      B2 = C2.subst (Subst.openPath q).lift := by
  cases T with
  | pairTy S0 A0 C1 C2 =>
    simp only [Ty.open, Ty.subst] at he
    injection he with hs h1 h2 h3 h4
    subst h2
    exact ⟨S0, C1, C2, rfl, h1.symm, h3.symm, h4.symm⟩
  | top => cases he
  | bot => cases he
  | arrow _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTm _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | single p => simp only [Ty.open, Ty.subst] at he; cases he
  | tsel p A => simp only [Ty.open, Ty.subst] at he; cases he

/-! ### Read-off: arrows -/

/-- Mutually-aliased singleton subtyping from two co-chaining paths. -/
theorem Chains.mutual_sub {Θ : Sto} {p q : Path 0} {ℓ0 : Nat}
    (hcp : Chains Θ p ℓ0) (hcq : Chains Θ q ℓ0) :
    Sub Θ .empty (.ty (.single p)) (.ty (.single q)) :=
  .trans hcp.to_sub (.symm hcq.wf hcq.to_sub)

/-- The pushed replacement instance: opened bodies of a binder transfer
across co-chaining paths in any pushed context. -/
theorem Sub.repl_push {Θ : Sto} {p q : Path 0} {ℓ0 : Nat} {S0 : Ty 0} {B0 : Ty 2}
    (hcp : Chains Θ p ℓ0) (hcq : Chains Θ q ℓ0) :
    Sub Θ (Ctx.empty.push S0)
      (.ty (B0.subst (Subst.openPath p).lift))
      (.ty (B0.subst (Subst.openPath q).lift)) := by
  have h := Sub.repl (T := B0.rename Rename.swap)
    (Γ := Ctx.empty.push S0)
    (hcp.wf.weaken) (hcq.wf.weaken)
    ((hcp.mutual_sub hcq).weaken) ((hcq.mutual_sub hcp).weaken)
  simp only [Path.weaken] at h
  rwa [Ty.swap_open_weaken, Ty.swap_open_weaken] at h

/-- A location whose possible types include a function type stores a λ
whose recorded signature relates: tight on the domain, general under
the domain on the codomain. -/
theorem Inv.arrow_inv {Θ : Sto} {h : Heap} {ℓ : Nat} {S : Ty 0} {T : Ty 1}
    (hh : HeapTyped Θ h) (hi : Inv Θ ℓ (.arrow S T)) :
    ∃ T0 T1, Sto.Lookup Θ ℓ (.arrow T0 T1) ∧
      TightSub Θ (.ty S) (.ty T0) ∧
      Sub Θ (Ctx.empty.push S) (.ty T1) (.ty T) := by
  generalize hU : Ty.arrow S T = U at hi
  induction hi generalizing S T with
  | precise hl =>
    cases hU
    exact ⟨S, T, hl, .refl, .refl⟩
  | sngl _ => cases hU
  | top => cases hU
  | arrow_sub hi' ht hg ih =>
    cases hU
    obtain ⟨T0, T1, hl, ht', hg'⟩ := ih rfl
    exact ⟨T0, T1, hl, ht.trans ht',
      .trans (hg'.narrow ht.to_sub) hg⟩
  | pair_tm_sub _ _ _ _ => cases hU
  | pair_ty_sub _ _ _ _ => cases hU
  | tsel_intro _ _ _ _ => cases hU
  | open_repl hi' hcp hcq ih =>
    obtain ⟨S0, B0, hTt, hS, hB⟩ := Ty.open_eq_arrow hU.symm
    subst hTt
    subst hS
    subst hB
    obtain ⟨T0, T1, hl, ht', hg'⟩ := ih rfl
    refine ⟨T0, T1, hl, ?_, ?_⟩
    · exact (TightSub.repl hcq hcp).trans ht'
    · have hnarrowed := hg'.narrow (TightSub.repl hcq hcp).to_sub
      exact .trans hnarrowed (Sub.repl_push hcp hcq)

end LambdaP
