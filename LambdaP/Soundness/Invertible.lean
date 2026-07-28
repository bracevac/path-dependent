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
    (_hh : HeapTyped Θ h) (hi : Inv Θ ℓ (.arrow S T)) :
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

/-! ### Interval inversion -/

/-- Forward interval tracking: a subtyping derivation from an interval
ends at an interval, with componentwise residues (contravariant lower,
covariant upper). Intervals only arise from refl, trans, and ival. -/
theorem Sub.intv_main {Θ : Sto} {Γ : Ctx s} {τ1 τ2 : Tau s}
    (hs : Sub Θ Γ τ1 τ2) :
    ∀ A B, τ1 = .intv A B →
      ∃ C D, τ2 = .intv C D ∧ Sub Θ Γ (.ty C) (.ty A) ∧ Sub Θ Γ (.ty B) (.ty D) := by
  induction hs using Sub.rec (motive_2 := fun {s} Θ Γ p _ => True)
  · intro A B hE
    exact ⟨A, B, hE, .refl, .refl⟩
  · rename_i h1 h2 ih1 ih2
    intro A B hE
    obtain ⟨E, F, hmid, h1a, h1b⟩ := ih1 A B hE
    obtain ⟨C, D, hend, h2a, h2b⟩ := ih2 E F hmid
    exact ⟨C, D, hend, .trans h2a h1a, .trans h1b h2b⟩
  · intro A B hE; cases hE
  · intro A B hE; cases hE
  · intro A B hE; cases hE
  · intro A B hE; cases hE
  · intro A B hE; cases hE
  · intro A B hE; cases hE
  · intro A B hE; cases hE
  · intro A B hE; cases hE
  · intro A B hE; cases hE
  · intro A B hE; cases hE
  · intro A B hE; cases hE
  · intro A B hE; cases hE
  · intro A B hE; cases hE
  · rename_i h1 h2 h3 ih1 ih2 ih3
    intro A B hE
    cases hE
    exact ⟨_, _, rfl, h1, h2⟩
  · intro A B hE; cases hE
  · intro A B hE; cases hE
  · intro A B hE; cases hE
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-- Interval subtyping inverts componentwise. -/
theorem Sub.intv_inv {Θ : Sto} {Γ : Ctx s} {A B C D : Ty s}
    (hs : Sub Θ Γ (.intv A B) (.intv C D)) :
    Sub Θ Γ (.ty C) (.ty A) ∧ Sub Θ Γ (.ty B) (.ty D) := by
  obtain ⟨C', D', hE, h1, h2⟩ := hs.intv_main A B rfl
  cases hE
  exact ⟨h1, h2⟩

/-! ### Read-off: pairs -/

/-- A location with a possible term-member pair type stores that pair,
with a tight residue on the first component and a general residue under
it on the member. -/
theorem Inv.pairTm_inv {Θ : Sto} {h : Heap} {ℓ : Nat} {S : Ty 0}
    {a : Name} {T : Ty 1}
    (hh : HeapTyped Θ h) (hi : Inv Θ ℓ (.pairTm S a T)) :
    ∃ ℓ1 ℓ2, Sto.Lookup Θ ℓ
        (.pairTm (.single (.var (.free ℓ1))) a (Ty.single (.var (.free ℓ2))).weaken) ∧
      TightSub Θ (.ty (.single (.var (.free ℓ1)))) (.ty S) ∧
      Sub Θ (Ctx.empty.push (.single (.var (.free ℓ1))))
        (.ty (Ty.single (.var (.free ℓ2))).weaken) (.ty T) := by
  generalize hU : Ty.pairTm S a T = U at hi
  induction hi generalizing S T with
  | precise hl =>
    subst hU
    rcases HeapTyped.lookup_shape hh hl with ⟨_, _, he⟩ | ⟨ℓ1, a', ℓ2, he⟩ | ⟨_, _, _, he⟩ <;>
      cases he
    exact ⟨ℓ1, ℓ2, hl, .refl, .refl⟩
  | sngl _ => cases hU
  | top => cases hU
  | arrow_sub _ _ _ _ => cases hU
  | pair_tm_sub hi' ht hg ih =>
    cases hU
    obtain ⟨ℓ1, ℓ2, hl, ht', hg'⟩ := ih rfl
    exact ⟨ℓ1, ℓ2, hl, ht'.trans ht,
      .trans hg' (hg.narrow ht'.to_sub)⟩
  | pair_ty_sub _ _ _ _ => cases hU
  | tsel_intro _ _ _ _ => cases hU
  | open_repl hi' hcp hcq ih =>
    obtain ⟨S0, B0, hTt, hS, hB⟩ := Ty.open_eq_pairTm hU.symm
    subst hTt
    subst hS
    subst hB
    obtain ⟨ℓ1, ℓ2, hl, ht', hg'⟩ := ih rfl
    exact ⟨ℓ1, ℓ2, hl, ht'.trans (TightSub.repl hcp hcq),
      .trans hg' (Sub.repl_push hcp hcq)⟩

/-- A location with a possible type-member pair type stores that pair;
the declared interval sandwiches the stored alias. -/
theorem Inv.pairTy_inv {Θ : Sto} {h : Heap} {ℓ : Nat} {S : Ty 0}
    {A : Name} {T1 T2 : Ty 1}
    (hh : HeapTyped Θ h) (hi : Inv Θ ℓ (.pairTy S A T1 T2)) :
    ∃ (ℓ1 : Nat) (W : Ty 0), Sto.Lookup Θ ℓ
        (.pairTy (.single (.var (.free ℓ1))) A W.weaken W.weaken) ∧
      TightSub Θ (.ty (.single (.var (.free ℓ1)))) (.ty S) ∧
      Sub Θ (Ctx.empty.push (.single (.var (.free ℓ1))))
        (.ty T1) (.ty W.weaken) ∧
      Sub Θ (Ctx.empty.push (.single (.var (.free ℓ1))))
        (.ty W.weaken) (.ty T2) := by
  generalize hU : Ty.pairTy S A T1 T2 = U at hi
  induction hi generalizing S T1 T2 with
  | precise hl =>
    subst hU
    rcases HeapTyped.lookup_shape hh hl with ⟨_, _, he⟩ | ⟨_, _, _, he⟩ | ⟨ℓ1, A', W, he⟩ <;>
      cases he
    exact ⟨ℓ1, W, hl, .refl, .refl, .refl⟩
  | sngl _ => cases hU
  | top => cases hU
  | arrow_sub _ _ _ _ => cases hU
  | pair_tm_sub _ _ _ _ => cases hU
  | pair_ty_sub hi' ht hg ih =>
    cases hU
    obtain ⟨ℓ1, W, hl, ht', hlo', hhi'⟩ := ih rfl
    obtain ⟨hlo, hhi⟩ := hg.intv_inv
    exact ⟨ℓ1, W, hl, ht'.trans ht,
      .trans (hlo.narrow ht'.to_sub) hlo',
      .trans hhi' (hhi.narrow ht'.to_sub)⟩
  | tsel_intro _ _ _ _ => cases hU
  | open_repl hi' hcp hcq ih =>
    obtain ⟨S0, C1, C2, hTt, hS, hB1, hB2⟩ := Ty.open_eq_pairTy hU.symm
    subst hTt
    subst hS
    subst hB1
    subst hB2
    obtain ⟨ℓ1, W, hl, ht', hlo', hhi'⟩ := ih rfl
    exact ⟨ℓ1, W, hl, ht'.trans (TightSub.repl hcp hcq),
      .trans (Sub.repl_push hcq hcp) hlo',
      .trans hhi' (Sub.repl_push hcp hcq)⟩

/-! ### Read-off: singletons, selections, bottom -/

theorem Ty.open_eq_single {T : Ty 1} {q : Path 0} {r : Path 0}
    (he : T.open q = .single r) :
    ∃ P0, T = .single P0 ∧ r = P0.subst (Subst.openPath q) := by
  cases T with
  | single P0 =>
    simp only [Ty.open, Ty.subst] at he
    injection he with hs h1
    exact ⟨P0, rfl, h1.symm⟩
  | top => cases he
  | bot => cases he
  | arrow _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTm _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTy _ _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | tsel _ _ => simp only [Ty.open, Ty.subst] at he; cases he

theorem Ty.open_eq_tsel {T : Ty 1} {q : Path 0} {r : Path 0} {A : Name}
    (he : T.open q = .tsel r A) :
    ∃ P0, T = .tsel P0 A ∧ r = P0.subst (Subst.openPath q) := by
  cases T with
  | tsel P0 A0 =>
    simp only [Ty.open, Ty.subst] at he
    injection he with hs h1 h2
    subst h2
    exact ⟨P0, rfl, h1.symm⟩
  | top => cases he
  | bot => cases he
  | arrow _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTm _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTy _ _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | single _ => simp only [Ty.open, Ty.subst] at he; cases he

theorem Ty.open_eq_bot {T : Ty 1} {q : Path 0}
    (he : T.open q = .bot) : T = .bot := by
  cases T with
  | bot => rfl
  | top => cases he
  | single _ => simp only [Ty.open, Ty.subst] at he; cases he
  | tsel _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | arrow _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTm _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he
  | pairTy _ _ _ _ => simp only [Ty.open, Ty.subst] at he; cases he

/-- Pointwise co-resolution of two closing substitutions. -/
def CoChains (Θ : Sto) (σ1 σ2 : Subst s 0) : Prop :=
  ∀ (x : BVar s) (m : Nat), Chains Θ (σ1.var x) m ↔ Chains Θ (σ2.var x) m

/-- Resolution of a substituted path only depends on the targets of the
substituted-in paths (store-side mirror of `PathEval.subst_congr`). -/
theorem Chains.subst_congr {Θ : Sto} {σ1 σ2 : Subst s 0}
    (hco : CoChains Θ σ1 σ2) :
    ∀ {p : Path s} {m : Nat},
      Chains Θ (p.subst σ1) m -> Chains Θ (p.subst σ2) m := by
  intro p m he
  generalize hE : p.subst σ1 = r at he
  induction he generalizing p with
  | loc hl =>
    match p, hE with
    | .var (.bound b), hE =>
      exact (hco b _).mp (by show Chains Θ ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .loc hl)
    | .var (.free n), hE =>
      cases hE
      exact .loc hl
  | fst_tm he' hl ih =>
    match p, hE with
    | .var (.bound b), hE =>
      exact (hco b _).mp (by show Chains Θ ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .fst_tm he' hl)
    | .var (.free n), hE => cases hE
    | .fst p', hE =>
      simp only [Path.subst] at hE
      cases hE
      exact .fst_tm (ih (p := p') rfl) hl
  | fst_ty he' hl ih =>
    match p, hE with
    | .var (.bound b), hE =>
      exact (hco b _).mp (by show Chains Θ ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .fst_ty he' hl)
    | .var (.free n), hE => cases hE
    | .fst p', hE =>
      simp only [Path.subst] at hE
      cases hE
      exact .fst_ty (ih (p := p') rfl) hl
  | sel he' hl ih =>
    match p, hE with
    | .var (.bound b), hE =>
      exact (hco b _).mp (by show Chains Θ ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .sel he' hl)
    | .var (.free n), hE => cases hE
    | .sel p' a', hE =>
      simp only [Path.subst] at hE
      cases hE
      exact .sel (ih (p := p') rfl) hl
  | sel_skip_tm hp hl hne hin ihp ihin =>
    match p, hE with
    | .var (.bound b), hE =>
      exact (hco b _).mp (by show Chains Θ ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .sel_skip_tm hp hl hne hin)
    | .var (.free n), hE => cases hE
    | .sel p' a', hE =>
      simp only [Path.subst] at hE
      cases hE
      exact .sel_skip_tm (ihp (p := p') rfl) hl hne
        (ihin (p := (Path.fst p').sel _) (by simp only [Path.subst]))
  | sel_skip_ty hp hl hin ihp ihin =>
    match p, hE with
    | .var (.bound b), hE =>
      exact (hco b _).mp (by show Chains Θ ((Path.var (Var.bound b)).subst σ1) _; rw [hE]; exact .sel_skip_ty hp hl hin)
    | .var (.free n), hE => cases hE
    | .sel p' a', hE =>
      simp only [Path.subst] at hE
      cases hE
      exact .sel_skip_ty (ihp (p := p') rfl) hl
        (ihin (p := (Path.fst p').sel _) (by simp only [Path.subst]))

/-- Co-resolution of the two opening substitutions of co-resolving
opener paths. -/
theorem CoChains.openPath {Θ : Sto} {q q' : Path 0} {ℓq : Nat}
    (hq : Chains Θ q ℓq) (hq' : Chains Θ q' ℓq) :
    CoChains Θ (Subst.openPath q) (Subst.openPath q') := by
  intro x m
  cases x with
  | here =>
    constructor
    · intro he
      cases Chains.deterministic he hq
      exact hq'
    · intro he
      cases Chains.deterministic he hq'
      exact hq
  | there b => exact nomatch b

/-- Resolution of an opened path only depends on the target of the
opening path (the store-side mirror of `PathEval.open_congr`). -/
theorem Chains.open_congr {Θ : Sto} {q q' : Path 0} {ℓq : Nat}
    (hq : Chains Θ q ℓq) (hq' : Chains Θ q' ℓq) :
    ∀ {p : Path 1} {m : Nat},
      Chains Θ (p.subst (Subst.openPath q)) m ->
      Chains Θ (p.subst (Subst.openPath q')) m :=
  fun he => Chains.subst_congr (CoChains.openPath hq hq') he

/-- A location with a possible singleton type is the path's target. -/
theorem Inv.single_inv {Θ : Sto} {h : Heap} {ℓ : Nat} {q : Path 0}
    (hh : HeapTyped Θ h) (hi : Inv Θ ℓ (.single q)) :
    Chains Θ q ℓ := by
  generalize hU : Ty.single q = U at hi
  induction hi generalizing q with
  | precise hl =>
    subst hU
    rcases HeapTyped.lookup_shape hh hl with ⟨_, _, he⟩ | ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩ <;>
      cases he
  | sngl hc => cases hU; exact hc
  | top => cases hU
  | arrow_sub _ _ _ _ => cases hU
  | pair_tm_sub _ _ _ _ => cases hU
  | pair_ty_sub _ _ _ _ => cases hU
  | tsel_intro _ _ _ _ => cases hU
  | open_repl hi' hcp hcq ih =>
    obtain ⟨P0, hTt, hr⟩ := Ty.open_eq_single hU.symm
    subst hTt
    subst hr
    exact Chains.open_congr hcp hcq (ih rfl)

/-- A location with a possible selection type: the selected path chains
to a stored type-member pair whose alias is itself possible. -/
theorem Inv.tsel_inv {Θ : Sto} {h : Heap} {ℓ : Nat} {q : Path 0} {A : Name}
    (hh : HeapTyped Θ h) (hi : Inv Θ ℓ (.tsel q A)) :
    ∃ (m ℓ1 : Nat) (W : Ty 0), Chains Θ q m ∧
      Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A W.weaken W.weaken) ∧
      Inv Θ ℓ W := by
  generalize hU : Ty.tsel q A = U at hi
  induction hi generalizing q with
  | precise hl =>
    subst hU
    rcases HeapTyped.lookup_shape hh hl with ⟨_, _, he⟩ | ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩ <;>
      cases he
  | sngl _ => cases hU
  | top => cases hU
  | arrow_sub _ _ _ _ => cases hU
  | pair_tm_sub _ _ _ _ => cases hU
  | pair_ty_sub _ _ _ _ => cases hU
  | tsel_intro hc hl hiW _ =>
    cases hU
    exact ⟨_, _, _, hc, hl, hiW⟩
  | open_repl hi' hcp hcq ih =>
    obtain ⟨P0, hTt, hr⟩ := Ty.open_eq_tsel hU.symm
    subst hTt
    subst hr
    obtain ⟨m, ℓ1, W, hc, hl, hiW⟩ := ih rfl
    exact ⟨m, ℓ1, W, Chains.open_congr hcp hcq hc, hl, hiW⟩

/-- No location has possible type ⊥. -/
theorem Inv.bot_elim {Θ : Sto} {h : Heap} {ℓ : Nat}
    (hh : HeapTyped Θ h) (hi : Inv Θ ℓ .bot) : False := by
  generalize hU : (Ty.bot : Ty 0) = U at hi
  induction hi with
  | precise hl =>
    subst hU
    rcases HeapTyped.lookup_shape hh hl with ⟨_, _, he⟩ | ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩ <;>
      cases he
  | sngl _ => cases hU
  | top => cases hU
  | arrow_sub _ _ _ _ => cases hU
  | pair_tm_sub _ _ _ _ => cases hU
  | pair_ty_sub _ _ _ _ => cases hU
  | tsel_intro _ _ _ _ => cases hU
  | open_repl hi' hcp hcq ih =>
    have hTt := Ty.open_eq_bot hU.symm
    subst hTt
    exact ih rfl

/-! ### The closure lemma: possible types are closed under tight steps -/

/-- Weakening of types is injective (open any weakened type to recover it). -/
theorem Ty.weaken_inj {T1 T2 : Ty s} (h : T1.weaken = T2.weaken) : T1 = T2 := by
  have := congrArg (fun X => Ty.open X (.var (.free 0))) h
  simpa [Ty.weaken_open] using this

/-- Possible types at the generalized-type level (intervals carry no
membership content). -/
def InvTau (Θ : Sto) (ℓ : Nat) : Tau 0 -> Prop
| .ty U => Inv Θ ℓ U
| .intv _ _ => True

/-- Closure: tight subtyping preserves possible types. -/
theorem TightSub.inv_closure {Θ : Sto} {h : Heap} (hh : HeapTyped Θ h)
    {τ1 τ2 : Tau 0} (ht : TightSub Θ τ1 τ2) :
    ∀ ℓ, InvTau Θ ℓ τ1 -> InvTau Θ ℓ τ2 := by
  induction ht with
  | refl => exact fun _ hi => hi
  | trans _ _ ih1 ih2 => exact fun ℓ hi => ih2 ℓ (ih1 ℓ hi)
  | bot => exact fun ℓ hi => absurd hi (fun hi => Inv.bot_elim hh hi)
  | top => exact fun ℓ _ => .top
  | var_free hl =>
    intro ℓ' hi
    have hc := Inv.single_inv hh hi
    cases hc with
    | loc _ =>
      show Inv _ _ _
      rw [Ty.fromClosed_zero]
      exact .precise hl
  | symm hc _ ih =>
    intro ℓ' hi
    have hcq' := Inv.single_inv hh hi
    have hcq := Inv.single_inv hh (ih _ (.sngl hc))
    cases Chains.deterministic hcq' hcq
    exact .sngl hc
  | fst_tm hc hl =>
    intro ℓ' hi
    have hcf := Inv.single_inv hh hi
    cases hcf with
    | fst_tm hc' hl' =>
      cases Chains.deterministic hc' hc
      have heq := Option.some_inj.mp ((Eq.symm hl').trans hl)
      injection heq with hs h1 h2 h3
      cases h1
      have hm := (List.getElem?_eq_some_iff.mp hl).1
      have hlt := Nat.lt_trans ((hh.2 hl).1).1 hm
      obtain ⟨T1, hl1⟩ := Sto.lookup_lt hlt
      exact .sngl (.loc hl1)
    | fst_ty hc' hl' =>
      cases Chains.deterministic hc' hc
      have heq := Option.some_inj.mp ((Eq.symm hl').trans hl)
      cases heq
  | fst_ty hc hl =>
    intro ℓ' hi
    have hcf := Inv.single_inv hh hi
    cases hcf with
    | fst_tm hc' hl' =>
      cases Chains.deterministic hc' hc
      have heq := Option.some_inj.mp ((Eq.symm hl').trans hl)
      cases heq
    | fst_ty hc' hl' =>
      cases Chains.deterministic hc' hc
      have heq := Option.some_inj.mp ((Eq.symm hl').trans hl)
      injection heq with hs h1 h2 h3 h4
      cases h1
      have hm := (List.getElem?_eq_some_iff.mp hl).1
      have hlt := Nat.lt_trans ((hh.2 hl).1).1 hm
      obtain ⟨T1, hl1⟩ := Sto.lookup_lt hlt
      exact .sngl (.loc hl1)
  | sel_tm hc hl =>
    intro ℓ' hi
    have hcf := Inv.single_inv hh hi
    cases hcf with
    | sel hc' hl' =>
      cases Chains.deterministic hc' hc
      have heq := Option.some_inj.mp ((Eq.symm hl').trans hl)
      injection heq with hs h1 h2 h3
      have h3' := Ty.weaken_inj h3
      cases h3'
      have hm := (List.getElem?_eq_some_iff.mp hl).1
      have hlt := Nat.lt_trans (Ty.locsBelow_rename.mp ((hh.2 hl).1).2) hm
      obtain ⟨T1, hl1⟩ := Sto.lookup_lt hlt
      exact .sngl (.loc hl1)
    | sel_skip_tm hc' hl' hne' hin' =>
      cases Chains.deterministic hc' hc
      have heq := Option.some_inj.mp ((Eq.symm hl').trans hl)
      injection heq with hs h1 h2 h3
      exact absurd h2.symm hne'
    | sel_skip_ty hc' hl' hin' =>
      cases Chains.deterministic hc' hc
      cases Option.some_inj.mp ((Eq.symm hl').trans hl)
  | sel_hi hc hl =>
    intro ℓ' hi
    obtain ⟨m'', ℓ1'', W'', hc'', hl'', hiW⟩ := Inv.tsel_inv hh hi
    cases Chains.deterministic hc'' hc
    have heq := Option.some_inj.mp ((Eq.symm hl'').trans hl)
    injection heq with hs h1 h2 h3 h4
    cases Ty.weaken_inj h3
    exact hiW
  | sel_lo hc hl =>
    intro ℓ' hi
    exact .tsel_intro hc hl hi
  | arrow ht hg ih =>
    intro ℓ' hi
    exact .arrow_sub hi ht hg
  | pair_tm ht hg ih =>
    intro ℓ' hi
    exact .pair_tm_sub hi ht hg
  | pair_ty ht hg ih =>
    intro ℓ' hi
    exact .pair_ty_sub hi ht hg
  | ival _ _ _ _ _ _ => exact fun _ _ => trivial
  | repl hcp hcq =>
    intro ℓ' hi
    exact .open_repl hi hcp hcq

end LambdaP
