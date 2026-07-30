import LambdaP.Soundness.Pushback

/-! The embedding: `Sub` at the empty context embeds into the sized
runtime judgment `SSub` — the collapse, made well-founded by scoping.
At scope 0 the evidence-shaped selection rules are vacuous (no bound
variables), so every empty-context derivation is already built from
the store-anchored and structural rules, which map 1:1 onto SSub.

Proof discipline (will recur in the P3 completeness proof): the joint
Sub/Path.Wf recursor with motive_2 := True; positional `·` bullets in
declaration order (named tags collide across the mutual block); per
case `intro h; rename_i ...; subst h`; sizes equalized with SSub.mono
at trans/repl. -/

namespace LambdaP

/-- Ctx 0 is structurally forced to be empty (re-homed from quarantined
Progress.lean). -/
theorem Ctx.eq_empty' (Γ : Ctx 0) : Γ = .empty := by
  cases Γ
  rfl

/-- At scope 0 no path is bound-var-rooted (BVar 0 is uninhabited),
so the evidence-shaped selection rules are vacuous. -/
theorem Path.root_not_isBound_zero (p : Path 0) : ¬ p.root.IsBound := by
  cases hv : p.root with
  | bound b => exact nomatch b
  | free ℓ => exact fun hb => hb

/-- The embedding motive at scope 0: ty-ty is the SSub existence goal,
intv-intv is trivial, mixed shapes are impossible (False), which bakes
tau-kind preservation into the induction (consumed at trans). -/
def EmbGoal0 : Sto -> Tau 0 -> Tau 0 -> Prop
  | Θ, .ty T1, .ty T2 => ∃ n, SSub Θ T1 T2 n
  | _, .intv _ _, .intv _ _ => True
  | _, _, _ => False

theorem Sub.to_ssub_aux {s : Sig} {Θ : Sto} {Γ : Ctx s} {τ1 τ2 : Tau s}
    (hs : Sub Θ Γ τ1 τ2) : ∀ (h : s = 0), EmbGoal0 Θ (h ▸ τ1) (h ▸ τ2) := by
  induction hs using Sub.rec (motive_2 := fun {s} Θ Γ p _ => True)
  -- refl
  · intro h
    rename_i τ
    subst h
    cases τ
    · exact ⟨1, .refl⟩
    · trivial
  -- trans
  · intro h
    rename_i τ1 τ2 τ3 h1 h2 ih1 ih2
    subst h
    have e1 := ih1 rfl
    have e2 := ih2 rfl
    cases τ1 <;> cases τ2 <;> cases τ3 <;>
      first
      | trivial
      | exact (e1 : False).elim
      | exact (e2 : False).elim
      | (obtain ⟨n1, hs1⟩ := e1
         obtain ⟨n2, hs2⟩ := e2
         exact ⟨max n1 n2 + 1,
           .trans (hs1.mono (Nat.le_max_left n1 n2))
                  (hs2.mono (Nat.le_max_right n1 n2))⟩)
  -- bot
  · intro h; subst h
    exact ⟨1, .bot⟩
  -- top
  · intro h; subst h
    exact ⟨1, .top⟩
  -- var_bound
  · intro h
    rename_i x T Θx hx
    subst h
    exact nomatch x
  -- var_free
  · intro h
    rename_i hl
    subst h
    exact ⟨1, .var_free hl⟩
  -- symm
  · intro h
    rename_i hw hsub ihw ih
    subst h
    have hE := Ctx.eq_empty' ‹Ctx 0›
    subst hE
    obtain ⟨n, hn⟩ := ih rfl
    exact ⟨n + 1, .symm hw hn⟩
  -- fst_tm
  · intro h
    rename_i hsub ih
    subst h
    obtain ⟨n, hn⟩ := ih rfl
    exact ⟨n + 1, .fst_tm hn⟩
  -- fst_ty
  · intro h
    rename_i hsub ih
    subst h
    obtain ⟨n, hn⟩ := ih rfl
    exact ⟨n + 1, .fst_ty hn⟩
  -- sel_tm (vacuous at scope 0)
  · intro h
    rename_i hr hsub ih
    subst h
    exact (Path.root_not_isBound_zero _ hr).elim
  -- sel_tm_loc
  · intro h
    rename_i hc hl
    subst h
    exact ⟨1, .sel_tm_loc hc hl⟩
  -- sel_hi (vacuous at scope 0)
  · intro h
    rename_i hr hw h1 h2 ihw ih1 ih2
    subst h
    exact (Path.root_not_isBound_zero _ hr).elim
  -- sel_lo (vacuous at scope 0)
  · intro h
    rename_i hr hw h1 h2 ihw ih1 ih2
    subst h
    exact (Path.root_not_isBound_zero _ hr).elim
  -- sel_hi_loc
  · intro h
    rename_i hc hl
    subst h
    exact ⟨2, .sel_hi_loc hc hl .refl⟩
  -- sel_lo_loc
  · intro h
    rename_i hc hl
    subst h
    exact ⟨2, .sel_lo_loc hc hl .refl⟩
  -- arrow
  · intro h
    rename_i h1 h2 ih1 ih2
    subst h
    have hE := Ctx.eq_empty' ‹Ctx 0›
    subst hE
    obtain ⟨n, hn⟩ := ih1 rfl
    exact ⟨n + 1, .arrow hn h2⟩
  -- pair_tm
  · intro h
    rename_i h1 h2 ih1 ih2
    subst h
    have hE := Ctx.eq_empty' ‹Ctx 0›
    subst hE
    obtain ⟨n, hn⟩ := ih1 rfl
    exact ⟨n + 1, .pair_tm hn h2⟩
  -- pair_ty
  · intro h
    rename_i h1 h2 h3 ih1 ih2 ih3
    subst h
    have hE := Ctx.eq_empty' ‹Ctx 0›
    subst hE
    obtain ⟨n, hn⟩ := ih1 rfl
    exact ⟨n + 1, .pair_ty hn h2 h3⟩
  -- repl
  · intro h
    rename_i hwp hwq h1 h2 ihwp ihwq ih1 ih2
    subst h
    have hE := Ctx.eq_empty' ‹Ctx 0›
    subst hE
    obtain ⟨n1, hs1⟩ := ih1 rfl
    obtain ⟨n2, hs2⟩ := ih2 rfl
    exact ⟨max n1 n2 + 1,
      .repl hwp hwq (hs1.mono (Nat.le_max_left n1 n2))
                    (hs2.mono (Nat.le_max_right n1 n2))⟩
  -- skip_tm (vacuous at scope 0)
  · intro h
    rename_i hr hsub hne ih
    subst h
    exact (Path.root_not_isBound_zero _ hr).elim
  -- skip_ty (vacuous at scope 0)
  · intro h
    rename_i hr hsub ih
    subst h
    exact (Path.root_not_isBound_zero _ hr).elim
  -- skip_tm_loc
  · intro h
    rename_i hc hl hne
    subst h
    exact ⟨1, .skip_tm_loc hc hl hne⟩
  -- skip_ty_loc
  · intro h
    rename_i hc hl
    subst h
    exact ⟨1, .skip_ty_loc hc hl⟩
  -- Path.Wf cases (motive_2 := True)
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-- The embedding theorem (target statement). -/
theorem Sub.to_ssub {Θ : Sto} {T1 T2 : Ty 0}
    (hs : Sub Θ .empty (.ty T1) (.ty T2)) : ∃ n, SSub Θ T1 T2 n :=
  hs.to_ssub_aux rfl

/-! ### First harvest: inversion for the declarative judgment, and the
theorems that fall out of it. -/

/-- Inversion for declarative runtime subtyping: embed, then invert. -/
theorem Sub.invert {Θ : Sto} {T1 T2 : Ty 0} (hwf : Sto.Shaped Θ)
    (h : Sub Θ .empty (.ty T1) (.ty T2)) : ∃ n, SOut Θ n T1 T2 := by
  obtain ⟨n, hs⟩ := h.to_ssub
  exact ⟨n, SSub.invert hwf n hs⟩

/-- Unconditional syntactic consistency, at every shaped store:
`⊤ <: ⊥` is underivable. Subsumes the empty-store consistency theorem
(the empty store is vacuously shaped). -/
theorem Sub.consistency {Θ : Sto} (hwf : Sto.Shaped Θ) :
    ¬ Sub Θ .empty (.ty .top) (.ty .bot) := by
  intro h
  obtain ⟨n, o⟩ := Sub.invert hwf h
  exact o

/-- Consistency at the empty store, with no hypotheses at all. -/
theorem Sub.consistency_empty : ¬ Sub [] .empty (.ty .top) (.ty .bot) :=
  Sub.consistency (fun {ℓ T} hl => nomatch hl)

/-- Runtime collapse-freedom (the ⊥-collapse never reaches typed
heaps): no path is below ⊥ at a shaped store. -/
theorem Sub.no_bot_path {Θ : Sto} {p : Path 0} (hwf : Sto.Shaped Θ)
    (h : Sub Θ .empty (.ty (.single p)) (.ty .bot)) : False := by
  obtain ⟨n, o⟩ := Sub.invert hwf h
  obtain ⟨ℓ0, E, hcp, hE0, m, hm, hEbot⟩ := o
  have oE := SSub.invert hwf m hEbot
  rcases (hwf hE0).1 with hs | hs | hs
  all_goals exact (oE : False).elim

#print axioms LambdaP.Sub.consistency
#print axioms LambdaP.Sub.no_bot_path

/-! ### Anchored read-offs: what a single-below-shape fact says about
the store. These are the currency of canonical forms, path progress,
and the realized substitution lemma. -/

/-- A path below a term-member pair type chains to a term-member pair
entry with the same label, whose first component is below the declared
first component. -/
theorem Sub.single_pairTm_anchor {Θ : Sto} {p : Path 0} {S : Ty 0}
    {a : Name} {T : Ty 1} (hwf : Sto.Shaped Θ)
    (h : Sub Θ .empty (.ty (.single p)) (.ty (.pairTm S a T))) :
    ∃ ℓ0 ℓ1 ℓ2, Chains Θ p ℓ0 ∧
      Sto.Lookup Θ ℓ0 (.pairTm (.single (.var (.free ℓ1))) a
        (Ty.single (.var (.free ℓ2))).weaken) ∧
      (∃ m, SSub Θ (.single (.var (.free ℓ1))) S m) ∧
      Sub Θ (Ctx.empty.push (.single (.var (.free ℓ1))))
        (.ty (Ty.single (.var (.free ℓ2))).weaken) (.ty T) := by
  obtain ⟨n, o⟩ := Sub.invert hwf h
  obtain ⟨ℓ0, E, hcp, hE0, m, hm, hres⟩ := o
  have oE := SSub.invert hwf m hres
  rcases (hwf hE0).1 with hs | hs | hs
  · exact (oE : False).elim
  · obtain ⟨hba, ⟨m2, hm2, dom⟩, res⟩ := oE
    subst hba
    exact ⟨ℓ0, _, _, hcp, hE0, ⟨m2, dom⟩, res⟩
  · exact (oE : False).elim

/-- A path below a type-member pair type chains to a type-member pair
entry with the same label and a stored alias interval. -/
theorem Sub.single_pairTy_anchor {Θ : Sto} {p : Path 0} {S : Ty 0}
    {A : Name} {T1 T2 : Ty 1} (hwf : Sto.Shaped Θ)
    (h : Sub Θ .empty (.ty (.single p)) (.ty (.pairTy S A T1 T2))) :
    ∃ ℓ0 ℓ1 W, Chains Θ p ℓ0 ∧
      Sto.Lookup Θ ℓ0 (.pairTy (.single (.var (.free ℓ1))) A
        (Ty.weaken W) (Ty.weaken W)) ∧
      (∃ m, SSub Θ (.single (.var (.free ℓ1))) S m) ∧
      Sub Θ (Ctx.empty.push (.single (.var (.free ℓ1))))
        (.ty T1) (.ty (Ty.weaken W)) ∧
      Sub Θ (Ctx.empty.push (.single (.var (.free ℓ1))))
        (.ty (Ty.weaken W)) (.ty T2) := by
  obtain ⟨n, o⟩ := Sub.invert hwf h
  obtain ⟨ℓ0, E, hcp, hE0, m, hm, hres⟩ := o
  have oE := SSub.invert hwf m hres
  rcases (hwf hE0).1 with hs | hs | hs
  · exact (oE : False).elim
  · exact (oE : False).elim
  · obtain ⟨hBA, ⟨m2, hm2, dom⟩, lo, hi⟩ := oE
    subst hBA
    exact ⟨ℓ0, _, _, hcp, hE0, ⟨m2, dom⟩, lo, hi⟩

/-- Canonical-forms seed (M3): a path below an arrow type chains to an
arrow entry whose domain is above the declared domain and whose
codomain is below the declared codomain under the declared domain. -/
theorem Sub.single_arrow_anchor {Θ : Sto} {p : Path 0} {S : Ty 0}
    {T : Ty 1} (hwf : Sto.Shaped Θ)
    (h : Sub Θ .empty (.ty (.single p)) (.ty (.arrow S T))) :
    ∃ ℓ0 S0 T0, Chains Θ p ℓ0 ∧
      Sto.Lookup Θ ℓ0 (.arrow S0 T0) ∧
      (∃ m, SSub Θ S S0 m) ∧
      Sub Θ (Ctx.empty.push S) (.ty T0) (.ty T) := by
  obtain ⟨n, o⟩ := Sub.invert hwf h
  obtain ⟨ℓ0, E, hcp, hE0, m, hm, hres⟩ := o
  have oE := SSub.invert hwf m hres
  rcases (hwf hE0).1 with hs | hs | hs
  · obtain ⟨⟨m2, hm2, dom⟩, res⟩ := oE
    exact ⟨ℓ0, _, _, hcp, hE0, ⟨m2, dom⟩, res⟩
  · exact (oE : False).elim
  · exact (oE : False).elim

/-- Path progress (M2): wellformed runtime paths resolve through the
store. Manual application of the joint recursor (trivial Sub motive);
goal order is argument order. -/
theorem Path.Wf.chains {s0 : Sig} {Θ0 : Sto} {Γ0 : Ctx s0} {p0 : Path s0}
    (hwf : Sto.Shaped Θ0) (h : Path.Wf Θ0 Γ0 p0) :
    ∀ (hs : s0 = 0), ∃ m, Chains Θ0 (hs ▸ p0) m := by
  suffices core : ∀ hs : s0 = 0, Sto.Shaped Θ0 → ∃ m, Chains Θ0 (hs ▸ p0) m from
    fun hs => core hs hwf
  refine Path.Wf.rec (motive_1 := fun {s} Θ Γ τ1 τ2 _ => True)
    (motive_2 := fun {s} Θ Γ p _ =>
      ∀ hs : s = 0, Sto.Shaped Θ → ∃ m, Chains Θ (hs ▸ p) m)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · -- Wf.var_bound
    intro s Γ x T Θ hx hs hwf'
    subst hs
    exact nomatch x
  · -- Wf.var_free
    intro s Θ ℓ T Γ hl hs hwf'
    subst hs
    exact ⟨ℓ, .loc hl⟩
  · -- Wf.fst_tm
    intro s Θ Γ p S a T hwp hsub ihw ihs hs hwf'
    subst hs
    have hE := Ctx.eq_empty' Γ
    subst hE
    obtain ⟨ℓ0, ℓ1, ℓ2, hcp, hE0, -, -⟩ := Sub.single_pairTm_anchor hwf' hsub
    exact ⟨ℓ1, .fst_tm hcp hE0⟩
  · -- Wf.fst_ty
    intro s Θ Γ p S A T1 T2 hwp hsub ihw ihs hs hwf'
    subst hs
    have hE := Ctx.eq_empty' Γ
    subst hE
    obtain ⟨ℓ0, ℓ1, W, hcp, hE0, -, -, -⟩ := Sub.single_pairTy_anchor hwf' hsub
    exact ⟨ℓ1, .fst_ty hcp hE0⟩
  · -- Wf.sel
    intro s Θ Γ p S a T hwp hsub ihw ihs hs hwf'
    subst hs
    have hE := Ctx.eq_empty' Γ
    subst hE
    obtain ⟨ℓ0, ℓ1, ℓ2, hcp, hE0, -, -⟩ := Sub.single_pairTm_anchor hwf' hsub
    exact ⟨ℓ2, .sel hcp hE0⟩
  · -- Wf.sel_skip_tm
    intro s Θ Γ p a S b Tc hwin hsub hne ihw ihs hs hwf'
    subst hs
    have hE := Ctx.eq_empty' Γ
    subst hE
    obtain ⟨m, hm⟩ := ihw rfl hwf'
    obtain ⟨ℓ0, ℓ1, ℓ2, hcp, hE0, -, -⟩ := Sub.single_pairTm_anchor hwf' hsub
    exact ⟨m, .sel_skip_tm hcp hE0 hne hm⟩
  · -- Wf.sel_skip_ty
    intro s Θ Γ p a S B T1 T2 hwin hsub ihw ihs hs hwf'
    subst hs
    have hE := Ctx.eq_empty' Γ
    subst hE
    obtain ⟨m, hm⟩ := ihw rfl hwf'
    obtain ⟨ℓ0, ℓ1, W, hcp, hE0, -, -, -⟩ := Sub.single_pairTy_anchor hwf' hsub
    exact ⟨m, .sel_skip_ty hcp hE0 hm⟩


/-- Canonical forms for functions (M3): a runtime path below an arrow
type resolves to a stored lambda with a typed body, contravariant
domain, and covariant codomain under the declared domain. -/
theorem Sub.canonical_arrow {Θ : Sto} {h : Heap} {p : Path 0}
    {S : Ty 0} {T : Ty 1} (hh : HeapTyped Θ h)
    (hsub : Sub Θ .empty (.ty (.single p)) (.ty (.arrow S T))) :
    ∃ ℓ0 S0 T0 t, Chains Θ p ℓ0 ∧
      Heap.Lookup h ℓ0 (.abs S0 t) ∧
      Wf Θ .empty (.ty S0) ∧
      HasType Θ (Ctx.empty.push S0) t T0 ∧
      Sub Θ .empty (.ty S) (.ty S0) ∧
      Sub Θ (Ctx.empty.push S) (.ty T0) (.ty T) := by
  obtain ⟨ℓ0, S0, T0, hcp, hE0, ⟨m, dom⟩, res⟩ :=
    Sub.single_arrow_anchor hh.shaped hsub
  obtain ⟨-, v, hlv, -, hpre⟩ := hh.2 hE0
  cases hpre with
  | abs hwf0 hty =>
    exact ⟨ℓ0, S0, T0, _, hcp, hlv, hwf0, hty, dom.to_sub, res⟩


end LambdaP

section
open LambdaP
#print axioms LambdaP.Sub.to_ssub
end
