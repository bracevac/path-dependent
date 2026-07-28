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

/-- Motive for interval inversion: mixed tau shapes are impossible,
ty-ty is trivial, intv-intv yields the componentwise facts. -/
def IntvGoal (Θ : Sto) (Γ : Ctx s) : Tau s -> Tau s -> Prop
  | .ty _, .ty _ => True
  | .intv T1 T2, .intv T1' T2' =>
      Sub Θ Γ (.ty T1') (.ty T1) ∧ Sub Θ Γ (.ty T2) (.ty T2')
  | _, _ => False

theorem Sub.intv_inv_aux {s : Sig} {Θ : Sto} {Γ : Ctx s} {τ1 τ2 : Tau s}
    (hs : Sub Θ Γ τ1 τ2) : IntvGoal Θ Γ τ1 τ2 := by
  induction hs using Sub.rec (motive_2 := fun {s} Θ Γ p _ => True)
  -- refl
  · rename_i τ
    cases τ
    · trivial
    · exact ⟨.refl, .refl⟩
  -- trans
  · rename_i τ1 τ2 τ3 h1 h2 ih1 ih2
    cases τ1 <;> cases τ2 <;> cases τ3 <;>
      first
      | trivial
      | exact (ih1 : False).elim
      | exact (ih2 : False).elim
      | exact ⟨.trans ih2.1 ih1.1, .trans ih1.2 ih2.2⟩
  -- bot, top, var_bound, var_free, symm, fst_tm, fst_ty, sel_tm,
  -- sel_tm_loc, sel_hi, sel_lo, sel_hi_loc, sel_lo_loc, arrow,
  -- pair_tm, pair_ty (16 ty-ty conclusions)
  all_goals first
  | trivial
  | (rename_i h1 h2 h3 ih1 ih2 ih3; exact ⟨h1, h2⟩)
  | (intros; trivial)

/-- Interval subtyping inverts componentwise (the guard is not
recoverable and not returned). -/
theorem Sub.intv_inv {s : Sig} {Θ : Sto} {Γ : Ctx s} {T1 T2 T1' T2' : Ty s}
    (hs : Sub Θ Γ (.intv T1 T2) (.intv T1' T2')) :
    Sub Θ Γ (.ty T1') (.ty T1) ∧ Sub Θ Γ (.ty T2) (.ty T2') :=
  hs.intv_inv_aux

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
    rename_i h1 h2 ih1 ih2
    subst h
    have hE := Ctx.eq_empty' ‹Ctx 0›
    subst hE
    obtain ⟨n, hn⟩ := ih1 rfl
    obtain ⟨hlo, hhi⟩ := Sub.intv_inv h2
    exact ⟨n + 1, .pair_ty hn hlo hhi⟩
  -- ival
  · intro h; subst h
    trivial
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

end LambdaP

section
open LambdaP
#print axioms LambdaP.Sub.to_ssub
end
