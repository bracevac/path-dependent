import LambdaP.Soundness.Embedding

/-!
The scope-generic sized table `GSub` (V13 candidate 1; live since V14).

`GSub` is `Sub` with a fuel index, and it is 1:1 with `Sub` now that the
five `p.root.IsBound` premises are gone (V14 step 1): `Sub.to_gsub` and
`GSub.to_sub` below. What V13 settled: the declaration is kernel-legal,
and the instantiation theorem `GSub.subst` — NOTES V12 §5's KNOWN
OBSTACLE — goes through. What V14 adds: the round trip, fuel monotonicity,
and `GSub.subst_loc` (fuel-EXACT instantiation at an anchor location),
which is the arithmetic V15's collapse needs. Still missing for V15:
`GSub.rename`/`weaken` and hence the real `GSubstLift` (assumed here),
and the leg-bound index on `SSub` (NOTES V14 §3.2).

`GSub Θ Γ τ1 τ2 n` is `Sub` with (a) a fuel index, (b) the five evidence
rules IsBound-FREE (deviation-11 reversal), and (c) the congruence rows
carrying their pushed-context legs as PLAIN SIZED FIELDS
(`GSub Θ (Γ.push S) _ _ n`) instead of raw `Sub` legs.

Kernel legality is the first question: (c) is a plain field, not a
∀-hypothesis, so the V12 positivity/nesting obstructions do not apply.

The second question — the one NOTES V12 §5 flagged as the KNOWN OBSTACLE
— is the substitution/instantiation theorem at PUSHED contexts: "an
evidence case whose image is location-rooted would need inversion at a
NON-empty context". `GSub.subst` below decides it.
-/

namespace LambdaP

/-- Scope-generic sized subtyping. Rows carry pushed-context legs as
sized fields; the five evidence rules carry `Path.Wf` but NOT
`p.root.IsBound`. -/
inductive GSub (Θ : Sto) : {s : Sig} -> Ctx s -> Tau s -> Tau s -> Nat -> Prop where
| refl :
  GSub Θ Γ τ τ (n+1)
| trans :
  GSub Θ Γ τ1 τ2 n -> GSub Θ Γ τ2 τ3 n -> GSub Θ Γ τ1 τ3 (n+1)
| bot :
  GSub Θ Γ (.ty .bot) (.ty T) (n+1)
| top :
  GSub Θ Γ (.ty T) (.ty .top) (n+1)
| var_bound :
  Ctx.LookupVar Γ x T ->
  GSub Θ Γ (.ty (.single (.var (.bound x)))) (.ty T) (n+1)
| var_free :
  Sto.Lookup Θ ℓ T ->
  GSub Θ Γ (.ty (.single (.var (.free ℓ)))) (.ty T.fromClosed) (n+1)
| symm :
  Path.Wf Θ Γ p ->
  GSub Θ Γ (.ty (.single p)) (.ty (.single q)) n ->
  GSub Θ Γ (.ty (.single q)) (.ty (.single p)) (n+1)
| fst_tm :
  GSub Θ Γ (.ty (.single p)) (.ty (.pairTm S a T)) n ->
  GSub Θ Γ (.ty (.single p.fst)) (.ty S) (n+1)
| fst_ty :
  GSub Θ Γ (.ty (.single p)) (.ty (.pairTy S A T1 T2)) n ->
  GSub Θ Γ (.ty (.single p.fst)) (.ty S) (n+1)
-- the five evidence rules, IsBound-FREE
| sel_tm :
  Path.Wf Θ Γ p ->
  GSub Θ Γ (.ty (.single p)) (.ty (.pairTm S a T)) n ->
  GSub Θ Γ (.ty (.single (p.sel a))) (.ty (T.open p.fst)) (n+1)
| sel_hi :
  Path.Wf Θ Γ p ->
  GSub Θ Γ (.ty (.single p)) (.ty (.pairTy S A T1 T2)) n ->
  GSub Θ Γ (.ty (T1.open p.fst)) (.ty (T2.open p.fst)) n ->
  GSub Θ Γ (.ty (.tsel p A)) (.ty (T2.open p.fst)) (n+1)
| sel_lo :
  Path.Wf Θ Γ p ->
  GSub Θ Γ (.ty (.single p)) (.ty (.pairTy S A T1 T2)) n ->
  GSub Θ Γ (.ty (T1.open p.fst)) (.ty (T2.open p.fst)) n ->
  GSub Θ Γ (.ty (T1.open p.fst)) (.ty (.tsel p A)) (n+1)
| skip_tm :
  Path.Wf Θ Γ p ->
  GSub Θ Γ (.ty (.single p)) (.ty (.pairTm S b T)) n ->
  a ≠ b ->
  GSub Θ Γ (.ty (.single (p.sel a))) (.ty (.single ((Path.fst p).sel a))) (n+1)
| skip_ty :
  Path.Wf Θ Γ p ->
  GSub Θ Γ (.ty (.single p)) (.ty (.pairTy S B T1 T2)) n ->
  GSub Θ Γ (.ty (.single (p.sel a))) (.ty (.single ((Path.fst p).sel a))) (n+1)
-- the store-anchored rules (unchanged)
| sel_tm_loc :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTm S a (Ty.single (.var (.free ℓ2))).weaken) ->
  GSub Θ Γ (.ty (.single (p.sel a))) (.ty (.single (.var (.free ℓ2)))) (n+1)
| sel_hi_loc :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A (Ty.weaken W) (Ty.weaken W)) ->
  GSub Θ Γ (.ty (.tsel p A)) (.ty (Ty.fromClosed W)) (n+1)
| sel_lo_loc :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A (Ty.weaken W) (Ty.weaken W)) ->
  GSub Θ Γ (.ty (Ty.fromClosed W)) (.ty (.tsel p A)) (n+1)
| skip_tm_loc :
  Chains Θ p ℓ ->
  Sto.Lookup Θ ℓ (.pairTm S b Tc) ->
  a ≠ b ->
  GSub Θ Γ (.ty (.single (p.sel a))) (.ty (.single ((Path.fst p).sel a))) (n+1)
| skip_ty_loc :
  Chains Θ p ℓ ->
  Sto.Lookup Θ ℓ (.pairTy S B T1 T2) ->
  GSub Θ Γ (.ty (.single (p.sel a))) (.ty (.single ((Path.fst p).sel a))) (n+1)
-- the congruence rows: pushed-context legs are SIZED FIELDS (candidate 1)
| arrow :
  GSub Θ Γ (.ty S') (.ty S) n ->
  GSub Θ (Γ.push S') (.ty T) (.ty T') n ->
  GSub Θ Γ (.ty (.arrow S T)) (.ty (.arrow S' T')) (n+1)
| pair_tm :
  GSub Θ Γ (.ty S) (.ty S') n ->
  GSub Θ (Γ.push S) (.ty T) (.ty T') n ->
  GSub Θ Γ (.ty (.pairTm S a T)) (.ty (.pairTm S' a T')) (n+1)
| pair_ty :
  GSub Θ Γ (.ty S) (.ty S') n ->
  GSub Θ (Γ.push S) (.ty T1') (.ty T1) n ->
  GSub Θ (Γ.push S) (.ty T2) (.ty T2') n ->
  GSub Θ Γ (.ty (.pairTy S A T1 T2)) (.ty (.pairTy S' A T1' T2')) (n+1)
| repl :
  Path.Wf Θ Γ p -> Path.Wf Θ Γ q ->
  GSub Θ Γ (.ty (.single p)) (.ty (.single q)) n ->
  GSub Θ Γ (.ty (.single q)) (.ty (.single p)) n ->
  GSub Θ Γ (.ty (Ty.open T p)) (.ty (Ty.open T q)) (n+1)

/-! ### The instantiation theorem (NOTES V12 §5's KNOWN OBSTACLE).

Uniform-fuel conformance (the discipline `SSub` already uses), so the
transport is fuel-EXACT and the recursion is plainly structural. The
`Path.Wf` transport is a field: after the deviation-11 reversal it is
`Path.Wf.subst` verbatim (V11 (p2): dropping `SubstTyping.rooted` is a
pure deletion), and taking it as a field keeps this probe compiling
against the UNMODIFIED `Typing.lean`. -/

structure GSubstTyping (Θ : Sto) (σ : Subst s1 s2) (Γ : Ctx s1) (Δ : Ctx s2) : Prop where
  base : SubstTyping Θ σ Γ Δ
  conforms : ∀ {x : BVar s1} {T : Ty s1}, Ctx.LookupVar Γ x T ->
    ∀ n, GSub Θ Δ (.ty (.single (σ.var x))) (.ty (T.subst σ)) (n+1)

/-- The `Path.Wf` transport, from the ordinary substitution lemma (V14:
it is `Path.Wf.subst` verbatim, as V13 predicted). -/
theorem GSubstTyping.wf {Θ : Sto} {σ : Subst s1 s2} {Γ : Ctx s1} {Δ : Ctx s2}
    (hσ : GSubstTyping Θ σ Γ Δ) {p : Path s1} (hp : Path.Wf Θ Γ p) :
    Path.Wf Θ Δ (p.subst σ) := hp.subst hσ.base

/-- Closure under binder extension: `var_bound .here` for the new
variable + `GSub.weaken` for the rest, exactly as `SubstTyping.lift`.
PROVED below (`GSubstTyping.lift`/`gsubstLift`); kept as a named `Prop`
because `GSub.subst`'s structural recursion takes it as a parameter. -/
def GSubstLift (Θ : Sto) : Prop :=
  ∀ {s1 s2 : Sig} {σ : Subst s1 s2} {Γ : Ctx s1} {Δ : Ctx s2},
    GSubstTyping Θ σ Γ Δ -> ∀ {S : Ty s1},
      GSubstTyping Θ σ.lift (Γ.push S) (Δ.push (S.subst σ))

/-- **THE V12 §5 OBSTACLE, DISCHARGED.** Instantiation at pushed
contexts, fuel-exact, plain structural recursion. The evidence cases
(`sel_tm`/`sel_hi`/`sel_lo`/`skip_tm`/`skip_ty`) are the ones V12 §5
flagged: "an evidence case whose image is location-rooted would need
inversion at a NON-empty context — false in general". They do not: with
the rules IsBound-FREE they simply RE-EMIT on the substituted premises.
No inertness condition, no fresh-location trick, no context predicate
(so no re-entry into V10's refuted branch). -/
theorem GSub.subst {Θ : Sto} (hlift : GSubstLift Θ) {s1 : Sig} {Γ : Ctx s1}
    {τ1 τ2 : Tau s1} {n : Nat} (h : GSub Θ Γ τ1 τ2 n) :
    ∀ {s2 : Sig} {σ : Subst s1 s2} {Δ : Ctx s2}, GSubstTyping Θ σ Γ Δ ->
      GSub Θ Δ (τ1.subst σ) (τ2.subst σ) n :=
  match h with
  | .refl => fun _ => .refl
  | .trans h1 h2 => fun hσ => .trans (h1.subst hlift hσ) (h2.subst hlift hσ)
  | .bot => fun _ => .bot
  | .top => fun _ => .top
  | .var_bound hx => fun hσ => hσ.conforms hx _
  | .var_free hl => fun _ => by
    simp only [Tau.subst, Ty.subst, Path.subst, Var.subst, Ty.fromClosed_subst]
    exact .var_free hl
  | .symm hw h1 => fun hσ => .symm (hσ.wf hw) (h1.subst hlift hσ)
  | .fst_tm h1 => fun hσ => .fst_tm (h1.subst hlift hσ)
  | .fst_ty h1 => fun hσ => .fst_ty (h1.subst hlift hσ)
  -- THE FLAGGED CASES: images may be location-rooted; the liberalized
  -- rules RE-EMIT, so no inversion at a non-empty context is needed.
  | .sel_tm hw h1 => fun hσ => by
    simp only [Tau.subst, Ty.subst, Path.subst]
    rw [← Ty.open_subst_comm]
    exact GSub.sel_tm (hσ.wf hw) (h1.subst hlift hσ)
  | .sel_hi hw h1 h2 => fun hσ => by
    have h2' := h2.subst hlift hσ
    simp only [Tau.subst] at h2'
    rw [← Ty.open_subst_comm, ← Ty.open_subst_comm] at h2'
    simp only [Tau.subst, Ty.subst]
    rw [← Ty.open_subst_comm]
    exact GSub.sel_hi (hσ.wf hw) (h1.subst hlift hσ) h2'
  | .sel_lo hw h1 h2 => fun hσ => by
    have h2' := h2.subst hlift hσ
    simp only [Tau.subst] at h2'
    rw [← Ty.open_subst_comm, ← Ty.open_subst_comm] at h2'
    simp only [Tau.subst, Ty.subst]
    rw [← Ty.open_subst_comm]
    exact GSub.sel_lo (hσ.wf hw) (h1.subst hlift hσ) h2'
  | .skip_tm hw h1 hne => fun hσ =>
    .skip_tm (hσ.wf hw) (h1.subst hlift hσ) hne
  | .skip_ty hw h1 => fun hσ =>
    .skip_ty (hσ.wf hw) (h1.subst hlift hσ)
  | .sel_tm_loc hc hl => fun _ => by
    simp only [Tau.subst, Ty.subst, Path.subst, Var.subst]
    exact GSub.sel_tm_loc hc.subst hl
  | .sel_hi_loc hc hl => fun _ => by
    simp only [Tau.subst, Ty.subst, Ty.fromClosed_subst]
    exact GSub.sel_hi_loc hc.subst hl
  | .sel_lo_loc hc hl => fun _ => by
    simp only [Tau.subst, Ty.subst, Ty.fromClosed_subst]
    exact GSub.sel_lo_loc hc.subst hl
  | .skip_tm_loc hc hl hne => fun _ => by
    simp only [Tau.subst, Ty.subst, Path.subst]
    exact GSub.skip_tm_loc hc.subst hl hne
  | .skip_ty_loc hc hl => fun _ => by
    simp only [Tau.subst, Ty.subst, Path.subst]
    exact GSub.skip_ty_loc hc.subst hl
  | .arrow h1 h2 => fun hσ =>
    .arrow (h1.subst hlift hσ) (h2.subst hlift (hlift hσ))
  | .pair_tm h1 h2 => fun hσ =>
    .pair_tm (h1.subst hlift hσ) (h2.subst hlift (hlift hσ))
  | .pair_ty h1 h2 h3 => fun hσ =>
    .pair_ty (h1.subst hlift hσ) (h2.subst hlift (hlift hσ))
      (h3.subst hlift (hlift hσ))
  | .repl hwp hwq h1 h2 => fun hσ => by
    simp only [Tau.subst]
    rw [← Ty.open_subst_comm, ← Ty.open_subst_comm]
    exact GSub.repl (hσ.wf hwp) (hσ.wf hwq) (h1.subst hlift hσ) (h2.subst hlift hσ)

/-! ### V14: renaming, weakening, and the REAL `GSubstLift`

`GSubstTyping` now carries the ordinary `SubstTyping` as a field (`base`)
instead of a bare `Path.Wf` transport, which is what makes the lift
provable: `SubstTyping.lift` handles the unsized half, `var_bound` and
`GSub.weaken` the sized half. So the `hlift` hypothesis of `GSub.subst`
is discharged (`gsubstLift`) and the instantiation theorems are real
theorems, not conditionals. -/

/-- `GSub` is preserved under context-respecting renamings, fuel-exactly. -/
theorem GSub.rename {Θ : Sto} {s1 : Sig} {Γ : Ctx s1} {τ1 τ2 : Tau s1} {n : Nat}
    (h : GSub Θ Γ τ1 τ2 n) :
    ∀ {s2 : Sig} {f : Rename s1 s2} {Δ : Ctx s2}, Renaming Γ f Δ ->
      GSub Θ Δ (τ1.rename f) (τ2.rename f) n :=
  match h with
  | .refl => fun _ => .refl
  | .trans h1 h2 => fun ρ => .trans (h1.rename ρ) (h2.rename ρ)
  | .bot => fun _ => .bot
  | .top => fun _ => .top
  | .var_bound hx => fun ρ => .var_bound (ρ hx)
  | .var_free hl => fun _ => by
    simp only [Tau.rename, Ty.rename, Path.rename, Var.rename, Ty.fromClosed_rename]
    exact .var_free hl
  | .symm hw h1 => fun ρ => .symm (hw.rename ρ) (h1.rename ρ)
  | .fst_tm h1 => fun ρ => .fst_tm (h1.rename ρ)
  | .fst_ty h1 => fun ρ => .fst_ty (h1.rename ρ)
  | .sel_tm hw h1 => fun ρ => by
    simp only [Tau.rename, Ty.rename, Path.rename]
    rw [← Ty.open_rename_comm]
    exact GSub.sel_tm (hw.rename ρ) (h1.rename ρ)
  | .sel_hi hw h1 h2 => fun ρ => by
    have h2' := h2.rename ρ
    simp only [Tau.rename] at h2'
    rw [← Ty.open_rename_comm, ← Ty.open_rename_comm] at h2'
    simp only [Tau.rename, Ty.rename]
    rw [← Ty.open_rename_comm]
    exact GSub.sel_hi (hw.rename ρ) (h1.rename ρ) h2'
  | .sel_lo hw h1 h2 => fun ρ => by
    have h2' := h2.rename ρ
    simp only [Tau.rename] at h2'
    rw [← Ty.open_rename_comm, ← Ty.open_rename_comm] at h2'
    simp only [Tau.rename, Ty.rename]
    rw [← Ty.open_rename_comm]
    exact GSub.sel_lo (hw.rename ρ) (h1.rename ρ) h2'
  | .skip_tm hw h1 hne => fun ρ => .skip_tm (hw.rename ρ) (h1.rename ρ) hne
  | .skip_ty hw h1 => fun ρ => .skip_ty (hw.rename ρ) (h1.rename ρ)
  | .sel_tm_loc hc hl => fun _ => by
    simp only [Tau.rename, Ty.rename, Path.rename, Var.rename]
    exact GSub.sel_tm_loc hc.rename hl
  | .sel_hi_loc hc hl => fun _ => by
    simp only [Tau.rename, Ty.rename, Ty.fromClosed_rename]
    exact GSub.sel_hi_loc hc.rename hl
  | .sel_lo_loc hc hl => fun _ => by
    simp only [Tau.rename, Ty.rename, Ty.fromClosed_rename]
    exact GSub.sel_lo_loc hc.rename hl
  | .skip_tm_loc hc hl hne => fun _ => by
    simp only [Tau.rename, Ty.rename, Path.rename]
    exact GSub.skip_tm_loc hc.rename hl hne
  | .skip_ty_loc hc hl => fun _ => by
    simp only [Tau.rename, Ty.rename, Path.rename]
    exact GSub.skip_ty_loc hc.rename hl
  | .arrow h1 h2 => fun ρ => .arrow (h1.rename ρ) (h2.rename (Renaming.ext ρ))
  | .pair_tm h1 h2 => fun ρ => .pair_tm (h1.rename ρ) (h2.rename (Renaming.ext ρ))
  | .pair_ty h1 h2 h3 => fun ρ =>
    .pair_ty (h1.rename ρ) (h2.rename (Renaming.ext ρ)) (h3.rename (Renaming.ext ρ))
  | .repl hwp hwq h1 h2 => fun ρ => by
    simp only [Tau.rename]
    rw [← Ty.open_rename_comm, ← Ty.open_rename_comm]
    exact GSub.repl (hwp.rename ρ) (hwq.rename ρ) (h1.rename ρ) (h2.rename ρ)

/-- Weakening, fuel-exact. -/
theorem GSub.weaken {Θ : Sto} {s : Sig} {Γ : Ctx s} {τ1 τ2 : Tau s} {S : Ty s}
    {n : Nat} (h : GSub Θ Γ τ1 τ2 n) : GSub Θ (Γ.push S) τ1.weaken τ2.weaken n :=
  h.rename Renaming.succ

/-- Conforming sized substitutions extend under a binder. -/
theorem GSubstTyping.lift {Θ : Sto} {s1 s2 : Sig} {σ : Subst s1 s2}
    {Γ : Ctx s1} {Δ : Ctx s2} (hσ : GSubstTyping Θ σ Γ Δ) {S : Ty s1} :
    GSubstTyping Θ σ.lift (Γ.push S) (Δ.push (S.subst σ)) := by
  constructor
  · exact hσ.base.lift
  · intro x T h n
    cases h with
    | here =>
      rw [Ty.weaken_subst_comm]
      exact .var_bound .here
    | there h' =>
      rw [Ty.weaken_subst_comm]
      exact (hσ.conforms h' n).weaken

/-- **The assumed closure property, discharged.** -/
theorem gsubstLift (Θ : Sto) : GSubstLift Θ := fun hσ => hσ.lift

/-! ### V14: fuel monotonicity and the round trip with `Sub` -/

/-- Growing a derivation by one. -/
theorem GSub.succ {Θ : Sto} {s : Sig} {Γ : Ctx s} {τ1 τ2 : Tau s} {n : Nat}
    (h : GSub Θ Γ τ1 τ2 n) : GSub Θ Γ τ1 τ2 (n+1) := by
  induction h with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | bot => exact .bot
  | top => exact .top
  | var_bound hx => exact .var_bound hx
  | var_free hl => exact .var_free hl
  | symm hw _ ih => exact .symm hw ih
  | fst_tm _ ih => exact .fst_tm ih
  | fst_ty _ ih => exact .fst_ty ih
  | sel_tm hw _ ih => exact .sel_tm hw ih
  | sel_hi hw _ _ ih1 ih2 => exact .sel_hi hw ih1 ih2
  | sel_lo hw _ _ ih1 ih2 => exact .sel_lo hw ih1 ih2
  | skip_tm hw _ hne ih => exact .skip_tm hw ih hne
  | skip_ty hw _ ih => exact .skip_ty hw ih
  | sel_tm_loc hc hl => exact .sel_tm_loc hc hl
  | sel_hi_loc hc hl => exact .sel_hi_loc hc hl
  | sel_lo_loc hc hl => exact .sel_lo_loc hc hl
  | skip_tm_loc hc hl hne => exact .skip_tm_loc hc hl hne
  | skip_ty_loc hc hl => exact .skip_ty_loc hc hl
  | arrow _ _ ih1 ih2 => exact .arrow ih1 ih2
  | pair_tm _ _ ih1 ih2 => exact .pair_tm ih1 ih2
  | pair_ty _ _ _ ih1 ih2 ih3 => exact .pair_ty ih1 ih2 ih3
  | repl hwp hwq _ _ ih1 ih2 => exact .repl hwp hwq ih1 ih2

/-- Sizes are monotone. -/
theorem GSub.mono {Θ : Sto} {s : Sig} {Γ : Ctx s} {τ1 τ2 : Tau s} {n n' : Nat}
    (h : GSub Θ Γ τ1 τ2 n) (hle : n ≤ n') : GSub Θ Γ τ1 τ2 n' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction k with
  | zero => exact h
  | succ k ih => exact ih.succ

/-- The sized table is sound for `Sub` — 1:1, since V14 step 1 made the
five evidence rules `IsBound`-free on both sides. -/
theorem GSub.to_sub {Θ : Sto} {s : Sig} {Γ : Ctx s} {τ1 τ2 : Tau s} {n : Nat}
    (h : GSub Θ Γ τ1 τ2 n) : Sub Θ Γ τ1 τ2 := by
  induction h with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | bot => exact .bot
  | top => exact .top
  | var_bound hx => exact .var_bound hx
  | var_free hl => exact .var_free hl
  | symm hw _ ih => exact .symm hw ih
  | fst_tm _ ih => exact .fst_tm ih
  | fst_ty _ ih => exact .fst_ty ih
  | sel_tm hw _ ih => exact .sel_tm hw ih
  | sel_hi hw _ _ ih1 ih2 => exact .sel_hi hw ih1 ih2
  | sel_lo hw _ _ ih1 ih2 => exact .sel_lo hw ih1 ih2
  | skip_tm hw _ hne ih => exact .skip_tm hw ih hne
  | skip_ty hw _ ih => exact .skip_ty hw ih
  | sel_tm_loc hc hl => exact .sel_tm_loc hc hl
  | sel_hi_loc hc hl => exact .sel_hi_loc hc hl
  | sel_lo_loc hc hl => exact .sel_lo_loc hc hl
  | skip_tm_loc hc hl hne => exact .skip_tm_loc hc hl hne
  | skip_ty_loc hc hl => exact .skip_ty_loc hc hl
  | arrow _ _ ih1 ih2 => exact .arrow ih1 ih2
  | pair_tm _ _ ih1 ih2 => exact .pair_tm ih1 ih2
  | pair_ty _ _ _ ih1 ih2 ih3 => exact .pair_ty ih1 ih2 ih3
  | repl hwp hwq _ _ ih1 ih2 => exact .repl hwp hwq ih1 ih2

/-- Every `Sub` derivation is sized: the joint recursor with
`motive_2 := True`, positional bullets in declaration order, sizes
equalized with `GSub.mono` at the multi-premise rules. (This is the
direction that needed V14 step 1 in no way — but its converse
`GSub.to_sub` did.) -/
theorem Sub.to_gsub {Θ : Sto} {s : Sig} {Γ : Ctx s} {τ1 τ2 : Tau s}
    (hs : Sub Θ Γ τ1 τ2) : ∃ n, GSub Θ Γ τ1 τ2 n := by
  induction hs using Sub.rec (motive_2 := fun {s} Θ Γ p _ => True)
  -- refl
  · exact ⟨1, .refl⟩
  -- trans
  · rename_i h1 h2 ih1 ih2
    obtain ⟨n1, k1⟩ := ih1
    obtain ⟨n2, k2⟩ := ih2
    exact ⟨max n1 n2 + 1, .trans (k1.mono (by omega)) (k2.mono (by omega))⟩
  -- bot
  · exact ⟨1, .bot⟩
  -- top
  · exact ⟨1, .top⟩
  -- var_bound
  · rename_i hx
    exact ⟨1, .var_bound hx⟩
  -- var_free
  · rename_i hl
    exact ⟨1, .var_free hl⟩
  -- symm
  · rename_i hw h1 ihw ih
    obtain ⟨n, k⟩ := ih
    exact ⟨n + 1, .symm hw k⟩
  -- fst_tm
  · rename_i h1 ih
    obtain ⟨n, k⟩ := ih
    exact ⟨n + 1, .fst_tm k⟩
  -- fst_ty
  · rename_i h1 ih
    obtain ⟨n, k⟩ := ih
    exact ⟨n + 1, .fst_ty k⟩
  -- sel_tm
  · rename_i hw h1 ihw ih
    obtain ⟨n, k⟩ := ih
    exact ⟨n + 1, .sel_tm hw k⟩
  -- sel_tm_loc
  · rename_i hc hl
    exact ⟨1, .sel_tm_loc hc hl⟩
  -- sel_hi
  · rename_i hw h1 h2 ihw ih1 ih2
    obtain ⟨n1, k1⟩ := ih1
    obtain ⟨n2, k2⟩ := ih2
    exact ⟨max n1 n2 + 1, .sel_hi hw (k1.mono (by omega)) (k2.mono (by omega))⟩
  -- sel_lo
  · rename_i hw h1 h2 ihw ih1 ih2
    obtain ⟨n1, k1⟩ := ih1
    obtain ⟨n2, k2⟩ := ih2
    exact ⟨max n1 n2 + 1, .sel_lo hw (k1.mono (by omega)) (k2.mono (by omega))⟩
  -- sel_hi_loc
  · rename_i hc hl
    exact ⟨1, .sel_hi_loc hc hl⟩
  -- sel_lo_loc
  · rename_i hc hl
    exact ⟨1, .sel_lo_loc hc hl⟩
  -- arrow
  · rename_i h1 h2 ih1 ih2
    obtain ⟨n1, k1⟩ := ih1
    obtain ⟨n2, k2⟩ := ih2
    exact ⟨max n1 n2 + 1, .arrow (k1.mono (by omega)) (k2.mono (by omega))⟩
  -- pair_tm
  · rename_i h1 h2 ih1 ih2
    obtain ⟨n1, k1⟩ := ih1
    obtain ⟨n2, k2⟩ := ih2
    exact ⟨max n1 n2 + 1, .pair_tm (k1.mono (by omega)) (k2.mono (by omega))⟩
  -- pair_ty
  · rename_i h1 h2 h3 ih1 ih2 ih3
    obtain ⟨n1, k1⟩ := ih1
    obtain ⟨n2, k2⟩ := ih2
    obtain ⟨n3, k3⟩ := ih3
    exact ⟨max n1 (max n2 n3) + 1, .pair_ty (k1.mono (by omega))
      (k2.mono (by omega)) (k3.mono (by omega))⟩
  -- repl
  · rename_i hwp hwq h1 h2 ihwp ihwq ih1 ih2
    obtain ⟨n1, k1⟩ := ih1
    obtain ⟨n2, k2⟩ := ih2
    exact ⟨max n1 n2 + 1, .repl hwp hwq (k1.mono (by omega)) (k2.mono (by omega))⟩
  -- skip_tm
  · rename_i hw h1 hne ihw ih
    obtain ⟨n, k⟩ := ih
    exact ⟨n + 1, .skip_tm hw k hne⟩
  -- skip_ty
  · rename_i hw h1 ihw ih
    obtain ⟨n, k⟩ := ih
    exact ⟨n + 1, .skip_ty hw k⟩
  -- skip_tm_loc
  · rename_i hc hl hne
    exact ⟨1, .skip_tm_loc hc hl hne⟩
  -- skip_ty_loc
  · rename_i hc hl
    exact ⟨1, .skip_ty_loc hc hl⟩
  -- Path.Wf cases (motive_2 := True)
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-! ### V14: the instantiation the embedding actually needs, FUEL-EXACT

The V14 leaf (`Sto.ResidueCollapse`, `Soundness/Embedding.lean`) consumes
the store residue at ONE opener: the entry's own first component `⌊ℓ⌋`,
where the conformance obligation is `refl` — available at EVERY fuel,
since `GSub.refl` is a leaf rule. That is what makes the instantiation
below fuel-EXACT (`n` in, `n` out, no `+c` for a conformance derivation),
which is the arithmetic the V15 collapse needs: at a `sel_tm`/`sel_hi`/
`sel_lo` row of fuel `n+1`, the residue leg comes back at fuel `≤ n` and
survives instantiation at fuel `≤ n`, so a strong induction on the fuel
may re-enter on it.

Note the two premises that V14 step 1 turned into non-obligations:
`SubstTyping.openPath` now needs no `q.root.IsBound` (its image here is a
BARE LOCATION), and the `wf` field is `Path.Wf.subst` at that same
substitution. -/
theorem GSub.subst_loc {Θ : Sto} {ℓ : Nat} {E : Ty 0}
    (hE : Sto.Lookup Θ ℓ E) {A B : Ty 1} {n : Nat}
    (h : GSub Θ (Ctx.empty.push (.single (.var (.free ℓ)))) (.ty A) (.ty B) n) :
    GSub Θ .empty (.ty (A.open (.var (.free ℓ))))
      (.ty (B.open (.var (.free ℓ)))) n := by
  have hst : SubstTyping Θ (Subst.openPath (.var (.free ℓ) : Path 0))
      (Ctx.empty.push (.single (.var (.free ℓ)))) Ctx.empty :=
    SubstTyping.openPath (.var_free hE) .refl
  have hg : GSubstTyping Θ (Subst.openPath (.var (.free ℓ) : Path 0))
      (Ctx.empty.push (.single (.var (.free ℓ)))) Ctx.empty := by
    constructor
    · exact hst
    · intro x T hx m
      cases hx with
      | here =>
        have he : (Ty.single (.var (.free ℓ)) : Ty 0).weaken.subst
            (Subst.openPath (.var (.free ℓ) : Path 0)) = .single (.var (.free ℓ)) :=
          Ty.weaken_open
        rw [he]
        exact .refl
      | there hx' => exact nomatch hx'
  exact h.subst (gsubstLift Θ) hg



end LambdaP

section
open LambdaP
#print axioms LambdaP.GSub.subst
#print axioms LambdaP.GSub.to_sub
#print axioms LambdaP.Sub.to_gsub
#print axioms LambdaP.GSub.subst_loc
end
