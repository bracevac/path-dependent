import LambdaP.Soundness.Embedding

/-!
V13: CANDIDATE 1 — the scope-generic sized table `GSub` (the V14 seed).

NOT in the live build yet: `Sub.to_gsub`/`GSub.to_sub` need the
deviation-11 reversal (V14 step 1), and `SSub`'s congruence rows must be
re-based on `GSub` legs (V14 step 3). What IS settled here is the two
questions that decided the V13 route (see NOTES.md, "V13 ROUTE
DECISION"): the declaration is kernel-legal, and the instantiation
theorem `GSub.subst` — NOTES V12 §5's KNOWN OBSTACLE — goes through.

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
| ival :
  GSub Θ Γ (.ty S') (.ty S) n ->
  GSub Θ Γ (.ty T) (.ty T') n ->
  GSub Θ Γ (.intv S T) (.intv S' T') (n+1)
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
  conforms : ∀ {x : BVar s1} {T : Ty s1}, Ctx.LookupVar Γ x T ->
    ∀ n, GSub Θ Δ (.ty (.single (σ.var x))) (.ty (T.subst σ)) (n+1)
  wf : ∀ {p : Path s1}, Path.Wf Θ Γ p -> Path.Wf Θ Δ (p.subst σ)

/-- Closure under binder extension (routine: `var_bound .here` for the
new variable + a `GSub` weakening lemma for the rest — the same proof as
`SubstTyping.lift`). Assumed here, since it is orthogonal to the flagged
obstacle. -/
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
  | .ival h1 h2 => fun hσ => .ival (h1.subst hlift hσ) (h2.subst hlift hσ)
  | .repl hwp hwq h1 h2 => fun hσ => by
    simp only [Tau.subst]
    rw [← Ty.open_subst_comm, ← Ty.open_subst_comm]
    exact GSub.repl (hσ.wf hwp) (hσ.wf hwq) (h1.subst hlift hσ) (h2.subst hlift hσ)

end LambdaP

section
open LambdaP
#print axioms LambdaP.GSub.subst
end
