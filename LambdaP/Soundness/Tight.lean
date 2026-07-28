import LambdaP.Soundness.Precise

/-!
Tight subtyping: the runtime-restricted judgment at the empty context.
Selection rules anchor to precise store entries (whose member intervals
are aliases, so both bounds collapse to the stored member type);
replacement and symmetry take store-side resolution (`Chains`) evidence
instead of derivation premises. Context-extending premises stay general
(as in pDOT's tight typing). The collapse theorem (general implies
tight over a well-typed heap) is the goal of this layer; this file
gives the definition and the embedding back into general subtyping.
-/

namespace LambdaP

/-- Tight subtyping over a store typing, empty context only. -/
inductive TightSub (Θ : Sto) : Tau 0 -> Tau 0 -> Prop where
| refl :
  TightSub Θ τ τ
| trans :
  TightSub Θ τ1 τ2 ->
  TightSub Θ τ2 τ3 ->
  TightSub Θ τ1 τ3
| bot :
  TightSub Θ (.ty .bot) (.ty T)
| top :
  TightSub Θ (.ty T) (.ty .top)
| var_free :
  Sto.Lookup Θ ℓ T ->
  TightSub Θ (.ty (.single (.var (.free ℓ)))) (.ty T.fromClosed)
| symm :
  Chains Θ p ℓp ->
  TightSub Θ (.ty (.single p)) (.ty (.single q)) ->
  TightSub Θ (.ty (.single q)) (.ty (.single p))
| fst_tm :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTm (.single (.var (.free ℓ1))) a Tc) ->
  TightSub Θ (.ty (.single p.fst)) (.ty (.single (.var (.free ℓ1))))
| fst_ty :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A T1 T2) ->
  TightSub Θ (.ty (.single p.fst)) (.ty (.single (.var (.free ℓ1))))
| sel_tm :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTm S a (Ty.single (.var (.free ℓ2))).weaken) ->
  TightSub Θ (.ty (.single (p.sel a))) (.ty (.single (.var (.free ℓ2))))
| sel_hi :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A W.weaken W.weaken) ->
  TightSub Θ (.ty (.tsel p A)) (.ty W)
| sel_lo :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A W.weaken W.weaken) ->
  TightSub Θ (.ty W) (.ty (.tsel p A))
| arrow :
  TightSub Θ (.ty S') (.ty S) ->
  Sub Θ (Ctx.empty.push S') (.ty T) (.ty T') ->
  TightSub Θ (.ty (.arrow S T)) (.ty (.arrow S' T'))
| pair_tm :
  TightSub Θ (.ty S) (.ty S') ->
  Sub Θ (Ctx.empty.push S) (.ty T) (.ty T') ->
  TightSub Θ (.ty (.pairTm S a T)) (.ty (.pairTm S' a T'))
| pair_ty :
  TightSub Θ (.ty S) (.ty S') ->
  Sub Θ (Ctx.empty.push S) (.intv T1 T2) (.intv T1' T2') ->
  TightSub Θ (.ty (.pairTy S A T1 T2)) (.ty (.pairTy S' A T1' T2'))
| ival :
  TightSub Θ (.ty S') (.ty S) ->
  TightSub Θ (.ty T) (.ty T') ->
  TightSub Θ (.ty S) (.ty T) ->
  TightSub Θ (.intv S T) (.intv S' T')
| repl :
  Chains Θ p ℓ ->
  Chains Θ q ℓ ->
  TightSub Θ (.ty (Ty.open T p)) (.ty (Ty.open T q))

/-! ### Chains embed into the general judgments -/

/-- Store-side resolution yields general singleton subtyping to the
target location (the Θ-mirror of `PathEval.to_sub`). -/
theorem Chains.to_sub {Θ : Sto} {p : Path 0} {ℓ : Nat}
    (hc : Chains Θ p ℓ) :
    Sub Θ .empty (.ty (.single p)) (.ty (.single (.var (.free ℓ)))) := by
  induction hc with
  | loc _ => exact .refl
  | fst_tm _ hl ih =>
    have hvf := Sub.var_free (Γ := (Ctx.empty : Ctx 0)) hl
    rw [Ty.fromClosed_zero] at hvf
    exact .fst_tm (.trans ih hvf)
  | fst_ty _ hl ih =>
    have hvf := Sub.var_free (Γ := (Ctx.empty : Ctx 0)) hl
    rw [Ty.fromClosed_zero] at hvf
    exact .fst_ty (.trans ih hvf)
  | sel _ hl ih =>
    have hvf := Sub.var_free (Γ := (Ctx.empty : Ctx 0)) hl
    rw [Ty.fromClosed_zero] at hvf
    have hs := Sub.sel_tm (.trans ih hvf)
    rwa [Ty.weaken_open] at hs

/-- Store-side resolution yields general path wellformedness. -/
theorem Chains.wf {Θ : Sto} {p : Path 0} {ℓ : Nat}
    (hc : Chains Θ p ℓ) : Path.Wf Θ .empty p := by
  induction hc with
  | loc hl => exact .var_free hl
  | fst_tm hc hl ih =>
    have hvf := Sub.var_free (Γ := (Ctx.empty : Ctx 0)) hl
    rw [Ty.fromClosed_zero] at hvf
    exact .fst_tm ih (.trans hc.to_sub hvf)
  | fst_ty hc hl ih =>
    have hvf := Sub.var_free (Γ := (Ctx.empty : Ctx 0)) hl
    rw [Ty.fromClosed_zero] at hvf
    exact .fst_ty ih (.trans hc.to_sub hvf)
  | sel hc hl ih =>
    have hvf := Sub.var_free (Γ := (Ctx.empty : Ctx 0)) hl
    rw [Ty.fromClosed_zero] at hvf
    exact .sel ih (.trans hc.to_sub hvf)

/-- The precise pair-type evidence used by the anchored selection rules,
in general form: a chaining path sits below its target's entry. -/
theorem Chains.to_sub_entry {Θ : Sto} {p : Path 0} {m : Nat} {T : Ty 0}
    (hc : Chains Θ p m) (hl : Sto.Lookup Θ m T) :
    Sub Θ .empty (.ty (.single p)) (.ty T) := by
  have hvf := Sub.var_free (Γ := (Ctx.empty : Ctx 0)) hl
  rw [Ty.fromClosed_zero] at hvf
  exact .trans hc.to_sub hvf

/-- Tight subtyping is sound for general subtyping. -/
theorem TightSub.to_sub {Θ : Sto} {τ1 τ2 : Tau 0}
    (h : TightSub Θ τ1 τ2) : Sub Θ .empty τ1 τ2 := by
  induction h with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | bot => exact .bot
  | top => exact .top
  | var_free hl => exact .var_free hl
  | symm hc _ ih => exact .symm hc.wf ih
  | fst_tm hc hl => exact (Chains.fst_tm hc hl).to_sub
  | fst_ty hc hl => exact (Chains.fst_ty hc hl).to_sub
  | sel_tm hc hl => exact (Chains.sel hc hl).to_sub
  | sel_hi hc hl =>
    have hs := Sub.sel_hi (hc.to_sub_entry hl) .refl
    rwa [Ty.weaken_open] at hs
  | sel_lo hc hl =>
    have hs := Sub.sel_lo hc.wf (hc.to_sub_entry hl) .refl
    rwa [Ty.weaken_open] at hs
  | arrow _ hg ih => exact .arrow ih hg
  | pair_tm _ hg ih => exact .pair_tm ih hg
  | pair_ty _ hg ih => exact .pair_ty ih hg
  | ival _ _ _ ih1 ih2 ih3 => exact .ival ih1 ih2 ih3
  | repl hcp hcq =>
    exact .repl hcp.wf hcq.wf
      (.trans hcp.to_sub (.symm hcq.wf hcq.to_sub))
      (.trans hcq.to_sub (.symm hcp.wf hcp.to_sub))

end LambdaP
