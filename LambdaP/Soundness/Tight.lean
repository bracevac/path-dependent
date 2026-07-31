import LambdaP.Soundness.Precise

/-!
Tight subtyping: the runtime-restricted judgment at the empty context.
Selection rules anchor to precise store entries (whose member intervals
are aliases, so both bounds collapse to the stored member type);
replacement and symmetry take store-side resolution (`Chains`) evidence
instead of derivation premises. Context-extending premises stay general
(as in pDOT's tight typing). V13: the two anchored selection rules now
map onto the store-anchored `sel_hi_loc`/`sel_lo_loc` of deviation 9
(which is what those rules were introduced for), `pair_ty` carries the
two split interval legs of the current `Sub.pair_ty`, and the `ival` rule
is gone with `Sub`'s. NOTE (V13 route decision): this layer is SUPERSEDED
by `SSub`/`SOut` (`Soundness/Pushback.lean` + `Embedding.lean`) — kept as
documentation, not on the critical path. The collapse theorem (general implies
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
  Sub Θ (Ctx.empty.push S) (.ty T1') (.ty T1) ->
  Sub Θ (Ctx.empty.push S) (.ty T2) (.ty T2') ->
  TightSub Θ (.ty (.pairTy S A T1 T2)) (.ty (.pairTy S' A T1' T2'))
| repl :
  Chains Θ p ℓ ->
  Chains Θ q ℓ ->
  TightSub Θ (.ty (Ty.open T p)) (.ty (Ty.open T q))

/- `Chains.to_sub`, `Chains.wf` and `Chains.to_sub_entry` were promoted
into `Soundness/Pushback.lean` (live build) during the pushback campaign;
they are imported from there (V13). -/

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
    -- deviation 9: the store-anchored rule is exactly this tight rule
    have hs := Sub.sel_hi_loc (Γ := (Ctx.empty : Ctx 0)) hc hl
    rwa [Ty.fromClosed_zero] at hs
  | sel_lo hc hl =>
    have hs := Sub.sel_lo_loc (Γ := (Ctx.empty : Ctx 0)) hc hl
    rwa [Ty.fromClosed_zero] at hs
  | arrow _ hg ih => exact .arrow ih hg
  | pair_tm _ hg ih => exact .pair_tm ih hg
  | pair_ty _ hg1 hg2 ih => exact .pair_ty ih hg1 hg2
  | repl hcp hcq =>
    exact .repl hcp.wf hcq.wf
      (.trans hcp.to_sub (.symm hcq.wf hcq.to_sub))
      (.trans hcq.to_sub (.symm hcp.wf hcp.to_sub))

end LambdaP
