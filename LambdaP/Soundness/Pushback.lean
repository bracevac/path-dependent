import LambdaP.Soundness.Store

/-!
The trans-free runtime subtyping pipeline (deviation 9 endgame):

1. `SSub`: `Sub` at the empty context with a derivation-size index
   (minidot's `stp`). Structural premises are sized (the pushback
   recursion walks them); congruence premises and wellformedness stay
   at the general judgment (lazy). At scope 0 the evidence-shaped
   selection rules of `Sub` are vacuous — `Var 0` has no bound
   variables — so runtime derivations are forced through the
   store-anchored rules, which is what makes this complete for
   `Sub Θ ∅` and invertible after pushback.
-/

namespace LambdaP

/-- Sized runtime subtyping over proper types at the empty context. -/
inductive SSub (Θ : Sto) : Ty 0 -> Ty 0 -> Nat -> Prop where
| refl :
  SSub Θ T T (n+1)
| trans :
  SSub Θ T1 T2 n -> SSub Θ T2 T3 n ->
  SSub Θ T1 T3 (n+1)
| bot :
  SSub Θ .bot T (n+1)
| top :
  SSub Θ T .top (n+1)
| var_free :
  Sto.Lookup Θ ℓ T ->
  SSub Θ (.single (.var (.free ℓ))) T.fromClosed (n+1)
| symm :
  Path.Wf Θ .empty p ->
  SSub Θ (.single p) (.single q) n ->
  SSub Θ (.single q) (.single p) (n+1)
| fst_tm :
  SSub Θ (.single p) (.pairTm S a T) n ->
  SSub Θ (.single p.fst) S (n+1)
| fst_ty :
  SSub Θ (.single p) (.pairTy S A T1 T2) n ->
  SSub Θ (.single p.fst) S (n+1)
| sel_tm :
  SSub Θ (.single p) (.pairTm S a T) n ->
  SSub Θ (.single (p.sel a)) (T.open p.fst) (n+1)
| sel_hi_loc :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A (Ty.weaken W) (Ty.weaken W)) ->
  SSub Θ (Ty.fromClosed W) U n ->
  SSub Θ (.tsel p A) U (n+1)
| sel_lo_loc :
  Chains Θ p m ->
  Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A (Ty.weaken W) (Ty.weaken W)) ->
  SSub Θ U (Ty.fromClosed W) n ->
  SSub Θ U (.tsel p A) (n+1)
| arrow :
  Sub Θ .empty (.ty S') (.ty S) ->
  Sub Θ (Ctx.empty.push S') (.ty T) (.ty T') ->
  SSub Θ (.arrow S T) (.arrow S' T') (n+1)
| pair_tm :
  Sub Θ .empty (.ty S) (.ty S') ->
  Sub Θ (Ctx.empty.push S) (.ty T) (.ty T') ->
  SSub Θ (.pairTm S a T) (.pairTm S' a T') (n+1)
| pair_ty :
  Sub Θ .empty (.ty S) (.ty S') ->
  Sub Θ (Ctx.empty.push S) (.intv T1 T2) (.intv T1' T2') ->
  SSub Θ (.pairTy S A T1 T2) (.pairTy S' A T1' T2') (n+1)
| repl :
  Path.Wf Θ .empty p -> Path.Wf Θ .empty q ->
  SSub Θ (.single p) (.single q) n ->
  SSub Θ (.single q) (.single p) n ->
  SSub Θ (Ty.open T p) (Ty.open T q) (n+1)
| skip_tm :
  SSub Θ (.single p) (.pairTm S b T) n ->
  a ≠ b ->
  SSub Θ (.single (p.sel a)) (.single ((Path.fst p).sel a)) (n+1)
| skip_ty :
  SSub Θ (.single p) (.pairTy S B T1 T2) n ->
  SSub Θ (.single (p.sel a)) (.single ((Path.fst p).sel a)) (n+1)

/-- Growing a derivation by one (right-premise growth keeps the size
arithmetic definitional). -/
theorem SSub.succ {Θ} {T1 T2 : Ty 0} {n : Nat}
    (h : SSub Θ T1 T2 n) : SSub Θ T1 T2 (n+1) := by
  induction h with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | bot => exact .bot
  | top => exact .top
  | var_free hl => exact .var_free hl
  | symm hw _ ih => exact .symm hw ih
  | fst_tm _ ih => exact .fst_tm ih
  | fst_ty _ ih => exact .fst_ty ih
  | sel_tm _ ih => exact .sel_tm ih
  | sel_hi_loc hc hl _ ih => exact .sel_hi_loc hc hl ih
  | sel_lo_loc hc hl _ ih => exact .sel_lo_loc hc hl ih
  | arrow h1 h2 => exact .arrow h1 h2
  | pair_tm h1 h2 => exact .pair_tm h1 h2
  | pair_ty h1 h2 => exact .pair_ty h1 h2
  | repl hwp hwq _ _ ih1 ih2 => exact .repl hwp hwq ih1 ih2
  | skip_tm _ hne ih => exact .skip_tm ih hne
  | skip_ty _ ih => exact .skip_ty ih

/-- Sizes are monotone (minidot's upgrade idiom). -/
theorem SSub.mono {Θ} {T1 T2 : Ty 0} {n n' : Nat}
    (h : SSub Θ T1 T2 n) (hle : n ≤ n') : SSub Θ T1 T2 n' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction k with
  | zero => exact h
  | succ k ih => exact ih.succ

end LambdaP
