import LambdaP.Soundness.Invertible

/-!
Syntactic possible-types interpretation: the store-side mirror of the
semantic denotation, with `Chains` for evaluation and the inductive
`Inv` in place of the level-indexed oracle at member boundaries. Because
`Inv` is a previously defined constant, the recursion is on path-erased
structure alone — no levels, no tie. The type-member sandwich stores
`PT`/`Inv` transfer fields, which is what makes the selection cases of
the collapse exact (mirroring the semantic proof's tie identities).
-/

namespace LambdaP

/-- Possible-types interpretation of a closed type over the store. -/
def PT (Θ : Sto) : Ty 0 -> Nat -> Prop
| .top, _ => True
| .bot, _ => False
| .single q, ℓ => Chains Θ q ℓ
| .tsel q A, ℓ =>
    ∃ (m ℓ1 : Nat) (W : Ty 0), Chains Θ q m ∧
      Sto.Lookup Θ m (.pairTy (.single (.var (.free ℓ1))) A W.weaken W.weaken) ∧
      Inv Θ ℓ W
| .arrow S T, ℓ =>
    ∃ T0 T1, Sto.Lookup Θ ℓ (.arrow T0 T1) ∧
      Sub Θ .empty (.ty S) (.ty T0) ∧
      Sub Θ (Ctx.empty.push S) (.ty T1) (.ty T)
| .pairTm S a T, ℓ =>
    ∃ ℓ1 ℓ2, Sto.Lookup Θ ℓ
        (.pairTm (.single (.var (.free ℓ1))) a (Ty.single (.var (.free ℓ2))).weaken) ∧
      Sub Θ .empty (.ty (.single (.var (.free ℓ1)))) (.ty S) ∧
      PT Θ S ℓ1 ∧
      ∀ q', Chains Θ q' ℓ1 -> PT Θ (T.open q') ℓ2
| .pairTy S A T1 T2, ℓ =>
    ∃ (ℓ1 : Nat) (W : Ty 0), Sto.Lookup Θ ℓ
        (.pairTy (.single (.var (.free ℓ1))) A W.weaken W.weaken) ∧
      Sub Θ .empty (.ty (.single (.var (.free ℓ1)))) (.ty S) ∧
      PT Θ S ℓ1 ∧
      ∀ q', Chains Θ q' ℓ1 ->
        (∀ y, PT Θ (T1.open q') y -> Inv Θ y W) ∧
        (∀ y, Inv Θ y W -> PT Θ (T2.open q') y)
termination_by T _ => T.structSize
decreasing_by all_goals simp [Ty.structSize, Ty.structSize_open]; omega

/-- The generalized-type reading (intervals carry no membership). -/
def PTau (Θ : Sto) (ℓ : Nat) : Tau 0 -> Prop
| .ty U => PT Θ U ℓ
| .intv _ _ => True

end LambdaP
