import LambdaP.Soundness.Progress
import LambdaP.Soundness.RealizedSubst

/-!
Smoke tests: small derivations exercising the system, and an axiom audit
of the main theorems (they must use nothing beyond `propext` and
`Quot.sound`).
-/

namespace LambdaP.Examples

open LambdaP

/-- ⊤..⊤ is a wellformed interval over any store/context. -/
example {Θ : Sto} {Γ : Ctx s} : Wf Θ Γ (.intv .top .top) :=
  .intv .top .top .refl

/-- Sealing: a pair with the alias interval T..T widens to the fully
abstract member ⊥..⊤ — componentwise, guard-free (deviation 11). -/
example {Θ : Sto} {Γ : Ctx s} {S : Ty s} {T : Ty s} {A : Name} :
    Sub Θ Γ (.ty (.pairTy S A T.weaken T.weaken))
            (.ty (.pairTy S A .bot .top)) :=
  .pair_ty .refl .bot .top

/-- The identity function at ⊤, typed closed. -/
example {Θ : Sto} : HasType Θ .empty (.abs .top (.path (.var (.bound .here)))) (.arrow .top .top) :=
  .abs .top (.sub (.path (.var_bound .here)) .top .top)

/-- A dependent pair with a sealed type member: typing ⟨y, A = ⊤⟩ gives the
precise singleton pair type with the alias interval ⊤..⊤. -/
example {Θ : Sto} {ℓ : Nat} {A : Name} (hl : Sto.Lookup Θ ℓ .top) :
    HasType Θ .empty (.pairTy (.free ℓ) A .top)
      (.pairTy (.single (.var (.free ℓ))) A (Ty.top).weaken (Ty.top).weaken) :=
  .pair_ty (.var_free hl) .top

/-! ### A sealed abstract type, end to end

`let f = λ(x:⊤).x in let p = ⟨f, A = ⊤⟩ in let g = λ(y: p.A).y in g f`
seals ⊤ as the abstract member `p.A`, consumes it through a function
whose domain is the abstract type, and runs to a location. -/

/-- The sealed-member example program. -/
def sealed : Tm 0 :=
  .letin (.abs .top (.path (.var (.bound .here))))
    (.letin (.pairTy (.bound .here) 0 .top)
      (.letin (.abs (.tsel (.var (.bound .here)) 0) (.path (.var (.bound .here))))
        (.app (.var (.bound .here)) (.var (.bound (.there (.there .here)))))))

/-- It runs: three allocations, one β-step, a final location. -/
example : ∃ h', Reduce [] sealed h' (.path (.var (.free 0))) :=
  ⟨_, .step (.let_val .abs)
      (.step (.let_val .pairTy)
        (.step (.let_val .abs)
          (.step (.apply .var .var rfl) .refl)))⟩

/-- The three let-bound types of `sealed`, in order. -/
private abbrev SealF : Ty 0 := .arrow .top .top
private abbrev SealP : Ty 1 :=
  .pairTy (.single (.var (.bound .here))) 0 (Ty.top).weaken (Ty.top).weaken
private abbrev SealG : Ty 2 :=
  .arrow (.tsel (.var (.bound .here)) 0) (.single (.var (.bound .here)))
private abbrev SealCtx : Ctx 3 :=
  ((Ctx.empty.push SealF).push SealP).push SealG

/-- ... and it types, at ⊤, in the empty store. The domain of `g` is the
abstract selection `p.A`; the argument `f` enters it through the sealed
member's lower bound (`sel-lo`, whose subject is bound-rooted). -/
example : HasType [] .empty sealed .top := by
  refine .letin (.abs .top (.sub (.path (.var_bound .here)) .top .top)) .top ?_
  refine .letin (.pair_ty (.var_bound .here) .top) .top ?_
  refine .letin
    (.abs (.tsel (.var_bound .here) (.var_bound .here)) (.path (.var_bound .here)))
    .top ?_
  have hlkp : Ctx.LookupVar SealCtx (.there .here) SealP.weaken.weaken :=
    .there .here
  have hwp : Path.Wf [] SealCtx (.var (.bound (.there .here))) := .var_bound hlkp
  have hpair : Sub [] SealCtx
      (.ty (.single (.var (.bound (.there .here))))) (.ty SealP.weaken.weaken) :=
    .var_bound hlkp
  have hsel : Sub [] SealCtx (.ty .top)
      (.ty (.tsel (.var (.bound (.there .here))) 0)) := by
    have h := Sub.sel_lo hwp hpair .refl
    exact h
  have hwfD : Wf [] SealCtx (.ty (.tsel (.var (.bound (.there .here))) 0)) :=
    .tsel hwp hpair
  refine .sub
    (.app (S := .tsel (.var (.bound (.there .here))) 0)
          (T := .single (.var (.bound .here))) ?hg ?hf) .top .top
  case hg =>
    refine .sub (.path (.var_bound .here)) (.var_bound .here) ?_
    exact .arrow hwfD (.single (.var_bound .here))
  case hf =>
    exact .sub (.path (.var_bound (.there (.there .here)))) (.trans .top hsel) hwfD

/-! ### Consistency and collapse-freedom (now syntactic) -/

/-- Subtyping is consistent at the empty store, unconditionally. -/
theorem consistency : ¬ Sub [] .empty (.ty .top) (.ty .bot) :=
  Sub.consistency_empty

/-! ### Axiom audit -/

#print axioms LambdaP.Sub.to_ssub
#print axioms LambdaP.SSub.invert
#print axioms LambdaP.Sub.consistency
#print axioms LambdaP.Sub.no_bot_path
#print axioms LambdaP.Path.Wf.chains
#print axioms LambdaP.Sub.canonical_arrow
#print axioms LambdaP.progress
#print axioms LambdaP.Sub.subst
#print axioms LambdaP.Examples.consistency

end LambdaP.Examples
