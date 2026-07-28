import LambdaP.Soundness.Safety
import LambdaP.Soundness.Invertible

/-!
Smoke tests: small derivations exercising the system, and an axiom audit
of the main theorems (they must use nothing beyond `propext`, `Quot.sound`,
and `Classical.choice`).
-/

namespace LambdaP.Examples

open LambdaP

/-- ⊤..⊤ is a wellformed interval over any store/context. -/
example {Θ : Sto} {Γ : Ctx s} : Wf Θ Γ (.intv .top .top) :=
  .intv .top .top .refl

/-- Sealing: the alias interval T..T widens to the full interval ⊥..⊤
(the draft's motivating "sealed abstract type" pattern), provided T is a
wellformed non-empty bound. -/
example {Θ : Sto} {Γ : Ctx s} {T : Ty s} :
    Sub Θ Γ (.intv T T) (.intv .bot .top) :=
  .ival .bot .top .refl

/-- The identity function at ⊤, typed closed: λ(x:⊤).x : ⊤ → ⊤ ... via the
singleton: the body x has type single x <: ⊤ by subsumption. -/
example {Θ : Sto} : HasType Θ .empty (.abs .top (.path (.var (.bound .here)))) (.arrow .top .top) :=
  .abs .top (.sub (.path (.var_bound .here)) .top .top)

/-- A dependent pair with a sealed type member: typing ⟨y, A = ⊤⟩ gives the
precise singleton pair type with the alias interval ⊤..⊤. -/
example {Θ : Sto} {ℓ : Nat} (hl : Sto.Lookup Θ ℓ .top) :
    HasType Θ .empty (.pairTy (.free ℓ) A .top)
      (.pairTy (.single (.var (.free ℓ))) A (Ty.top).weaken (Ty.top).weaken) :=
  .pair_ty (.var_free hl) .top

/-- Empty-heap safety, specialized: any term typed against the empty store
reduces without getting stuck, given the semantic-store hypothesis. -/
example (hgood : SemStoExists) {t t' : Tm 0} {h' : Heap} {T : Ty 0}
    (ht : HasType [] .empty t T) (hred : Reduce [] t h' t') :
    Final t' ∨ ∃ h'' t'', Step h' t' h'' t'' :=
  type_safety_init hgood ht hred

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
member's lower bound (`sel-lo`). -/
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

/-! ### Consistency -/

/-- Subtyping is consistent: ⊤ <: ⊥ is underivable at the empty context
(unconditionally — the empty heap's semantic store typing is trivial). -/
theorem consistency : ¬ Sub [] .empty (.ty .top) (.ty .bot) := by
  intro h
  have hd := Sub.den_empty (Ξ := fun _ _ _ _ => True) h HeapTyped.empty (SemStoOk.empty (Ξ := fun _ _ _ _ => True)) 0 0
  simp only [Den] at hd
  exact hd trivial

/-! ### Axiom audit -/

#print axioms LambdaP.Sub.den
#print axioms LambdaP.progress
#print axioms LambdaP.preservation
#print axioms LambdaP.type_safety
#print axioms LambdaP.Den.open_coeval
#print axioms LambdaP.Examples.consistency
#print axioms LambdaP.TightSub.inv_closure

end LambdaP.Examples
