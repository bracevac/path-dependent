import Coercions.Selective.Fsub
/-!
# Probe P2: hidden and dynamic chains, minimality of the examples

In `ctxYX` (`Y <: Top → Top, X <: Y`), `X = var 0`, `Y = var 1`; in `Witness.Γ3`
(`Z <: Top → Top, Y <: Z, X <: Y`), `X, Y, Z = var 0, 1, 2`.
-/
namespace SelFsub.Review2
open SelFsub SelFsub.Witness SelFsub.Examples

/-! ## One written step suffices where the examples write two -/

/-- `argProg` with the single cast `x ▷ step[X, Y]`: the second step `Y ≤₀ Top → Top` is the
implicit argument check. -/
theorem arg_one_written_step :
    synthTm .nil [] (argProg (.cast (.var 0) (.step (.var 0) (.var 1)))) =
      some (.all tt (.all (.var 0) (.arr (.var 0) tt))) := by decide

/-- The reduct of `tb_step` with one written step; `tbReduct` ("a hand-minimal annotation")
writes two. -/
def tbReduct1 : Tm 2 := .lam (.var 0) (.app (.lam tt (.var 0)) (.cast (.var 0) (.step (.var 0) (.var 1))))
theorem tbReduct1_erase : tbReduct1.erase = tbReductBare := rfl
theorem tbReduct1_typed : synthTm ctxYX [] tbReduct1 = some (.arr (.var 0) tt) := by decide
theorem tbReduct_two_steps : tbReduct ≠ tbReduct1 := by decide

/-- The callee example with one written step: `F ▷ allBound step[Y, Top → Top]`, then `[X]`
with the implicit `X ≤₀ Y`. -/
def calleeApp1 : Tm 2 := .tapp (.cast calleeF ((Cert.step (.var 1) tt).allBound calleeBody)) (.var 0)
theorem calleeApp1_typed : synthTm ctxYX [] calleeApp1 = some (.arr (.var 0) tt) := by decide

/-! ## A cast-free program whose β-reduct needs a chain at a type-application bound

`(λ(g : ∀(Z <: Y). Z → Z). g [X]) f` with `f = Λ(Z <: Top → Top). λ(z : Z). z`. The argument
check `∀(Z <: Top → Top). Z → Z ≤₀ ∀(Z <: Y). Z → Z` is one primitive universal step (bound
`Y ≤₀ Top → Top`); the bound check of `g [X]` is `X ≤₀ Y`. After β the bound check of `f [X]` is
`X ≤₀ Top → Top`, two bound steps. -/

def fId : Tm 2 := .tlam tt (.lam (.var 0) (.var 0))
def gTy : Ty 2 := .all (.var 1) (.arr (.var 0) (.var 0))
def gProg : Tm 2 := .app (.lam gTy (.tapp (.var 0) (.var 0))) fId
def gReductBare : Tm 2 := .tapp fId (.var 0)

theorem gProg_castfree : gProg.erase = gProg := rfl
theorem gProg_typed : synthTm ctxYX [] gProg = some (.arr (.var 0) (.var 0)) := by decide
theorem g_step : Step gProg.erase gReductBare := .beta .tlam
theorem g_bare_rejected : synthTm ctxYX [] gReductBare = none := by decide
/-- Repaired by one written step on the callee. -/
def gReduct : Tm 2 :=
  .tapp (.cast fId ((Cert.step (.var 1) tt).allBound (.arr (.var 0) (.var 0)))) (.var 0)
theorem gReduct_erase : gReduct.erase = gReductBare := rfl
theorem gReduct_typed : synthTm ctxYX [] gReduct = some (.arr (.var 0) (.var 0)) := by decide

/-! ## Three implicit steps, one per application, meet after two β-steps

In `Γ3`, with `Hᵢ = Xᵢ → Top` for `X₀ = Z`, `X₁ = Y`, `X₂ = X` and `v = λ(z : Top → Top). z`:
`(λ(h₀ : H₀). (λ(h₁ : H₁). (λ(h₂ : H₂). h₂) h₁) h₀) v`, cast-free; each argument check is one
primitive step. After two β-steps `v` meets `H₂`, which needs `X ≤ Top → Top` (three bound steps). -/

def H0 : Ty 3 := .arr (.var 2) .top
def H1 : Ty 3 := .arr (.var 1) .top
def H2 : Ty 3 := .arr (.var 0) .top
def vId : Tm 3 := .lam tt (.var 0)
def hProg : Tm 3 :=
  .app (.lam H0 (.app (.lam H1 (.app (.lam H2 (.var 0)) (.var 0))) (.var 0))) vId
def hMid : Tm 3 := .app (.lam H1 (.app (.lam H2 (.var 0)) (.var 0))) vId
def hReductBare : Tm 3 := .app (.lam H2 (.var 0)) vId

theorem hProg_typed : synthTm Γ3 [] hProg = some H2 := by decide
theorem h_steps : Steps hProg.erase hReductBare := .step (.beta .lam) (.step (.beta .lam) .refl)
theorem hMid_bare_rejected : synthTm Γ3 [] hMid = none := by decide
theorem h_bare_rejected : synthTm Γ3 [] hReductBare = none := by decide
/-- One written step at the argument is not enough here, -/
theorem h_one_step_rejected :
    synthTm Γ3 [] (.app (.lam H2 (.var 0)) (.cast vId (.step (.arr tt tt) H0))) = none := by decide
/-- two are (the third is the implicit check `H₁ ≤₀ H₂`). -/
theorem h_two_steps_typed :
    synthTm Γ3 [] (.app (.lam H2 (.var 0))
      (.cast vId (.seq (.step (.arr tt tt) H0) (.step H0 H1)))) = some H2 := by decide

#print axioms arg_one_written_step
#print axioms tbReduct1_typed
#print axioms calleeApp1_typed
#print axioms gProg_typed
#print axioms g_bare_rejected
#print axioms gReduct_typed
#print axioms hProg_typed
#print axioms h_bare_rejected
#print axioms h_one_step_rejected
#print axioms h_two_steps_typed

/-! ## No chain inside `Prim`'s universal rule

The body is compared under the target bound, so a bound step on the bound variable yields the
target bound and does not compose with the bound comparison: `∀(Z <: Top → Top). Z ≤₀ ∀(Z <: Y). Y`
holds, `∀(Z <: Top → Top). Z ≤₀ ∀(Z <: Y). Top → Top` does not (declaratively it holds through
`Z <: Y <: Top → Top`). -/
theorem all_rule_target_bound : Prim ctxYX (.all tt (.var 0)) (.all (.var 1) (.var 2)) := by decide
theorem all_rule_no_chain : ¬ Prim ctxYX (.all tt (.var 0)) (.all (.var 1) tt) := by decide
theorem all_rule_chain_cert : CTy ctxYX
    (Cert.all (.step (.var 1) tt) (.seq (.step (.var 0) (.var 2)) (.step (.var 2) tt)))
    (.all tt (.var 0)) (.all (.var 1) tt) := by decide

#print axioms all_rule_no_chain
#print axioms all_rule_chain_cert

end SelFsub.Review2
