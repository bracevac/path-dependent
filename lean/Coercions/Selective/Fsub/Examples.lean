import Coercions.Selective.Fsub.Exact
import Coercions.Selective.Fsub.Witness
/-!
# Examples for the term layer

Kernel-checked programs, typed by `synthTm` under `decide`. Variables are de Bruijn
indices. In `ctxYX` (`Y <: Top → Top, X <: Y`) `X` is `var 0` and `Y` is `var 1`; the
composite `X ≤ Top → Top` takes two bound steps and is not primitive (`ctxYX_not`).

The written annotations below are not minimal: at each boundary the implicit check can
take one of the two bound steps, so one written step (`step[X, Y]` on an argument,
`step[Y, Top → Top]` under the bound lift on the callee) suffices where the full chain
is written. The examples show that a boundary adds at most one implicit step after the
last written cast.
-/
namespace SelFsub.Examples
open Witness (tt)

/-- `X ⇒ Y ⇒ Top → Top` in `ctxYX`. -/
def chain : Cert 2 := .seq (.step (.var 0) (.var 1)) (.step (.var 1) tt)

def idT : Tm n := .lam .top (.var 0)

/-! ## An argument two bound steps below the domain

`Λ(Y <: Top → Top). Λ(X <: Y). λ(x : X). (λ(g : Top → Top). g) a` for an argument `a`. -/

def argProg (a : Tm 2) : Tm 0 :=
  .tlam tt (.tlam (.var 0) (.lam (.var 0) (.app (.lam tt (.var 0)) a)))

/-- Bare, the argument `x : X` would need `X ≤₀ Top → Top`. -/
theorem arg_bare_rejected : synthTm .nil [] (argProg (.var 0)) = none := by decide
/-- One written step `step[X, Top → Top]` is not primitive either. -/
theorem arg_one_step_rejected :
    synthTm .nil [] (argProg (.cast (.var 0) (.step (.var 0) tt))) = none := by decide
theorem arg_cast_typed : synthTm .nil [] (argProg (.cast (.var 0) chain)) =
    some (.all tt (.all (.var 0) (.arr (.var 0) tt))) := by decide

/-- The program applied to `Top → Top`, `Top → Top` and `λ(z : Top). z`. -/
def argRun : Tm 0 := .app (.tapp (.tapp (argProg (.cast (.var 0) chain)) tt) tt) idT

theorem argRun_typed : synthTm .nil [] argRun = some tt := by decide
/-- It runs to a value: two type-β steps and two β steps. -/
theorem argRun_steps : Steps argRun.erase idT :=
  .step (.appL (.tappL .tbeta))
    (.step (.appL .tbeta) (.step (.beta .lam) (.step (.beta .lam) .refl)))
theorem argRun_value : Value (idT : Tm 0) := .lam

/-! ## Nested casts compose only through their written endpoints

Under `x : X` in `ctxYX`. -/

theorem nest_typed : synthTm ctxYX [] (.lam (.var 0) (.cast (.cast (.var 0)
    (.step (.var 0) (.var 1))) (.step (.var 1) tt))) = some (.arr (.var 0) tt) := by decide
/-- The subject of a cast must have exactly the certificate's source: `x : X` is not
cast by `step[Y, Top → Top]`. -/
theorem nest_subject_rejected :
    synthTm ctxYX [] (.lam (.var 0) (.cast (.var 0) (.step (.var 1) tt))) = none := by decide
/-- Both casts check on their own, but `Y` and `Top → Top` differ. -/
theorem nest_mismatch_rejected : synthTm ctxYX [] (.lam (.var 0) (.cast (.cast (.var 0)
    (.step (.var 0) (.var 1))) (.step tt tt))) = none := by decide

/-! ## A type argument two bound steps below the bound: cast on the callee

`F = Λ(Z <: Top → Top). λ(z : Z). (λ(g : Top → Top). g) z`, applied to `X` in `ctxYX`. -/

def calleeF : Tm 2 := .tlam tt (.lam (.var 0) (.app (.lam tt (.var 0)) (.var 0)))
/-- The body of the type of `F`, `Z → (Top → Top)`. -/
def calleeBody : Ty 3 := .arr (.var 0) tt

theorem calleeF_typed : synthTm ctxYX [] calleeF = some (.all tt calleeBody) := by decide
theorem callee_bare_rejected : synthTm ctxYX [] (.tapp calleeF (.var 0)) = none := by decide

/-- `F ▷ allBound chain : ∀(Z <: X). Z → (Top → Top)`, then `[X]` with `X ≤₀ X`. -/
def calleeApp : Tm 2 := .tapp (.cast calleeF (chain.allBound calleeBody)) (.var 0)

theorem calleeApp_typed : synthTm ctxYX [] calleeApp = some (.arr (.var 0) tt) := by decide

/-! ## Type-β: the reduct needs a certificate that the redex does not contain

Inside `F` the argument `z : Z` is checked by the bound step `Z ≤₀ Top → Top`. After
`[X/Z]` it would be `X ≤₀ Top → Top`, which is not primitive. -/

def tbReductBare : Tm 2 := .lam (.var 0) (.app (.lam tt (.var 0)) (.var 0))

theorem tb_step : Step calleeApp.erase tbReductBare := .tbeta
theorem tb_bare_rejected : synthTm ctxYX [] tbReductBare = none := by decide

/-- An annotation of the reduct with the written chain on the argument. -/
def tbReduct : Tm 2 := .lam (.var 0) (.app (.lam tt (.var 0)) (.cast (.var 0) chain))

theorem tbReduct_erase : tbReduct.erase = tbReductBare := rfl
theorem tbReduct_typed : synthTm ctxYX [] tbReduct = some (.arr (.var 0) tt) := by decide

/-- The entry for `Z` as the proof of preservation constructs it, transcribed by hand:
`step[X, X]` followed by the bound certificate that `Cert.allInv` extracts from the
callee's casts. The proof's witness is an existential in `Prop` and is not extracted. -/
def tbEntry : Cert 2 := .seq (.step (.var 0) (.var 0)) ((Cert.seq
  (.step (.all tt calleeBody) (.all tt calleeBody)) (chain.allBound calleeBody)).allInv.1)

theorem tbEntry_eq : tbEntry = .seq (.step (.var 0) (.var 0))
    (.seq (.seq (.step (.var 0) (.var 1)) (.step (.var 1) tt)) (.step tt tt)) := rfl
/-- `HTy.substTy` casts the argument by the substituted step `step[Z, Top → Top]`, which
`Cert.subst` turns into the entry. -/
theorem tb_arg_cast :
    (Cert.step (.var 0) tt).subst (sub0 (.var 0)) (instT 0 tbEntry) = tbEntry := rfl
theorem tb_arg_cast_typed : synthTm ctxYX []
    (.lam (.var 0) (.app (.lam tt (.var 0)) (.cast (.var 0) tbEntry))) =
      some (.arr (.var 0) tt) := by decide

/-! ## β: two implicit steps meet at one position

`(λ(h : Y → Top). (λ(k : X → Top). k) h) v` with `v = λ(z : Top → Top). z`. The outer
argument is checked by `(Top → Top) → (Top → Top) ≤₀ Y → Top` (through `Y ≤₀ Top → Top`),
the inner one by `Y → Top ≤₀ X → Top` (through `X ≤₀ Y`). After β the value meets the inner
domain directly, and `(Top → Top) → (Top → Top) ≤₀ X → Top` is not primitive. -/

def bV : Tm 2 := .lam tt (.var 0)
def YT : Ty 2 := .arr (.var 1) .top
def XT : Ty 2 := .arr (.var 0) .top
def bRedex : Tm 2 := .app (.lam YT (.app (.lam XT (.var 0)) (.var 0))) bV
def bReductBare : Tm 2 := .app (.lam XT (.var 0)) bV

theorem bRedex_typed : synthTm ctxYX [] bRedex = some XT := by decide
theorem b_step : Step bRedex.erase bReductBare := .beta .lam
theorem b_bare_rejected : synthTm ctxYX [] bReductBare = none := by decide

/-- One written step suffices: the outer implicit step is written on the value. -/
theorem b_min_typed :
    synthTm ctxYX [] (.app (.lam XT (.var 0)) (.cast bV (.step (.arr tt tt) YT))) = some XT := by
  decide

/-- A hand-written annotation of the reduct, transcribed from the construction in the
proof of preservation: the value cast by `step[V, S] ; dom` and the result by `cod`, with
`dom` and `cod` from `Cert.arrInv` of the callee's (here reflexive) certificate. The
proof's witness is an existential in `Prop` and is not extracted, so this term is
checked by `synthTm`, not compared with it. -/
def bReduct : Tm 2 :=
  .cast (.app (.lam XT (.var 0)) (.cast bV (.seq (.step (.arr tt tt) YT) (.step YT YT))))
    (.step XT XT)

theorem bReduct_erase : bReduct.erase = bReductBare := rfl
theorem bReduct_typed : synthTm ctxYX [] bReduct = some XT := by decide

end SelFsub.Examples
