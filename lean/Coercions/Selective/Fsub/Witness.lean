import Coercions.Selective.Fsub.Complete
import Coercions.Selective.Fsub.Invert
/-!
# Witnesses

Kernel-checked examples: chains of bound steps in both associations, chains inside
arrows and universals, a mismatched-endpoint certificate that is rejected, and
narrowing and type substitution turning a primitive step into a composite one.
Variables are de Bruijn indices; each context lists its names innermost first.
-/
namespace SelFsub.Witness

/-- `Top → Top`, the final endpoint of the chains: neither `Top` nor a variable. -/
def tt : Ty n := .arr .top .top

/-! ## Three bound steps -/

/-- `Z <: Top → Top, Y <: Z, X <: Y`; `X, Y, Z` are `var 0, 1, 2`. -/
def Γ3 : Ctx 3 := .snoc (.snoc (.snoc .nil tt) (.var 0)) (.var 0)

def sXY : Cert 3 := .step (.var 0) (.var 1)
def sYZ : Cert 3 := .step (.var 1) (.var 2)
def sZT : Cert 3 := .step (.var 2) tt
def chainL : Cert 3 := .seq (.seq sXY sYZ) sZT
def chainR : Cert 3 := .seq sXY (.seq sYZ sZT)

theorem chainL_typed : CTy Γ3 chainL (.var 0) tt := by decide
theorem chainR_typed : CTy Γ3 chainR (.var 0) tt := by decide
theorem chain_not_prim : ¬ Prim Γ3 (.var 0) tt := by decide
theorem chain_step_rejected : synthC Γ3 (.step (.var 0) tt) = none := by decide
theorem chain_middle_not_prim : ¬ Prim Γ3 (.var 0) (.var 2) ∧ ¬ Prim Γ3 (.var 1) tt := by decide

/-! ## Chains inside arrows and universals -/

/-- A chain in the domain (reversed) and in the result: `(Top → Top) → X ⇒ X → (Top → Top)`. -/
theorem arr_typed : CTy Γ3 (Cert.arr chainL chainR) (.arr tt (.var 0)) (.arr (.var 0) tt) :=
  .arr chainL_typed chainR_typed
theorem arr_not_prim : ¬ Prim Γ3 (.arr tt (.var 0)) (.arr (.var 0) tt) := by decide

/-- A chain in the bound (reversed) and in the body, under the final bound `W <: X`:
`∀(W <: Top → Top). X ⇒ ∀(W <: X). Top → Top`. -/
theorem all_typed :
    CTy Γ3 (Cert.all chainL chainR.weaken) (.all tt (.var 1)) (.all (.var 0) tt) :=
  .all chainL_typed (chainR_typed.weaken _)
theorem all_not_prim : ¬ Prim Γ3 (.all tt (.var 1)) (.all (.var 0) tt) := by decide

/-! ## Mismatched endpoints -/

/-- In `Y <: Top → Top, X <: Y`: `X ⇒ Y` and `Top → Top ⇒ Top → Top` composed although
`Y` and `Top → Top` differ syntactically. -/
def bad : Cert 2 := .seq (.step (.var 0) (.var 1)) (.step tt tt)

theorem bad_parts : CTy ctxYX (.step (.var 0) (.var 1)) (.var 0) (.var 1) ∧
    CTy ctxYX (.step tt tt) tt tt := by decide
theorem bad_rejected : synthC ctxYX bad = none := by decide
theorem bad_untyped (S T : Ty 2) : ¬ CTy ctxYX bad S T := by
  rw [← synthC_iff, bad_rejected]; exact nofun
/-- Another certificate for the same outer endpoints checks. -/
theorem good_typed :
    CTy ctxYX (.seq (.step (.var 0) (.var 1)) (.step (.var 1) tt)) (.var 0) tt := by decide

/-! ## Narrowing -/

/-- `Z <: Top → Top, Y <: Z`; `Y, Z` are `var 0, 1`. The binder `X <: Z` is narrowed to
`X <: Y` along `dYZ : Y ⇒ Z`. -/
def Γ2 : Ctx 2 := .snoc (.snoc .nil tt) (.var 0)
def dYZ : Cert 2 := .step (.var 0) (.var 1)
theorem dYZ_typed : CTy Γ2 dYZ (.var 0) (.var 1) := by decide

/-- Under `X <: Z` (`X = var 0`, `Z = var 2`): the bound step `X ≤₀ Z`. -/
def nb : Cert 3 := .step (.var 0) (.var 2)

theorem nb_narrow : nb.narrow 0 dYZ = .seq (.step (.var 0) (.var 1)) (.step (.var 1) (.var 2)) :=
  rfl
theorem nb_narrow_typed : CTy (Γ2.snoc (.var 0)) (nb.narrow 0 dYZ) (.var 0) (.var 2) :=
  CTy.narrow .nil dYZ_typed (.step (.bound 0))
theorem nb_not_prim : ¬ Prim (Γ2.snoc (.var 0)) (.var 0) (.var 2) := by decide

/-- Under `X <: Z, W <: Top` (`W, X, Z = var 0, 1, 3`): `Top → X ≤₀ Top → Z`. -/
def na : Cert 4 := .step (.arr .top (.var 1)) (.arr .top (.var 3))

theorem na_narrow : na.narrow 1 dYZ =
    .seq (.step (.arr .top (.var 1)) (.arr .top (.var 1)))
      (.seq (.step (.arr .top (.var 1)) (.arr .top (.var 2)))
        (.step (.arr .top (.var 2)) (.arr .top (.var 3)))) := rfl
theorem na_narrow_typed :
    CTy ((Γ2.snoc (.var 0)).snoc .top) (na.narrow 1 dYZ) (.arr .top (.var 1)) (.arr .top (.var 3)) :=
  CTy.narrow (.snoc .nil .top) dYZ_typed (by decide)
theorem na_not_prim :
    ¬ Prim ((Γ2.snoc (.var 0)).snoc .top) (.arr .top (.var 1)) (.arr .top (.var 3)) := by decide

/-- Under `X <: Z`: `∀(W <: Top). X ≤₀ ∀(W <: Top). Z`, a bound step in a universal body. -/
def nu : Cert 3 := .step (.all .top (.var 1)) (.all .top (.var 3))

theorem nu_narrow_typed :
    CTy (Γ2.snoc (.var 0)) (nu.narrow 0 dYZ) (.all .top (.var 1)) (.all .top (.var 3)) :=
  CTy.narrow .nil dYZ_typed (by decide)
theorem nu_not_prim : ¬ Prim (Γ2.snoc (.var 0)) (.all .top (.var 1)) (.all .top (.var 3)) := by
  decide

/-! ## Type substitution -/

/-- `d : W ⇒ Z` in `Γ3` (named `W, Y, Z` here), a composite. -/
def dWZ : Cert 3 := .seq (.step (.var 0) (.var 1)) (.step (.var 1) (.var 2))
theorem dWZ_typed : CTy Γ3 dWZ (.var 0) (.var 2) := by decide

/-- Under `X <: Z` (`X = var 0`, `Z = var 3`), the bound step `X ≤₀ Z` becomes `d` under
`[W/X]`. -/
def sb : Cert 4 := .step (.var 0) (.var 3)

theorem sb_inst : sb.inst 0 (.var 0) dWZ = dWZ := rfl
theorem sb_inst_typed : CTy Γ3 (sb.inst 0 (.var 0) dWZ) (.var 0) (.var 2) :=
  CTy.inst .nil dWZ_typed (.step (.bound 0))

/-- Under `X <: Z, V <: Top` (`V, X, Z = var 0, 1, 4`), a contravariant occurrence:
`Z → Top ≤₀ X → Top`. After `[W/X]` the domain carries `d` reversed into position. -/
def sa : Cert 5 := .step (.arr (.var 4) .top) (.arr (.var 1) .top)

theorem sa_inst : sa.inst 1 (.var 0) dWZ =
    .seq (.seq (.step (.arr (.var 3) .top) (.arr (.var 2) .top))
        (.step (.arr (.var 2) .top) (.arr (.var 1) .top)))
      (.step (.arr (.var 1) .top) (.arr (.var 1) .top)) := rfl
theorem sa_inst_typed :
    CTy (Γ3.snoc .top) (sa.inst 1 (.var 0) dWZ) (.arr (.var 3) .top) (.arr (.var 1) .top) :=
  CTy.inst (.snoc .nil .top) dWZ_typed
    (by decide : CTy ((Γ3.snoc (.var 2)).snoc .top) sa (.arr (.var 4) .top) (.arr (.var 1) .top))
theorem sa_not_prim : ¬ Prim (Γ3.snoc .top) (.arr (.var 3) .top) (.arr (.var 1) .top) := by decide

/-! ## Inversion -/

/-- Inverting the arrow certificate returns certificates for the reversed domain and the
codomain; inverting the universal one aligns the body links by narrowing. -/
theorem arr_inv_components : CTy Γ3 (Cert.arr chainL chainR).arrInv.1 (.var 0) tt ∧
    CTy Γ3 (Cert.arr chainL chainR).arrInv.2 (.var 0) tt := by decide
theorem all_inv_components : CTy Γ3 (Cert.all chainL chainR.weaken).allInv.1 (.var 0) tt ∧
    CTy (Γ3.snoc (.var 0)) (Cert.all chainL chainR.weaken).allInv.2 (.var 1) tt := by decide

end SelFsub.Witness
