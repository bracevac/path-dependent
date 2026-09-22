import Coercions.FCdotR.Typing

/-!
# Locality of observation evidence

The target's reading of the reference's `GH = GU ++ GL`.

```text
Γ ⊢ v :: abs x : T   ≃   Γ.upTo x ⊢ v :: abs (varUpTo x) : T
Γ ⊢ v :: conc ℓ : T  ≃   Γ' ⊢ v :: conc ℓ : T      for any Γ'
```

An observation of a variable is determined by that variable's own prefix, and
an observation of a location does not depend on the local context at all.  The
reference has to state this as a side condition on one rule
(`length GL = S x`, `GH = GU ++ GL`, `dot.v:391-392`) and then split and
re-split the append in its proofs — `gh_match`, `sub_env1`, `exists_GH1L`,
`exists_GH0U` exist for no other purpose.  Here it is a strengthening and a
weakening, each a one-line structural recursion, because every former of `VcTy`
already consults only `ctxAt Γ p`.

No transport appears.  `varUpTo x` is literally `.here`, so
`scopeUpTo (varUpTo x)` is `scopeUpTo x` definitionally, and the two context
lemmas of `Prefix` supply the rest.

This is what makes the substitution theorem's restricted-substitution premise
derivable rather than an extra field, so it is the device the whole layering
rests on.

As in `Typing`, the subject has to be passed wherever elaboration would
otherwise have to guess it through `scopeAt`, which is not injective.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Ctx Store scopeUpTo varUpTo)

/-- An observation of an abstract variable lives in that variable's prefix. -/
def VcTy.strengthen {σ s : Sig} {G : Store σ σ} {W : StoreTy σ}
    {Γ : Ctx σ s} {x : BVar s .var} : {v : Vc σ (scopeUpTo x)} →
    {T : Ty σ (scopeUpTo x)} →
    VcTy G W Γ (.abs x) v T → VcTy G W (Γ.upTo x) (.abs (varUpTo x)) v T
  | _, _, .vcVar => lookupAt_upTo_self Γ x ▸ .vcVar
  | _, _, .vcUnfold d => .vcUnfold (strengthen d)
  | _, _, .vcSub T1 d e =>
      .vcSub (Γ := Γ.upTo x) (p := .abs (varUpTo x)) T1 (strengthen d) (by
        rw [show ctxAt (Γ.upTo x) (Vr.abs (varUpTo x)) = Γ.upTo x from
              upTo_upTo_self Γ x]
        exact e)

/-- An observation of a location does not use the local context. -/
def VcTy.ofLoc {σ s s' : Sig} {G : Store σ σ} {W : StoreTy σ}
    {Γ : Ctx σ s} {Γ' : Ctx σ s'} {l : BVar σ .var} :
    {v : Vc σ []} → {T : Ty σ []} →
    VcTy G W Γ (.conc l) v T → VcTy G W Γ' (.conc l) v T
  | _, _, .vcLoc => .vcLoc
  | _, _, .vcPack d => .vcPack (ofLoc d)
  | _, _, .vcUnfold d => .vcUnfold (ofLoc d)
  | _, _, .vcSub T1 d e => .vcSub (Γ := Γ') (p := .conc l) T1 (ofLoc d) e

end FCdotR
