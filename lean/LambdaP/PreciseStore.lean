import LambdaP.Renaming
import LambdaP.Store

/-!
Syntax-directed typing for values and exact stores in the calculus.
-/

namespace LambdaP

/-- The type assigned directly by a value-introduction rule. -/
inductive Tm.PreciseTy : Ctx n -> Tm n -> LambdaP.Ty n -> Prop where
| abs :
    Tm.Ty (Gamma.snoc S) t T ->
    Tau.Wf Gamma (Tau.ty S) ->
    Tm.PreciseTy Gamma (Tm.abs S t) (Ty.Fun S T)
| pair :
    Ctx.Binds Gamma y S ->
    Ctx.Binds Gamma z T ->
    Tm.PreciseTy Gamma (Tm.pair y a (Def.val z))
      (Ty.Pair (Ty.Single (Path.var y)) a
        (Tau.ty (Ty.Single (Path.var z).weaken)))
| tpair :
    Ctx.Binds Gamma y S ->
    Tau.Wf Gamma (Tau.ty T) ->
    Tm.PreciseTy Gamma (Tm.pair y A (Def.type T))
      (Ty.Pair (Ty.Single (Path.var y)) A (Tau.intv T T).weaken)

theorem Tm.PreciseTy.isValue (h : Tm.PreciseTy Gamma v T) : v.IsValue := by
  cases h <;> constructor

theorem Tm.PreciseTy.toTy (h : Tm.PreciseTy Gamma v T) : Tm.Ty Gamma v T := by
  cases h with
  | abs ht hwf => exact Tm.Ty.abs ht hwf
  | pair hy hz => exact Tm.Ty.pair hy hz
  | tpair hy hwf => exact Tm.Ty.tpair hy hwf

theorem Tm.PreciseTy.rename {n : Nat} {Gamma : Ctx n} {v : Tm n}
    {T : LambdaP.Ty n} (h : Tm.PreciseTy Gamma v T) :
    forall {m} {f : FinFun n m} {Delta : Ctx m},
      Renaming Gamma f Delta -> Tm.PreciseTy Delta (v.rename f) (T.rename f) := by
  cases h with
  | abs ht hwf =>
      intro m f Delta rho
      simpa [Tm.rename, Ty.rename] using
        Tm.PreciseTy.abs (ht.rename (Renaming.ext rho)) (hwf.rename rho)
  | pair hy hz =>
      intro m f Delta rho
      simpa [Tm.rename, Def.rename, Ty.rename, Tau.rename, Path.rename,
        Path.weaken_rename] using
        Tm.PreciseTy.pair (rho hy) (rho hz)
  | tpair hy hwf =>
      intro m f Delta rho
      simpa only [Tm.rename, Def.rename, LambdaP.Ty.rename,
        Tau.rename, Path.rename, ← Tau.weaken_rename] using
        Tm.PreciseTy.tpair (rho hy) (hwf.rename rho)

theorem Tm.PreciseTy.weaken (h : Tm.PreciseTy Gamma v T) :
    Tm.PreciseTy (Gamma.snoc S) v.weaken T.weaken := by
  simpa [Tm.weaken, Ty.weaken] using h.rename (Renaming.weaken (S := S))

/-- A store and context built in lockstep from exact value-introduction types. -/
inductive Store.PreciseTy : Ctx n -> Store n -> Prop where
| empty : Store.PreciseTy Ctx.nil (Store.empty : Store 0)
| val :
    Store.PreciseTy Gamma sigma ->
    Tm.PreciseTy Gamma v T ->
    (vv : v.IsValue) ->
    Store.PreciseTy (Gamma.snoc T) (Store.val sigma v vv)

theorem Store.PreciseTy.toTy (h : Store.PreciseTy Gamma sigma) :
    Store.Ty Gamma sigma := by
  induction h with
  | empty => exact Store.Ty.empty
  | val _ hv _ ih => exact Store.Ty.val ih hv.toTy

theorem Store.PreciseTy.of_store_binds
    (hsigma : Store.PreciseTy Gamma sigma) (hb : Store.Binds sigma x v) :
    exists T, Ctx.Binds Gamma x T /\ Tm.PreciseTy Gamma v T := by
  induction hsigma with
  | empty => exact Fin.elim0 x
  | val hsigma hv vv ih =>
      cases hb with
      | here => exact ⟨_, Ctx.Binds.here, hv.weaken⟩
      | there hb =>
          obtain ⟨U, hU, hp⟩ := ih hb
          exact ⟨U.weaken, Ctx.Binds.there hU, hp.weaken⟩

theorem Store.PreciseTy.of_ctx_binds
    (hsigma : Store.PreciseTy Gamma sigma) (hb : Ctx.Binds Gamma x T) :
    exists v, Store.Binds sigma x v /\ Tm.PreciseTy Gamma v T := by
  induction hsigma with
  | empty => exact Fin.elim0 x
  | val hsigma hv vv ih =>
      cases hb with
      | here => exact ⟨_, Store.Binds.here, hv.weaken⟩
      | there hb =>
          obtain ⟨u, hu, hp⟩ := ih hb
          exact ⟨u.weaken, Store.Binds.there hu, hp.weaken⟩

theorem Store.PreciseTy.lookup
    (hsigma : Store.PreciseTy Gamma sigma)
    (hs : Store.Binds sigma x v) (hc : Ctx.Binds Gamma x T) :
    Tm.PreciseTy Gamma v T := by
  obtain ⟨U, hU, hv⟩ := hsigma.of_store_binds hs
  cases hU.unique hc
  exact hv

end LambdaP
