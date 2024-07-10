import PathDependent.LambdaP.Syntax
import PathDependent.LambdaP.Context

namespace LambdaP.Typing

  open Syntax
  open Ty
  open Context
  open Ctx
  open Tau

  -- Path typing classifies a path as either a field selection with a Type, or a type selection with an Interval
  inductive Path.Ty: Ctx n -> Path n -> Tau n κ -> Prop
  | var : Binds Γ x T ->
          ------------------------------
          Path.Ty Γ (Path.var x) (ty T)

  | fst : Path.Ty Γ p (ty (Pair S α τ)) ->
          ---------------------------------
          Path.Ty Γ p.fst (ty S)

  | sel_r : Path.Ty Γ p (ty (Pair S α τ)) ->
          -----------------------------------
          Path.Ty Γ (p.sel a) (τ.open p.fst)

  | sel_l : Path.Ty Γ p (ty (Pair S β τ')) ->
          Path.Ty Γ (p.fst.sel α) τ ->
          α ≠ β ->
          ------------------------------------
          Path.Ty Γ (p.sel a) τ -- FIXME: check with Martin, there's no dependency required

  inductive Tau.Sub: Ctx n -> Tau n κ -> Tau n κ -> Prop
  | refl  : Tau.Sub Γ τ τ

  | trans : Tau.Sub Γ τ1 τ2 ->
          Tau.Sub Γ τ2 τ3 ->
          ------------------
          Tau.Sub Γ τ1 τ3

  | bot   : Tau.Sub Γ (ty Bot) (ty T)

  | top   : Tau.Sub Γ (ty T) (ty Top)

  | widen  : Path.Ty Γ p (ty T) ->
            ---------------------------------
            Tau.Sub Γ (ty p) (ty T)

  | symm  : Path.Ty Γ p (ty (Single q)) ->
            ------------------------------------------
            Tau.Sub Γ (ty q) (ty p)

  | sel_hi: Path.Ty Γ (Path.sel p A) (intv S T) ->
            Tau.Sub Γ (ty S) (ty T) ->
            -----------------------------------------
            Tau.Sub Γ (ty (p.sel A)) (ty T)

  | sel_lo: Path.Ty Γ (Path.sel p A) (intv S T) ->
            Tau.Sub Γ (ty S) (ty T) ->
            -----------------------------------------
            Tau.Sub Γ (ty S) (ty (p.sel A))

  | fun   : Tau.Sub Γ (ty S') (ty S) ->
            Tau.Sub (Γ.snoc S') (ty T) (ty T') ->
            ------------------------------------------
            Tau.Sub Γ (ty (Fun S T)) (ty (Fun S' T'))

  | pair  : Tau.Sub Γ (ty S) (ty S') ->
            Tau.Sub (Γ.snoc S) τ τ' ->
            ------------------------------------------------
            Tau.Sub Γ (ty (Pair S α τ)) (ty (Pair S' α τ'))

  | bounds: Tau.Sub Γ (ty S') (ty S) ->
            Tau.Sub Γ (ty T) (ty T') ->
            Tau.Sub Γ (ty S) (ty T)  ->
            --------------------------------
            Tau.Sub Γ (intv S T) (intv S' T')

  inductive Tau.Wf: Ctx n -> Tau n κ -> Prop
  | bot   : Tau.Wf Γ (ty Bot)

  | top   : Tau.Wf Γ (ty Top)

  | path  : Path.Ty Γ p (ty T) ->
            ------------------------
            Tau.Wf Γ (ty (Single p))

  | sel   : Path.Ty Γ p (ty (Pair S A (intv T U))) ->
            ------------------------------------------
            Tau.Wf Γ (ty (Single (p.sel A)))

  | fun   : Tau.Wf Γ (ty S) ->
            Tau.Wf (Γ.snoc S) (ty T) ->
            ---------------------------
            Tau.Wf Γ (ty (Fun S T))

  | pair  : Tau.Wf Γ (ty S) ->
            Tau.Wf (Γ.snoc S) τ ->
            --------------------------
            Tau.Wf Γ (ty (Pair S α τ))

  | bounds_wf: Tau.Wf Γ (ty S) ->
            Tau.Wf Γ (ty T) ->
            Tau.Sub Γ (ty S) (ty T) ->
            ---------------------------
            Tau.Wf Γ (intv S T)

  open Tm
  open Def

  inductive Tm.Ty: Ctx n -> Tm n -> Ty n -> Prop
  | path  : Path.Ty Γ p (ty T) ->
            ---------------------
            Tm.Ty Γ p p

  | abs   : Tm.Ty (Γ.snoc S) t T ->
            Tau.Wf Γ (ty S) ->
            ---------------------------
            Tm.Ty Γ (abs S t) (Fun S T)

  | app   : Tm.Ty Γ (path p) (Fun S T) ->
            Tm.Ty Γ (path q) S ->
            -------------------------------
            Tm.Ty Γ (app p q) (T.open q)

  | pair  : Binds Γ y S ->
            Binds Γ z T ->
            --------------------------------------------------------------------------------------------------------------
            Tm.Ty Γ (pair y a (val z)) (Pair (Path.var y) a (ty (Path.var z).weaken))

  | tpair : Binds Γ y S ->
            Tau.Wf Γ (ty T) ->
            ---------------------------------------------------------------------------
            Tm.Ty Γ (pair y A (type T)) (Pair (Path.var y) A (intv T T).weaken)

  | let   : Tm.Ty Γ s S ->
            Tau.Wf Γ (ty T) -> -- implies x ∉ fv(T)
            Tm.Ty (Γ.snoc S) t T.weaken ->
            ------------------------------
            Tm.Ty Γ (Tm.let s t) T

  | typed : Tm.Ty Γ t T ->
            Tau.Wf Γ (ty T) ->
            ---------------------
            Tm.Ty Γ (typed t T) T

  | sub   : Tm.Ty Γ t S ->
            Tau.Sub Γ (ty S) (ty T) ->
            Tau.Wf Γ (ty T) ->
            ---------------------------
            Tm.Ty Γ t T

end LambdaP.Typing
