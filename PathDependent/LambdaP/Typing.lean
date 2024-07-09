import PathDependent.LambdaP.Syntax
import PathDependent.LambdaP.Context

namespace LambdaP.Typing

  open Syntax
  open Ty
  open Context
  open Ctx
  open ComponentSig renaming field -> VAL, type -> TYPE

  -- Path typing classifies a path as either a field selection with a Type, or a type selection with an Interval
  inductive Path.Ty: Ctx n -> Path n -> ComponentSig n mκ -> Prop
  | var : Binds Γ x T ->
          ------------------------------
          Path.Ty Γ (Path.var x) (VAL T)

  | fst : Path.Ty Γ p (VAL (Pair S α τ)) ->
          ---------------------------------
          Path.Ty Γ p.fst (VAL S)

  | sel_r : Path.Ty Γ p (VAL (Pair S α τ)) ->
          -----------------------------------
          Path.Ty Γ (p.sel a) (τ.open p.fst)

  | sel_l : Path.Ty Γ p (VAL (Pair S β τ')) ->
          Path.Ty Γ (p.fst.sel α) τ ->
          α ≠ β ->
          ------------------------------------
          Path.Ty Γ (p.sel a) τ -- FIXME: check with Martin, there's no dependency required


  -- TODO: prefix with ComponentSig instead of Ty
  -- TODO: better names for Component{Sig,Def}
  inductive Ty.Sub: Ctx n -> ComponentSig n mκ -> ComponentSig n mκ -> Prop
  | refl  : Ty.Sub Γ τ τ

  | trans : Ty.Sub Γ τ1 τ2 ->
          Ty.Sub Γ τ2 τ3 ->
          ------------------
          Ty.Sub Γ τ1 τ3

  | bot   : Ty.Sub Γ (VAL Bot) (VAL T)

  | top   : Ty.Sub Γ (VAL T) (VAL Top)

  | widen  : Path.Ty Γ p (VAL T) ->
            ---------------------------------
            Ty.Sub Γ (VAL (Single p)) (VAL T)

  | symm  : Path.Ty Γ p (VAL (Single q)) ->
            ------------------------------------------
            Ty.Sub Γ (VAL (Single q)) (VAL (Single p))

  | sel_hi: Path.Ty Γ (Path.sel p A) (TYPE S T) ->
            Ty.Sub Γ (VAL S) (VAL T) ->
            -----------------------------------------
            Ty.Sub Γ (VAL (Single (p.sel A))) (VAL T)

  | sel_lo: Path.Ty Γ (Path.sel p A) (TYPE S T) ->
            Ty.Sub Γ (VAL S) (VAL T) ->
            -----------------------------------------
            Ty.Sub Γ (VAL S) (VAL (Single (p.sel A)))

  | fun   : Ty.Sub Γ (VAL S') (VAL S) ->
            Ty.Sub (Γ.snoc S') (VAL T) (VAL T') ->
            ------------------------------------------
            Ty.Sub Γ (VAL (Fun S T)) (VAL (Fun S' T'))

  | pair  : Ty.Sub Γ (VAL S) (VAL S') ->
            Ty.Sub (Γ.snoc S) τ τ' ->
            ------------------------------------------------
            Ty.Sub Γ (VAL (Pair S α τ)) (VAL (Pair S' α τ'))

  | bounds: Ty.Sub Γ (VAL S') (VAL S) ->
            Ty.Sub Γ (VAL T) (VAL T') ->
            Ty.Sub Γ (VAL S) (VAL T)  ->
            --------------------------------
            Ty.Sub Γ (TYPE S T) (TYPE S' T')

  inductive Ty.Wf: Ctx n -> ComponentSig n mκ -> Prop
  | bot   : Ty.Wf Γ (VAL Bot)

  | top   : Ty.Wf Γ (VAL Top)

  | path  : Path.Ty Γ p (VAL T) ->
            ------------------------
            Ty.Wf Γ (VAL (Single p))

  | sel   : Path.Ty Γ p (VAL (Pair S A (TYPE T U))) ->
            ------------------------------------------
            Ty.Wf Γ (VAL (Single (p.sel A)))

  | fun   : Ty.Wf Γ (VAL S) ->
            Ty.Wf (Γ.snoc S) (VAL T) ->
            ---------------------------
            Ty.Wf Γ (VAL (Fun S T))

  | pair  : Ty.Wf Γ (VAL S) ->
            Ty.Wf (Γ.snoc S) τ ->
            --------------------------
            Ty.Wf Γ (VAL (Pair S α τ))

  | bounds_wf: Ty.Wf Γ (VAL S) ->
            Ty.Wf Γ (VAL T) ->
            Ty.Sub Γ (VAL S) (VAL T) ->
            ---------------------------
            Ty.Wf Γ (TYPE S T)

  open Tm
  open ComponentDef renaming field -> val, type -> typ

  inductive Tm.Ty: Ctx n -> Tm n -> Ty n -> Prop
  | path  : Path.Ty Γ p (VAL T) ->
            ---------------------------
            Tm.Ty Γ (path p) (Single p)

  | abs   : Tm.Ty (Γ.snoc S) t T ->
            Ty.Wf Γ (VAL S) ->
            ---------------------------
            Tm.Ty Γ (abs S t) (Fun S T)

  | app   : Tm.Ty Γ (path p) (Fun S T) ->
            Tm.Ty Γ (path q) S ->
            -------------------------------
            Tm.Ty Γ (app p q) (Ty.open T q)

  | pair  : Binds Γ y S ->
            Binds Γ z T ->
            --------------------------------------------------------------------------------------------------------------
            Tm.Ty Γ (pair y a (val (path (Path.var z)))) (Pair (Single (Path.var y)) a (VAL (Single (Path.var z)).weaken))

  | tpair : Binds Γ y S ->
            Ty.Wf Γ (VAL T) ->
            ---------------------------------------------------------------------------
            Tm.Ty Γ (pair y A (typ T)) (Pair (Single (Path.var y)) A (TYPE T T).weaken)

  | let   : Tm.Ty Γ s S ->
            Ty.Wf Γ (VAL T) -> -- implies x ∉ fv(T)
            Tm.Ty (Γ.snoc S) t T.weaken ->
            ------------------------------
            Tm.Ty Γ (Tm.let s t) T

  | typed : Tm.Ty Γ t T ->
            Ty.Wf Γ (VAL T) ->
            ---------------------
            Tm.Ty Γ (typed t T) T

  | sub   : Tm.Ty Γ t S ->
            Ty.Sub Γ (VAL S) (VAL T) ->
            Ty.Wf Γ (VAL T) ->
            ---------------------------
            Tm.Ty Γ t T

end LambdaP.Typing
