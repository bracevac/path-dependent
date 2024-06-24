import PathDependent.LambdaP.Syntax
import PathDependent.LambdaP.Context

namespace LambdaP.Typing

  open Syntax
  open Ty
  open Context
  open Ctx

  inductive Path.Ty: Ctx n -> Path n -> Ty n -> Prop
  | var : Binds Γ x T ->
          -------------------------
          Path.Ty Γ (Path.var x) T

  | fst : Path.Ty Γ p (PairTm S a T) ->
          ------------------------------
          Path.Ty Γ (Path.fst p) S

  | snd : Path.Ty Γ p (PairTm S a T) ->
          ---------------------------------------------------
          Path.Ty Γ (Path.sel a p) (Ty.open T (Path.fst p))

  mutual

    inductive Ty.Sub: Ctx n -> Ty n -> Ty n -> Prop
    | refl  : Ty.Sub Γ T T

    | bot   : Ty.Sub Γ Bot T

    | top   : Ty.Sub Γ T Top

    | widen : Path.Ty Γ p T ->
              ----------------------
              Ty.Sub Γ (Single p) T

    | symm  : Path.Ty Γ p (Single q) ->
              -------------------------------
              Ty.Sub Γ (Single q) (Single p)

    | sel_hi: Path.Ty Γ p (PairTy U A (Range.I S T)) ->
              Ty.Sub (snoc Γ U) S T ->
              ---------------------------------------------
              Ty.Sub Γ (Sel A p) (Ty.open T (Path.fst p))

    | sel_lo: Path.Ty Γ p (PairTy U A (Range.I S T)) ->
              Ty.Sub (snoc Γ U) S T ->
              ---------------------------------------------
              Ty.Sub Γ (Ty.open S (Path.fst p)) (Sel A p)

    | pair  : Ty.Sub Γ S S' ->
              Ty.Sub (snoc Γ S) T T' ->
              -----------------------------------------
              Ty.Sub Γ (PairTm S a T) (PairTm S' a T')

    | tpair : Ty.Sub Γ U V ->
              Ty.Sub (snoc Γ U) S' S ->
              Ty.Sub (snoc Γ U) T T' ->
              Ty.Sub (snoc Γ U) S T ->
              -----------------------------------------
              Ty.Sub Γ (PairTy U A (Range.I S T)) (PairTy V A (Range.I S' T'))

    | fun   : Ty.Sub Γ S' S ->
              Ty.Sub (snoc Γ S') T T' -> -- TODO: check with martin
              -------------------------------
              Ty.Sub Γ (Fun S T) (Fun S' T')

    | trans : Ty.Sub Γ T1 T2 ->
              Ty.Sub Γ T2 T3 ->
              ------------------
              Ty.Sub Γ T1 T3

    inductive Ty.Wf: Ctx n -> Ty n -> Prop
    | bot   : Ty.Wf Γ Bot

    | top   : Ty.Wf Γ Top

    | path  : Path.Ty Γ p T ->
              ------------------
              Ty.Wf Γ (Single p)

    | sel   : Path.Ty Γ p (PairTy S A I) ->
              -----------------------------
              Ty.Wf Γ (Sel A p)

    | pair  : Ty.Wf Γ S ->
              Ty.Wf (snoc Γ S) T ->
              ----------------------
              Ty.Wf Γ (PairTm S a T)

    | tpair : Ty.Wf Γ U ->
              Ty.Wf (snoc Γ U) S ->
              Ty.Wf (snoc Γ U) T ->
              Ty.Sub (snoc Γ U) S T ->
              ----------------------------------
              Ty.Wf Γ (PairTy U A (Range.I S T))

    | fun   : Ty.Wf Γ S ->
              Ty.Wf (snoc Γ S) T ->
              ---------------------
              Ty.Wf Γ (Fun S T)
  end

  open Tm

  inductive Tm.Ty: Ctx n -> Tm n -> Ty n -> Prop
  | path  : Path.Ty Γ p T ->
            ---------------------------
            Tm.Ty Γ (path p) (Single P)

  | abs   : Tm.Ty (snoc Γ S) t T ->
            Ty.Wf Γ S ->
            ---------------------------
            Tm.Ty Γ (abs S t) (Fun S T)

  | app   : Tm.Ty Γ (path p) (Fun S T) ->
            Tm.Ty Γ (path q) S ->
            -------------------------------
            Tm.Ty Γ (app p q) (Ty.open T q)

  | pair  : Binds Γ y S ->
            Binds Γ z T ->
            -------------------------------------------------------------
            Tm.Ty Γ (pairtm y a z) (PairTm (Single (Path.var y)) a sorry) -- FIXME: needs weakening

  | tpair : Binds Γ y S ->
            Ty.Wf Γ T -> -- TODO check with martin
            -----------------------------------------
            Tm.Ty Γ (pairty y A T) (PairTy (Single (Path.var y)) A (Range.I sorry sorry)) -- FIXME: needs weakening

  | let   : Tm.Ty Γ s S ->
            Ty.Wf Γ T ->
            Tm.Ty (snoc Γ S) t sorry -> -- FIXME: needs weakening, + check with martin
            ---------------------------
            Tm.Ty Γ (Tm.let s t) T

  | sub   : Tm.Ty Γ t S ->
            Ty.Sub Γ S T ->
            Ty.Wf Γ T ->
            ---------------
            Tm.Ty Γ t T

end LambdaP.Typing
