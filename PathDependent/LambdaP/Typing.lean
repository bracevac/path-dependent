import PathDependent.LambdaP.Syntax
import PathDependent.LambdaP.Context

namespace LambdaP.Typing

  open Syntax
  open Ty
  open Context
  open Ctx

  inductive PathType: Ctx n -> Path n -> Ty n -> Prop
  | var : Binds Γ x T ->
          -------------------------
          PathType Γ (Path.var x) T

  | fst : PathType Γ p (PairTm S a T) ->
          ------------------------------
          PathType Γ (Path.fst p) S

  | snd : PathType Γ p (PairTm S a T) ->
          ---------------------------------------------------
          PathType Γ (Path.sel a p) (Ty.open T (Path.fst p))

  mutual

    inductive Subtype: Ctx n -> Ty n -> Ty n -> Prop
    | refl  : Subtype Γ T T

    | bot   : Subtype Γ Bot T

    | top   : Subtype Γ T Top

    | widen : PathType Γ p T ->
              -------------------------
              Subtype Γ (Ty.Single p) T

    | symm  : PathType Γ p (Ty.Single q) ->
              -------------------------------------
              Subtype Γ (Ty.Single q) (Ty.Single p)

    | sel_hi: PathType Γ p (PairTy U A (Range.I S T)) ->
              Subtype (snoc Γ U) S T ->
              ---------------------------------------------
              Subtype Γ (Sel A p) (Ty.open T (Path.fst p))

    | sel_lo: PathType Γ p (PairTy U A (Range.I S T)) ->
              Subtype (snoc Γ U) S T ->
              ---------------------------------------------
              Subtype Γ (Ty.open S (Path.fst p)) (Sel A p)

    | pair  : Subtype Γ S S' ->
              Subtype (snoc Γ S) T T' ->
              -----------------------------------------
              Subtype Γ (PairTm S a T) (PairTm S' a T')

    | tpair : Subtype Γ S S' ->
              Subrange (snoc Γ S) I I' ->
              -----------------------------------------
              Subtype Γ (PairTy S A I) (PairTy S' A I')

    | fun   : Subtype Γ S' S ->
              Subtype (snoc Γ S') T T' -> -- TODO: check with martin
              -------------------------------
              Subtype Γ (Fun S T) (Fun S' T')

    | trans : Subtype Γ T1 T2 ->
              Subtype Γ T2 T3 ->
              ------------------
              Subtype Γ T1 T3

    -- TODO: I'd avoid having too many mutually dependent things, inline this
    inductive Subrange: Ctx n -> Range n -> Range n -> Prop
    | bounds: Subtype Γ S' S ->
              Subtype Γ T T' ->
              Subtype Γ S T ->
              Subrange Γ (Range.I S T) (Range.I S' T')

  end

end LambdaP.Typing
