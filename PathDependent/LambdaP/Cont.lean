import PathDependent.FinFun.Basic
import PathDependent.LambdaP.Syntax
import PathDependent.LambdaP.Context
import PathDependent.LambdaP.Typing

namespace LambdaP.Cont

  open LambdaP.Syntax
  open FinFun
  open Context
  open Typing

  -- We model continuations as stacks (i.e. lists) of frames

  inductive Path.Frame: Type
  | fst  : Frame
  | sel  : Name -> Frame

  inductive Tm.Frame: Nat -> Type
  | let   : Tm (n + 1) -> Frame n
  | app_l : Path n -> Frame n
  | app_r : Fin n -> Frame n

  def Path.Cont := List Path.Frame
  def Tm.Cont (n: Nat) := List (Tm.Frame n)

  def Tm.Frame.rename (F: Tm.Frame n) (f: FinFun n m): Tm.Frame m := match F with
  | Tm.Frame.let t => Tm.Frame.let (t.rename f.ext)
  | app_l p => app_l (p.rename f)
  | app_r x => app_r (f x)

  def Tm.Frame.weaken (F : Tm.Frame n): Tm.Frame (n + 1) := F.rename FinFun.weaken
  def Tm.Cont.weaken: Tm.Cont n -> Tm.Cont (n + 1) := List.map Tm.Frame.weaken

  -- Path continuations only make sense for paths to field members, so we nail the kind to star here
  inductive Path.Cont.Ty : Ctx n -> Path.Cont -> Tau n Kind.star -> Tau n Kind.star -> Prop
  | hole: Tau.Sub Γ τ τ' ->
        Path.Cont.Ty Γ [] τ τ'

  | fst: Path.Cont.Ty Γ P τ (Tau.ty (Ty.Pair S α τ')) ->
        Path.Cont.Ty Γ (Path.Frame.fst :: P) τ (Tau.ty S)

  | sel_r: Path.Cont.Ty Γ P τ (Tau.ty (Ty.Pair S a τ')) ->

        Path.Cont.Ty Γ (Path.Frame.sel a :: P) τ (τ'.open S)


  inductive Tm.Cont.Ty : Ctx n -> Tm.Cont n -> Path.Cont -> Prop



end LambdaP.Cont
