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
  inductive Tm.Frame: Nat -> Type
  | let   : Tm (n + 1) -> Frame n

  def Tm.Cont (n: Nat) := List (Tm.Frame n)

  def Tm.Frame.rename (F: Tm.Frame n) (f: FinFun n m): Tm.Frame m := match F with
  | Tm.Frame.let t => Tm.Frame.let (t.rename f.ext)

  def Tm.Cont.rename (cont : Tm.Cont n) (f: FinFun n m): Tm.Cont m := List.map (fun F => F.rename f) cont

  def Tm.Frame.weaken (F : Tm.Frame n): Tm.Frame (n + 1) := F.rename FinFun.weaken
  def Tm.Cont.weaken (cont: Tm.Cont n): Tm.Cont (n + 1) := cont.rename FinFun.weaken

  -- frame and continuation typing
  inductive Tm.Frame.Ty : Ctx n -> Ty n -> Tm.Frame n -> Ty n -> Prop
  | let : Tm.Ty (Γ.snoc S) t T.weaken ->
          Tm.Frame.Ty Γ S (Tm.Frame.let t) T

  inductive Tm.Cont.Ty : Ctx n -> Ty n -> Tm.Cont n -> Ty n -> Prop
  | hole : Tau.Sub Γ (Tau.ty S) (Tau.ty T) ->
           Tm.Cont.Ty Γ S [] T

  | cons : Tm.Cont.Ty Γ S E T ->
           Tm.Frame.Ty Γ U F S ->
           Tm.Cont.Ty Γ U (F :: E) T

end LambdaP.Cont
