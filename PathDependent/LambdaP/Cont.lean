import PathDependent.FinFun.Basic
import PathDependent.LambdaP.Syntax

namespace LambdaP.Cont

  open LambdaP.Syntax
  open FinFun

  -- We model continuations as stacks (i.e. lists) of frames

  inductive Path.Frame: Type
  | fst  : Frame
  | sel  : Name -> Frame

  inductive Tm.Frame: Nat -> Type
  | path  : Frame n
  | let   : Tm (n + 1) -> Frame n
  | app_l : Path n -> Frame n
  | app_r : Fin n -> Frame n

  def Path.Cont := List Path.Frame
  def Tm.Cont (n: Nat) := List (Tm.Frame n)

  def Tm.Frame.rename (F: Tm.Frame n) (f: FinFun n m): Tm.Frame m := match F with
  | Tm.Frame.path => Tm.Frame.path
  | Tm.Frame.let t => Tm.Frame.let (t.rename f.ext)
  | app_l p => app_l (p.rename f)
  | app_r x => app_r (f x)

  def Tm.Frame.weaken (F : Tm.Frame n): Tm.Frame (n + 1) := F.rename FinFun.weaken
  def Tm.Cont.weaken: Tm.Cont n -> Tm.Cont (n + 1) := List.map Tm.Frame.weaken

end LambdaP.Cont
