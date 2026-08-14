import LambdaP.Renaming

/-!
Term continuations for the CK machine.  Monadic normal form
leaves only `let` evaluation contexts, so a frame stores the body waiting for
the value of its bound computation.
-/

namespace LambdaP

/-- A single term evaluation frame. -/
inductive Tm.Frame : Nat -> Type where
| «let» : Tm (n + 1) -> Tm.Frame n

/-- Continuations are stacks of term frames. -/
def Tm.Cont (n : Nat) : Type := List (Tm.Frame n)

def Tm.Frame.rename (F : Tm.Frame n) (f : FinFun n m) : Tm.Frame m :=
  match F with
  | .let t => .let (t.rename f.ext)

def Tm.Cont.rename (k : Tm.Cont n) (f : FinFun n m) : Tm.Cont m :=
  k.map (fun F => F.rename f)

def Tm.Frame.weaken (F : Tm.Frame n) : Tm.Frame (n + 1) :=
  F.rename FinFun.weaken

def Tm.Cont.weaken (k : Tm.Cont n) : Tm.Cont (n + 1) :=
  k.rename FinFun.weaken

/-! ## Frame and continuation typing -/

/-- A frame consumes a term of type `S` and resumes a computation of type
`T`. -/
inductive Tm.Frame.Ty :
    Ctx n -> LambdaP.Ty n -> Tm.Frame n ->
      LambdaP.Ty n -> Prop where
| «let» :
    Tm.Ty (Γ.snoc S) t T.weaken ->
    Tm.Frame.Ty Γ S (Tm.Frame.let t) T

/-- A continuation consumes a term of its input type and eventually returns
its output type. -/
inductive Tm.Cont.Ty :
    Ctx n -> LambdaP.Ty n -> Tm.Cont n ->
      LambdaP.Ty n -> Prop where
| hole :
    Tau.Sub Γ (Tau.ty S) (Tau.ty T) ->
    Tm.Cont.Ty Γ S [] T
| cons :
    Tm.Cont.Ty Γ S E T ->
    Tm.Frame.Ty Γ U F S ->
    Tm.Cont.Ty Γ U (F :: E) T

/-! ## Renaming and weakening -/

theorem Tm.Frame.Ty.rename
    (h : Tm.Frame.Ty Γ S F T)
    (ρ : Renaming Γ f Δ) :
    Tm.Frame.Ty Δ (S.rename f) (F.rename f) (T.rename f) := by
  cases h with
  | «let» ht =>
      apply Tm.Frame.Ty.let
      simpa [Ty.weaken_rename] using ht.rename (Renaming.ext ρ)

theorem Tm.Cont.Ty.rename
    (h : Tm.Cont.Ty Γ S k T)
    (ρ : Renaming Γ f Δ) :
    Tm.Cont.Ty Δ (S.rename f) (k.rename f) (T.rename f) := by
  induction h with
  | hole hsub =>
      simpa [Tm.Cont.rename] using Tm.Cont.Ty.hole (hsub.rename ρ)
  | cons hc hf ih =>
      simpa [Tm.Cont.rename] using Tm.Cont.Ty.cons ih (hf.rename ρ)

theorem Tm.Frame.Ty.weaken (h : Tm.Frame.Ty Γ S F T) :
    Tm.Frame.Ty (Γ.snoc U) S.weaken F.weaken T.weaken := by
  simpa [Tm.Frame.weaken, Ty.weaken] using
    h.rename (Renaming.weaken (S := U))

theorem Tm.Cont.Ty.weaken (h : Tm.Cont.Ty Γ S k T) :
    Tm.Cont.Ty (Γ.snoc U) S.weaken k.weaken T.weaken := by
  simpa [Tm.Cont.weaken, Ty.weaken] using
    h.rename (Renaming.weaken (S := U))

end LambdaP
