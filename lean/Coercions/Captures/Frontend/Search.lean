import Coercions.Captures.Frontend.Decide
import Coercions.Captures.Frontend.Surface
import Coercions.Captures.DotMNF.Examples

/-!
# The first view of a variable

A *view* of a context variable is a type the variable has, with its use set
and derivation.  The typer and the subtyping algorithm start from the first
view, `varView`.  A variable declared at the empty set is used at the empty
set and keeps its declared type.  Any other variable is used at `{x}` and has
its declared shape at `{x}`, by `Var`.  This is the least use set and the
least capture set the rules give a variable.

Every other type a variable has is reached from the first view on demand:
by the member lookup of `Look.lean` and by the `var` goal of `Sub.lean`.
-/

namespace CapturesFrontend

open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (Path CapAtom CaptureSet Shape Ty Defs Ctx Sub SubShape Subcap HasTy)
open scoped Captures.DotMNF

/-! ## Views -/

/-- A type a context variable has, at a use set, with the derivation. -/
structure View {s : Sig} (Γ : Ctx s) (x : BVar s .var) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) ty

/-- A pure binder at its declared type, at the empty use set.  `Var`
concludes at `{x}` for both sets, and `sc-var` takes both down to the declared
set, which is empty. -/
def pureVar {s : Sig} (Γ : Ctx s) (x : BVar s .var) (h : (Γ.lookup x).captureSet = []) :
    HasTy [] Γ (.path (.var x)) (Γ.lookup x) := by
  have hv : Subcap Γ [CapAtom.var x] ([] : CaptureSet s) := by
    have hb := Subcap.var (Γ := Γ) (x := x)
    rw [h] at hb
    exact hb
  have e : HasTy [] Γ (.path (.var x)) ((Γ.lookup x).shape ^ []) :=
    HasTy.sub HasTy.var (.capt .refl hv) hv
  have hT : (Γ.lookup x).shape ^ [] = Γ.lookup x := by
    rw [← h]
    exact (Ty.eta _).symm
  rw [hT] at e
  exact e

/-- The first view of a variable.  A binder declared at the empty set is used
at the empty set and keeps its declared type.  Any other binder is used at
`{x}` and has its declared shape at `{x}`, by `Var`. -/
def varView {s : Sig} (Γ : Ctx s) (x : BVar s .var) : View Γ x :=
  if h : (Γ.lookup x).captureSet = [] then ⟨[], Γ.lookup x, pureVar Γ x h⟩
  else ⟨[.var x], (Γ.lookup x).shape ^ [.var x], .var⟩

end CapturesFrontend
