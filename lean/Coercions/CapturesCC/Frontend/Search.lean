import Coercions.CapturesCC.Frontend.Decide
import Coercions.CapturesCC.Frontend.Surface

/-!
# The first view of a variable, and the certificate of a level escape

A *view* of a context variable is a type the variable has, with its use set and
derivation.  The typer and the subtyping algorithm start from the first view,
`varView`.  A variable declared at the empty set is used at the empty set and
keeps its declared type.  Any other variable is used at `{x}` and has its
declared shape at `{x}`, by `Var`.  This is the least use set and the least
capture set the rules give a variable.

Every other type a variable has is reached from the first view on demand, by
the member lookup of `Look.lean` and by the `var` goal of `Sub.lean`.

`escape_rejected_at` is the certificate carried by a rejection through a level
escape.  It is the contrapositive of the version's `source_lvl_safety`.
-/

namespace CapturesCCFrontend

open CapturesCC.FCdot (Kind Sig BVar Rename Label)
open CapturesCC.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Dom Cod Defs Ctx Sub SubShape Subcap
  ESub HasTy)
open scoped CapturesCC.DotMNF

/-! ## Views -/

/-- A type a context variable has, at a use set, with the derivation. -/
structure View {s : Sig} (Γ : Ctx s) (x : BVar s .var) where
  /-- The use set. -/
  uses : CaptureSet s
  /-- The type. -/
  ty : Ty s
  /-- The derivation. -/
  deriv : HasTy uses Γ (.path (.var x)) (.ty ty)

/-- A pure binder at its declared type, at the empty use set.  `Var` concludes
at `{x}` for both sets, and `sc-var` takes both down to the declared set, which
is empty. -/
def pureVar {s : Sig} (Γ : Ctx s) (x : BVar s .var) (h : (Γ.lookup x).captureSet = []) :
    HasTy [] Γ (.path (.var x)) (.ty (Γ.lookup x)) := by
  have hv : Subcap Γ [CapAtom.var x] ([] : CaptureSet s) := by
    have hb := Subcap.var (Γ := Γ) (x := x)
    rw [h] at hb
    exact hb
  have e : HasTy [] Γ (.path (.var x)) (.ty ((Γ.lookup x).shape ^ [])) :=
    HasTy.sub HasTy.var (.ty (.capt .refl hv)) hv
  have hT : (Γ.lookup x).shape ^ [] = Γ.lookup x := by
    rw [← h]
    exact (Ty.eta _).symm
  rw [hT] at e
  exact e

/-- The first view of a variable, at the least use set and capture set the
rules give it. -/
def varView {s : Sig} (Γ : Ctx s) (x : BVar s .var) : View Γ x :=
  if h : (Γ.lookup x).captureSet = [] then ⟨[], Γ.lookup x, pureVar Γ x h⟩
  else ⟨[.var x], (Γ.lookup x).shape ^ [.var x], .var⟩

/-! ## A rejection certificate

Failure of the search does not show that no derivation exists.  The level rule
is the one rule that relates a binder to a root, and its failure has a semantic
witness.  `source_lvl_safety`
(`lean/Coercions/CapturesCC/DotToFCdot/EvidenceTyped.lean`) says that a
member-free subcapturing keeps every resolved atom of `C` confined to whatever
atom `r` confines every resolved atom of `D`.  So a depth `n` at which the
resolution of `C` is not confined to `r`, while that of `D` is at every depth,
rules out every member-free derivation of `C <: D`.  The statement holds for any
target set and any atom of the target, so it also decides the escape at the top
of a program, where `r` is the target's universal root. -/

/-- No member-free subcapturing puts `C` below `D` when `D` is confined to
`r` at every depth and `C` is not at one depth `n`. -/
theorem escape_rejected_at {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} (hwf : Γ.Wf)
    (r : CapturesCC.FCdot.CapAtom s)
    (hD : ∀ m, Γ.translate.Confined (Γ.translate.caps m D.translate) r)
    (n : Nat) (hn : ¬ Γ.translate.Confined (Γ.translate.caps n C.translate) r) :
    ¬ ∃ d : Subcap Γ C D, d.MemberFree :=
  fun ⟨_, hd⟩ => hn (CapturesCC.DotMNF.source_lvl_safety hwf hd hD n)

end CapturesCCFrontend
