import Coercions.Classifiers.Frontend.Decide
import Coercions.Classifiers.Frontend.Surface

/-!
# The first view of a variable, and the certificate of a level escape

A *view* of a context variable is a type the variable has, with its use set
and derivation.  `varView` is the first view, the one the typer and the
subtyping algorithm start from.  A variable declared at the empty set is used
at the empty set and keeps its declared type.  Any other variable is used at
`{x}` with its declared shape at `{x}`, by `Var`.

Other types of a variable are reached on demand, by the member lookup of
`Look.lean` and the `var` goal of `Sub.lean`.

`escape_rejected_at` is the certificate carried by a rejection for a level
escape.  It is the contrapositive of `source_lvl_safety`.
-/

namespace ClassifiersFrontend

open Classifiers.FCdot (Kind Sig BVar Rename Label)
open Classifiers.DotMNF (Path CapAtom CaptureSet Shape Ty ETy Dom Cod Defs Ctx Sub SubShape Subcap
  ESub HasTy)
open scoped Classifiers.DotMNF

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
at `{x}`, and `sc-var` takes that down to the declared set, which is empty. -/
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

A failed search does not show that no derivation exists.  The level rule is the
one rule that relates a binder to a root, and its failure has a semantic
witness.  `source_lvl_safety`
(`lean/Coercions/Classifiers/DotToFCdot/EvidenceTyped.lean`) says that a
member-free subcapturing keeps every resolved atom of `C` confined to whatever
atom `r` confines every resolved atom of `D`.  So one depth `n` at which the
resolution of `C` is not confined to `r`, while that of `D` is at every depth,
rules out every member-free derivation of `C <: D`.  The statement holds for
any atom `r`, so it also decides the escape at the top of a program, where `r`
is the universal root. -/

/-- No member-free subcapturing puts `C` below `D` when `D` is confined to
`r` at every depth and `C` is not at one depth `n`. -/
theorem escape_rejected_at {s : Sig} {Γ : Ctx s} {C D : CaptureSet s} (hwf : Γ.Wf)
    (r : Classifiers.FCdot.CapAtom s)
    (hD : ∀ m, Γ.translate.Confined (Γ.translate.caps m D.translate) r)
    (n : Nat) (hn : ¬ Γ.translate.Confined (Γ.translate.caps n C.translate) r) :
    ¬ ∃ d : Subcap Γ C D, d.MemberFree :=
  fun ⟨_, hd⟩ => hn (Classifiers.DotMNF.source_lvl_safety hwf hd hD n)

end ClassifiersFrontend
