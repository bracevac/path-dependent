import Coercions.DotMNF.Syntax

/-!
# Annotated WadlerFest DOT syntax

This is an intrinsically scoped presentation of Figures 1--2 of Amin et al.,
*The Essence of Dependent Object Types* (WadlerFest 2016), revised version:
https://namin.seas.harvard.edu/files/dot_wadlerfest.pdf.

Types, variable paths, and labels are shared with `DotMNF`. Object values retain
the published self annotation: both the annotation and definitions are scoped
under the self binder. `eraseAnnotations` removes only object annotations.

As in DOT-MNF, constructors accept any `Label`; the intended published
fragment uses `.typ` for type labels and `.trm` for term labels. Those tag
restrictions are not enforced by the shared type syntax.
-/

namespace WadlerFest

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ty Path)

mutual

inductive Tm : Sig → Type where
  | path : Path s → Tm s
  | val : Value s → Tm s
  | app : BVar s .var → BVar s .var → Tm s
  | proj : BVar s .var → Label → Tm s
  | «let» : Tm s → Tm (s,x) → Tm s

inductive Value : Sig → Type where
  | obj : Ty (s,x) → Defs (s,x) → Value s
  | lam : Ty s → Tm (s,x) → Value s

inductive Defs : Sig → Type where
  | typ : Label → Ty s → Defs s
  | trm : Label → Tm s → Defs s
  | and : Defs s → Defs s → Defs s

end

mutual

def Tm.rename : Tm s₁ → Rename s₁ s₂ → Tm s₂
  | .path p, ρ => .path (p.rename ρ)
  | .val v, ρ => .val (v.rename ρ)
  | .app x y, ρ => .app (ρ.var x) (ρ.var y)
  | .proj x a, ρ => .proj (ρ.var x) a
  | .let t u, ρ => .let (t.rename ρ) (u.rename ρ.lift)

def Value.rename : Value s₁ → Rename s₁ s₂ → Value s₂
  | .obj T d, ρ => .obj (T.rename ρ.lift) (d.rename ρ.lift)
  | .lam S t, ρ => .lam (S.rename ρ) (t.rename ρ.lift)

def Defs.rename : Defs s₁ → Rename s₁ s₂ → Defs s₂
  | .typ A T, ρ => .typ A (T.rename ρ)
  | .trm a t, ρ => .trm a (t.rename ρ)
  | .and d₁ d₂, ρ => .and (d₁.rename ρ) (d₂.rename ρ)

end

def Tm.substVar (t : Tm (s,x)) (y : BVar s .var) : Tm s :=
  t.rename (Rename.subst y)

def Defs.substVar (d : Defs (s,x)) (y : BVar s .var) : Defs s :=
  d.rename (Rename.subst y)

def Defs.labels : Defs s → List Label
  | .typ A _ => [A]
  | .trm a _ => [a]
  | .and d₁ d₂ => d₁.labels ++ d₂.labels

mutual

def Tm.eraseAnnotations : Tm s → DotMNF.Tm s
  | .path p => .path p
  | .val v => .val v.eraseAnnotations
  | .app x y => .app x y
  | .proj x a => .proj x a
  | .let t u => .let t.eraseAnnotations u.eraseAnnotations

def Value.eraseAnnotations : Value s → DotMNF.Value s
  | .obj _ d => .obj d.eraseAnnotations
  | .lam S t => .lam S t.eraseAnnotations

def Defs.eraseAnnotations : Defs s → DotMNF.Defs s
  | .typ A T => .typ A T
  | .trm a t => .trm a t.eraseAnnotations
  | .and d₁ d₂ => .and d₁.eraseAnnotations d₂.eraseAnnotations

end

@[simp] theorem Defs.labels_eraseAnnotations : ∀ {s : Sig} (d : Defs s),
    d.eraseAnnotations.labels = d.labels
  | _, .typ _ _ => rfl
  | _, .trm _ _ => rfl
  | _, .and d₁ d₂ => by
      simp only [Defs.eraseAnnotations, DotMNF.Defs.labels, Defs.labels,
        Defs.labels_eraseAnnotations d₁, Defs.labels_eraseAnnotations d₂]

mutual

@[simp] theorem Tm.eraseAnnotations_rename (t : Tm s₁) (ρ : Rename s₁ s₂) :
    (t.rename ρ).eraseAnnotations = t.eraseAnnotations.rename ρ := by
  cases t with
  | path => rfl
  | val v => exact congrArg DotMNF.Tm.val (Value.eraseAnnotations_rename v ρ)
  | app => rfl
  | proj => rfl
  | «let» t u =>
      simp only [Tm.rename, Tm.eraseAnnotations, DotMNF.Tm.rename,
        Tm.eraseAnnotations_rename t ρ, Tm.eraseAnnotations_rename u ρ.lift]

@[simp] theorem Value.eraseAnnotations_rename (v : Value s₁) (ρ : Rename s₁ s₂) :
    (v.rename ρ).eraseAnnotations = v.eraseAnnotations.rename ρ := by
  cases v with
  | obj T d => exact congrArg DotMNF.Value.obj (Defs.eraseAnnotations_rename d ρ.lift)
  | lam S t =>
      exact congrArg (DotMNF.Value.lam (S.rename ρ)) (Tm.eraseAnnotations_rename t ρ.lift)

@[simp] theorem Defs.eraseAnnotations_rename (d : Defs s₁) (ρ : Rename s₁ s₂) :
    (d.rename ρ).eraseAnnotations = d.eraseAnnotations.rename ρ := by
  cases d with
  | typ => rfl
  | trm a t => exact congrArg (DotMNF.Defs.trm a) (Tm.eraseAnnotations_rename t ρ)
  | and d₁ d₂ =>
      simp only [Defs.rename, Defs.eraseAnnotations, DotMNF.Defs.rename,
        Defs.eraseAnnotations_rename d₁ ρ, Defs.eraseAnnotations_rename d₂ ρ]

end

@[simp] theorem Tm.eraseAnnotations_substVar (t : Tm (s,x)) (y : BVar s .var) :
    (t.substVar y).eraseAnnotations = t.eraseAnnotations.substVar y :=
  t.eraseAnnotations_rename (Rename.subst y)

@[simp] theorem Defs.eraseAnnotations_substVar (d : Defs (s,x)) (y : BVar s .var) :
    (d.substVar y).eraseAnnotations = d.eraseAnnotations.substVar y :=
  d.eraseAnnotations_rename (Rename.subst y)

end WadlerFest
