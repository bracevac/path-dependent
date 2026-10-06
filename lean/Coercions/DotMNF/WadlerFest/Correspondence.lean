import Coercions.DotMNF.WadlerFest.Typing
import Coercions.DotMNF.Structural

/-!
# From annotated WadlerFest DOT to DOT-MNF

Every derivation of the annotated calculus translates to a DOT-MNF derivation
after removing object annotations. The proof accounts explicitly for the
different self contexts: an opened assumption `self : T` is simulated by
recursive elimination from the local assumption `self : μ T`.

Context simulation supplies a typing derivation for every ordinary source
assumption. It does not assume lookup equality, inertness, good bounds, or
acyclic definitions. The empty-context corollary covers every closed typed
program of the independently stated annotated rules.
-/

namespace WadlerFest

open FCdot (Sig BVar Rename)
open DotMNF (Ty)

/-- Each published assumption is derivable in the local context. -/
def Ctx.Simulates (Γ : Ctx s) (Δ : DotMNF.Ctx s) : Type :=
  ∀ y, DotMNF.HasTy Δ (.path (.var y)) (Γ.lookup y)

def Ctx.Simulates.nil : Ctx.nil.Simulates DotMNF.Ctx.nil := fun y => nomatch y

def Ctx.Simulates.cons {Γ : Ctx s} {Δ : DotMNF.Ctx s}
    (h : Γ.Simulates Δ) (S : Ty s) : (Γ.cons S).Simulates (Δ.cons S) := by
  intro y
  cases y with
  | here => exact .var
  | there y => exact (h y).weaken S

/-- The body assumption is obtained by one use of recursive elimination. -/
def Ctx.Simulates.self {Γ : Ctx s} {Δ : DotMNF.Ctx s}
    (h : Γ.Simulates Δ) (d : DotMNF.Defs (s,x)) (T : Ty (s,x)) :
    (Γ.extend T).Simulates (Δ.consSelf d T) := by
  intro y
  cases y with
  | here =>
      have hu : DotMNF.HasTy (Δ.consSelf d T) (.path (.var .here))
          ((T.rename Rename.succ.lift).substVar .here) := .recE .var
      simpa only [DotMNF.Ty.open_self] using hu
  | there y => exact (h y).weakenSelf d T

mutual

/-- Subtyping correspondence under derivable source assumptions. -/
def Sub.eraseAnnotations {Γ : Ctx s} {S T : Ty s} (h : Sub Γ S T)
    {Δ : DotMNF.Ctx s} (hΓ : Γ.Simulates Δ) : DotMNF.Sub Δ S T :=
  match h with
  | .top => .top
  | .bot => .bot
  | .refl => .refl
  | .trans h₁ h₂ => .trans (h₁.eraseAnnotations hΓ) (h₂.eraseAnnotations hΓ)
  | .and1 => .and1
  | .and2 => .and2
  | .and h₁ h₂ => .and (h₁.eraseAnnotations hΓ) (h₂.eraseAnnotations hΓ)
  | .fld h => .fld (h.eraseAnnotations hΓ)
  | .typ h₁ h₂ => .typ (h₁.eraseAnnotations hΓ) (h₂.eraseAnnotations hΓ)
  | .selUpper h => .selUpper (h.eraseAnnotations hΓ)
  | .selLower h => .selLower (h.eraseAnnotations hΓ)
  | .all h₁ h₂ => .all (h₁.eraseAnnotations hΓ) (h₂.eraseAnnotations (hΓ.cons _))

/-- Annotation erasure preserves every published term-typing derivation. -/
def HasTy.eraseAnnotations {Γ : Ctx s} {t : Tm s} {T : Ty s} (h : HasTy Γ t T)
    {Δ : DotMNF.Ctx s} (hΓ : Γ.Simulates Δ) :
    DotMNF.HasTy Δ t.eraseAnnotations T :=
  match h with
  | .var => hΓ _
  | .lam h => .lam (h.eraseAnnotations (hΓ.cons _))
  | .app h₁ h₂ => .app (h₁.eraseAnnotations hΓ) (h₂.eraseAnnotations hΓ)
  | .obj h => .obj (h.eraseAnnotations (hΓ.self _ _)) h.eraseAnnotations_distinct
  | .proj h => .proj (h.eraseAnnotations hΓ)
  | .let h₁ h₂ => .let (h₁.eraseAnnotations hΓ) (h₂.eraseAnnotations (hΓ.cons _))
  | .recI h => .recI (h.eraseAnnotations hΓ)
  | .recE h => .recE (h.eraseAnnotations hΓ)
  | .andI h₁ h₂ => .andI (h₁.eraseAnnotations hΓ) (h₂.eraseAnnotations hΓ)
  | .sub h₁ h₂ => .sub (h₁.eraseAnnotations hΓ) (h₂.eraseAnnotations hΓ)

/-- Definition correspondence; distinctness is retained separately above. -/
def DefsTy.eraseAnnotations {Γ : Ctx s} {d : Defs s} {T : Ty s} (h : DefsTy Γ d T)
    {Δ : DotMNF.Ctx s} (hΓ : Γ.Simulates Δ) :
    DotMNF.DefsTy Δ d.eraseAnnotations T :=
  match h with
  | .typ => .typ
  | .trm h => .trm (h.eraseAnnotations hΓ)
  | .and h₁ h₂ _ => .and (h₁.eraseAnnotations hΓ) (h₂.eraseAnnotations hΓ)

end

/-- Every closed annotated program is accepted by the local source calculus. -/
def HasTy.eraseAnnotations_closed {t : Tm []} {T : Ty []} (h : HasTy .nil t T) :
    DotMNF.HasTy .nil t.eraseAnnotations T := h.eraseAnnotations .nil

end WadlerFest
