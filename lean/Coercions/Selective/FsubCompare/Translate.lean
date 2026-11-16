import Coercions.Selective.Fsub
import Coercions.FCsub
/-!
# Plain F-sub inside FCsub

A mechanical embedding of SelFsub's syntax (types, contexts, declarative derivations
`Sub`) into FCsub's, used only to generate the FCsub side of the comparison. Nothing here
is a theorem about FCsub; the evidence it produces is checked by FCsub's own `synthLe`.

Encoding of one F-sub bound `X <: B` in FCsub's heterogeneous scope: a type binder
followed by an inclusion-evidence binder (`Sg (n+1) = incl :: type :: Sg n`); the bound
is the type of the evidence binder `h : X <: B`. A bounded universal is `forallT` over a
telescope with one name and one inclusion; an arrow is `arr` with a (vacuous) term binder
in the codomain.
-/
namespace Compare

/-- The FCsub scope of a SelFsub context with `n` bounded type variables. -/
@[reducible] def Sg : Nat → FCsub.Sig
  | 0 => []
  | n+1 => (FCsub.BinderKind.evidence .inclusion) :: FCsub.BinderKind.type :: Sg n

def tvarOf : (n : Nat) → Fin n → FCsub.BVar (Sg n) .type
  | _+1, ⟨0, _⟩ => .there .here
  | n+1, ⟨i+1, h⟩ => .there (.there (tvarOf n ⟨i, by omega⟩))

def evOf : (n : Nat) → Fin n → FCsub.BVar (Sg n) (.evidence .inclusion)
  | _+1, ⟨0, _⟩ => .here
  | n+1, ⟨i+1, h⟩ => .there (.there (evOf n ⟨i, by omega⟩))

def tyOf : {n : Nat} → SelFsub.Ty n → FCsub.Ty (Sg n)
  | _, .top => .top
  | n, .var x => .tvar (tvarOf n x)
  | _, .arr A B => .arr (tyOf A) (tyOf B).weaken
  | _, .all A B =>
    .forallT (names := 1) (constraints := 1)
      (.snoc .nil (.inclusion (.tvar .here) (tyOf A).weaken)) (tyOf B)

def ctxOf : {n : Nat} → SelFsub.Ctx n → FCsub.Ctx (Sg n)
  | _, .nil => .nil
  | _, .snoc Γ A => ((ctxOf Γ).extendType).extendInclusion (.tvar .here) (tyOf A).weaken

/-- The telescope `X <: A` as an FCsub telescope in scope `Sg n`. -/
def telOf {n : Nat} (A : SelFsub.Ty n) : FCsub.Telescope (Sg n) 1 1 :=
  .snoc .nil (.inclusion (.tvar .here) (tyOf A).weaken)

/-- Translation of a declarative F-sub derivation into FCsub evidence. -/
def leOf : {n : Nat} → {Γ : SelFsub.Ctx n} → {S T : SelFsub.Ty n} →
    SelFsub.Sub Γ S T → FCsub.LeCo (Sg n)
  | _, _, _, _, .refl (A := A) => .refl (tyOf A)
  | _, _, _, _, .top (A := A) => .top (tyOf A)
  | n, _, _, _, .bound x => .var (evOf n x)
  | _, _, _, _, .trans h₁ h₂ => .trans (leOf h₁) (leOf h₂)
  | _, _, _, _, .arr h₁ h₂ => .arr (leOf h₁) (leOf h₂).weaken
  | _, _, _, _, .all (A₁ := A₁) (B₁ := B₁) (A₂ := A₂) (B₂ := B₂) h₁ h₂ =>
    .forallT
      (.map (telOf B₁) (telOf A₁)
        (.snoc .nil (.tvar (.there .here)))
        (.snoc .nil (.trans (.var .here) (leOf h₁).weaken.weaken)))
      (tyOf A₂) (tyOf B₂) (leOf h₂)

end Compare
