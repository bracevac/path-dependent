import Coercions.DotMNF.WadlerFest.Syntax

/-!
# The published WadlerFest typing rules

The judgments follow Figures 1--2 of Amin et al. (2016). Ordinary contexts
store types in the complete current scope. Consequently an object self may
have its opened body `T`, which mentions that same self. There is no literal
metadata in these contexts. Lambda domains and let results omit the new
binder by construction. Distinct labels are checked at `AndDef-I`, as in the
published rules, rather than by an extra object-typing premise.

The source is intrinsically scoped, so this module does not formalize the
separate conversion from named paper syntax modulo alpha-equivalence.
-/

namespace WadlerFest

open FCdot (Kind Sig BVar Label)
open DotMNF (Ty)

/-- An ordinary context, represented extensionally in its current scope. -/
structure Ctx (s : Sig) where
  lookup : BVar s .var → Ty s

def Ctx.nil : Ctx [] := ⟨fun x => nomatch x⟩

/-- Extend by an opened type, which may mention its own new variable. -/
def Ctx.extend (Γ : Ctx s) (T : Ty (s,x)) : Ctx (s,x) where
  lookup
    | .here => T
    | .there y => (Γ.lookup y).weaken

/-- Ordinary nonrecursive binding. Its domain cannot mention the new binder. -/
def Ctx.cons (Γ : Ctx s) (T : Ty s) : Ctx (s,x) := Γ.extend T.weaken

mutual

inductive Sub : {s : Sig} → Ctx s → Ty s → Ty s → Type where
  | top : Sub Γ T .top
  | bot : Sub Γ .bot T
  | refl : Sub Γ T T
  | trans : Sub Γ S M → Sub Γ M T → Sub Γ S T
  | and1 : Sub Γ (.and S T) S
  | and2 : Sub Γ (.and S T) T
  | and : Sub Γ S T → Sub Γ S U → Sub Γ S (.and T U)
  | fld : Sub Γ T U → Sub Γ (.fld a T) (.fld a U)
  | typ : Sub Γ S₂ S₁ → Sub Γ T₁ T₂ → Sub Γ (.typ A S₁ T₁) (.typ A S₂ T₂)
  | selUpper : HasTy Γ (.path (.var x)) (.typ A S T) → Sub Γ (.sel (.var x) A) T
  | selLower : HasTy Γ (.path (.var x)) (.typ A S T) → Sub Γ S (.sel (.var x) A)
  | all : Sub Γ S₂ S₁ → Sub (Γ.cons S₂) T₁ T₂ → Sub Γ (.all S₁ T₁) (.all S₂ T₂)

inductive HasTy : {s : Sig} → Ctx s → Tm s → Ty s → Type where
  | var : HasTy Γ (.path (.var x)) (Γ.lookup x)
  | lam : HasTy (Γ.cons S) t T → HasTy Γ (.val (.lam S t)) (.all S T)
  | app :
      HasTy Γ (.path (.var x)) (.all S T) →
      HasTy Γ (.path (.var y)) S →
      HasTy Γ (.app x y) (T.substVar y)
  /-- The published opened-self object rule. -/
  | obj : DefsTy (Γ.extend T) d T → HasTy Γ (.val (.obj T d)) (.mu T)
  | proj : HasTy Γ (.path (.var x)) (.fld a T) → HasTy Γ (.proj x a) T
  | «let» : HasTy Γ t T → HasTy (Γ.cons T) u U.weaken → HasTy Γ (.let t u) U
  | recI : HasTy Γ (.path (.var x)) (T.substVar x) → HasTy Γ (.path (.var x)) (.mu T)
  | recE : HasTy Γ (.path (.var x)) (.mu T) → HasTy Γ (.path (.var x)) (T.substVar x)
  | andI :
      HasTy Γ (.path (.var x)) T → HasTy Γ (.path (.var x)) U →
      HasTy Γ (.path (.var x)) (.and T U)
  | sub : HasTy Γ t T → Sub Γ T U → HasTy Γ t U

inductive DefsTy : {s : Sig} → Ctx s → Defs s → Ty s → Type where
  | typ : DefsTy Γ (.typ A T) (.typ A T T)
  | trm : HasTy Γ t T → DefsTy Γ (.trm a t) (.fld a T)
  | and :
      DefsTy Γ d₁ T₁ → DefsTy Γ d₂ T₂ →
      (∀ ℓ, ℓ ∈ d₁.labels → ℓ ∉ d₂.labels) →
      DefsTy Γ (.and d₁ d₂) (.and T₁ T₂)

end

/-- Definition typing already supplies the local distinctness condition. -/
theorem DefsTy.eraseAnnotations_distinct :
    ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s}, DefsTy Γ d T →
      DotMNF.Defs.Distinct d.eraseAnnotations
  | _, _, _, _, .typ => .typ
  | _, _, _, _, .trm _ => .trm
  | _, _, _, _, .and h₁ h₂ hd => by
      exact .and h₁.eraseAnnotations_distinct h₂.eraseAnnotations_distinct
        (by simpa using hd)

end WadlerFest
