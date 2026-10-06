import Coercions.DotMNF.Syntax

/-!
# DOT-MNF typing

Subtyping, term typing and definition typing, as three mutually inductive
families.  They live in `Type`, not in `Prop`: the translation of Plan III
§8 is a function on derivations and therefore needs `Type`-valued
elimination.

One deviation from the surface presentation of §3.4: `{}-I` is stated as

```text
Γ, x : μ(x. T) ⊢ d : T   ⟹   Γ ⊢ ν(x. d) : μ(x. T)
```

rather than with the *opened* self type `T^x` as the binding for `x`.  With
intrinsic scoping a context entry lives in the signature *before* its own
binder, so `T^x` cannot be an entry. `Rec-E` derives the opened assumption
from this recursive binding. `WadlerFest/Correspondence` uses this fact to
translate derivations with opened self contexts to the representation here,
which matches `FCdot.Ctx` binder for binder.

Recursive introduction and elimination accept arbitrary bodies, including
functions, selections, intersections, and nested recursive types. The
translation enters or exits a self-bound telescope when the body is not a
declaration shape. Lambda annotations and let result types are unrestricted.

Object definitions may refer to their own self or form alias cycles. The
target's alias-tolerant resolution handles these witnesses.
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Contexts -/

/-- A context is a list of types, newest binder first.  A binder introduced
by an object literal remembers the literal's definitions (`consSelf`); its
type is `μ(x. T)` like any other binder, and `lookup` does not distinguish
the two.  The translation of Plan III §8 does: such a binder is typed at the
literal's precise type in the target. -/
inductive Ctx : Sig → Type where
  | nil : Ctx []
  | cons : Ctx s → Ty s → Ctx (s,x)
  | consSelf : Ctx s → Defs (s,x) → Ty (s,x) → Ctx (s,x)

/-- The type of a variable, weakened into the current scope. -/
def Ctx.lookup : Ctx s → BVar s .var → Ty s
  | .cons _ T, .here => T.weaken
  | .cons Γ _, .there y => (Γ.lookup y).weaken
  | .consSelf _ _ T, .here => (Ty.mu T).weaken
  | .consSelf Γ _ _, .there y => (Γ.lookup y).weaken

/-! ## The judgments -/

mutual

/-- Subtyping.  No `Rec` rule: recursion is `Rec-I`/`Rec-E` on variables. -/
inductive Sub : {s : Sig} → Ctx s → Ty s → Ty s → Type where
  | top : Sub Γ T .top
  | bot : Sub Γ .bot T
  | refl : Sub Γ T T
  | trans : Sub Γ S M → Sub Γ M T → Sub Γ S T
  | and1 : Sub Γ (.and S T) S
  | and2 : Sub Γ (.and S T) T
  | and : Sub Γ S T → Sub Γ S U → Sub Γ S (.and T U)
  | fld : Sub Γ T U → Sub Γ (.fld a T) (.fld a U)
  | typ : Sub Γ S2 S1 → Sub Γ T1 T2 → Sub Γ (.typ A S1 T1) (.typ A S2 T2)
  /-- `Sel-<:`. -/
  | selUpper : HasTy Γ (.path (.var x)) (.typ A S T) → Sub Γ (.sel (.var x) A) T
  /-- `<:-Sel`. -/
  | selLower : HasTy Γ (.path (.var x)) (.typ A S T) → Sub Γ S (.sel (.var x) A)
  | all : Sub Γ S2 S1 → Sub (Γ.cons S2) T1 T2 → Sub Γ (.all S1 T1) (.all S2 T2)

/-- Term typing. -/
inductive HasTy : {s : Sig} → Ctx s → Tm s → Ty s → Type where
  | var : HasTy Γ (.path (.var x)) (Γ.lookup x)
  /-- `All-I`. -/
  | lam : HasTy (Γ.cons S) t T → HasTy Γ (.val (.lam S t)) (.all S T)
  /-- `All-E`. -/
  | app :
      HasTy Γ (.path (.var x)) (.all S T) →
      HasTy Γ (.path (.var y)) S →
      HasTy Γ (.app x y) (T.substVar y)
  /-- `{}-I`.  The self binder remembers the definitions. -/
  | obj :
      DefsTy (Γ.consSelf d T) d T →
      Defs.Distinct d →
      HasTy Γ (.val (.obj d)) (.mu T)
  /-- `{}-E`. -/
  | proj : HasTy Γ (.path (.var x)) (.fld a T) → HasTy Γ (.proj x a) T
  | «let» :
      HasTy Γ t T →
      HasTy (Γ.cons T) u U.weaken →
      HasTy Γ (.let t u) U
  /-- `Rec-I`, for arbitrary recursive bodies. -/
  | recI :
      HasTy Γ (.path (.var x)) (T.substVar x) →
      HasTy Γ (.path (.var x)) (.mu T)
  /-- `Rec-E`, for arbitrary recursive bodies. -/
  | recE :
      HasTy Γ (.path (.var x)) (.mu T) →
      HasTy Γ (.path (.var x)) (T.substVar x)
  /-- `And-I`, on variables only. -/
  | andI :
      HasTy Γ (.path (.var x)) T →
      HasTy Γ (.path (.var x)) U →
      HasTy Γ (.path (.var x)) (.and T U)
  | sub : HasTy Γ t T → Sub Γ T U → HasTy Γ t U

/-- Definition typing. -/
inductive DefsTy : {s : Sig} → Ctx s → Defs s → Ty s → Type where
  | typ : DefsTy Γ (.typ A T) (.typ A T T)
  | trm : HasTy Γ t T → DefsTy Γ (.trm a t) (.fld a T)
  | and : DefsTy Γ d1 T1 → DefsTy Γ d2 T2 → DefsTy Γ (.and d1 d2) (.and T1 T2)

end

end DotMNF
